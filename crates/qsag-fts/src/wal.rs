//! Authenticated append-only burn journal with descriptor-lifetime locking.
//! V3 binds the genesis MAC to the data inode; copied or legacy V2 journals fail closed.
//! Recovery fails closed on missing files and incomplete records. Keep the directory
//! private and use rollback-resistant storage: a complete old authenticated snapshot
//! cannot be distinguished from current state without an external monotonic anchor.
use qsag_accel::ct::{RedactedSecret, ct_eq_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

const MAGIC: &[u8; 8] = b"QSBURN03";
const HEADER_LEN: usize = 104;
const RECORD_LEN: usize = 42;

pub struct DurableBurnJournal {
    path: PathBuf,
    file: File,
    key: [u8; 32],
    genesis: [u8; 32],
    last_tag: [u8; 32],
    mac_key: RedactedSecret<32>,
    entries: BTreeSet<(u16, u64)>,
    failed: bool,
}
fn invalid() -> io::Error {
    io::Error::other("invalid, truncated, replaced, or locked burn journal")
}
fn private_file(path: &Path) -> io::Result<OpenOptions> {
    if fs::symlink_metadata(path).is_ok_and(|m| m.file_type().is_symlink()) {
        return Err(invalid());
    }
    let mut opts = OpenOptions::new();
    opts.read(true).append(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.mode(0o600);
        #[cfg(target_os = "linux")]
        opts.custom_flags(if cfg!(any(target_arch = "aarch64", target_arch = "arm")) { 0x8000 } else { 0x20000 } | 0x800); // O_NOFOLLOW | O_NONBLOCK
        #[cfg(target_os = "macos")]
        opts.custom_flags(0x0100 | 0x4); // O_NOFOLLOW | O_NONBLOCK
    }
    Ok(opts)
}
fn file_identity(file: &File) -> io::Result<[u8; 16]> {
    let metadata = file.metadata()?;
    if !metadata.is_file() { return Err(invalid()); }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let mut identity = [0; 16];
        identity[..8].copy_from_slice(&metadata.dev().to_be_bytes());
        identity[8..].copy_from_slice(&metadata.ino().to_be_bytes());
        Ok(identity)
    }
    #[cfg(not(unix))]
    Err(invalid())
}

impl DurableBurnJournal {
    /// Explicit epoch-zero provisioning. Never use this to recover an active key.
    /// Existing files, including incomplete provisioning attempts, are rejected.
    pub fn create(path: impl AsRef<Path>, key: [u8; 32], mac_key: [u8; 32]) -> io::Result<Self> {
        Self::load(path.as_ref(), key, mac_key, true)
    }
    /// Recover an existing authenticated journal; missing files are an error.
    pub fn open_existing(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
    ) -> io::Result<Self> {
        Self::load(path.as_ref(), key, mac_key, false)
    }
    /// Compatibility alias for existing-vault recovery only.
    pub fn open(path: impl AsRef<Path>, key: [u8; 32], mac_key: [u8; 32]) -> io::Result<Self> {
        Self::open_existing(path, key, mac_key)
    }
    fn load(path: &Path, key: [u8; 32], mac_key: [u8; 32], create: bool) -> io::Result<Self> {
        let mut options = private_file(path)?;
        if create {
            options.create_new(true);
        }
        let file = options.open(path)?;
        let identity = file_identity(&file)?;
        file.try_lock().map_err(|_| invalid())?;
        let mut journal = Self {
            path: path.to_path_buf(),
            file,
            key,
            genesis: [0; 32],
            last_tag: [0; 32],
            mac_key: RedactedSecret::new(mac_key),
            entries: BTreeSet::new(),
            failed: false,
        };
        if create {
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_err(|_| invalid())?
                .as_nanos()
                .to_be_bytes();
            // Uniqueness salt, not secret entropy; authentication uses mac_key.
            journal.genesis = cshake256_framed_32(
                b"QSAG.BURN.GENESIS.ID.V2",
                &[
                    journal.mac_key.expose(),
                    &key,
                    &now,
                    &std::process::id().to_be_bytes(),
                ],
            );
            let mut header = MAGIC.to_vec();
            header.extend_from_slice(&key);
            header.extend_from_slice(&journal.genesis);
            journal.last_tag = cshake256_framed_32(
                b"QSAG.BURN.GENESIS.V3",
                &[journal.mac_key.expose(), &identity, &header],
            );
            header.extend_from_slice(&journal.last_tag);
            journal.file.write_all(&header)?;
            journal.file.sync_all()?;
            #[cfg(unix)]
            File::open(
                path.parent()
                    .filter(|p| !p.as_os_str().is_empty())
                    .unwrap_or(Path::new(".")),
            )?
            .sync_all()?;
        } else {
            let mut bytes = std::vec::Vec::new();
            journal.file.read_to_end(&mut bytes)?;
            if bytes.len() < HEADER_LEN
                || !(bytes.len() - HEADER_LEN).is_multiple_of(RECORD_LEN)
                || &bytes[..8] != MAGIC
                || bytes[8..40] != key
            {
                return Err(invalid());
            }
            journal.genesis.copy_from_slice(&bytes[40..72]);
            journal.last_tag = cshake256_framed_32(
                b"QSAG.BURN.GENESIS.V3",
                &[journal.mac_key.expose(), &identity, &bytes[..72]],
            );
            if !ct_eq_bytes(&journal.last_tag, &bytes[72..104]) {
                return Err(invalid());
            }
            for record in bytes[HEADER_LEN..].as_chunks::<RECORD_LEN>().0 {
                let tag = journal.record_tag(&record[..10]);
                if !ct_eq_bytes(&tag, &record[10..]) {
                    return Err(invalid());
                }
                let party = u16::from_be_bytes(record[..2].try_into().map_err(|_| invalid())?);
                let epoch = u64::from_be_bytes(record[2..10].try_into().map_err(|_| invalid())?);
                if !journal.entries.insert((party, epoch)) {
                    return Err(invalid());
                }
                journal.last_tag = tag;
            }
        }
        journal.check_identity()?;
        Ok(journal)
    }
    fn record_tag(&self, record: &[u8]) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.BURN.RECORD.V2",
            &[
                self.mac_key.expose(),
                &self.key,
                &self.genesis,
                &self.last_tag,
                record,
            ],
        )
    }
    fn check_identity(&self) -> io::Result<()> {
        let metadata = fs::symlink_metadata(&self.path)?;
        if !metadata.is_file() {
            return Err(invalid());
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            let held = self.file.metadata()?;
            if metadata.dev() != held.dev() || metadata.ino() != held.ino() {
                return Err(invalid());
            }
        }
        if metadata.len() != (HEADER_LEN + RECORD_LEN * self.entries.len()) as u64 {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn reserve(&mut self, key: &[u8; 32], party: u16, epoch: u64) -> io::Result<()> {
        if self.failed || key != &self.key || self.entries.contains(&(party, epoch)) {
            return Err(invalid());
        }
        self.failed = true;
        self.check_identity()?;
        let mut record = [0; RECORD_LEN];
        record[..2].copy_from_slice(&party.to_be_bytes());
        record[2..10].copy_from_slice(&epoch.to_be_bytes());
        let tag = self.record_tag(&record[..10]);
        record[10..].copy_from_slice(&tag);
        self.file.write_all(&record)?;
        self.file.sync_all()?;
        self.entries.insert((party, epoch));
        self.last_tag = tag;
        self.check_identity()?;
        self.failed = false;
        Ok(())
    }
}
/// A successful reservation permanently spends exactly one WOTS leaf.
pub struct FsWalFtsEpochLatch(pub DurableBurnJournal);
impl FsWalFtsEpochLatch {
    pub fn create(path: impl AsRef<Path>, key: [u8; 32], mac_key: [u8; 32]) -> io::Result<Self> {
        DurableBurnJournal::create(path, key, mac_key).map(Self)
    }
    pub fn open(path: impl AsRef<Path>, key: [u8; 32], mac_key: [u8; 32]) -> io::Result<Self> {
        DurableBurnJournal::open(path, key, mac_key).map(Self)
    }
}
impl super::LeafBurnPersistence for FsWalFtsEpochLatch {
    fn burn_epoch_before_sign(
        &mut self,
        key: &[u8; 32],
        party: u16,
        epoch: u32,
        count: u8,
    ) -> Result<(), super::ParallelSeededError> {
        if count != 1 {
            return Err(super::ParallelSeededError::EpochUseBudgetExhausted);
        }
        self.0
            .reserve(key, party, u64::from(epoch))
            .map_err(|_| super::ParallelSeededError::PersistenceFailed)
    }
}

impl super::frontier::FtsEpochWal for FsWalFtsEpochLatch {
    fn uses_completed(&self, key: &[u8; 32]) -> Result<u8, super::FrontierFtsError> {
        if self.0.failed || key != &self.0.key || self.0.check_identity().is_err() {
            return Err(super::FrontierFtsError::PersistenceFailed);
        }
        let mut used = 0u8;
        for &(party, epoch) in &self.0.entries {
            if party != 0 || epoch != u64::from(used) { return Err(super::FrontierFtsError::PersistenceFailed); }
            used = used.checked_add(1).ok_or(super::FrontierFtsError::PersistenceFailed)?;
        }
        Ok(used)
    }
    fn reserve_use(&mut self, key: &[u8; 32], next: u8) -> Result<(), super::FrontierFtsError> {
        if next == 0 || self.uses_completed(key)? != next - 1 { return Err(super::FrontierFtsError::PersistenceFailed); }
        self.0.reserve(key, 0, u64::from(next - 1)).map_err(|_| super::FrontierFtsError::PersistenceFailed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn copied_journal_cannot_create_second_authority() {
        let path = std::env::temp_dir().join(std::format!("burn-copy-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let copy = path.with_extension("copy");
        let mut original = DurableBurnJournal::create(&path, [1; 32], [2; 32]).unwrap();
        original.reserve(&[1; 32], 1, 0).unwrap();
        fs::copy(&path, &copy).unwrap();
        assert!(DurableBurnJournal::open_existing(&copy, [1; 32], [2; 32]).is_err());
        drop(original);
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_ok());
        fs::remove_file(path).unwrap();
        fs::remove_file(copy).unwrap();
    }

    #[test]
    fn frontier_use_is_burned_across_regeneration() {
        let path = std::env::temp_dir().join(std::format!("frontier-restart-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let make = || crate::FrontierFtsSigningKey::keygen(crate::FrontierFtsProfile::Fast256Test, [1; 32], [2; 32], [3; 32], true, &qsag_accel::CpuReferenceBackend);
        let key = make();
        let id = key.wal_key();
        let wal = FsWalFtsEpochLatch::create(&path, id, [8; 32]).unwrap();
        let mut key = key.attach_wal(alloc::boxed::Box::new(wal)).unwrap();
        let dp = crate::FrontierDpTable::build(crate::FrontierFtsProfile::Fast256Test);
        let signature = key.sign(&dp, b"first", &[0; 32]).unwrap();
        crate::verify_frontier_fts(&key.pk, &dp, b"first", &signature).unwrap();
        drop(key);
        let wal = FsWalFtsEpochLatch::open(&path, id, [8; 32]).unwrap();
        let mut key = make().attach_wal(alloc::boxed::Box::new(wal)).unwrap();
        assert_eq!(key.sign(&dp, b"second", &[0; 32]), Err(crate::FrontierFtsError::UseBudgetExhausted));
        drop(key);
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn frontier_recovers_vault_reservation_before_wal_append() {
        let path = std::env::temp_dir().join(std::format!("frontier-gap-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let make = || crate::FrontierFtsSigningKey::keygen(crate::FrontierFtsProfile::Compact770, [1; 32], [2; 32], [3; 32], true, &qsag_accel::CpuReferenceBackend);
        let id = make().wal_key();
        drop(FsWalFtsEpochLatch::create(&path, id, [8; 32]).unwrap());
        // Simulate a crash after the vault committed use 1, before the WAL did.
        let wal = FsWalFtsEpochLatch::open(&path, id, [8; 32]).unwrap();
        let key = make().resume_at(1).unwrap().attach_wal(alloc::boxed::Box::new(wal)).unwrap();
        assert_eq!(key.uses_completed(), 1);
        drop(key);
        let wal = FsWalFtsEpochLatch::open(&path, id, [8; 32]).unwrap();
        let mut key = make().attach_wal(alloc::boxed::Box::new(wal)).unwrap();
        assert_eq!(key.uses_completed(), 1);
        let dp = crate::FrontierDpTable::build(crate::FrontierFtsProfile::Compact770);
        let signature = key.sign(&dp, b"after recovery", &[0; 32]).unwrap();
        crate::verify_frontier_fts(&key.pk, &dp, b"after recovery", &signature).unwrap();
        assert_eq!(key.uses_completed(), 2);
        assert_eq!(key.sign(&dp, b"exhausted", &[0; 32]), Err(crate::FrontierFtsError::UseBudgetExhausted));
        drop(key);
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn authenticated_recovery_and_descriptor_lock() {
        let dir = std::env::temp_dir().join(std::format!(
            "qsag-burn-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&dir).unwrap();
        let path = dir.join("journal");
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        let mut journal = DurableBurnJournal::create(&path, [1; 32], [2; 32]).unwrap();
        assert!(DurableBurnJournal::create(&path, [1; 32], [2; 32]).is_err());
        journal.reserve(&[1; 32], 7, 19).unwrap();
        // A sidecar's absence cannot affect the lock held on the journal itself.
        assert!(!dir.join("journal.lock").exists());
        assert!(DurableBurnJournal::open(&path, [1; 32], [2; 32]).is_err());
        drop(journal);
        let mut journal = DurableBurnJournal::open(&path, [1; 32], [2; 32]).unwrap();
        assert!(journal.reserve(&[1; 32], 7, 19).is_err());
        drop(journal);
        assert!(DurableBurnJournal::open(&path, [3; 32], [2; 32]).is_err());
        assert!(DurableBurnJournal::open(&path, [1; 32], [3; 32]).is_err());
        let original = fs::read(&path).unwrap();
        for len in [0, 40, HEADER_LEN - 1, original.len() - 1] {
            fs::write(&path, &original[..len]).unwrap();
            assert!(DurableBurnJournal::open(&path, [1; 32], [2; 32]).is_err());
        }
        for index in [8, 40, 72, HEADER_LEN, original.len() - 1] {
            let mut corrupt = original.clone();
            corrupt[index] ^= 1;
            fs::write(&path, corrupt).unwrap();
            assert!(DurableBurnJournal::open(&path, [1; 32], [2; 32]).is_err());
        }
        fs::write(&path, &original).unwrap();
        #[cfg(unix)]
        {
            let link = dir.join("link");
            std::os::unix::fs::symlink(&path, &link).unwrap();
            assert!(DurableBurnJournal::open(&link, [1; 32], [2; 32]).is_err());
            fs::remove_file(link).unwrap();
            let mut held = DurableBurnJournal::open(&path, [1; 32], [2; 32]).unwrap();
            fs::rename(&path, dir.join("old")).unwrap();
            fs::write(&path, &original).unwrap();
            assert!(held.reserve(&[1; 32], 7, 20).is_err());
            drop(held);
            fs::remove_file(dir.join("old")).unwrap();
        }
        fs::remove_file(&path).unwrap();
        assert!(DurableBurnJournal::open(&path, [1; 32], [2; 32]).is_err());
        fs::remove_dir(dir).unwrap();
    }
}
