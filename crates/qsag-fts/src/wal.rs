//! Authenticated append-only burn journal with descriptor-lifetime locking.
//! V4 binds both the genesis MAC and dual A/B high-water-mark header slots to the
//! data inode; copied, legacy, or tail-truncated journals fail closed even before an
//! external monotonic anchor is consulted. Keep the directory private and pair with an
//! external hardware/hypervisor monotonic anchor (`Tpm2NvMonotoneAnchor`,
//! `HypervisorGenerationAnchor`) to defeat full-file or whole-VM snapshot rollback.
use alloc::boxed::Box;
use qsag_accel::ct::{RedactedSecret, ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom};
#[cfg(not(unix))]
use std::io::Write;
use std::path::{Path, PathBuf};

const MAGIC: &[u8; 8] = b"QSBURN04";
const GENESIS_PREFIX_LEN: usize = 104;
const HWM_SLOT_LEN: usize = 80;
const HWM_SLOT_A_OFFSET: usize = GENESIS_PREFIX_LEN;
const HWM_SLOT_B_OFFSET: usize = GENESIS_PREFIX_LEN + HWM_SLOT_LEN;
const HEADER_LEN: usize = GENESIS_PREFIX_LEN + 2 * HWM_SLOT_LEN; // 264 bytes
const RECORD_LEN: usize = 42;
/// Defensive upper bound (64 MiB) checked via `fstat` prior to buffer allocation.
pub const MAX_JOURNAL_BYTES: u64 = 64 * 1024 * 1024;

pub struct DurableBurnJournal {
    path: PathBuf,
    file: File,
    identity: [u8; 16],
    key: [u8; 32],
    genesis: [u8; 32],
    last_tag: [u8; 32],
    mac_key: RedactedSecret<32>,
    entries: BTreeSet<(u16, u64)>,
    failed: bool,
    anchor: Option<Box<dyn ExternalMonotoneAnchor>>,
}
fn invalid() -> io::Error {
    io::Error::other("invalid, truncated, replaced, or locked burn journal")
}

/// Explicit Linux architecture mapping for `O_NOFOLLOW | O_NONBLOCK`.
/// Returns `None` on unrecognized targets so callers fail closed rather than
/// passing wrong architecture-specific `fcntl` constants (e.g. MIPS/SPARC/PowerPC).
pub(crate) const fn linux_open_nofollow_nonblock_flags(arch: &str) -> Option<i32> {
    match arch.as_bytes() {
        b"x86_64" | b"x86" | b"riscv64" | b"riscv32" | b"s390x" | b"loongarch64" => {
            Some(0x20000 | 0x800)
        }
        b"aarch64" | b"arm" | b"powerpc" | b"powerpc64" => Some(0x8000 | 0x800),
        b"mips" | b"mips64" => Some(0x20000 | 0x80),
        b"sparc" | b"sparc64" => Some(0x20000 | 0x4000),
        _ => None,
    }
}

fn guard_mac_key(mut raw: [u8; 32]) -> RedactedSecret<32> {
    let guarded = RedactedSecret::new(raw);
    ct_zeroize_bytes(&mut raw);
    guarded
}

fn write_at_exact(file: &mut File, offset: u64, bytes: &[u8]) -> io::Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::FileExt;
        file.write_all_at(bytes, offset)
    }
    #[cfg(not(unix))]
    {
        file.seek(SeekFrom::Start(offset))?;
        file.write_all(bytes)
    }
}

fn private_file(path: &Path) -> io::Result<OpenOptions> {
    if fs::symlink_metadata(path).is_ok_and(|m| m.file_type().is_symlink()) {
        return Err(invalid());
    }
    let mut opts = OpenOptions::new();
    opts.read(true).write(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.mode(0o600);
        #[cfg(target_os = "linux")]
        {
            let flags =
                linux_open_nofollow_nonblock_flags(std::env::consts::ARCH).ok_or_else(invalid)?;
            opts.custom_flags(flags);
        }
        #[cfg(target_os = "macos")]
        opts.custom_flags(0x0100 | 0x4); // O_NOFOLLOW | O_NONBLOCK
    }
    Ok(opts)
}
fn file_identity(file: &File) -> io::Result<[u8; 16]> {
    let metadata = file.metadata()?;
    if !metadata.is_file() {
        return Err(invalid());
    }
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
        let mac_key = guard_mac_key(mac_key);
        Self::load_guarded(path.as_ref(), key, mac_key, true)
    }
    /// Recover an existing authenticated journal; missing files are an error.
    pub fn open_existing(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
    ) -> io::Result<Self> {
        let mac_key = guard_mac_key(mac_key);
        Self::load_guarded(path.as_ref(), key, mac_key, false)
    }
    pub fn checkpoint(&self) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation: self.entries.len() as u64,
            tag: self.last_tag,
        }
    }
    pub fn open_at_least(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
        minimum: LedgerCheckpoint,
    ) -> io::Result<Self> {
        let mac_key = guard_mac_key(mac_key);
        let journal = Self::load_guarded(path.as_ref(), key, mac_key, false)?;
        journal.check_minimum(minimum)?;
        Ok(journal)
    }
    fn check_minimum(&self, minimum: LedgerCheckpoint) -> io::Result<()> {
        let current = self.checkpoint();
        if current.generation < minimum.generation
            || (current.generation == minimum.generation
                && !ct_eq_bytes(&current.tag, &minimum.tag))
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn create_anchored(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
        anchor: Box<dyn ExternalMonotoneAnchor>,
    ) -> io::Result<Self> {
        let mac_key = guard_mac_key(mac_key);
        if anchor.load()?.is_some() {
            return Err(invalid());
        }
        let mut journal = Self::load_guarded(path.as_ref(), key, mac_key, true)?;
        anchor.advance(journal.checkpoint())?;
        journal.anchor = Some(anchor);
        Ok(journal)
    }
    pub fn open_anchored(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
        anchor: Box<dyn ExternalMonotoneAnchor>,
    ) -> io::Result<Self> {
        let mac_key = guard_mac_key(mac_key);
        let minimum = anchor.load()?.ok_or_else(invalid)?;
        let mut journal = Self::load_guarded(path.as_ref(), key, mac_key, false)?;
        journal.check_minimum(minimum)?;
        anchor.advance(journal.checkpoint())?;
        journal.anchor = Some(anchor);
        Ok(journal)
    }
    /// Compatibility alias for existing-vault recovery only.
    pub fn open(path: impl AsRef<Path>, key: [u8; 32], mac_key: [u8; 32]) -> io::Result<Self> {
        Self::open_existing(path, key, mac_key)
    }

    fn encode_hwm_slot(&self, slot_idx: u8, generation: u64, tip_tag: &[u8; 32]) -> [u8; HWM_SLOT_LEN] {
        let mut slot = [0u8; HWM_SLOT_LEN];
        let gen_be = generation.to_be_bytes();
        slot[..8].copy_from_slice(&gen_be);
        slot[8..40].copy_from_slice(tip_tag);
        let reserved = [0u8; 8];
        let mac = cshake256_framed_32(
            b"QSAG.BURN.HWM.V4",
            &[
                self.mac_key.expose(),
                &self.identity,
                &self.key,
                &self.genesis,
                &[slot_idx],
                &gen_be,
                tip_tag,
                &reserved,
            ],
        );
        slot[40..72].copy_from_slice(&mac);
        slot
    }

    fn verify_hwm_slot(&self, slot_idx: u8, raw: &[u8]) -> io::Result<(u64, [u8; 32])> {
        if raw.len() != HWM_SLOT_LEN {
            return Err(invalid());
        }
        let gen_be: [u8; 8] = raw[..8].try_into().map_err(|_| invalid())?;
        let generation = u64::from_be_bytes(gen_be);
        let tip_tag: [u8; 32] = raw[8..40].try_into().map_err(|_| invalid())?;
        let stored_mac = &raw[40..72];
        let reserved = &raw[72..80];
        if !ct_eq_bytes(reserved, &[0u8; 8]) {
            return Err(invalid());
        }
        let expected_mac = cshake256_framed_32(
            b"QSAG.BURN.HWM.V4",
            &[
                self.mac_key.expose(),
                &self.identity,
                &self.key,
                &self.genesis,
                &[slot_idx],
                &gen_be,
                &tip_tag,
                reserved,
            ],
        );
        if !ct_eq_bytes(&expected_mac, stored_mac) {
            return Err(invalid());
        }
        Ok((generation, tip_tag))
    }

    fn sync_hwm_slots(&mut self, generation: u64, tip_tag: &[u8; 32]) -> io::Result<()> {
        let slot_a = self.encode_hwm_slot(0, generation, tip_tag);
        write_at_exact(&mut self.file, HWM_SLOT_A_OFFSET as u64, &slot_a)?;
        self.file.sync_all()?;
        let slot_b = self.encode_hwm_slot(1, generation, tip_tag);
        write_at_exact(&mut self.file, HWM_SLOT_B_OFFSET as u64, &slot_b)?;
        self.file.sync_all()
    }

    fn load_guarded(
        path: &Path,
        key: [u8; 32],
        mac_key: RedactedSecret<32>,
        create: bool,
    ) -> io::Result<Self> {
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
            identity,
            key,
            genesis: [0; 32],
            last_tag: [0; 32],
            mac_key,
            entries: BTreeSet::new(),
            failed: false,
            anchor: None,
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
            let mut header = std::vec::Vec::with_capacity(HEADER_LEN);
            header.extend_from_slice(MAGIC);
            header.extend_from_slice(&key);
            header.extend_from_slice(&journal.genesis);
            journal.last_tag = cshake256_framed_32(
                b"QSAG.BURN.GENESIS.V4",
                &[journal.mac_key.expose(), &identity, &header],
            );
            header.extend_from_slice(&journal.last_tag);
            let slot_a = journal.encode_hwm_slot(0, 0, &journal.last_tag);
            let slot_b = journal.encode_hwm_slot(1, 0, &journal.last_tag);
            header.extend_from_slice(&slot_a);
            header.extend_from_slice(&slot_b);
            debug_assert_eq!(header.len(), HEADER_LEN);
            write_at_exact(&mut journal.file, 0, &header)?;
            journal.file.sync_all()?;
            #[cfg(unix)]
            File::open(
                path.parent()
                    .filter(|p| !p.as_os_str().is_empty())
                    .unwrap_or(Path::new(".")),
            )?
            .sync_all()?;
        } else {
            let held_len = journal.file.metadata()?.len();
            if held_len < HEADER_LEN as u64 || held_len > MAX_JOURNAL_BYTES {
                return Err(invalid());
            }
            let cap = usize::try_from(held_len).map_err(|_| invalid())?;
            let mut bytes = std::vec::Vec::new();
            bytes.try_reserve_exact(cap).map_err(|_| invalid())?;
            journal.file.seek(SeekFrom::Start(0))?;
            journal.file.read_to_end(&mut bytes)?;
            if bytes.len() < HEADER_LEN
                || !(bytes.len() - HEADER_LEN).is_multiple_of(RECORD_LEN)
                || &bytes[..8] != MAGIC
                || !ct_eq_bytes(&bytes[8..40], &key)
            {
                return Err(invalid());
            }
            journal.genesis.copy_from_slice(&bytes[40..72]);
            journal.last_tag = cshake256_framed_32(
                b"QSAG.BURN.GENESIS.V4",
                &[journal.mac_key.expose(), &identity, &bytes[..72]],
            );
            if !ct_eq_bytes(&journal.last_tag, &bytes[72..GENESIS_PREFIX_LEN]) {
                return Err(invalid());
            }
            let (gen_a, tip_a) =
                journal.verify_hwm_slot(0, &bytes[HWM_SLOT_A_OFFSET..HWM_SLOT_B_OFFSET])?;
            let (gen_b, tip_b) =
                journal.verify_hwm_slot(1, &bytes[HWM_SLOT_B_OFFSET..HEADER_LEN])?;
            // Slot A is updated strictly before Slot B on each reservation, so valid
            // states satisfy either `gen_a == gen_b` (steady state) or `gen_a == gen_b + 1`
            // (crash between Slot A sync and Slot B sync).
            if gen_a < gen_b || gen_a - gen_b > 1 {
                return Err(invalid());
            }
            let hwm_gen = gen_a;
            let hwm_tip = tip_a;

            let mut prev_tag = journal.last_tag;
            for record in bytes[HEADER_LEN..].as_chunks::<RECORD_LEN>().0 {
                prev_tag = journal.last_tag;
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
            let actual_gen = journal.entries.len() as u64;
            // Reject any tail truncation (`actual_gen < hwm_gen`) or unexplained gap (`> hwm_gen + 1`).
            if actual_gen < hwm_gen || actual_gen > hwm_gen + 1 {
                return Err(invalid());
            }
            if actual_gen == hwm_gen {
                if !ct_eq_bytes(&journal.last_tag, &hwm_tip) {
                    return Err(invalid());
                }
                if gen_b != gen_a || !ct_eq_bytes(&tip_b, &hwm_tip) {
                    // Heal Slot B after crash between Slot A sync and Slot B sync.
                    let slot_b = journal.encode_hwm_slot(1, actual_gen, &journal.last_tag);
                    write_at_exact(&mut journal.file, HWM_SLOT_B_OFFSET as u64, &slot_b)?;
                    journal.file.sync_all()?;
                }
            } else {
                // `actual_gen == hwm_gen + 1`: crash occurred after full record sync, before Slot A sync.
                if !ct_eq_bytes(&prev_tag, &hwm_tip) || gen_a != gen_b || !ct_eq_bytes(&tip_a, &tip_b) {
                    return Err(invalid());
                }
                let tip = journal.last_tag;
                journal.sync_hwm_slots(actual_gen, &tip)?;
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
        if self.failed || !ct_eq_bytes(key, &self.key) || self.entries.contains(&(party, epoch)) {
            return Err(invalid());
        }
        self.failed = true;
        self.check_identity()?;
        let append_offset = (HEADER_LEN + RECORD_LEN * self.entries.len()) as u64;
        let mut record = [0; RECORD_LEN];
        record[..2].copy_from_slice(&party.to_be_bytes());
        record[2..10].copy_from_slice(&epoch.to_be_bytes());
        let tag = self.record_tag(&record[..10]);
        record[10..].copy_from_slice(&tag);
        write_at_exact(&mut self.file, append_offset, &record)?;
        self.file.sync_all()?;
        let next_gen = (self.entries.len() + 1) as u64;
        self.sync_hwm_slots(next_gen, &tag)?;
        self.entries.insert((party, epoch));
        self.last_tag = tag;
        self.check_identity()?;
        if let Some(anchor) = &self.anchor {
            anchor.advance(self.checkpoint())?;
        }
        self.failed = false;
        Ok(())
    }
}
/// A successful reservation permanently spends exactly one WOTS leaf.
pub struct FsWalFtsEpochLatch(pub DurableBurnJournal);
impl FsWalFtsEpochLatch {
    pub fn open_at_least(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
        minimum: LedgerCheckpoint,
    ) -> io::Result<Self> {
        DurableBurnJournal::open_at_least(path, key, mac_key, minimum).map(Self)
    }
    pub fn create_anchored(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
        anchor: Box<dyn ExternalMonotoneAnchor>,
    ) -> io::Result<Self> {
        DurableBurnJournal::create_anchored(path, key, mac_key, anchor).map(Self)
    }
    pub fn open_anchored(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
        anchor: Box<dyn ExternalMonotoneAnchor>,
    ) -> io::Result<Self> {
        DurableBurnJournal::open_anchored(path, key, mac_key, anchor).map(Self)
    }
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
            if party != 0 || epoch != u64::from(used) {
                return Err(super::FrontierFtsError::PersistenceFailed);
            }
            used = used
                .checked_add(1)
                .ok_or(super::FrontierFtsError::PersistenceFailed)?;
        }
        Ok(used)
    }
    fn reserve_use(&mut self, key: &[u8; 32], next: u8) -> Result<(), super::FrontierFtsError> {
        if next == 0 || self.uses_completed(key)? != next - 1 {
            return Err(super::FrontierFtsError::PersistenceFailed);
        }
        self.0
            .reserve(key, 0, u64::from(next - 1))
            .map_err(|_| super::FrontierFtsError::PersistenceFailed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retained_checkpoint_rejects_same_inode_tail_truncation() {
        let path = std::env::temp_dir().join(alloc::format!(
            "retained-tail-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let mut journal = DurableBurnJournal::create(&path, [1; 32], [2; 32]).unwrap();
        journal.reserve(&[1; 32], 0, 0).unwrap();
        let checkpoint = journal.checkpoint();
        drop(journal);
        std::fs::OpenOptions::new()
            .write(true)
            .open(&path)
            .unwrap()
            .set_len(HEADER_LEN as u64)
            .unwrap();
        assert!(DurableBurnJournal::open_at_least(&path, [1; 32], [2; 32], checkpoint).is_err());
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn copied_journal_cannot_create_second_authority() {
        let path = std::env::temp_dir().join(std::format!(
            "burn-copy-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
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
        let path = std::env::temp_dir().join(std::format!(
            "frontier-restart-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let make = || {
            crate::FrontierFtsSigningKey::keygen(
                crate::FrontierFtsProfile::Fast256Test,
                [1; 32],
                [2; 32],
                [3; 32],
                true,
                &qsag_accel::CpuReferenceBackend,
            )
        };
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
        assert_eq!(
            key.sign(&dp, b"second", &[0; 32]),
            Err(crate::FrontierFtsError::UseBudgetExhausted)
        );
        drop(key);
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn frontier_recovers_vault_reservation_before_wal_append() {
        let path = std::env::temp_dir().join(std::format!(
            "frontier-gap-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let make = || {
            crate::FrontierFtsSigningKey::keygen(
                crate::FrontierFtsProfile::Compact770,
                [1; 32],
                [2; 32],
                [3; 32],
                true,
                &qsag_accel::CpuReferenceBackend,
            )
        };
        let id = make().wal_key();
        drop(FsWalFtsEpochLatch::create(&path, id, [8; 32]).unwrap());
        // Simulate a crash after the vault committed use 1, before the WAL did.
        let wal = FsWalFtsEpochLatch::open(&path, id, [8; 32]).unwrap();
        let key = make()
            .resume_at(1)
            .unwrap()
            .attach_wal(alloc::boxed::Box::new(wal))
            .unwrap();
        assert_eq!(key.uses_completed(), 1);
        drop(key);
        let wal = FsWalFtsEpochLatch::open(&path, id, [8; 32]).unwrap();
        let mut key = make().attach_wal(alloc::boxed::Box::new(wal)).unwrap();
        assert_eq!(key.uses_completed(), 1);
        let dp = crate::FrontierDpTable::build(crate::FrontierFtsProfile::Compact770);
        let signature = key.sign(&dp, b"after recovery", &[0; 32]).unwrap();
        crate::verify_frontier_fts(&key.pk, &dp, b"after recovery", &signature).unwrap();
        assert_eq!(key.uses_completed(), 2);
        assert_eq!(
            key.sign(&dp, b"exhausted", &[0; 32]),
            Err(crate::FrontierFtsError::UseBudgetExhausted)
        );
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
        for index in [
            8,
            40,
            72,
            HWM_SLOT_A_OFFSET,
            HWM_SLOT_B_OFFSET,
            HEADER_LEN,
            original.len() - 1,
        ] {
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

    #[test]
    fn unanchored_open_rejects_same_inode_tail_truncation() {
        let path = std::env::temp_dir().join(alloc::format!(
            "unanchored-tail-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let mut journal = DurableBurnJournal::create(&path, [5; 32], [6; 32]).unwrap();
        journal.reserve(&[5; 32], 0, 0).unwrap();
        journal.reserve(&[5; 32], 0, 1).unwrap();
        drop(journal);
        // Truncate the last record (rewind 2 -> 1 burned leaves) on the exact same inode.
        std::fs::OpenOptions::new()
            .write(true)
            .open(&path)
            .unwrap()
            .set_len((HEADER_LEN + RECORD_LEN) as u64)
            .unwrap();
        // Even `open_existing` WITHOUT an external anchor must fail closed due to HWM slots!
        assert!(DurableBurnJournal::open_existing(&path, [5; 32], [6; 32]).is_err());
        // Truncating all records back to `HEADER_LEN` also fails closed.
        std::fs::OpenOptions::new()
            .write(true)
            .open(&path)
            .unwrap()
            .set_len(HEADER_LEN as u64)
            .unwrap();
        assert!(DurableBurnJournal::open_existing(&path, [5; 32], [6; 32]).is_err());
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn linux_nofollow_nonblock_flag_table_fails_closed_on_unknown_arch() {
        assert_eq!(
            linux_open_nofollow_nonblock_flags("x86_64"),
            Some(0x20000 | 0x800)
        );
        assert_eq!(
            linux_open_nofollow_nonblock_flags("riscv64"),
            Some(0x20000 | 0x800)
        );
        assert_eq!(
            linux_open_nofollow_nonblock_flags("aarch64"),
            Some(0x8000 | 0x800)
        );
        assert_eq!(
            linux_open_nofollow_nonblock_flags("powerpc64"),
            Some(0x8000 | 0x800)
        );
        assert_eq!(
            linux_open_nofollow_nonblock_flags("mips64"),
            Some(0x20000 | 0x80)
        );
        assert_eq!(linux_open_nofollow_nonblock_flags("unknown_isa"), None);
    }
}
