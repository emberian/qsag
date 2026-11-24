//! Authenticated append-only burn journal with descriptor-lifetime locking.
//! The genesis MAC and both A/B high-water-mark slots are bound to the data inode;
//! copied or tail-truncated journals fail closed even before an external
//! monotonic anchor is consulted. Keep the directory private and pair with an
//! external hardware/hypervisor monotonic anchor (`Tpm2NvMonotoneAnchor`,
//! `HypervisorGenerationAnchor`) to defeat full-file or whole-VM snapshot rollback.
//!
//! `QSBURN05` layout, in 4096-byte pages: page 0 holds the genesis prefix
//! (`magic || key || genesis || genesis MAC`), page 1 holds slot A, page 2 holds slot B,
//! and the records follow from page 3. Each slot owns its page, so a torn sector or
//! page write damages at most one of them and recovery repairs it from the other
//! (`TwoSlotHwm`). The rest of each header page is zero and is not read back.
//!
//! A burn interrupted while its record was being written leaves up to one record's
//! worth of unauthenticated bytes after the chain. Recovery truncates them once the
//! slots and every committed record verify; a record that did reach the disk whole
//! stays burned and the slots are advanced onto it.
use alloc::boxed::Box;
use qsag_accel::ct::{RedactedSecret, ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_asm::durable::{
    ChainHead, CounterOrder, HWM_PAGE_BYTES, HWM_SLOT_BYTES, HwmSlotState, TwoSlotHwm,
    file_dev_ino, no_follow_options, sync_parent_dir, write_at_exact,
};
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use std::collections::BTreeSet;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};

const MAGIC: &[u8; 8] = b"QSBURN05";
const GENESIS_PREFIX_LEN: usize = 104;
const PAGE_LEN: usize = HWM_PAGE_BYTES as usize;
const HWM_SLOT_LEN: usize = HWM_SLOT_BYTES;
/// First of the two consecutive slot pages (page 0 is the genesis prefix).
const HWM_FIRST_PAGE: u32 = 1;
const HWM_SLOT_A_OFFSET: usize = PAGE_LEN;
const HWM_SLOT_B_OFFSET: usize = 2 * PAGE_LEN;
const HEADER_LEN: usize = 3 * PAGE_LEN;
const _: () = assert!(GENESIS_PREFIX_LEN <= PAGE_LEN && HWM_SLOT_LEN <= PAGE_LEN);
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

fn guard_mac_key(mut raw: [u8; 32]) -> RedactedSecret<32> {
    let guarded = RedactedSecret::new(raw);
    ct_zeroize_bytes(&mut raw);
    guarded
}

fn check_private_regular(metadata: &fs::Metadata) -> io::Result<()> {
    if !metadata.is_file() {
        return Err(invalid());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if metadata.permissions().mode() & 0o077 != 0 {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "burn journal must have private (0600) permissions",
            ));
        }
    }
    Ok(())
}

fn private_file(path: &Path) -> io::Result<OpenOptions> {
    match fs::symlink_metadata(path) {
        Ok(meta) => {
            if meta.file_type().is_symlink() {
                return Err(invalid());
            }
            check_private_regular(&meta)?;
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    let mut opts = no_follow_options().map_err(|_| invalid())?;
    opts.read(true).write(true);
    Ok(opts)
}

/// `dev_be64 || ino_be64` of the held descriptor. The big-endian layout is bound
/// into the genesis and high-water-mark MACs of the journal format.
fn file_identity(file: &File) -> io::Result<[u8; 16]> {
    let metadata = file.metadata()?;
    check_private_regular(&metadata)?;
    let (dev, ino) = file_dev_ino(&metadata).ok_or_else(invalid)?;
    let mut identity = [0; 16];
    identity[..8].copy_from_slice(&dev.to_be_bytes());
    identity[8..].copy_from_slice(&ino.to_be_bytes());
    Ok(identity)
}

/// True when at least one HWM slot authenticates and every valid slot lies within
/// `hwm_counter <= committed <= hwm_counter + 1` (permitting torn-tail recovery when
/// Slot A = `c` and Slot B = `c - 1`, or when `committed = c + 1` reached disk before HWM).
fn slots_permit_tail_truncation(
    hwm: &TwoSlotHwm<'_>,
    raw_a: &[u8],
    raw_b: &[u8],
    committed: u64,
) -> bool {
    let mut any_valid = false;
    for (slot, raw) in [(0, raw_a), (1, raw_b)] {
        if let HwmSlotState::Valid { counter, .. } = hwm.classify(slot, raw) {
            any_valid = true;
            if !(counter <= committed && committed <= counter.saturating_add(1)) {
                return false;
            }
        }
    }
    any_valid
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

    /// Runs `f` with this journal's two anti-truncation slots: big-endian generation,
    /// MAC bound to the storage key, file identity, public key and genesis.
    fn with_hwm<T>(&self, f: impl FnOnce(&TwoSlotHwm<'_>, &File) -> T) -> T {
        let mac = |slot: u8, generation: &[u8; 8], tip: &[u8; 32], reserved: &[u8; 8]| {
            cshake256_framed_32(
                b"QSAG.BURN.HWM.V4",
                &[
                    self.mac_key.expose(),
                    &self.identity,
                    &self.key,
                    &self.genesis,
                    &[slot],
                    generation,
                    tip,
                    reserved,
                ],
            )
        };
        let hwm = TwoSlotHwm::paged(HWM_FIRST_PAGE, CounterOrder::Big, &mac);
        debug_assert_eq!(
            (hwm.offset_a, hwm.offset_b),
            (HWM_SLOT_A_OFFSET as u64, HWM_SLOT_B_OFFSET as u64)
        );
        f(&hwm, &self.file)
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
            debug_assert_eq!(header.len(), GENESIS_PREFIX_LEN);
            let (slot_a, slot_b) = journal.with_hwm(|hwm, _| {
                (
                    hwm.encode(0, 0, &journal.last_tag),
                    hwm.encode(1, 0, &journal.last_tag),
                )
            });
            // One write of all three header pages, zero filled: no page is left sparse.
            header.resize(HEADER_LEN, 0);
            header[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN].copy_from_slice(&slot_a);
            header[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN].copy_from_slice(&slot_b);
            write_at_exact(&journal.file, 0, &header)?;
            journal.file.sync_all()?;
            sync_parent_dir(path)?;
        } else {
            journal.check_path_identity()?;
            let held_len = journal.file.metadata()?.len();
            if held_len < HEADER_LEN as u64 || held_len > MAX_JOURNAL_BYTES {
                return Err(invalid());
            }
            let cap = usize::try_from(held_len).map_err(|_| invalid())?;
            let mut bytes = std::vec::Vec::new();
            bytes.try_reserve_exact(cap).map_err(|_| invalid())?;
            journal.file.seek(SeekFrom::Start(0))?;
            // Read at most one byte past the `fstat` length: a file growing under the
            // read is refused below instead of being buffered without bound.
            (&mut journal.file)
                .take(held_len + 1)
                .read_to_end(&mut bytes)?;
            if bytes.len() != cap
                || bytes.len() < HEADER_LEN
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
            let mut prev_tag = journal.last_tag;
            let (records, partial) = bytes[HEADER_LEN..].as_chunks::<RECORD_LEN>();
            // Bytes after the authenticated chain: everything from the first record whose
            // tag does not verify, or the partial record at the end of the file.
            let mut tail_len = partial.len();
            for (index, record) in records.iter().enumerate() {
                let tag = journal.record_tag(&record[..10]);
                if !ct_eq_bytes(&tag, &record[10..]) {
                    tail_len = bytes.len() - HEADER_LEN - index * RECORD_LEN;
                    break;
                }
                let party = u16::from_be_bytes(record[..2].try_into().map_err(|_| invalid())?);
                let epoch = u64::from_be_bytes(record[2..10].try_into().map_err(|_| invalid())?);
                if !journal.entries.insert((party, epoch)) {
                    return Err(invalid());
                }
                prev_tag = journal.last_tag;
                journal.last_tag = tag;
            }
            let committed = journal.entries.len() as u64;
            let slot_a = &bytes[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN];
            let slot_b = &bytes[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN];
            // An interrupted `reserve` leaves at most one record's worth of unauthenticated
            // bytes after the authenticated prefix. Verify descriptor/path identity before
            // healing slots or truncating a torn tail.
            if tail_len > RECORD_LEN {
                return Err(invalid());
            }
            journal.check_path_identity()?;
            // Rejects tail truncation and unexplained gaps; heals the crash states (record
            // synced before slot A, slot A synced before slot B, one slot torn mid-write).
            journal
                .with_hwm(|hwm, file| {
                    if tail_len != 0
                        && !slots_permit_tail_truncation(hwm, slot_a, slot_b, committed)
                    {
                        return Err(invalid());
                    }
                    hwm.recover(
                        file,
                        slot_a,
                        slot_b,
                        &ChainHead {
                            len: committed,
                            tip: &journal.last_tag,
                            previous_tip: &prev_tag,
                        },
                    )
                })
                .map_err(|_| invalid())?;
            if tail_len != 0 {
                // Truncate the unauthenticated tail after prefix authentication and converge
                // both HWM slots onto `committed`.
                let committed_len = (HEADER_LEN + RECORD_LEN * journal.entries.len()) as u64;
                journal.file.set_len(committed_len)?;
                journal.file.sync_all()?;
                journal
                    .with_hwm(|hwm, file| hwm.commit(file, committed, &journal.last_tag))
                    .map_err(|_| invalid())?;
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
    fn check_path_identity(&self) -> io::Result<fs::Metadata> {
        let metadata = fs::symlink_metadata(&self.path)?;
        check_private_regular(&metadata)?;
        let held = self.file.metadata()?;
        check_private_regular(&held)?;
        if file_dev_ino(&metadata) != file_dev_ino(&held)
            || file_identity(&self.file)? != self.identity
        {
            return Err(invalid());
        }
        Ok(metadata)
    }
    fn check_identity(&self) -> io::Result<()> {
        let metadata = self.check_path_identity()?;
        if metadata.len() != (HEADER_LEN + RECORD_LEN * self.entries.len()) as u64 {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn reserve(&mut self, key: &[u8; 32], party: u16, epoch: u64) -> io::Result<()> {
        if self.failed || !ct_eq_bytes(key, &self.key) || self.entries.contains(&(party, epoch)) {
            return Err(invalid());
        }
        // Recovery refuses a journal above `MAX_JOURNAL_BYTES`, so never grow one past
        // it. A full journal is a refusal, not damage: the handle stays readable.
        let append_offset = (HEADER_LEN + RECORD_LEN * self.entries.len()) as u64;
        if append_offset + RECORD_LEN as u64 > MAX_JOURNAL_BYTES {
            return Err(invalid());
        }
        self.failed = true;
        self.check_identity()?;
        let mut record = [0; RECORD_LEN];
        record[..2].copy_from_slice(&party.to_be_bytes());
        record[2..10].copy_from_slice(&epoch.to_be_bytes());
        let tag = self.record_tag(&record[..10]);
        record[10..].copy_from_slice(&tag);
        write_at_exact(&self.file, append_offset, &record)?;
        self.file.sync_all()?;
        let next_gen = (self.entries.len() + 1) as u64;
        self.with_hwm(|hwm, file| hwm.commit(file, next_gen, &tag))?;
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
    pub fn open_existing(
        path: impl AsRef<Path>,
        key: [u8; 32],
        mac_key: [u8; 32],
    ) -> io::Result<Self> {
        DurableBurnJournal::open_existing(path, key, mac_key).map(Self)
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
        let wal = FsWalFtsEpochLatch::open_existing(&path, id, [8; 32]).unwrap();
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
                crate::FrontierFtsProfile::Full256Bit,
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
        let wal = FsWalFtsEpochLatch::open_existing(&path, id, [8; 32]).unwrap();
        let key = make()
            .resume_at(1)
            .unwrap()
            .attach_wal(alloc::boxed::Box::new(wal))
            .unwrap();
        assert_eq!(key.uses_completed(), 1);
        drop(key);
        let wal = FsWalFtsEpochLatch::open_existing(&path, id, [8; 32]).unwrap();
        let mut key = make().attach_wal(alloc::boxed::Box::new(wal)).unwrap();
        assert_eq!(key.uses_completed(), 1);
        assert_eq!(key.uses_remaining(), 0);
        let dp = crate::FrontierDpTable::build(crate::FrontierFtsProfile::Full256Bit);
        assert_eq!(
            key.sign(&dp, b"after recovery", &[0; 32]),
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
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        drop(journal);
        let mut journal = DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).unwrap();
        assert!(journal.reserve(&[1; 32], 7, 19).is_err());
        drop(journal);
        assert!(DurableBurnJournal::open_existing(&path, [3; 32], [2; 32]).is_err());
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [3; 32]).is_err());
        let original = fs::read(&path).unwrap();
        for len in [0, 40, HEADER_LEN - 1, original.len() - 1] {
            fs::write(&path, &original[..len]).unwrap();
            assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        }
        for index in [0, 7, 8, 40, 72, HEADER_LEN, original.len() - 1] {
            let mut corrupt = original.clone();
            corrupt[index] ^= 1;
            fs::write(&path, corrupt).unwrap();
            assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        }
        // Damage to both slots at once leaves nothing to recover from.
        let mut corrupt = original.clone();
        corrupt[HWM_SLOT_A_OFFSET] ^= 1;
        corrupt[HWM_SLOT_B_OFFSET] ^= 1;
        fs::write(&path, corrupt).unwrap();
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        fs::write(&path, &original).unwrap();
        #[cfg(unix)]
        {
            let link = dir.join("link");
            std::os::unix::fs::symlink(&path, &link).unwrap();
            assert!(DurableBurnJournal::open_existing(&link, [1; 32], [2; 32]).is_err());
            fs::remove_file(link).unwrap();
            let mut held = DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).unwrap();
            fs::rename(&path, dir.join("old")).unwrap();
            fs::write(&path, &original).unwrap();
            assert!(held.reserve(&[1; 32], 7, 20).is_err());
            drop(held);
            fs::remove_file(dir.join("old")).unwrap();
        }
        fs::remove_file(&path).unwrap();
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
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

    fn temp_journal(tag: &str) -> PathBuf {
        std::env::temp_dir().join(std::format!(
            "{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    fn junk(len: usize, seed: u64) -> std::vec::Vec<u8> {
        let mut x = seed | 1;
        (0..len)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x as u8
            })
            .collect()
    }

    /// Overwrite `len` bytes at `offset` with pseudo-random bytes, as a torn write would.
    fn tear(path: &Path, offset: usize, len: usize, seed: u64) {
        let file = OpenOptions::new().write(true).open(path).unwrap();
        write_at_exact(&file, offset as u64, &junk(len, seed)).unwrap();
    }

    /// A journal holding two burns (`(0, 0)` and `(0, 1)`), closed.
    struct TwoBurns {
        path: PathBuf,
        /// The file with both burns committed.
        committed: std::vec::Vec<u8>,
        /// The record a third burn of `(0, 2)` appends.
        next: [u8; RECORD_LEN],
        /// The file after that third burn committed.
        advanced: std::vec::Vec<u8>,
        checkpoint: LedgerCheckpoint,
    }

    impl TwoBurns {
        fn new(tag: &str) -> Self {
            let path = temp_journal(tag);
            let mut journal = DurableBurnJournal::create(&path, [1; 32], [2; 32]).unwrap();
            journal.reserve(&[1; 32], 0, 0).unwrap();
            journal.reserve(&[1; 32], 0, 1).unwrap();
            let checkpoint = journal.checkpoint();
            let committed = fs::read(&path).unwrap();
            journal.reserve(&[1; 32], 0, 2).unwrap();
            drop(journal);
            let advanced = fs::read(&path).unwrap();
            let next = advanced[committed.len()..].try_into().unwrap();
            // `fs::write` truncates in place: the inode the MACs bind is kept.
            fs::write(&path, &committed).unwrap();
            Self {
                path,
                committed,
                next,
                advanced,
                checkpoint,
            }
        }
        /// Put the committed file back, followed by `tail`.
        fn with_tail(&self, tail: &[u8]) -> std::vec::Vec<u8> {
            let mut bytes = self.committed.clone();
            bytes.extend_from_slice(tail);
            fs::write(&self.path, &bytes).unwrap();
            bytes
        }
        fn open(&self) -> io::Result<DurableBurnJournal> {
            DurableBurnJournal::open_at_least(&self.path, [1; 32], [2; 32], self.checkpoint)
        }
        /// Recovery lands on the two committed burns with the tail gone, and the journal
        /// then burns the third leaf as if the tear had never happened.
        fn assert_recovers_and_continues(&self) {
            let mut journal = self.open().unwrap();
            assert_eq!(journal.checkpoint().generation, 2);
            assert!(journal.checkpoint().tag == self.checkpoint.tag);
            assert_eq!(fs::read(&self.path).unwrap(), self.committed);
            assert!(journal.reserve(&[1; 32], 0, 1).is_err());
            journal.reserve(&[1; 32], 0, 2).unwrap();
            assert_eq!(journal.checkpoint().generation, 3);
            drop(journal);
            let journal = self.open().unwrap();
            assert_eq!(journal.checkpoint().generation, 3);
            drop(journal);
            assert_eq!(fs::read(&self.path).unwrap(), self.advanced);
        }
        /// Recovery refuses the file as it stands and leaves every byte alone.
        fn assert_fails_closed(&self, on_disk: &[u8]) {
            assert!(self.open().is_err());
            assert!(DurableBurnJournal::open_existing(&self.path, [1; 32], [2; 32]).is_err());
            assert_eq!(fs::read(&self.path).unwrap(), on_disk);
        }
    }

    impl Drop for TwoBurns {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.path);
        }
    }

    #[test]
    fn torn_tail_record_is_truncated_and_the_journal_continues() {
        let journal = TwoBurns::new("burn-tail-partial");
        for cut in [1, 9, 10, 11, RECORD_LEN - 1] {
            // A prefix of the real record, a prefix that never left the page cache as
            // data (zeros), and arbitrary bytes.
            for tail in [
                journal.next[..cut].to_vec(),
                std::vec![0; cut],
                junk(cut, cut as u64),
            ] {
                journal.with_tail(&tail);
                journal.assert_recovers_and_continues();
            }
        }
        // The tear may coincide with one unreadable slot; the other still marks the chain.
        for slot_offset in [HWM_SLOT_A_OFFSET, HWM_SLOT_B_OFFSET] {
            journal.with_tail(&journal.next[..17]);
            tear(&journal.path, slot_offset, HWM_SLOT_LEN, 31);
            journal.assert_recovers_and_continues();
        }
    }

    #[test]
    fn full_length_unauthenticated_tail_is_truncated() {
        let journal = TwoBurns::new("burn-tail-full");
        let mut bad_tag = journal.next;
        bad_tag[RECORD_LEN - 1] ^= 1;
        let mut bad_body = journal.next;
        bad_body[9] ^= 1;
        for tail in [
            bad_tag.to_vec(),
            bad_body.to_vec(),
            std::vec![0; RECORD_LEN],
            junk(RECORD_LEN, 5),
        ] {
            journal.with_tail(&tail);
            journal.assert_recovers_and_continues();
        }
    }

    #[test]
    fn synced_unacknowledged_record_is_rolled_forward_not_truncated() {
        let journal = TwoBurns::new("burn-tail-valid");
        journal.with_tail(&journal.next);
        let mut reopened = journal.open().unwrap();
        assert_eq!(reopened.checkpoint().generation, 3);
        assert!(reopened.reserve(&[1; 32], 0, 2).is_err());
        drop(reopened);
        assert_eq!(fs::read(&journal.path).unwrap(), journal.advanced);
    }

    #[test]
    fn torn_tail_never_excuses_a_corrupt_committed_record() {
        let journal = TwoBurns::new("burn-tail-corrupt");
        for record in [0, 1] {
            for index in [0, 9, 10, RECORD_LEN - 1] {
                for tail in [
                    &journal.next[..17],
                    &junk(RECORD_LEN, 7)[..],
                    &journal.next[..],
                    &[][..],
                ] {
                    let mut bytes = journal.with_tail(tail);
                    bytes[HEADER_LEN + record * RECORD_LEN + index] ^= 1;
                    fs::write(&journal.path, &bytes).unwrap();
                    journal.assert_fails_closed(&bytes);
                }
            }
        }
    }

    #[test]
    fn torn_tail_never_excuses_a_slot_ahead_of_the_chain() {
        let journal = TwoBurns::new("burn-tail-short");
        for kept in [0, 1] {
            for tail in [
                &journal.next[..17],
                &junk(RECORD_LEN, 9)[..],
                &junk(RECORD_LEN - 1, 10)[..],
            ] {
                let mut bytes = journal.committed[..HEADER_LEN + kept * RECORD_LEN].to_vec();
                bytes.extend_from_slice(tail);
                fs::write(&journal.path, &bytes).unwrap();
                journal.assert_fails_closed(&bytes);
            }
        }
        // One slot ahead of the other is the crash between the two slot writes; the record
        // it points at must be there, torn tail or not.
        let mut bytes = journal.committed.clone();
        bytes[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN].copy_from_slice(
            &journal.advanced[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN],
        );
        for tail in [&journal.next[..17], &junk(RECORD_LEN, 11)[..], &[][..]] {
            let mut bytes = bytes.clone();
            bytes.extend_from_slice(tail);
            fs::write(&journal.path, &bytes).unwrap();
            journal.assert_fails_closed(&bytes);
        }
    }

    #[test]
    fn tail_longer_than_one_record_fails_closed() {
        let journal = TwoBurns::new("burn-tail-long");
        for len in [RECORD_LEN + 1, 2 * RECORD_LEN - 1, 2 * RECORD_LEN, 4096] {
            let bytes = journal.with_tail(&junk(len, len as u64));
            journal.assert_fails_closed(&bytes);
        }
        // A synced record the slots have not reached, followed by more than one record's
        // worth of unauthenticated bytes, still fails closed.
        for extra in [RECORD_LEN + 1, 2 * RECORD_LEN] {
            let mut tail = journal.next.to_vec();
            tail.extend_from_slice(&junk(extra, 3));
            let bytes = journal.with_tail(&tail);
            journal.assert_fails_closed(&bytes);
        }
        // An unauthenticated record followed by an authentic-looking one is no better.
        let mut tail = junk(RECORD_LEN, 4);
        tail.extend_from_slice(&journal.next);
        let bytes = journal.with_tail(&tail);
        journal.assert_fails_closed(&bytes);
    }

    #[test]
    fn lone_lagging_slot_with_every_torn_tail_length() {
        let journal = TwoBurns::new("lone-lag-tail");
        for damaged in [HWM_SLOT_A_OFFSET, HWM_SLOT_B_OFFSET] {
            for tail_len in 1..=RECORD_LEN {
                let mut bytes = journal.committed.clone();
                bytes.extend_from_slice(&journal.next);
                bytes.extend_from_slice(&junk(tail_len, 71));
                bytes[damaged..damaged + HWM_SLOT_LEN].fill(0xa5);
                std::fs::write(&journal.path, &bytes).unwrap();
                let recovered = journal.open().unwrap();
                assert_eq!(recovered.checkpoint().generation, 3);
                drop(recovered);
                assert_eq!(fs::read(&journal.path).unwrap(), journal.advanced);
            }
        }
        // A valid survivor two records behind cannot justify truncating a tail.
        let mut live = journal.open().unwrap();
        live.reserve(&[1; 32], 0, 3).unwrap();
        drop(live);
        let advanced_twice = fs::read(&journal.path).unwrap();
        for tail_len in 1..=RECORD_LEN {
            let mut bytes = advanced_twice.clone();
            bytes[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN].fill(0xa5);
            bytes[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN].copy_from_slice(
                &journal.committed[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN],
            );
            bytes.extend_from_slice(&junk(tail_len, 72));
            std::fs::write(&journal.path, &bytes).unwrap();
            journal.assert_fails_closed(&bytes);
        }
    }

    #[test]
    fn lagging_slots_with_torn_tail_recover_and_converge_hwm() {
        let journal = TwoBurns::new("burn-tail-lagging-slots");
        // Case 1: `committed = c + 1` (`3` records synced, both HWM slots still at `c = 2`)
        // alongside `1..=RECORD_LEN` stray trailing bytes.
        for extra in [1, 17, RECORD_LEN] {
            let mut tail = journal.next.to_vec();
            tail.extend_from_slice(&junk(extra, 3));
            journal.with_tail(&tail);
            let mut reopened = journal.open().unwrap();
            assert_eq!(reopened.checkpoint().generation, 3);
            assert!(reopened.reserve(&[1; 32], 0, 2).is_err());
            drop(reopened);
            assert_eq!(fs::read(&journal.path).unwrap(), journal.advanced);
        }

        // Case 2: `Slot A = c` (`3`) and `Slot B = c - 1` (`2`) with `committed = c` (`3`)
        // alongside `1..=RECORD_LEN` torn trailing bytes of a fourth attempt.
        for extra in [1, 17, RECORD_LEN] {
            let mut mixed = journal.advanced.clone();
            mixed[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN].copy_from_slice(
                &journal.committed[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN],
            );
            mixed.extend_from_slice(&junk(extra, 19));
            fs::write(&journal.path, &mixed).unwrap();
            let mut reopened = journal.open().unwrap();
            assert_eq!(reopened.checkpoint().generation, 3);
            assert!(reopened.reserve(&[1; 32], 0, 2).is_err());
            drop(reopened);
            assert_eq!(fs::read(&journal.path).unwrap(), journal.advanced);
        }

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::write(&journal.path, &journal.committed).unwrap();
            fs::set_permissions(&journal.path, fs::Permissions::from_mode(0o644)).unwrap();
            assert!(DurableBurnJournal::open_existing(&journal.path, [1; 32], [2; 32]).is_err());
            fs::set_permissions(&journal.path, fs::Permissions::from_mode(0o600)).unwrap();
            assert!(DurableBurnJournal::open_existing(&journal.path, [1; 32], [2; 32]).is_ok());
        }
    }

    #[test]
    fn header_and_each_slot_own_a_page() {
        assert_eq!(
            (HWM_SLOT_A_OFFSET, HWM_SLOT_B_OFFSET, HEADER_LEN),
            (4096, 8192, 12288)
        );
        let path = temp_journal("burn-layout");
        let mut journal = DurableBurnJournal::create(&path, [1; 32], [2; 32]).unwrap();
        assert_eq!(fs::metadata(&path).unwrap().len(), HEADER_LEN as u64);
        journal.reserve(&[1; 32], 0, 0).unwrap();
        drop(journal);
        let bytes = fs::read(&path).unwrap();
        assert_eq!(bytes.len(), HEADER_LEN + RECORD_LEN);
        assert_eq!(&bytes[..8], MAGIC);
        // Everything in the header pages outside the prefix and the two slots is zero.
        for (start, end) in [
            (GENESIS_PREFIX_LEN, HWM_SLOT_A_OFFSET),
            (HWM_SLOT_A_OFFSET + HWM_SLOT_LEN, HWM_SLOT_B_OFFSET),
            (HWM_SLOT_B_OFFSET + HWM_SLOT_LEN, HEADER_LEN),
        ] {
            assert!(bytes[start..end].iter().all(|&b| b == 0), "{start}..{end}");
        }
        assert!(
            bytes[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN]
                .iter()
                .any(|&b| b != 0)
        );
        assert!(
            bytes[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN]
                .iter()
                .any(|&b| b != 0)
        );
        fs::remove_file(&path).unwrap();
    }

    #[test]
    fn torn_slot_b_recovers_the_committed_mark_and_is_repaired() {
        let path = temp_journal("burn-torn-b");
        let mut journal = DurableBurnJournal::create(&path, [1; 32], [2; 32]).unwrap();
        journal.reserve(&[1; 32], 0, 0).unwrap();
        journal.reserve(&[1; 32], 0, 1).unwrap();
        let checkpoint = journal.checkpoint();
        drop(journal);
        let committed = fs::read(&path).unwrap();
        for (seed, len) in [(1u64, 1usize), (2, 17), (3, HWM_SLOT_LEN), (4, PAGE_LEN)] {
            tear(&path, HWM_SLOT_B_OFFSET, len, seed);
            assert_ne!(fs::read(&path).unwrap(), committed);
            let journal =
                DurableBurnJournal::open_at_least(&path, [1; 32], [2; 32], checkpoint).unwrap();
            assert_eq!(journal.checkpoint().generation, 2);
            assert!(journal.checkpoint().tag == checkpoint.tag);
            drop(journal);
            let repaired = fs::read(&path).unwrap();
            assert_eq!(
                repaired[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN],
                committed[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN]
            );
            assert_eq!(
                repaired[..HWM_SLOT_B_OFFSET],
                committed[..HWM_SLOT_B_OFFSET]
            );
            assert_eq!(repaired[HEADER_LEN..], committed[HEADER_LEN..]);
            fs::write(&path, &committed).unwrap();
        }
        // The repaired journal still burns and still refuses a replayed leaf.
        tear(&path, HWM_SLOT_B_OFFSET, HWM_SLOT_LEN, 9);
        let mut journal = DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).unwrap();
        assert!(journal.reserve(&[1; 32], 0, 1).is_err());
        drop(journal);
        let mut journal = DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).unwrap();
        journal.reserve(&[1; 32], 0, 2).unwrap();
        assert_eq!(journal.checkpoint().generation, 3);
        drop(journal);
        fs::remove_file(&path).unwrap();
    }

    #[test]
    fn torn_slot_a_recovers_from_slot_b_and_is_repaired() {
        let path = temp_journal("burn-torn-a");
        let mut journal = DurableBurnJournal::create(&path, [1; 32], [2; 32]).unwrap();
        journal.reserve(&[1; 32], 0, 0).unwrap();
        let before = fs::read(&path).unwrap();
        let checkpoint_before = journal.checkpoint();
        journal.reserve(&[1; 32], 0, 1).unwrap();
        let checkpoint = journal.checkpoint();
        drop(journal);
        let committed = fs::read(&path).unwrap();

        // Slot A damaged in the steady state: slot B carries the committed mark.
        tear(&path, HWM_SLOT_A_OFFSET, PAGE_LEN, 11);
        let journal =
            DurableBurnJournal::open_at_least(&path, [1; 32], [2; 32], checkpoint).unwrap();
        assert_eq!(journal.checkpoint().generation, 2);
        drop(journal);
        let repaired = fs::read(&path).unwrap();
        assert_eq!(
            repaired[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN],
            committed[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN]
        );
        assert_eq!(
            repaired[HWM_SLOT_B_OFFSET..],
            committed[HWM_SLOT_B_OFFSET..]
        );

        // Crash in the middle of the first slot write of the second burn: the record is
        // synced, slot A is torn, slot B still holds the mark from before the burn. The
        // synced record is kept (the leaf stays burned) and both slots end on it.
        let mut crashed = before.clone();
        crashed.extend_from_slice(&committed[HEADER_LEN + RECORD_LEN..]);
        fs::write(&path, &crashed).unwrap();
        tear(&path, HWM_SLOT_A_OFFSET, HWM_SLOT_LEN, 12);
        let mut journal =
            DurableBurnJournal::open_at_least(&path, [1; 32], [2; 32], checkpoint_before).unwrap();
        assert_eq!(journal.checkpoint().generation, 2);
        assert!(journal.checkpoint().tag == checkpoint.tag);
        assert!(journal.reserve(&[1; 32], 0, 1).is_err());
        drop(journal);
        let healed = fs::read(&path).unwrap();
        assert_eq!(
            healed[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN],
            committed[HWM_SLOT_A_OFFSET..HWM_SLOT_A_OFFSET + HWM_SLOT_LEN]
        );
        assert_eq!(
            healed[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN],
            committed[HWM_SLOT_B_OFFSET..HWM_SLOT_B_OFFSET + HWM_SLOT_LEN]
        );

        // A torn slot never excuses a truncated chain.
        fs::write(&path, &committed[..HEADER_LEN + RECORD_LEN]).unwrap();
        tear(&path, HWM_SLOT_A_OFFSET, HWM_SLOT_LEN, 13);
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        fs::remove_file(&path).unwrap();
    }

    #[test]
    fn both_slots_torn_fails_closed_without_writing() {
        let path = temp_journal("burn-torn-both");
        let mut journal = DurableBurnJournal::create(&path, [1; 32], [2; 32]).unwrap();
        journal.reserve(&[1; 32], 0, 0).unwrap();
        drop(journal);
        tear(&path, HWM_SLOT_A_OFFSET, HWM_SLOT_LEN, 21);
        tear(&path, HWM_SLOT_B_OFFSET, HWM_SLOT_LEN, 22);
        let damaged = fs::read(&path).unwrap();
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        assert_eq!(fs::read(&path).unwrap(), damaged);
        // Two slot pages that were never written are no better.
        let mut blank = damaged.clone();
        blank[HWM_SLOT_A_OFFSET..HEADER_LEN].fill(0);
        fs::write(&path, &blank).unwrap();
        assert!(DurableBurnJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        assert_eq!(fs::read(&path).unwrap(), blank);
        fs::remove_file(&path).unwrap();
    }
}
