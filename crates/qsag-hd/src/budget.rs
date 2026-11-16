//! Durable family query budgets. An attempted disclosure is burned before release.
//! Files and their permanent lock sidecars belong in trusted local storage. Recovery
//! never creates missing state. Restoring an older valid filesystem snapshot still
//! requires an external monotonic anchor; a MAC alone cannot detect full-disk rollback,
//! though unlinking and recreating the budget journal on a new inode fails closed.
use crate::HdError;
use alloc::boxed::Box;
use qsag_accel::ct::{RedactedSecret, ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_asm::durable::{
    ChainHead, CounterOrder, HWM_PAGE_BYTES, HWM_SLOT_BYTES, HwmSlotState, LockedRecord,
    RECORD_HEADER_BYTES, TwoSlotHwm, file_identity, no_follow_options, sync_parent_dir,
    write_at_exact,
};
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use std::fs::{self, File};
use std::io;
use std::path::{Path, PathBuf};

const LIMIT: u64 = 128;
const RECORD: usize = 40;
const DATA_SEAL_BYTES: usize = 16;
// Header, each HWM slot, and the chain occupy disjoint physical pages.
// Page 0 payload layout (`[0..4080)` after the 16-byte `QSAGREC1` record header):
// - `[0..16)`: `data_seal` (`dev_le64 || ino_le64` of the data file)
// - `[16..24)`: `QSHDQB04` format magic
// - `[24..48)`: `lock_identity` (`dev_le64 || ino_le64 || seal8` of the `.lock` sidecar)
// - `[48..80)`: `genesis_seal_mac` authenticating `(key, family, lock_identity, data_seal, LIMIT)`
// - `[80..4080)`: reserved zero padding before Slot A on physical page 1 (`4096`).
const FORMAT_MAGIC: &[u8; 8] = b"QSHDQB04";
const LOCK_IDENTITY_OFFSET: usize = DATA_SEAL_BYTES + FORMAT_MAGIC.len();
const LOCK_IDENTITY_BYTES: usize = 24;
const GENESIS_SEAL_MAC_OFFSET: usize = LOCK_IDENTITY_OFFSET + LOCK_IDENTITY_BYTES;
const GENESIS_SEAL_END: usize = GENESIS_SEAL_MAC_OFFSET + 32;
const HWM_SLOT_A_PAYLOAD_OFFSET: usize = HWM_PAGE_BYTES as usize - RECORD_HEADER_BYTES;
const HWM_SLOT_B_PAYLOAD_OFFSET: usize = 2 * HWM_PAGE_BYTES as usize - RECORD_HEADER_BYTES;
const FILE_PREFIX_BYTES: usize = 3 * HWM_PAGE_BYTES as usize;
const PAYLOAD_HEADER_BYTES: usize = FILE_PREFIX_BYTES - RECORD_HEADER_BYTES;
const MAX_BUDGET_PAYLOAD_BYTES: usize = PAYLOAD_HEADER_BYTES + RECORD * (LIMIT as usize + 1);

/// Append-only authenticated journal, held under an exclusive OS lock and pinned
/// to the genesis regular-file `(dev, ino)` identity across both live `reserve()`
/// calls and offline `open()` recovery.
/// No Clone, reset, truncate, restore-counter or increase-limit operation exists.
pub struct DurableQueryBudget {
    path: PathBuf,
    record: LockedRecord,
    lock_identity: [u8; 24],
    file: File,
    data_seal: [u8; 16],
    last_mac: [u8; 32],
    family: [u8; 32],
    key: RedactedSecret<32>,
    used: u64,
    failed: bool,
    anchor: Option<Box<dyn ExternalMonotoneAnchor>>,
}

fn storage<T>(value: io::Result<T>) -> Result<T, HdError> {
    value.map_err(|_| HdError::BudgetStorageFailed)
}

fn guard_key(mut raw: [u8; 32]) -> RedactedSecret<32> {
    let guarded = RedactedSecret::new(raw);
    ct_zeroize_bytes(&mut raw);
    guarded
}

/// Everything a journal's MACs bind besides the record itself: the storage key,
/// the family, the lock sidecar's full `(dev, ino, seal)` identity (via the genesis
/// Page-0 seal MAC) and creation seal, and the data file's `(dev, ino)`.
struct Binding<'a> {
    key: &'a [u8; 32],
    family: &'a [u8; 32],
    lock_seal: [u8; 8],
    data_seal: [u8; 16],
}

impl Binding<'_> {
    /// Authenticates the 24-byte `.lock` sidecar `(dev, ino, seal)` identity in Page 0.
    /// Length-framed with 5 slices (24-byte `lock_identity` at index 2), strictly disjoint
    /// from the 7-slice `record()` preimage (8-byte `lock_seal` at index 2).
    fn genesis_seal_mac(&self, lock_identity: &[u8; LOCK_IDENTITY_BYTES]) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.HD.QUERY_BUDGET.V3",
            &[
                self.key,
                self.family,
                lock_identity,
                &self.data_seal,
                &LIMIT.to_le_bytes(),
            ],
        )
    }

    /// Record `count` of the chain and its MAC, which is the next record's `prev_mac`.
    fn record(&self, count: u64, prev_mac: &[u8; 32]) -> ([u8; RECORD], [u8; 32]) {
        let mut out = [0u8; RECORD];
        out[..8].copy_from_slice(&count.to_le_bytes());
        let mac = cshake256_framed_32(
            b"QSAG.HD.QUERY_BUDGET.V3",
            &[
                self.key,
                self.family,
                &self.lock_seal,
                &self.data_seal,
                &LIMIT.to_le_bytes(),
                &out[..8],
                prev_mac,
            ],
        );
        out[8..].copy_from_slice(&mac);
        (out, mac)
    }

    /// Runs `f` with the two anti-truncation slots: little-endian use count, MAC
    /// bound to everything in `self` and to the limit.
    fn with_hwm<T>(&self, f: impl FnOnce(&TwoSlotHwm<'_>) -> T) -> T {
        let mac = |slot: u8, used: &[u8; 8], tip: &[u8; 32], reserved: &[u8; 8]| {
            cshake256_framed_32(
                b"QSAG.HD.QUERY_BUDGET.HWM.V4",
                &[
                    self.key,
                    self.family,
                    &self.lock_seal,
                    &self.data_seal,
                    &[slot],
                    &LIMIT.to_le_bytes(),
                    used,
                    tip,
                    reserved,
                ],
            )
        };
        let hwm = TwoSlotHwm::paged(1, CounterOrder::Little, &mac);
        assert!(hwm.slots_on_distinct_pages());
        f(&hwm)
    }
}

/// True when at least one HWM slot authenticates and every valid slot lies within
/// `hwm_counter <= used <= hwm_counter + 1` (permitting torn-tail recovery when
/// Slot A = `c` and Slot B = `c - 1`, or when `used = c + 1` reached disk before HWM).
fn slots_permit_tail_truncation(
    hwm: &TwoSlotHwm<'_>,
    raw_a: &[u8],
    raw_b: &[u8],
    used: u64,
) -> bool {
    let mut any_valid = false;
    for (slot, raw) in [(0, raw_a), (1, raw_b)] {
        if let HwmSlotState::Valid { counter, .. } = hwm.classify(slot, raw) {
            any_valid = true;
            if !(counter <= used && used <= counter.saturating_add(1)) {
                return false;
            }
        }
    }
    any_valid
}

fn checkpoint_at_least(current: LedgerCheckpoint, minimum: LedgerCheckpoint) -> bool {
    current.generation > minimum.generation
        || (current.generation == minimum.generation && ct_eq_bytes(&current.tag, &minimum.tag))
}

/// The journal path and the held descriptor both still name the private regular
/// file sealed at genesis, at exactly `expected_len` bytes. Metadata only: this is
/// the whole per-`reserve` integrity check, and recovery repeats it around repairs.
fn verify_data_identity(
    path: &Path,
    file: &File,
    data_seal: &[u8; 16],
    expected_len: u64,
) -> Result<(), HdError> {
    let sealed = |meta: fs::Metadata| {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if meta.permissions().mode() & 0o077 != 0 {
                return false;
            }
        }
        meta.is_file()
            && ct_eq_bytes(&file_identity(&meta), data_seal)
            && meta.len() == expected_len
    };
    if sealed(storage(fs::symlink_metadata(path))?) && sealed(storage(file.metadata())?) {
        Ok(())
    } else {
        Err(HdError::BudgetStorageFailed)
    }
}

impl DurableQueryBudget {
    pub fn checkpoint(&self) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation: self.used,
            tag: self.last_mac,
        }
    }
    pub fn open_at_least(
        path: impl AsRef<Path>,
        family: [u8; 32],
        key: [u8; 32],
        minimum: LedgerCheckpoint,
    ) -> Result<Self, HdError> {
        let key_secret = guard_key(key);
        let journal = Self::open_guarded(path.as_ref(), family, key_secret)?;
        if !checkpoint_at_least(journal.checkpoint(), minimum) {
            return Err(HdError::BudgetStorageFailed);
        }
        Ok(journal)
    }
    pub fn create_anchored(
        path: impl AsRef<Path>,
        family: [u8; 32],
        key: [u8; 32],
        anchor: Box<dyn ExternalMonotoneAnchor>,
    ) -> Result<Self, HdError> {
        let key_secret = guard_key(key);
        if storage(anchor.load())?.is_some() {
            return Err(HdError::BudgetStorageFailed);
        }
        let mut journal = Self::create_guarded(path.as_ref(), family, key_secret)?;
        storage(anchor.advance(journal.checkpoint()))?;
        journal.anchor = Some(anchor);
        Ok(journal)
    }
    pub fn open_anchored(
        path: impl AsRef<Path>,
        family: [u8; 32],
        key: [u8; 32],
        anchor: Box<dyn ExternalMonotoneAnchor>,
    ) -> Result<Self, HdError> {
        let key_secret = guard_key(key);
        let minimum = storage(anchor.load())?.ok_or(HdError::BudgetStorageFailed)?;
        let mut journal = Self::open_guarded(path.as_ref(), family, key_secret)?;
        let current = journal.checkpoint();
        if !checkpoint_at_least(current, minimum) {
            return Err(HdError::BudgetStorageFailed);
        }
        storage(anchor.advance(current))?;
        journal.anchor = Some(anchor);
        Ok(journal)
    }
    /// Enroll once. A pre-existing sidecar or journal path (including a dangling symlink)
    /// prevents accidental recreation after deletion.
    pub fn create(
        path: impl AsRef<Path>,
        family: [u8; 32],
        key: [u8; 32],
    ) -> Result<Self, HdError> {
        let key_secret = guard_key(key);
        Self::create_guarded(path.as_ref(), family, key_secret)
    }

    fn create_guarded(
        path: &Path,
        family: [u8; 32],
        key_secret: RedactedSecret<32>,
    ) -> Result<Self, HdError> {
        let path_buf = path.to_path_buf();
        let record = storage(LockedRecord::create_new(&path_buf))?;
        let file = storage(
            storage(no_follow_options())?
                .read(true)
                .write(true)
                .create_new(true)
                .open(&path_buf),
        )?;
        let meta = storage(file.metadata())?;
        if !meta.is_file() {
            return Err(HdError::BudgetStorageFailed);
        }
        let binding = Binding {
            key: key_secret.expose(),
            family: &family,
            lock_seal: record.lock_seal(),
            data_seal: file_identity(&meta),
        };
        let lock_identity = record.lock_identity_seal();
        let genesis_seal_mac = binding.genesis_seal_mac(&lock_identity);
        let (genesis_rec, genesis_mac) = binding.record(0, &[0u8; 32]);
        let (slot_a, slot_b) = binding.with_hwm(|hwm| {
            (
                hwm.encode(0, 0, &genesis_mac),
                hwm.encode(1, 0, &genesis_mac),
            )
        });

        let mut init_buf = [0u8; FILE_PREFIX_BYTES + RECORD];
        init_buf[..RECORD_HEADER_BYTES].copy_from_slice(&record.record_header());
        let payload = &mut init_buf[RECORD_HEADER_BYTES..];
        payload[..DATA_SEAL_BYTES].copy_from_slice(&binding.data_seal);
        payload[DATA_SEAL_BYTES..DATA_SEAL_BYTES + FORMAT_MAGIC.len()]
            .copy_from_slice(FORMAT_MAGIC);
        payload[LOCK_IDENTITY_OFFSET..LOCK_IDENTITY_OFFSET + LOCK_IDENTITY_BYTES]
            .copy_from_slice(&lock_identity);
        payload[GENESIS_SEAL_MAC_OFFSET..GENESIS_SEAL_END].copy_from_slice(&genesis_seal_mac);
        payload[HWM_SLOT_A_PAYLOAD_OFFSET..HWM_SLOT_A_PAYLOAD_OFFSET + HWM_SLOT_BYTES]
            .copy_from_slice(&slot_a);
        payload[HWM_SLOT_B_PAYLOAD_OFFSET..HWM_SLOT_B_PAYLOAD_OFFSET + HWM_SLOT_BYTES]
            .copy_from_slice(&slot_b);
        payload[PAYLOAD_HEADER_BYTES..].copy_from_slice(&genesis_rec);
        storage(write_at_exact(&file, 0, &init_buf))?;
        storage(file.sync_all())?;
        storage(sync_parent_dir(&path_buf))?;

        let verified_payload = storage(record.read_bounded(MAX_BUDGET_PAYLOAD_BYTES))?;
        if !ct_eq_bytes(&verified_payload, &init_buf[RECORD_HEADER_BYTES..]) {
            return Err(HdError::BudgetStorageFailed);
        }

        let data_seal = binding.data_seal;
        Ok(Self {
            path: path_buf,
            record,
            lock_identity,
            file,
            data_seal,
            last_mac: genesis_mac,
            family,
            key: key_secret,
            used: 0,
            failed: false,
            anchor: None,
        })
    }

    /// Recover strictly. Missing, wrong-key, wrong-family, reordered, symlinked,
    /// tail-truncated, or unlinked-and-recreated (new inode) journals fail closed, and so
    /// does damage to any committed record. The one repair besides the slots: up to one
    /// record's worth of unauthenticated bytes after the chain, left by a `reserve`
    /// interrupted while writing its record, is truncated. A record that reached the
    /// disk whole stays spent and the slots are advanced onto it.
    pub fn open(path: impl AsRef<Path>, family: [u8; 32], key: [u8; 32]) -> Result<Self, HdError> {
        let key_secret = guard_key(key);
        Self::open_guarded(path.as_ref(), family, key_secret)
    }

    fn open_guarded(
        path: &Path,
        family: [u8; 32],
        key_secret: RedactedSecret<32>,
    ) -> Result<Self, HdError> {
        let path_buf = path.to_path_buf();
        let record = storage(LockedRecord::open_existing(&path_buf))?;

        let path_meta = storage(fs::symlink_metadata(&path_buf))?;
        if !path_meta.is_file() {
            return Err(HdError::BudgetStorageFailed);
        }
        let file = storage(
            storage(no_follow_options())?
                .read(true)
                .write(true)
                .open(&path_buf),
        )?;
        let file_meta = storage(file.metadata())?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if file_meta.permissions().mode() & 0o077 != 0 {
                return Err(HdError::BudgetStorageFailed);
            }
        }
        if !file_meta.is_file() {
            return Err(HdError::BudgetStorageFailed);
        }
        let data_seal = file_identity(&file_meta);
        if !ct_eq_bytes(&data_seal, &file_identity(&path_meta)) {
            return Err(HdError::BudgetStorageFailed);
        }

        let payload = storage(record.read_bounded(MAX_BUDGET_PAYLOAD_BYTES))?;
        if payload.len() < PAYLOAD_HEADER_BYTES + RECORD
            || &payload[DATA_SEAL_BYTES..DATA_SEAL_BYTES + FORMAT_MAGIC.len()] != FORMAT_MAGIC
        {
            return Err(HdError::BudgetStorageFailed);
        }
        let records_slice = &payload[PAYLOAD_HEADER_BYTES..];
        if records_slice.len() > RECORD * (LIMIT as usize + 1)
            || file_meta.len() != (RECORD_HEADER_BYTES + payload.len()) as u64
            || !ct_eq_bytes(&payload[..DATA_SEAL_BYTES], &data_seal)
        {
            return Err(HdError::BudgetStorageFailed);
        }

        let binding = Binding {
            key: key_secret.expose(),
            family: &family,
            lock_seal: record.lock_seal(),
            data_seal,
        };
        let stored_lock_identity: [u8; LOCK_IDENTITY_BYTES] = payload
            [LOCK_IDENTITY_OFFSET..LOCK_IDENTITY_OFFSET + LOCK_IDENTITY_BYTES]
            .try_into()
            .map_err(|_| HdError::BudgetStorageFailed)?;
        let stored_seal_mac = &payload[GENESIS_SEAL_MAC_OFFSET..GENESIS_SEAL_END];
        let expected_seal_mac = binding.genesis_seal_mac(&stored_lock_identity);
        if !ct_eq_bytes(&stored_lock_identity[16..24], &record.lock_seal())
            || !ct_eq_bytes(stored_seal_mac, &expected_seal_mac)
            || payload[GENESIS_SEAL_END..HWM_SLOT_A_PAYLOAD_OFFSET]
                .iter()
                .any(|&b| b != 0)
        {
            return Err(HdError::BudgetStorageFailed);
        }
        let mut prev_mac = [0u8; 32];
        let mut penultimate_mac = [0u8; 32];
        // Records from the genesis record on that continue the chain. Whatever follows
        // the first one that does not is the tail.
        let mut verified = 0usize;
        for rec_bytes in records_slice.as_chunks::<RECORD>().0 {
            let (expected, mac) = binding.record(verified as u64, &prev_mac);
            if !ct_eq_bytes(&expected, rec_bytes) {
                break;
            }
            penultimate_mac = prev_mac;
            prev_mac = mac;
            verified += 1;
        }
        // The genesis record is never a tail.
        let used = (verified as u64)
            .checked_sub(1)
            .ok_or(HdError::BudgetStorageFailed)?;
        let tail_len = records_slice.len() - verified * RECORD;
        // An interrupted `reserve` leaves at most one record's worth of unauthenticated
        // bytes after the chain. Every readable slot must be on the chain's count
        // or one behind it; a longer tail or wider lag is refused before writing.
        if tail_len > RECORD {
            return Err(HdError::BudgetStorageFailed);
        }
        let slot_a =
            &payload[HWM_SLOT_A_PAYLOAD_OFFSET..HWM_SLOT_A_PAYLOAD_OFFSET + HWM_SLOT_BYTES];
        let slot_b =
            &payload[HWM_SLOT_B_PAYLOAD_OFFSET..HWM_SLOT_B_PAYLOAD_OFFSET + HWM_SLOT_BYTES];

        // `read_bounded` used its own descriptor. Before any repair write, confirm the
        // held `.lock` sidecar matches the MAC-authenticated genesis `stored_lock_identity`
        // (never comparing `record.lock_identity_seal()` tautologically against itself)
        // and the path still names the descriptor held here.
        storage(record.verify_lock_identity(&stored_lock_identity))?;
        verify_data_identity(&path_buf, &file, &data_seal, file_meta.len())?;
        // Rejects tail truncation and unexplained gaps; heals the crash states (record
        // synced before slot A, slot A synced before slot B, one slot torn mid-write).
        storage(binding.with_hwm(|hwm| {
            if tail_len != 0 && !slots_permit_tail_truncation(hwm, slot_a, slot_b, used) {
                return Err(io::Error::other("unexplained journal tail"));
            }
            hwm.recover(
                &file,
                slot_a,
                slot_b,
                &ChainHead {
                    len: used,
                    tip: &prev_mac,
                    previous_tip: &penultimate_mac,
                },
            )
        }))?;
        if tail_len != 0 {
            // Truncate the unauthenticated tail after prefix authentication and converge
            // both HWM slots onto `used`.
            storage(file.set_len((FILE_PREFIX_BYTES + verified * RECORD) as u64))?;
            storage(file.sync_all())?;
            storage(binding.with_hwm(|hwm| hwm.commit(&file, used, &prev_mac)))?;
        }

        verify_data_identity(
            &path_buf,
            &file,
            &data_seal,
            (FILE_PREFIX_BYTES + verified * RECORD) as u64,
        )?;
        Ok(Self {
            path: path_buf,
            record,
            lock_identity: stored_lock_identity,
            file,
            data_seal,
            last_mac: prev_mac,
            family,
            key: key_secret,
            used,
            failed: false,
            anchor: None,
        })
    }

    pub fn family_id(&self) -> [u8; 32] {
        self.family
    }

    pub fn used(&self) -> u64 {
        self.used
    }

    fn binding(&self) -> Binding<'_> {
        Binding {
            key: self.key.expose(),
            family: &self.family,
            lock_seal: self.record.lock_seal(),
            data_seal: self.data_seal,
        }
    }

    fn verify_live_journal_integrity(&self) -> Result<(), HdError> {
        storage(self.record.verify_lock_identity(&self.lock_identity))?;
        let expected_len = (FILE_PREFIX_BYTES + ((self.used as usize) + 1) * RECORD) as u64;
        verify_data_identity(&self.path, &self.file, &self.data_seal, expected_len)
    }

    /// Burns even if later protocol work aborts. Any I/O or path-integrity error
    /// permanently disables this handle without recreating unlinked files.
    pub fn reserve(&mut self) -> Result<(), HdError> {
        if self.failed {
            return Err(HdError::BudgetStorageFailed);
        }
        if self.used >= LIMIT {
            return Err(HdError::EvaluationBudgetExceeded);
        }
        self.failed = true;
        self.verify_live_journal_integrity()?;

        let next_count = self.used + 1;
        let binding = self.binding();
        let (next_rec, next_mac) = binding.record(next_count, &self.last_mac);
        let append_offset = (FILE_PREFIX_BYTES + (next_count as usize) * RECORD) as u64;
        storage(write_at_exact(&self.file, append_offset, &next_rec))?;
        storage(self.file.sync_all())?;
        storage(binding.with_hwm(|hwm| hwm.commit(&self.file, next_count, &next_mac)))?;

        self.last_mac = next_mac;
        self.used = next_count;
        self.verify_live_journal_integrity()?;
        if let Some(anchor) = &self.anchor {
            storage(anchor.advance(self.checkpoint()))?;
        }
        self.failed = false;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::OpenOptions;
    use std::io::Write;

    fn tear_slot_pages(pages: &[u64], recoverable: bool) {
        let dir = std::env::temp_dir().join(alloc::format!(
            "hd-budget-paged-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("budget");
        let mut budget = DurableQueryBudget::create(&path, [1; 32], [2; 32]).unwrap();
        budget.reserve().unwrap();
        let checkpoint = budget.checkpoint();
        drop(budget);
        let file = OpenOptions::new().write(true).open(&path).unwrap();
        for &page in pages {
            write_at_exact(
                &file,
                page * HWM_PAGE_BYTES,
                &[0xa5; HWM_PAGE_BYTES as usize],
            )
            .unwrap();
        }
        file.sync_all().unwrap();
        drop(file);
        let reopened = DurableQueryBudget::open(&path, [1; 32], [2; 32]);
        if recoverable {
            let mut budget = reopened.unwrap();
            assert_eq!(budget.checkpoint(), checkpoint);
            budget.reserve().unwrap();
            assert_eq!(budget.used(), 2);
        } else {
            assert_eq!(reopened.err(), Some(HdError::BudgetStorageFailed));
        }
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn torn_slot_a_page_recovers() {
        tear_slot_pages(&[1], true);
    }
    #[test]
    fn torn_slot_b_page_recovers() {
        tear_slot_pages(&[2], true);
    }
    #[test]
    fn both_slot_pages_torn_fail_closed() {
        tear_slot_pages(&[1, 2], false);
    }

    #[cfg(unix)]
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
        let mut journal = DurableQueryBudget::create(&path, [1; 32], [2; 32]).unwrap();
        journal.reserve().unwrap();
        let checkpoint = journal.checkpoint();
        drop(journal);
        std::fs::OpenOptions::new()
            .write(true)
            .open(&path)
            .unwrap()
            .set_len(FILE_PREFIX_BYTES as u64)
            .unwrap();
        assert!(DurableQueryBudget::open_at_least(&path, [1; 32], [2; 32], checkpoint).is_err());
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_file(path.with_file_name(alloc::format!(
            "{}.lock",
            path.file_name().unwrap().to_str().unwrap()
        )))
        .unwrap();
    }

    #[test]
    fn rejects_replaced_sidecar_and_symlink() {
        use std::os::unix::fs::symlink;
        let dir = std::env::temp_dir().join(alloc::format!(
            "hd-budget-path-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("budget");
        let lock = dir.join("budget.lock");
        let mut budget = DurableQueryBudget::create(&path, [1; 32], [2; 32]).unwrap();
        std::fs::rename(&lock, dir.join("old.lock")).unwrap();
        std::fs::copy(dir.join("old.lock"), &lock).unwrap();
        assert!(DurableQueryBudget::open(&path, [1; 32], [2; 32]).is_err());
        assert!(budget.reserve().is_err());
        drop(budget);
        // Rewriting the copied sidecar's `header[16..32]` (`dev || ino`) to match the new
        // `.lock` inode while keeping `lock_seal` MUST still fail closed (both with untouched
        // Page-0 `lock_identity` and with forged Page-0 `lock_identity`).
        {
            use std::os::unix::fs::PermissionsExt;
            let mut lock_bytes = std::fs::read(&lock).unwrap();
            let new_lock_id = file_identity(&std::fs::symlink_metadata(&lock).unwrap());
            lock_bytes[16..32].copy_from_slice(&new_lock_id);
            std::fs::write(&lock, &lock_bytes).unwrap();
            std::fs::set_permissions(&lock, std::fs::Permissions::from_mode(0o600)).unwrap();
            assert_eq!(
                DurableQueryBudget::open(&path, [1; 32], [2; 32]).err(),
                Some(HdError::BudgetStorageFailed)
            );
            // Also patch unauthenticated `lock_identity` in Page 0 (`[40..64]`) without key:
            // genesis seal MAC rejects it!
            let mut data_bytes = std::fs::read(&path).unwrap();
            data_bytes[RECORD_HEADER_BYTES + LOCK_IDENTITY_OFFSET
                ..RECORD_HEADER_BYTES + LOCK_IDENTITY_OFFSET + 16]
                .copy_from_slice(&new_lock_id);
            std::fs::write(&path, &data_bytes).unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
            assert_eq!(
                DurableQueryBudget::open(&path, [1; 32], [2; 32]).err(),
                Some(HdError::BudgetStorageFailed)
            );
        }
        std::fs::remove_file(&lock).unwrap();
        symlink(dir.join("old.lock"), &lock).unwrap();
        assert!(DurableQueryBudget::open(&path, [1; 32], [2; 32]).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn rejects_live_unlink_offline_unlink_recreate_and_journal_symlinks() {
        use std::os::unix::fs::symlink;
        let dir = std::env::temp_dir().join(alloc::format!(
            "hd-budget-unlink-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();

        // 1. Pre-existing symlink at journal path rejected on `create` without touching target.
        let target = dir.join("innocent-target");
        std::fs::write(&target, b"keep-safe").unwrap();
        let sym_budget = dir.join("sym-budget");
        symlink(&target, &sym_budget).unwrap();
        assert!(DurableQueryBudget::create(&sym_budget, [1; 32], [2; 32]).is_err());
        assert_eq!(std::fs::read(&target).unwrap(), b"keep-safe");

        // 2. Live unlink of `budget` while open MUST fail closed and MUST NOT recreate `budget`.
        let live_path = dir.join("live-budget");
        let mut live_budget = DurableQueryBudget::create(&live_path, [4; 32], [5; 32]).unwrap();
        live_budget.reserve().unwrap();
        assert_eq!(live_budget.used(), 1);
        std::fs::remove_file(&live_path).unwrap();
        assert_eq!(live_budget.reserve(), Err(HdError::BudgetStorageFailed));
        assert!(!live_path.exists());
        // Handle remains permanently disabled even if an attacker drops a file back in place.
        assert_eq!(live_budget.reserve(), Err(HdError::BudgetStorageFailed));
        drop(live_budget);

        // 3. Offline unlink + recreate with saved pre-spend bytes (new inode rollback attack)
        // MUST fail closed even if the attacker patches the unverified header `data_seal`.
        let replay_path = dir.join("replay-budget");
        let mut budget = DurableQueryBudget::create(&replay_path, [7; 32], [8; 32]).unwrap();
        let saved_genesis_bytes = std::fs::read(&replay_path).unwrap();
        for _ in 0..10 {
            budget.reserve().unwrap();
        }
        assert_eq!(budget.used(), 10);
        drop(budget);

        // Unlink the spent journal and recreate a new inode containing `saved_genesis_bytes`
        // (force a distinct inode by holding the spent inode open via rename before writing).
        let parked_old = dir.join("parked-spent");
        std::fs::rename(&replay_path, &parked_old).unwrap();
        std::fs::write(&replay_path, &saved_genesis_bytes).unwrap();
        assert_eq!(
            DurableQueryBudget::open(&replay_path, [7; 32], [8; 32]).err(),
            Some(HdError::BudgetStorageFailed)
        );

        // Even patching the header's `data_seal` to match the new inode fails closed because
        // `data_seal` is cryptographically authenticated inside `QSAG.HD.QUERY_BUDGET.V3`.
        let new_meta = std::fs::symlink_metadata(&replay_path).unwrap();
        let forged_seal = file_identity(&new_meta);
        let mut patched = saved_genesis_bytes.clone();
        patched[16..32].copy_from_slice(&forged_seal);
        std::fs::write(&replay_path, &patched).unwrap();
        assert_eq!(
            DurableQueryBudget::open(&replay_path, [7; 32], [8; 32]).err(),
            Some(HdError::BudgetStorageFailed)
        );

        // 4. Replacing `replay_path` with a symlink to `parked_old` (which still has the
        // original `(dev, ino)` and valid MACs!) MUST STILL fail closed on `open`.
        std::fs::remove_file(&replay_path).unwrap();
        symlink(&parked_old, &replay_path).unwrap();
        assert_eq!(
            DurableQueryBudget::open(&replay_path, [7; 32], [8; 32]).err(),
            Some(HdError::BudgetStorageFailed)
        );

        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn restart_lock_corruption_missing_and_exhaustion() {
        let dir = std::env::temp_dir().join(alloc::format!(
            "hd-budget-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("budget");
        let mut budget = DurableQueryBudget::create(&path, [1; 32], [2; 32]).unwrap();
        assert!(DurableQueryBudget::open(&path, [1; 32], [2; 32]).is_err());
        for _ in 0..127 {
            budget.reserve().unwrap();
        }
        drop(budget);
        assert!(DurableQueryBudget::open(&path, [3; 32], [2; 32]).is_err());
        assert!(DurableQueryBudget::open(&path, [1; 32], [3; 32]).is_err());
        let mut budget = DurableQueryBudget::open(&path, [1; 32], [2; 32]).unwrap();
        assert_eq!(budget.used(), 127);
        budget.reserve().unwrap();
        drop(budget);
        let mut budget = DurableQueryBudget::open(&path, [1; 32], [2; 32]).unwrap();
        assert_eq!(budget.reserve(), Err(HdError::EvaluationBudgetExceeded));
        drop(budget);
        OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap()
            .write_all(&[0])
            .unwrap();
        assert!(DurableQueryBudget::open(&path, [1; 32], [2; 32]).is_err());
        std::fs::remove_file(&path).unwrap();
        assert!(DurableQueryBudget::open(&path, [1; 32], [2; 32]).is_err());
        assert!(DurableQueryBudget::create(&path, [1; 32], [2; 32]).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    fn junk(len: usize, seed: u64) -> alloc::vec::Vec<u8> {
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

    /// A budget with two uses spent, closed.
    struct TwoUses {
        dir: PathBuf,
        path: PathBuf,
        /// The file with both uses committed (genesis record plus two).
        committed: alloc::vec::Vec<u8>,
        /// The record a third use appends.
        next: [u8; RECORD],
        /// The file after that third use committed.
        advanced: alloc::vec::Vec<u8>,
        checkpoint: LedgerCheckpoint,
    }

    impl TwoUses {
        fn new(tag: &str) -> Self {
            let dir = std::env::temp_dir().join(alloc::format!(
                "hd-budget-{tag}-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            std::fs::create_dir(&dir).unwrap();
            let path = dir.join("budget");
            let mut budget = DurableQueryBudget::create(&path, [1; 32], [2; 32]).unwrap();
            budget.reserve().unwrap();
            budget.reserve().unwrap();
            let checkpoint = budget.checkpoint();
            let committed = std::fs::read(&path).unwrap();
            assert_eq!(committed.len(), FILE_PREFIX_BYTES + 3 * RECORD);
            budget.reserve().unwrap();
            drop(budget);
            let advanced = std::fs::read(&path).unwrap();
            let next = advanced[committed.len()..].try_into().unwrap();
            // `fs::write` truncates in place: the inode the MACs bind is kept.
            std::fs::write(&path, &committed).unwrap();
            Self {
                dir,
                path,
                committed,
                next,
                advanced,
                checkpoint,
            }
        }
        /// Put the committed file back, followed by `tail`.
        fn with_tail(&self, tail: &[u8]) -> alloc::vec::Vec<u8> {
            let mut bytes = self.committed.clone();
            bytes.extend_from_slice(tail);
            std::fs::write(&self.path, &bytes).unwrap();
            bytes
        }
        fn open(&self) -> Result<DurableQueryBudget, HdError> {
            DurableQueryBudget::open_at_least(&self.path, [1; 32], [2; 32], self.checkpoint)
        }
        /// Recovery lands on the two committed uses with the tail gone, and the budget
        /// then spends the third use as if the tear had never happened.
        fn assert_recovers_and_continues(&self) {
            let mut budget = self.open().unwrap();
            assert_eq!(budget.used(), 2);
            assert_eq!(budget.checkpoint(), self.checkpoint);
            assert_eq!(std::fs::read(&self.path).unwrap(), self.committed);
            budget.reserve().unwrap();
            assert_eq!(budget.used(), 3);
            drop(budget);
            let budget = self.open().unwrap();
            assert_eq!(budget.used(), 3);
            drop(budget);
            assert_eq!(std::fs::read(&self.path).unwrap(), self.advanced);
        }
        /// Recovery refuses the file as it stands and leaves every byte alone.
        fn assert_fails_closed(&self, on_disk: &[u8]) {
            assert_eq!(self.open().err(), Some(HdError::BudgetStorageFailed));
            assert_eq!(
                DurableQueryBudget::open(&self.path, [1; 32], [2; 32]).err(),
                Some(HdError::BudgetStorageFailed)
            );
            assert_eq!(std::fs::read(&self.path).unwrap(), on_disk);
        }
    }

    impl Drop for TwoUses {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }

    #[test]
    fn torn_tail_record_is_truncated_and_the_budget_continues() {
        let budget = TwoUses::new("tail-partial");
        for cut in [1, 7, 8, 9, RECORD - 1] {
            // A prefix of the real record, a prefix that never left the page cache as
            // data (zeros), and arbitrary bytes.
            for tail in [
                budget.next[..cut].to_vec(),
                alloc::vec![0; cut],
                junk(cut, cut as u64),
            ] {
                budget.with_tail(&tail);
                budget.assert_recovers_and_continues();
            }
        }
        // The tear may coincide with one unreadable slot; the other still marks the chain.
        for page in [1, 2] {
            budget.with_tail(&budget.next[..17]);
            let file = OpenOptions::new().write(true).open(&budget.path).unwrap();
            write_at_exact(&file, page * HWM_PAGE_BYTES, &junk(HWM_SLOT_BYTES, 31)).unwrap();
            drop(file);
            budget.assert_recovers_and_continues();
        }
    }

    #[test]
    fn full_length_unauthenticated_tail_is_truncated() {
        let budget = TwoUses::new("tail-full");
        let mut bad_mac = budget.next;
        bad_mac[RECORD - 1] ^= 1;
        let mut bad_count = budget.next;
        bad_count[0] ^= 1;
        for tail in [
            bad_mac.to_vec(),
            bad_count.to_vec(),
            alloc::vec![0; RECORD],
            junk(RECORD, 5),
        ] {
            budget.with_tail(&tail);
            budget.assert_recovers_and_continues();
        }
    }

    #[test]
    fn synced_unacknowledged_record_is_rolled_forward_not_truncated() {
        let budget = TwoUses::new("tail-valid");
        budget.with_tail(&budget.next);
        let reopened = budget.open().unwrap();
        assert_eq!(reopened.used(), 3);
        drop(reopened);
        assert_eq!(std::fs::read(&budget.path).unwrap(), budget.advanced);
    }

    #[test]
    fn torn_tail_never_excuses_a_corrupt_committed_record() {
        let budget = TwoUses::new("tail-corrupt");
        // Record 0 is the genesis record; 1 and 2 are the committed uses.
        for record in [0, 1, 2] {
            for index in [0, 7, 8, RECORD - 1] {
                for tail in [
                    &budget.next[..17],
                    &junk(RECORD, 7)[..],
                    &budget.next[..],
                    &[][..],
                ] {
                    let mut bytes = budget.with_tail(tail);
                    bytes[FILE_PREFIX_BYTES + record * RECORD + index] ^= 1;
                    std::fs::write(&budget.path, &bytes).unwrap();
                    budget.assert_fails_closed(&bytes);
                }
            }
        }
    }

    #[test]
    fn torn_tail_never_excuses_a_slot_ahead_of_the_chain() {
        let budget = TwoUses::new("tail-short");
        // Keep the genesis record alone, then genesis plus one use; the slots say two.
        for kept in [1, 2] {
            for tail in [
                &budget.next[..17],
                &junk(RECORD, 9)[..],
                &junk(RECORD - 1, 10)[..],
            ] {
                let mut bytes = budget.committed[..FILE_PREFIX_BYTES + kept * RECORD].to_vec();
                bytes.extend_from_slice(tail);
                std::fs::write(&budget.path, &bytes).unwrap();
                budget.assert_fails_closed(&bytes);
            }
        }
        // One slot ahead of the other is the crash between the two slot writes; the record
        // it points at must be there, torn tail or not.
        let slot_a = HWM_PAGE_BYTES as usize..HWM_PAGE_BYTES as usize + HWM_SLOT_BYTES;
        let mut ahead = budget.committed.clone();
        ahead[slot_a.clone()].copy_from_slice(&budget.advanced[slot_a]);
        for tail in [&budget.next[..17], &junk(RECORD, 11)[..], &[][..]] {
            let mut bytes = ahead.clone();
            bytes.extend_from_slice(tail);
            std::fs::write(&budget.path, &bytes).unwrap();
            budget.assert_fails_closed(&bytes);
        }
    }

    #[test]
    fn tail_longer_than_one_record_fails_closed() {
        let budget = TwoUses::new("tail-long");
        for len in [RECORD + 1, 2 * RECORD - 1, 2 * RECORD, 4096] {
            let bytes = budget.with_tail(&junk(len, len as u64));
            budget.assert_fails_closed(&bytes);
        }
        // A synced record the slots have not reached, followed by more than one record's
        // worth of unauthenticated bytes, still fails closed.
        for extra in [RECORD + 1, 2 * RECORD] {
            let mut tail = budget.next.to_vec();
            tail.extend_from_slice(&junk(extra, 3));
            let bytes = budget.with_tail(&tail);
            budget.assert_fails_closed(&bytes);
        }
        // An unauthenticated record followed by an authentic-looking one is no better.
        let mut tail = junk(RECORD, 4);
        tail.extend_from_slice(&budget.next);
        let bytes = budget.with_tail(&tail);
        budget.assert_fails_closed(&bytes);
    }

    #[test]
    fn failed_reservation_stays_poisoned_before_and_after_append() {
        struct FailingAnchor;
        impl ExternalMonotoneAnchor for FailingAnchor {
            fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
                Ok(None)
            }
            fn advance(&self, _: LedgerCheckpoint) -> io::Result<()> {
                Err(io::Error::other("injected anchor failure"))
            }
        }
        let fixture = TwoUses::new("failed-reserve");
        std::fs::write(&fixture.path, &fixture.committed).unwrap();
        let mut live = fixture.open().unwrap();
        // Same inode and length, but the held descriptor cannot write.
        live.file = File::open(&fixture.path).unwrap();
        assert_eq!(live.reserve(), Err(HdError::BudgetStorageFailed));
        assert_eq!(live.used(), 2);
        live.file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(&fixture.path)
            .unwrap();
        assert_eq!(live.reserve(), Err(HdError::BudgetStorageFailed));
        assert_eq!(std::fs::read(&fixture.path).unwrap(), fixture.committed);
        drop(live);
        // Fail after record + slots have reached disk: that use must remain burned.
        let mut live = fixture.open().unwrap();
        live.anchor = Some(Box::new(FailingAnchor));
        assert_eq!(live.reserve(), Err(HdError::BudgetStorageFailed));
        assert_eq!(live.used(), 3);
        assert_eq!(std::fs::read(&fixture.path).unwrap(), fixture.advanced);
        live.anchor = None;
        assert_eq!(live.reserve(), Err(HdError::BudgetStorageFailed));
        drop(live);
        let mut recovered = fixture.open().unwrap();
        assert_eq!(recovered.used(), 3);
        recovered.reserve().unwrap();
        assert_eq!(recovered.used(), 4);
    }

    #[test]
    fn lone_lagging_slot_with_every_torn_tail_length() {
        let journal = TwoUses::new("lone-lag-tail");
        for damaged in [HWM_PAGE_BYTES as usize, 2 * HWM_PAGE_BYTES as usize] {
            for tail_len in 1..=RECORD {
                let mut bytes = journal.committed.clone();
                bytes.extend_from_slice(&journal.next);
                bytes.extend_from_slice(&junk(tail_len, 71));
                bytes[damaged..damaged + HWM_SLOT_BYTES].fill(0xa5);
                std::fs::write(&journal.path, &bytes).unwrap();
                let recovered = journal.open().unwrap();
                assert_eq!(recovered.used(), 3);
                drop(recovered);
                assert_eq!(std::fs::read(&journal.path).unwrap(), journal.advanced);
            }
        }
        // A valid survivor two records behind cannot justify truncating a tail.
        let mut live = journal.open().unwrap();
        live.reserve().unwrap();
        drop(live);
        let advanced_twice = std::fs::read(&journal.path).unwrap();
        for tail_len in 1..=RECORD {
            let mut bytes = advanced_twice.clone();
            bytes[HWM_PAGE_BYTES as usize..HWM_PAGE_BYTES as usize + HWM_SLOT_BYTES].fill(0xa5);
            bytes[2 * HWM_PAGE_BYTES as usize..2 * HWM_PAGE_BYTES as usize + HWM_SLOT_BYTES]
                .copy_from_slice(
                    &journal.committed
                        [2 * HWM_PAGE_BYTES as usize..2 * HWM_PAGE_BYTES as usize + HWM_SLOT_BYTES],
                );
            bytes.extend_from_slice(&junk(tail_len, 72));
            std::fs::write(&journal.path, &bytes).unwrap();
            journal.assert_fails_closed(&bytes);
        }
    }

    #[test]
    fn lagging_slots_with_torn_tail_recover_and_converge_hwm() {
        let budget = TwoUses::new("tail-lagging-slots");
        // Case 1: `used = c + 1` (`3` uses synced, both HWM slots still at `c = 2`)
        // alongside `1..=RECORD` stray trailing bytes.
        for extra in [1, 17, RECORD] {
            let mut tail = budget.next.to_vec();
            tail.extend_from_slice(&junk(extra, 3));
            budget.with_tail(&tail);
            let reopened = budget.open().unwrap();
            assert_eq!(reopened.used(), 3);
            drop(reopened);
            assert_eq!(std::fs::read(&budget.path).unwrap(), budget.advanced);
        }

        // Case 2: `Slot A = c` (`3`) and `Slot B = c - 1` (`2`) with `used = c` (`3`)
        // alongside `1..=RECORD` torn trailing bytes of a fourth attempt.
        let slot_b = 2 * HWM_PAGE_BYTES as usize..2 * HWM_PAGE_BYTES as usize + HWM_SLOT_BYTES;
        for extra in [1, 17, RECORD] {
            let mut mixed = budget.advanced.clone();
            mixed[slot_b.clone()].copy_from_slice(&budget.committed[slot_b.clone()]);
            mixed.extend_from_slice(&junk(extra, 19));
            std::fs::write(&budget.path, &mixed).unwrap();
            let reopened = budget.open().unwrap();
            assert_eq!(reopened.used(), 3);
            drop(reopened);
            assert_eq!(std::fs::read(&budget.path).unwrap(), budget.advanced);
        }
    }

    #[cfg(unix)]
    #[test]
    fn unanchored_open_rejects_same_inode_tail_truncation() {
        let dir = std::env::temp_dir().join(alloc::format!(
            "hd-budget-unanchored-tail-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("budget");
        let mut budget = DurableQueryBudget::create(&path, [9; 32], [10; 32]).unwrap();
        budget.reserve().unwrap();
        budget.reserve().unwrap();
        assert_eq!(budget.used(), 2);
        drop(budget);

        // Truncate the last 40-byte record on the same inode (attempting to rewind `used = 2 -> 1`).
        std::fs::OpenOptions::new()
            .write(true)
            .open(&path)
            .unwrap()
            .set_len((FILE_PREFIX_BYTES + 2 * RECORD) as u64)
            .unwrap();

        // Even `open()` WITHOUT an external anchor must fail closed due to in-file HWM slots!
        assert_eq!(
            DurableQueryBudget::open(&path, [9; 32], [10; 32]).err(),
            Some(HdError::BudgetStorageFailed)
        );
        std::fs::remove_dir_all(dir).unwrap();
    }
}
