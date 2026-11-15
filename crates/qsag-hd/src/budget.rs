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
    ChainHead, CounterOrder, HWM_SLOT_BYTES, LockedRecord, RECORD_HEADER_BYTES, TwoSlotHwm,
    file_identity, no_follow_options, sync_parent_dir, write_at_exact,
};
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use std::fs::{self, File};
use std::io;
use std::path::{Path, PathBuf};

const LIMIT: u64 = 128;
const RECORD: usize = 40;
const DATA_SEAL_BYTES: usize = 16;
const HWM_SLOT_A_PAYLOAD_OFFSET: usize = DATA_SEAL_BYTES;
const HWM_SLOT_B_PAYLOAD_OFFSET: usize = DATA_SEAL_BYTES + HWM_SLOT_BYTES;
const PAYLOAD_HEADER_BYTES: usize = DATA_SEAL_BYTES + 2 * HWM_SLOT_BYTES; // 176 bytes
const FILE_PREFIX_BYTES: usize = RECORD_HEADER_BYTES + PAYLOAD_HEADER_BYTES; // 192 bytes
const MAX_BUDGET_PAYLOAD_BYTES: usize = PAYLOAD_HEADER_BYTES + RECORD * (LIMIT as usize + 1);

/// Append-only authenticated journal, held under an exclusive OS lock and pinned
/// to the genesis regular-file `(dev, ino)` identity across both live `reserve()`
/// calls and offline `open()` recovery.
/// No Clone, reset, truncate, restore-counter or increase-limit operation exists.
pub struct DurableQueryBudget {
    path: PathBuf,
    record: LockedRecord,
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
/// the family, the lock sidecar's seal and the data file's `(dev, ino)`.
struct Binding<'a> {
    key: &'a [u8; 32],
    family: &'a [u8; 32],
    lock_seal: [u8; 8],
    data_seal: [u8; 16],
}

impl Binding<'_> {
    /// Record `count` of the chain and its MAC, which is the next record's `prev_mac`.
    fn record(&self, count: u64, prev_mac: &[u8; 32]) -> ([u8; RECORD], [u8; 32]) {
        let mut out = [0u8; RECORD];
        out[..8].copy_from_slice(&count.to_le_bytes());
        let mac = cshake256_framed_32(
            b"QSAG.HD.QUERY_BUDGET.V2",
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
                b"QSAG.HD.QUERY_BUDGET.HWM.V3",
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
        f(&TwoSlotHwm {
            offset_a: (RECORD_HEADER_BYTES + HWM_SLOT_A_PAYLOAD_OFFSET) as u64,
            offset_b: (RECORD_HEADER_BYTES + HWM_SLOT_B_PAYLOAD_OFFSET) as u64,
            order: CounterOrder::Little,
            mac: &mac,
        })
    }
}

fn checkpoint_at_least(current: LedgerCheckpoint, minimum: LedgerCheckpoint) -> bool {
    current.generation > minimum.generation
        || (current.generation == minimum.generation && ct_eq_bytes(&current.tag, &minimum.tag))
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
        let (genesis_rec, genesis_mac) = binding.record(0, &[0u8; 32]);
        let (slot_a, slot_b) =
            binding.with_hwm(|hwm| (hwm.encode(0, 0, &genesis_mac), hwm.encode(1, 0, &genesis_mac)));

        let mut init_buf = [0u8; FILE_PREFIX_BYTES + RECORD];
        init_buf[..RECORD_HEADER_BYTES].copy_from_slice(&record.record_header());
        let payload = &mut init_buf[RECORD_HEADER_BYTES..];
        payload[..DATA_SEAL_BYTES].copy_from_slice(&binding.data_seal);
        payload[HWM_SLOT_A_PAYLOAD_OFFSET..HWM_SLOT_B_PAYLOAD_OFFSET].copy_from_slice(&slot_a);
        payload[HWM_SLOT_B_PAYLOAD_OFFSET..PAYLOAD_HEADER_BYTES].copy_from_slice(&slot_b);
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

    /// Recover strictly. Missing, torn, wrong-key, wrong-family, reordered, symlinked,
    /// tail-truncated, or unlinked-and-recreated (new inode) journals fail closed.
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
        if !file_meta.is_file() {
            return Err(HdError::BudgetStorageFailed);
        }
        let data_seal = file_identity(&file_meta);
        if !ct_eq_bytes(&data_seal, &file_identity(&path_meta)) {
            return Err(HdError::BudgetStorageFailed);
        }

        let payload = storage(record.read_bounded(MAX_BUDGET_PAYLOAD_BYTES))?;
        if payload.len() < PAYLOAD_HEADER_BYTES + RECORD {
            return Err(HdError::BudgetStorageFailed);
        }
        let records_slice = &payload[PAYLOAD_HEADER_BYTES..];
        if records_slice.len() > RECORD * (LIMIT as usize + 1)
            || records_slice.len() % RECORD != 0
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
        let mut prev_mac = [0u8; 32];
        let mut penultimate_mac = [0u8; 32];
        let mut used = 0u64;
        for (i, rec_bytes) in records_slice.as_chunks::<RECORD>().0.iter().enumerate() {
            let count = i as u64;
            penultimate_mac = prev_mac;
            let (expected, mac) = binding.record(count, &prev_mac);
            if !ct_eq_bytes(&expected, rec_bytes) {
                return Err(HdError::BudgetStorageFailed);
            }
            prev_mac = mac;
            used = count;
        }

        // Rejects tail truncation and unexplained gaps; heals the two crash states
        // (record synced before slot A, slot A synced before slot B).
        storage(binding.with_hwm(|hwm| {
            hwm.recover(
                &file,
                &payload[HWM_SLOT_A_PAYLOAD_OFFSET..HWM_SLOT_B_PAYLOAD_OFFSET],
                &payload[HWM_SLOT_B_PAYLOAD_OFFSET..PAYLOAD_HEADER_BYTES],
                &ChainHead {
                    len: used,
                    tip: &prev_mac,
                    previous_tip: &penultimate_mac,
                },
            )
        }))?;

        Ok(Self {
            path: path_buf,
            record,
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
        let path_meta = storage(fs::symlink_metadata(&self.path))?;
        if !path_meta.is_file() || !ct_eq_bytes(&file_identity(&path_meta), &self.data_seal) {
            return Err(HdError::BudgetStorageFailed);
        }
        let expected_records_len = ((self.used as usize) + 1) * RECORD;
        let fd_meta = storage(self.file.metadata())?;
        if !fd_meta.is_file()
            || !ct_eq_bytes(&file_identity(&fd_meta), &self.data_seal)
            || fd_meta.len() != (FILE_PREFIX_BYTES + expected_records_len) as u64
        {
            return Err(HdError::BudgetStorageFailed);
        }
        let (slot_a, slot_b) = self.binding().with_hwm(|hwm| {
            (
                hwm.encode(0, self.used, &self.last_mac),
                hwm.encode(1, self.used, &self.last_mac),
            )
        });
        let payload = storage(self.record.read_bounded(MAX_BUDGET_PAYLOAD_BYTES))?;
        if payload.len() != PAYLOAD_HEADER_BYTES + expected_records_len
            || !ct_eq_bytes(&payload[..DATA_SEAL_BYTES], &self.data_seal)
            || !ct_eq_bytes(
                &payload[HWM_SLOT_A_PAYLOAD_OFFSET..HWM_SLOT_B_PAYLOAD_OFFSET],
                &slot_a,
            )
            || !ct_eq_bytes(
                &payload[HWM_SLOT_B_PAYLOAD_OFFSET..PAYLOAD_HEADER_BYTES],
                &slot_b,
            )
            || !ct_eq_bytes(&payload[payload.len() - 32..], &self.last_mac)
        {
            return Err(HdError::BudgetStorageFailed);
        }
        Ok(())
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
        // `data_seal` is cryptographically authenticated inside `QSAG.HD.QUERY_BUDGET.V2`.
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
