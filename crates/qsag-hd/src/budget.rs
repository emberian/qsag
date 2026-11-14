//! Durable family query budgets. An attempted disclosure is burned before release.
//! Files and their permanent lock sidecars belong in trusted local storage. Recovery
//! never creates missing state. Restoring an older valid filesystem snapshot still
//! requires an external monotonic anchor; a MAC alone cannot detect full-disk rollback,
//! though unlinking and recreating the budget journal on a new inode fails closed.
use crate::HdError;
use alloc::boxed::Box;
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use qsag_accel::ct::{RedactedSecret, ct_eq_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_asm::durable::LockedRecord;
use std::fs::{self, File, Metadata, OpenOptions};
use std::io::{self, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

const LIMIT: u64 = 128;
const RECORD: usize = 40;
const RECORD_MAGIC: &[u8; 8] = b"QSAGREC1";
const PAYLOAD_HEADER_BYTES: usize = 16;
const FILE_PREFIX_BYTES: usize = 16 + PAYLOAD_HEADER_BYTES;

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

fn invalid_io() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        "invalid or replaced durable query budget journal",
    )
}

fn no_follow_options() -> io::Result<OpenOptions> {
    let mut options = OpenOptions::new();
    #[cfg(all(target_os = "linux", any(target_arch = "aarch64", target_arch = "arm")))]
    let flags = 0x8000 | 0x800; // O_NOFOLLOW | O_NONBLOCK
    #[cfg(all(
        target_os = "linux",
        any(
            target_arch = "x86_64",
            target_arch = "x86",
            target_arch = "riscv64",
            target_arch = "riscv32"
        )
    ))]
    let flags = 0x20000 | 0x800; // O_NOFOLLOW | O_NONBLOCK
    #[cfg(target_os = "macos")]
    let flags = 0x100 | 0x4; // O_NOFOLLOW | O_NONBLOCK
    #[cfg(any(
        target_os = "macos",
        all(
            target_os = "linux",
            any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86",
                target_arch = "riscv64",
                target_arch = "riscv32"
            )
        )
    ))]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600).custom_flags(flags);
        Ok(options)
    }
    #[cfg(not(any(
        target_os = "macos",
        all(
            target_os = "linux",
            any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86",
                target_arch = "riscv64",
                target_arch = "riscv32"
            )
        )
    )))]
    {
        let _ = &mut options;
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "no-follow budget journal unavailable on this target",
        ))
    }
}

fn file_identity(meta: &Metadata) -> [u8; 16] {
    let mut id = [0u8; 16];
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        id[..8].copy_from_slice(&meta.dev().to_le_bytes());
        id[8..].copy_from_slice(&meta.ino().to_le_bytes());
    }
    id
}

fn sync_parent_dir(path: &Path) -> io::Result<()> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    File::open(parent)?.sync_all()
}

fn compute_record_bytes(
    key: &[u8; 32],
    family: &[u8; 32],
    lock_seal: &[u8; 8],
    data_seal: &[u8; 16],
    count: u64,
    prev_mac: &[u8; 32],
) -> ([u8; RECORD], [u8; 32]) {
    let mut out = [0u8; RECORD];
    out[..8].copy_from_slice(&count.to_le_bytes());
    let mac = cshake256_framed_32(
        b"QSAG.HD.QUERY_BUDGET.V2",
        &[
            key,
            family,
            lock_seal,
            data_seal,
            &LIMIT.to_le_bytes(),
            &out[..8],
            prev_mac,
        ],
    );
    out[8..].copy_from_slice(&mac);
    (out, mac)
}

impl DurableQueryBudget {
    pub fn checkpoint(&self) -> LedgerCheckpoint {
        LedgerCheckpoint { generation: self.used, tag: self.last_mac }
    }
    pub fn open_at_least(path: impl AsRef<Path>, family: [u8; 32], key: [u8; 32], minimum: LedgerCheckpoint) -> Result<Self, HdError> {
        let journal = Self::open(path, family, key)?;
        let current = journal.checkpoint();
        if current.generation < minimum.generation ||
            (current.generation == minimum.generation && current.tag != minimum.tag) {
            return Err(HdError::BudgetStorageFailed);
        }
        Ok(journal)
    }
    pub fn create_anchored(path: impl AsRef<Path>, family: [u8; 32], key: [u8; 32], anchor: Box<dyn ExternalMonotoneAnchor>) -> Result<Self, HdError> {
        if storage(anchor.load())?.is_some() { return Err(HdError::BudgetStorageFailed); }
        let mut journal = Self::create(path, family, key)?;
        storage(anchor.advance(journal.checkpoint()))?;
        journal.anchor = Some(anchor);
        Ok(journal)
    }
    pub fn open_anchored(path: impl AsRef<Path>, family: [u8; 32], key: [u8; 32], anchor: Box<dyn ExternalMonotoneAnchor>) -> Result<Self, HdError> {
        let minimum = storage(anchor.load())?.ok_or(HdError::BudgetStorageFailed)?;
        let mut journal = Self::open_at_least(path, family, key, minimum)?;
        storage(anchor.advance(journal.checkpoint()))?;
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
        let path_buf = path.as_ref().to_path_buf();
        let record = storage(LockedRecord::create_new(&path_buf))?;
        let key_secret = RedactedSecret::new(key);
        let mut file = storage(
            storage(no_follow_options())?
                .read(true)
                .write(true)
                .create_new(true)
                .open(&path_buf),
        )?;
        let meta = storage(file.metadata())?;
        if meta.file_type().is_symlink() || !meta.is_file() {
            return Err(HdError::BudgetStorageFailed);
        }
        let data_seal = file_identity(&meta);
        let lock_seal = record.lock_seal();
        let (genesis_rec, genesis_mac) = compute_record_bytes(
            key_secret.expose(),
            &family,
            &lock_seal,
            &data_seal,
            0,
            &[0u8; 32],
        );

        let mut init_buf = [0u8; FILE_PREFIX_BYTES + RECORD];
        init_buf[..8].copy_from_slice(RECORD_MAGIC);
        init_buf[8..16].copy_from_slice(&lock_seal);
        init_buf[16..32].copy_from_slice(&data_seal);
        init_buf[32..].copy_from_slice(&genesis_rec);
        storage(file.write_all(&init_buf))?;
        storage(file.sync_all())?;
        storage(sync_parent_dir(&path_buf))?;

        let verified_payload = storage(record.read())?;
        if verified_payload.len() != PAYLOAD_HEADER_BYTES + RECORD
            || !ct_eq_bytes(&verified_payload[..16], &data_seal)
            || !ct_eq_bytes(&verified_payload[16..], &genesis_rec)
        {
            return Err(HdError::BudgetStorageFailed);
        }

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
    /// or unlinked-and-recreated (new inode) journals fail closed.
    pub fn open(path: impl AsRef<Path>, family: [u8; 32], key: [u8; 32]) -> Result<Self, HdError> {
        let path_buf = path.as_ref().to_path_buf();
        let record = storage(LockedRecord::open_existing(&path_buf))?;
        let key_secret = RedactedSecret::new(key);

        let path_meta = storage(fs::symlink_metadata(&path_buf))?;
        if path_meta.file_type().is_symlink() || !path_meta.is_file() {
            return Err(HdError::BudgetStorageFailed);
        }
        let mut file = storage(
            storage(no_follow_options())?
                .read(true)
                .write(true)
                .create(false)
                .open(&path_buf),
        )?;
        let file_meta = storage(file.metadata())?;
        if file_meta.file_type().is_symlink() || !file_meta.is_file() {
            return Err(HdError::BudgetStorageFailed);
        }
        let actual_data_seal = file_identity(&file_meta);
        if !ct_eq_bytes(&actual_data_seal, &file_identity(&path_meta)) {
            return Err(HdError::BudgetStorageFailed);
        }

        let payload = storage(record.read())?;
        if payload.len() < PAYLOAD_HEADER_BYTES + RECORD {
            return Err(HdError::BudgetStorageFailed);
        }
        let records_slice = &payload[PAYLOAD_HEADER_BYTES..];
        if records_slice.is_empty()
            || records_slice.len() > RECORD * (LIMIT as usize + 1)
            || records_slice.len() % RECORD != 0
            || file_meta.len() != (16 + payload.len()) as u64
            || !ct_eq_bytes(&payload[..PAYLOAD_HEADER_BYTES], &actual_data_seal)
        {
            return Err(HdError::BudgetStorageFailed);
        }

        let lock_seal = record.lock_seal();
        let mut prev_mac = [0u8; 32];
        let mut used = 0u64;
        for (i, rec_bytes) in records_slice.as_chunks::<RECORD>().0.iter().enumerate() {
            let count = i as u64;
            let (expected, mac) = compute_record_bytes(
                key_secret.expose(),
                &family,
                &lock_seal,
                &actual_data_seal,
                count,
                &prev_mac,
            );
            if !ct_eq_bytes(&expected, rec_bytes) {
                return Err(HdError::BudgetStorageFailed);
            }
            prev_mac = mac;
            used = count;
        }
        storage(file.seek(SeekFrom::End(0)))?;

        Ok(Self {
            path: path_buf,
            record,
            file,
            data_seal: actual_data_seal,
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

    fn verify_live_journal_integrity(&self) -> Result<(), HdError> {
        let path_meta = storage(fs::symlink_metadata(&self.path))?;
        if path_meta.file_type().is_symlink()
            || !path_meta.is_file()
            || !ct_eq_bytes(&file_identity(&path_meta), &self.data_seal)
        {
            return storage(Err(invalid_io()));
        }
        let expected_records_len = ((self.used as usize) + 1) * RECORD;
        let expected_file_len = (FILE_PREFIX_BYTES + expected_records_len) as u64;
        let fd_meta = storage(self.file.metadata())?;
        if fd_meta.file_type().is_symlink()
            || !fd_meta.is_file()
            || !ct_eq_bytes(&file_identity(&fd_meta), &self.data_seal)
            || fd_meta.len() != expected_file_len
        {
            return storage(Err(invalid_io()));
        }
        let payload = storage(self.record.read())?;
        if payload.len() != PAYLOAD_HEADER_BYTES + expected_records_len
            || !ct_eq_bytes(&payload[..PAYLOAD_HEADER_BYTES], &self.data_seal)
            || !ct_eq_bytes(&payload[payload.len() - 32..], &self.last_mac)
        {
            return storage(Err(invalid_io()));
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

        let next_count = self
            .used
            .checked_add(1)
            .ok_or(HdError::BudgetStorageFailed)?;
        let lock_seal = self.record.lock_seal();
        let (next_rec, next_mac) = compute_record_bytes(
            self.key.expose(),
            &self.family,
            &lock_seal,
            &self.data_seal,
            next_count,
            &self.last_mac,
        );
        storage(self.file.seek(SeekFrom::End(0)))?;
        storage(self.file.write_all(&next_rec))?;
        storage(self.file.sync_all())?;

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

    #[cfg(unix)]
    #[test]
    fn retained_checkpoint_rejects_same_inode_tail_truncation() {
        let path = std::env::temp_dir().join(alloc::format!("retained-tail-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let mut journal = DurableQueryBudget::create(&path, [1; 32], [2; 32]).unwrap();
        journal.reserve().unwrap();
        let checkpoint = journal.checkpoint();
        drop(journal);
        std::fs::OpenOptions::new().write(true).open(&path).unwrap().set_len(FILE_PREFIX_BYTES as u64).unwrap();
        assert!(DurableQueryBudget::open_at_least(&path, [1; 32], [2; 32], checkpoint).is_err());
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_file(path.with_file_name(alloc::format!("{}.lock", path.file_name().unwrap().to_str().unwrap()))).unwrap();
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
}
