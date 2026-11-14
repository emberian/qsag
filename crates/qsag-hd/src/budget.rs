//! Durable family query budgets. An attempted disclosure is burned before release.
//! Files and their permanent lock sidecars belong in trusted local storage. Recovery
//! never creates missing state. Restoring an older valid filesystem snapshot still
//! requires an external monotonic anchor; a MAC alone cannot detect rollback.
use crate::HdError;
use alloc::vec::Vec;
use qsag_accel::ct::{RedactedSecret, ct_eq_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

const LIMIT: u64 = 128;
const RECORD: usize = 40;

/// Append-only authenticated journal, held under an exclusive OS lock.
/// No Clone, reset, truncate, restore-counter or increase-limit operation exists.
pub struct DurableQueryBudget {
    file: File,
    _lock: File,
    family: [u8; 32],
    key: RedactedSecret<32>,
    used: u64,
    failed: bool,
}
fn storage<T>(value: std::io::Result<T>) -> Result<T, HdError> {
    value.map_err(|_| HdError::BudgetStorageFailed)
}
fn options() -> OpenOptions {
    let mut options = OpenOptions::new();
    options.read(true).write(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    options
}
fn lock_path(path: &Path) -> PathBuf {
    let mut name = path.as_os_str().to_os_string();
    name.push(".lock");
    PathBuf::from(name)
}
impl DurableQueryBudget {
    /// Enroll once. A pre-existing sidecar prevents accidental recreation after deletion.
    pub fn create(
        path: impl AsRef<Path>,
        family: [u8; 32],
        key: [u8; 32],
    ) -> Result<Self, HdError> {
        let path = path.as_ref();
        let lock = storage(options().create_new(true).open(lock_path(path)))?;
        lock.try_lock().map_err(|_| HdError::BudgetStorageFailed)?;
        let file = storage(options().create_new(true).append(true).open(path))?;
        let mut out = Self {
            file,
            _lock: lock,
            family,
            key: RedactedSecret::new(key),
            used: 0,
            failed: false,
        };
        out.append(0)?;
        let parent = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        storage(storage(File::open(parent))?.sync_all())?;
        Ok(out)
    }
    /// Recover strictly. Missing, torn, wrong-key, wrong-family and reordered records fail.
    pub fn open(path: impl AsRef<Path>, family: [u8; 32], key: [u8; 32]) -> Result<Self, HdError> {
        let path = path.as_ref();
        let lock = storage(options().open(lock_path(path)))?;
        lock.try_lock().map_err(|_| HdError::BudgetStorageFailed)?;
        let mut file = storage(options().append(true).open(path))?;
        let len = storage(file.metadata())?.len();
        if len == 0 || len > RECORD as u64 * (LIMIT + 1) || len % RECORD as u64 != 0 {
            return Err(HdError::BudgetStorageFailed);
        }
        let mut bytes = Vec::new();
        storage(
            (&mut file)
                .take(RECORD as u64 * (LIMIT + 1) + 1)
                .read_to_end(&mut bytes),
        )?;
        if bytes.len() as u64 != len {
            return Err(HdError::BudgetStorageFailed);
        }
        let mut out = Self {
            file,
            _lock: lock,
            family,
            key: RedactedSecret::new(key),
            used: 0,
            failed: false,
        };
        for (i, record) in bytes.as_chunks::<RECORD>().0.iter().enumerate() {
            let expected = out.record(i as u64);
            if !ct_eq_bytes(&expected, record) {
                return Err(HdError::BudgetStorageFailed);
            }
            out.used = i as u64;
        }
        Ok(out)
    }
    pub fn family_id(&self) -> [u8; 32] {
        self.family
    }
    pub fn used(&self) -> u64 {
        self.used
    }
    fn record(&self, count: u64) -> [u8; RECORD] {
        let mut out = [0; RECORD];
        out[..8].copy_from_slice(&count.to_le_bytes());
        let mac = cshake256_framed_32(
            b"QSAG.HD.QUERY_BUDGET.V1",
            &[
                self.key.expose(),
                &self.family,
                &LIMIT.to_le_bytes(),
                &out[..8],
            ],
        );
        out[8..].copy_from_slice(&mac);
        out
    }
    fn append(&mut self, count: u64) -> Result<(), HdError> {
        self.failed = true;
        storage(self.file.write_all(&self.record(count)))?;
        storage(self.file.sync_all())?;
        self.failed = false;
        Ok(())
    }
    /// Burns even if later protocol work aborts. Any I/O error disables this handle.
    pub fn reserve(&mut self) -> Result<(), HdError> {
        if self.failed {
            return Err(HdError::BudgetStorageFailed);
        }
        if self.used >= LIMIT {
            return Err(HdError::EvaluationBudgetExceeded);
        }
        self.append(self.used + 1)?;
        self.used += 1;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
