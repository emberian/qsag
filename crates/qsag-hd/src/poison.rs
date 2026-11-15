//! Caller-provided durable family quarantine for standard and embedded custody.
#[cfg(feature = "std")]
pub type PoisonJournalError = std::io::Error;
#[cfg(not(feature = "std"))]
pub type PoisonJournalError = crate::HdError;
pub type JournalResult<T> = Result<T, PoisonJournalError>;
fn unsupported() -> PoisonJournalError {
    #[cfg(feature = "std")]
    {
        std::io::Error::other("disclosure transactions unsupported")
    }
    #[cfg(not(feature = "std"))]
    {
        crate::HdError::MacCheckFailed
    }
}
pub trait HdPoisonJournal: Send + Sync {
    fn is_poisoned(&self) -> JournalResult<bool>;
    fn poison(&self) -> JournalResult<()>;
    fn family_id(&self) -> [u8; 32];
    /// Persist quarantine before releasing MAC material. Unsupported journals fail closed.
    fn begin_disclosure(&self, _session: [u8; 32]) -> JournalResult<()> {
        Err(unsupported())
    }
    fn disclosure_active(&self, _session: [u8; 32]) -> JournalResult<bool> {
        Ok(false)
    }
    fn complete_disclosure(&self, _session: [u8; 32]) -> JournalResult<()> {
        Err(unsupported())
    }
}

pub use HdPoisonJournal as PoisonJournal;
#[cfg(feature = "std")]
pub use filesystem::FsHdPoisonJournal;

#[cfg(feature = "std")]
mod filesystem {
    use super::HdPoisonJournal;
    use qsag_accel::ct::{RedactedSecret, ct_eq_bytes};
    use qsag_accel::keccak::cshake256_framed_32;
    use qsag_asm::durable::LockedRecord;
    use std::io;

    pub struct FsHdPoisonJournal {
        lock_id: [u8; 16],
        record: LockedRecord,
        family: [u8; 32],
        key: RedactedSecret<32>,
        failed: std::sync::atomic::AtomicBool,
        active: std::sync::Mutex<Option<[u8; 32]>>,
    }
    impl FsHdPoisonJournal {
        pub fn create_new(
            path: impl Into<std::path::PathBuf>,
            family: [u8; 32],
            key: [u8; 32],
        ) -> io::Result<Self> {
            let record = LockedRecord::create_new(path)?;
            let lock_id = record.lock_inode();
            let this = Self {
                lock_id,
                record,
                family,
                key: RedactedSecret::new(key),
                failed: std::sync::atomic::AtomicBool::new(false),
                active: std::sync::Mutex::new(None),
            };
            this.persist(false)?;
            Ok(this)
        }
        pub fn open_existing(
            path: impl Into<std::path::PathBuf>,
            family: [u8; 32],
            key: [u8; 32],
        ) -> io::Result<Self> {
            let record = LockedRecord::open_existing(path)?;
            let lock_id = record.lock_inode();
            let this = Self {
                lock_id,
                record,
                family,
                key: RedactedSecret::new(key),
                failed: std::sync::atomic::AtomicBool::new(false),
                active: std::sync::Mutex::new(None),
            };
            this.is_poisoned()?;
            Ok(this)
        }
        fn tag(&self, flag: u8) -> [u8; 32] {
            cshake256_framed_32(
                b"QSAG.HD.POISON.V2",
                &[
                    self.key.expose(),
                    &self.family,
                    &self.lock_id,
                    &self.record.lock_seal(),
                    &[flag],
                ],
            )
        }
        fn read_authenticated(&self) -> io::Result<alloc::vec::Vec<u8>> {
            let result = (|| {
                if self.failed.load(std::sync::atomic::Ordering::Acquire) {
                    return Err(io::Error::other("HD poison journal failed"));
                }
                let bytes = self.record.read()?;
                if bytes.len() != 33
                    || bytes[0] > 1
                    || !ct_eq_bytes(&bytes[1..], &self.tag(bytes[0]))
                {
                    return Err(io::Error::other("invalid HD poison journal"));
                }
                Ok(bytes)
            })();
            if result.is_err() {
                self.failed
                    .store(true, std::sync::atomic::Ordering::Release);
            }
            result
        }
        fn persist(&self, poisoned: bool) -> io::Result<()> {
            use std::sync::atomic::Ordering;
            if self.failed.load(Ordering::Acquire) {
                return Err(io::Error::other("HD poison journal failed"));
            }
            let result = self.persist_inner(poisoned);
            if result.is_err() {
                self.failed.store(true, Ordering::Release);
            }
            result
        }
        fn persist_inner(&self, poisoned: bool) -> io::Result<()> {
            let mut bytes = [0; 33];
            bytes[0] = u8::from(poisoned);
            let tag = self.tag(bytes[0]);
            bytes[1..].copy_from_slice(&tag);
            self.record.replace(&bytes)
        }
    }
    impl HdPoisonJournal for FsHdPoisonJournal {
        fn family_id(&self) -> [u8; 32] {
            self.family
        }
        fn is_poisoned(&self) -> io::Result<bool> {
            if self.failed.load(std::sync::atomic::Ordering::Acquire)
                || self
                    .active
                    .lock()
                    .map_err(|_| io::Error::other("poison journal mutex"))?
                    .is_some()
            {
                return Ok(true);
            }
            let bytes = self.read_authenticated()?;
            if bytes.len() != 33 || bytes[0] > 1 || !ct_eq_bytes(&bytes[1..], &self.tag(bytes[0])) {
                self.failed
                    .store(true, std::sync::atomic::Ordering::Release);
                return Err(io::Error::other("invalid HD poison journal"));
            }
            Ok(bytes[0] != 0)
        }
        fn disclosure_active(&self, session: [u8; 32]) -> io::Result<bool> {
            if self.failed.load(std::sync::atomic::Ordering::Acquire) {
                return Ok(false);
            }
            let active = self
                .active
                .lock()
                .map_err(|_| io::Error::other("poison journal mutex"))?;
            let bytes = self.read_authenticated()?;
            Ok(*active == Some(session)
                && bytes.len() == 33
                && bytes[0] == 1
                && ct_eq_bytes(&bytes[1..], &self.tag(1)))
        }
        fn poison(&self) -> io::Result<()> {
            let mut active = self
                .active
                .lock()
                .map_err(|_| io::Error::other("poison journal mutex"))?;
            self.persist(true)?;
            *active = None;
            Ok(())
        }
        fn begin_disclosure(&self, session: [u8; 32]) -> io::Result<()> {
            let mut active = self
                .active
                .lock()
                .map_err(|_| io::Error::other("poison journal mutex"))?;
            if active.is_some() {
                return Err(io::Error::other("disclosure already active"));
            }
            let bytes = self.read_authenticated()?;
            if bytes.len() != 33 || bytes[0] != 0 || !ct_eq_bytes(&bytes[1..], &self.tag(0)) {
                return Err(io::Error::other("family quarantined"));
            }
            self.persist(true)?;
            *active = Some(session);
            Ok(())
        }
        fn complete_disclosure(&self, session: [u8; 32]) -> io::Result<()> {
            let mut active = self
                .active
                .lock()
                .map_err(|_| io::Error::other("poison journal mutex"))?;
            if *active != Some(session) {
                return Err(io::Error::other("disclosure session mismatch"));
            }
            self.persist(false)?;
            *active = None;
            Ok(())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn pending_disclosure_survives_process_loss_and_success_releases_it() {
            let dir = std::env::temp_dir().join(std::format!(
                "hd-pending-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            std::fs::create_dir(&dir).unwrap();
            let path = dir.join("journal");
            let journal = FsHdPoisonJournal::create_new(&path, [1; 32], [2; 32]).unwrap();
            journal.begin_disclosure([3; 32]).unwrap();
            assert!(journal.is_poisoned().unwrap());
            assert!(journal.disclosure_active([3; 32]).unwrap());
            assert!(journal.begin_disclosure([4; 32]).is_err());
            assert!(journal.complete_disclosure([4; 32]).is_err());
            journal.complete_disclosure([3; 32]).unwrap();
            drop(journal);
            let journal = FsHdPoisonJournal::open_existing(&path, [1; 32], [2; 32]).unwrap();
            assert!(!journal.is_poisoned().unwrap());
            journal.begin_disclosure([5; 32]).unwrap();
            drop(journal); // No abort handler: models loss of the process after disclosure.
            let journal = FsHdPoisonJournal::open_existing(&path, [1; 32], [2; 32]).unwrap();
            assert!(journal.is_poisoned().unwrap());
            assert!(journal.begin_disclosure([6; 32]).is_err());
            drop(journal);
            std::fs::remove_dir_all(dir).unwrap();
        }
        #[test]
        fn poison_survives_restart_and_rejects_wrong_family() {
            let path = std::env::temp_dir().join(std::format!(
                "hd-poison-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            let journal = FsHdPoisonJournal::create_new(&path, [1; 32], [2; 32]).unwrap();
            assert!(!journal.is_poisoned().unwrap());
            journal.poison().unwrap();
            drop(journal);
            assert!(FsHdPoisonJournal::open_existing(&path, [3; 32], [2; 32]).is_err());
            let journal = FsHdPoisonJournal::open_existing(&path, [1; 32], [2; 32]).unwrap();
            assert!(journal.is_poisoned().unwrap());
            drop(journal);
            std::fs::remove_file(&path).unwrap();
            std::fs::remove_file(std::format!("{}.lock", path.display())).unwrap();
        }
    }
}
