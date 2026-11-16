//! Fsynced dual-slot checkpoint authority. Its directory must reside in a
//! rollback domain independent of the journals it protects.
//!
//! The directory is private (`0700`) and holds one [`TwoSlotRecord`] (`genesis`,
//! `slot_a`, `slot_b`). Nothing outside retains a minimum for it, so every advance
//! is mirrored into both slots before it is acknowledged: the loss of either slot
//! then recovers the acknowledged checkpoint, never its predecessor.
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint, TwoSlotPaths, TwoSlotRecord};
use std::{io, path::Path, sync::Mutex};

use crate::hash::SecretKey;

const DOMAIN: &[u8] = b"QSAG.DIRECTORY.ANCHOR.V2";
const CHECKPOINT_LEN: usize = 8 + 32;

pub struct FsDirectoryMonotoneAnchor {
    record: Mutex<TwoSlotRecord>,
}

fn invalid() -> io::Error {
    io::Error::other("monotone directory anchor failed or rolled back")
}
fn paths(directory: &Path) -> TwoSlotPaths {
    TwoSlotPaths {
        genesis: directory.join("genesis"),
        slots: [directory.join("slot_a"), directory.join("slot_b")],
    }
}
fn encode(checkpoint: LedgerCheckpoint) -> [u8; CHECKPOINT_LEN] {
    let mut bytes = [0; CHECKPOINT_LEN];
    bytes[..8].copy_from_slice(&checkpoint.generation.to_be_bytes());
    bytes[8..].copy_from_slice(&checkpoint.tag);
    bytes
}
/// An empty payload is the unenrolled authority.
fn decode(payload: &[u8]) -> io::Result<Option<LedgerCheckpoint>> {
    if payload.is_empty() {
        return Ok(None);
    }
    let bytes: &[u8; CHECKPOINT_LEN] = payload.try_into().map_err(|_| invalid())?;
    Ok(Some(LedgerCheckpoint {
        generation: u64::from_be_bytes(bytes[..8].try_into().map_err(|_| invalid())?),
        tag: bytes[8..].try_into().map_err(|_| invalid())?,
    }))
}
impl FsDirectoryMonotoneAnchor {
    /// Provision an empty authority. Existing directories are never overwritten.
    pub fn create_new(path: impl AsRef<Path>, key: [u8; 32]) -> io::Result<Self> {
        let key = SecretKey(key);
        let path = path.as_ref();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            std::fs::DirBuilder::new().mode(0o700).create(path)?;
        }
        #[cfg(not(unix))]
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "private directories require Unix permissions",
        ));
        qsag_asm::durable::sync_parent_dir(path)?;
        let record = TwoSlotRecord::create(paths(path), key.0, DOMAIN, CHECKPOINT_LEN, &[])?;
        std::fs::File::open(path)?.sync_all()?;
        Ok(Self {
            record: Mutex::new(record),
        })
    }
    pub fn open_existing(path: impl AsRef<Path>, key: [u8; 32]) -> io::Result<Self> {
        let key = SecretKey(key);
        let path = path.as_ref();
        let metadata = std::fs::symlink_metadata(path)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o077 != 0 {
                return Err(invalid());
            }
        }
        if !metadata.is_dir() {
            return Err(invalid());
        }
        let record = TwoSlotRecord::open(paths(path), key.0, DOMAIN, CHECKPOINT_LEN, None)?;
        decode(&record.read()?)?;
        Ok(Self {
            record: Mutex::new(record),
        })
    }
}
impl ExternalMonotoneAnchor for FsDirectoryMonotoneAnchor {
    fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
        let record = self.record.lock().map_err(|_| invalid())?;
        decode(&record.read()?)
    }
    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        let mut record = self.record.lock().map_err(|_| invalid())?;
        match decode(&record.read()?)? {
            Some(old)
                if old.generation == checkpoint.generation
                    && qsag_core::wipe::ct_eq_bytes32(&old.tag, &checkpoint.tag) =>
            {
                Ok(())
            }
            // A refused advance means the caller and this authority disagree about
            // history; the handle stops answering until it is reopened.
            Some(old) if old.generation >= checkpoint.generation => {
                record.latch_failure();
                Err(invalid())
            }
            _ => record.commit_mirrored(&encode(checkpoint)).map(|_| ()),
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    #[test]
    fn directory_and_records_are_private_and_symlinks_are_rejected() {
        use std::os::unix::fs::{PermissionsExt, symlink};
        let root = std::env::temp_dir().join(format!(
            "private-anchor-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let anchor = FsDirectoryMonotoneAnchor::create_new(&root, [7; 32]).unwrap();
        assert_eq!(
            std::fs::metadata(&root).unwrap().permissions().mode() & 0o777,
            0o700
        );
        for name in [
            "genesis",
            "slot_a",
            "slot_b",
            "genesis.lock",
            "slot_a.lock",
            "slot_b.lock",
        ] {
            assert_eq!(
                std::fs::metadata(root.join(name))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o777,
                0o600
            );
        }
        drop(anchor);
        let link = root.with_extension("link");
        symlink(&root, &link).unwrap();
        assert!(FsDirectoryMonotoneAnchor::open_existing(&link, [7; 32]).is_err());
        std::fs::remove_file(link).unwrap();
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o755)).unwrap();
        assert!(FsDirectoryMonotoneAnchor::open_existing(&root, [7; 32]).is_err());
        std::fs::remove_dir_all(root).unwrap();
    }
    use super::*;
    #[test]
    fn durable_dual_slot_authority_rejects_rollback_and_latches_failure() {
        let path = std::env::temp_dir().join(format!(
            "directory-anchor-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let anchor = FsDirectoryMonotoneAnchor::create_new(&path, [9; 32]).unwrap();
        assert_eq!(anchor.load().unwrap(), None);
        let first = LedgerCheckpoint {
            generation: 1,
            tag: [1; 32],
        };
        let second = LedgerCheckpoint {
            generation: 2,
            tag: [2; 32],
        };
        anchor.advance(first).unwrap();
        anchor.advance(second).unwrap();
        anchor.advance(second).unwrap();
        assert!(anchor.advance(first).is_err());
        assert!(anchor.load().is_err());
        assert!(anchor.advance(second).is_err());
        drop(anchor);
        let anchor = FsDirectoryMonotoneAnchor::open_existing(&path, [9; 32]).unwrap();
        assert_eq!(anchor.load().unwrap(), Some(second));
        assert!(
            anchor
                .advance(LedgerCheckpoint {
                    generation: 2,
                    tag: [3; 32]
                })
                .is_err()
        );
        drop(anchor);
        std::fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn an_acknowledged_advance_survives_the_loss_of_either_slot() {
        for lost in ["slot_a", "slot_b"] {
            let path = std::env::temp_dir().join(format!(
                "directory-anchor-mirror-{lost}-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            let anchor = FsDirectoryMonotoneAnchor::create_new(&path, [9; 32]).unwrap();
            let checkpoint = |generation: u64| LedgerCheckpoint {
                generation,
                tag: [generation as u8; 32],
            };
            anchor.advance(checkpoint(1)).unwrap();
            anchor.advance(checkpoint(5)).unwrap();
            drop(anchor);
            std::fs::write(path.join(lost), b"torn").unwrap();
            assert!(FsDirectoryMonotoneAnchor::open_existing(&path, [8; 32]).is_err());
            let anchor = FsDirectoryMonotoneAnchor::open_existing(&path, [9; 32]).unwrap();
            assert_eq!(anchor.load().unwrap(), Some(checkpoint(5)));
            assert!(anchor.advance(checkpoint(4)).is_err());
            drop(anchor);
            let anchor = FsDirectoryMonotoneAnchor::open_existing(&path, [9; 32]).unwrap();
            anchor.advance(checkpoint(6)).unwrap();
            drop(anchor);
            std::fs::write(path.join("slot_a"), b"torn").unwrap();
            std::fs::write(path.join("slot_b"), b"torn").unwrap();
            assert!(FsDirectoryMonotoneAnchor::open_existing(&path, [9; 32]).is_err());
            std::fs::remove_dir_all(path).unwrap();
        }
    }
}
