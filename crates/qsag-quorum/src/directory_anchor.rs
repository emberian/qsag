//! Fsynced dual-slot checkpoint authority. Its directory must reside in a
//! rollback domain independent of the journals it protects.
use qsag_asm::durable::LockedRecord;
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use std::{io, path::Path, sync::Mutex};

use crate::hash::{SecretKey, mac32, mac32_verify};

pub struct FsDirectoryMonotoneAnchor {
    state: Mutex<State>,
}
struct State {
    slots: [LockedRecord; 2],
    key: [u8; 32],
    current: Option<LedgerCheckpoint>,
    failed: bool,
}
impl Drop for State {
    fn drop(&mut self) {
        qsag_core::wipe::wipe_bytes32(&mut self.key);
    }
}
fn same_checkpoint(a: Option<LedgerCheckpoint>, b: Option<LedgerCheckpoint>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => {
            a.generation == b.generation && qsag_core::wipe::ct_eq_bytes32(&a.tag, &b.tag)
        }
        (None, None) => true,
        _ => false,
    }
}

fn invalid() -> io::Error {
    io::Error::other("monotone directory anchor failed or rolled back")
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
        if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
            std::fs::File::open(parent)?.sync_all()?;
        }
        let slots = [
            LockedRecord::create_new(path.join("slot_a"))?,
            LockedRecord::create_new(path.join("slot_b"))?,
        ];
        let state = State {
            slots,
            key: key.0,
            current: None,
            failed: false,
        };
        for slot in &state.slots {
            slot.replace(&state.encode(slot, None))?;
        }
        std::fs::File::open(path)?.sync_all()?;
        Ok(Self {
            state: Mutex::new(state),
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
        let slots = [
            LockedRecord::open_existing(path.join("slot_a"))?,
            LockedRecord::open_existing(path.join("slot_b"))?,
        ];
        let mut state = State {
            slots,
            key: key.0,
            current: None,
            failed: false,
        };
        state.current = state.read()?;
        Ok(Self {
            state: Mutex::new(state),
        })
    }
}
impl State {
    fn encode(&self, slot: &LockedRecord, checkpoint: Option<LedgerCheckpoint>) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(73);
        bytes.push(u8::from(checkpoint.is_some()));
        let checkpoint = checkpoint.unwrap_or(LedgerCheckpoint {
            generation: 0,
            tag: [0; 32],
        });
        bytes.extend_from_slice(&checkpoint.generation.to_be_bytes());
        bytes.extend_from_slice(&checkpoint.tag);
        let tag = mac32(
            &self.key,
            b"QSAG.DIRECTORY.ANCHOR.V1",
            &[&slot.lock_seal(), &bytes],
        );
        bytes.extend_from_slice(&tag);
        bytes
    }
    fn read(&self) -> io::Result<Option<LedgerCheckpoint>> {
        let mut best: Option<LedgerCheckpoint> = None;
        for slot in &self.slots {
            let bytes = slot.read()?;
            if bytes.len() != 73 || bytes[0] > 1 {
                return Err(invalid());
            }
            let tag: [u8; 32] = bytes[41..].try_into().map_err(|_| invalid())?;
            if !mac32_verify(
                &self.key,
                b"QSAG.DIRECTORY.ANCHOR.V1",
                &[&slot.lock_seal(), &bytes[..41]],
                &tag,
            ) {
                return Err(invalid());
            }
            if bytes[0] == 0 {
                if bytes[1..41].iter().any(|&b| b != 0) {
                    return Err(invalid());
                }
                continue;
            }
            let checkpoint = LedgerCheckpoint {
                generation: u64::from_be_bytes(bytes[1..9].try_into().map_err(|_| invalid())?),
                tag: bytes[9..41].try_into().map_err(|_| invalid())?,
            };
            if let Some(old) = best {
                if old.generation == checkpoint.generation
                    && !qsag_core::wipe::ct_eq_bytes32(&old.tag, &checkpoint.tag)
                {
                    return Err(invalid());
                }
                if old.generation > checkpoint.generation {
                    continue;
                }
            }
            best = Some(checkpoint);
        }
        Ok(best)
    }
    fn check_live(&mut self) -> io::Result<()> {
        if self.failed {
            return Err(invalid());
        }
        self.failed = true;
        if !same_checkpoint(self.read()?, self.current) {
            return Err(invalid());
        }
        self.failed = false;
        Ok(())
    }
}
impl ExternalMonotoneAnchor for FsDirectoryMonotoneAnchor {
    fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
        let mut state = self.state.lock().map_err(|_| invalid())?;
        state.check_live()?;
        Ok(state.current)
    }
    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        let mut state = self.state.lock().map_err(|_| invalid())?;
        state.check_live()?;
        state.failed = true;
        if let Some(old) = state.current
            && (checkpoint.generation < old.generation
                || (checkpoint.generation == old.generation
                    && !qsag_core::wipe::ct_eq_bytes32(&checkpoint.tag, &old.tag)))
        {
            return Err(invalid());
        }
        // Both copies become durable before acknowledging. A crash between copies
        // recovers the higher generation; equal-generation updates are idempotent.
        for slot in &state.slots {
            slot.replace(&state.encode(slot, Some(checkpoint)))?;
        }
        state.current = Some(checkpoint);
        state.failed = false;
        Ok(())
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
        for name in ["slot_a", "slot_b", "slot_a.lock", "slot_b.lock"] {
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
}
