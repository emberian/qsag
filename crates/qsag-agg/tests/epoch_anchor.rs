#![cfg(all(feature = "std", unix))]

use qsag_agg::sig::{EpochWalSink, ExternalMonotoneAnchor, FsWalEpochSink, LedgerCheckpoint};
use std::sync::{Arc, Mutex};

#[derive(Clone, Default)]
struct Anchor(Arc<Mutex<Option<LedgerCheckpoint>>>);

impl ExternalMonotoneAnchor for Anchor {
    fn load(&self) -> std::io::Result<Option<LedgerCheckpoint>> {
        Ok(*self.0.lock().unwrap())
    }
    fn advance(&self, next: LedgerCheckpoint) -> std::io::Result<()> {
        let mut old = self.0.lock().unwrap();
        if old.is_some_and(|old| {
            old.generation > next.generation
                || (old.generation == next.generation && old.tag != next.tag)
        }) {
            return Err(std::io::Error::other("rollback"));
        }
        *old = Some(next);
        Ok(())
    }
}

#[test]
fn anchored_epoch_rejects_rollback_and_replaced_lock() {
    let dir = std::process::Command::new("mktemp")
        .arg("-d")
        .output()
        .unwrap();
    assert!(dir.status.success());
    let dir = std::path::PathBuf::from(String::from_utf8(dir.stdout).unwrap().trim());
    let path = dir.join("epoch");
    let anchor = Anchor::default();
    let root = [42; 32];
    let key = [73; 32];
    let (mut wal, _) =
        FsWalEpochSink::create_anchored(&path, &root, key, Box::new(anchor.clone())).unwrap();
    let genesis = std::fs::read(&path).unwrap();
    wal.persist_latched_epoch(&root, 1, 0, &[7; 32]).unwrap();
    let latest = std::fs::read(&path).unwrap();
    drop(wal);
    std::fs::write(&path, &genesis).unwrap();
    assert!(FsWalEpochSink::open_anchored(&path, &root, key, Box::new(anchor.clone())).is_err());
    std::fs::write(&path, &latest).unwrap();
    let (wal, recovered) =
        FsWalEpochSink::open_anchored(&path, &root, key, Box::new(anchor.clone())).unwrap();
    assert_eq!(recovered, Some((1, 0, [7; 32])));
    drop(wal);
    assert!(FsWalEpochSink::open_or_recover(&path, &root, key).is_err());

    // Replacing the sidecar with identical bytes still changes the permanent identity.
    let lock = dir.join("epoch.lock");
    let lock_bytes = std::fs::read(&lock).unwrap();
    std::fs::rename(&lock, dir.join("old-lock")).unwrap();
    std::fs::write(&lock, lock_bytes).unwrap();
    assert!(FsWalEpochSink::open_anchored(&path, &root, key, Box::new(anchor)).is_err());
    assert!(FsWalEpochSink::open_or_recover(&path, &root, key).is_err());
    std::fs::remove_dir_all(dir).unwrap();
}
