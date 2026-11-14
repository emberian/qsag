//! Authenticated two-slot snapshots under a permanent genesis lock.
//! An independently retained checkpoint is a minimum generation, not an exact snapshot:
//! recovery also accepts a durable successor whose external checkpoint was not yet saved.
use crate::{
    sponge::Cshake256Xof,
    wipe::{ct_eq_bytes32, wipe_bytes32},
};
use alloc::{collections::BTreeMap, vec::Vec};
use qsag_asm::durable::LockedRecord;

/// Persist outside the snapshot's rollback domain before releasing reserved material.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LedgerCheckpoint {
    pub generation: u64,
    pub tag: [u8; 32],
}

/// Independently durable, per-resource rollback protection (for example a TPM or
/// remote monotonic service). The anchor must not share the WAL's rollback domain.
/// `advance` atomically rejects older generations and unequal tags at equal generation;
/// success means the checkpoint survives a crash. A fresh resource returns `None`.
pub trait ExternalMonotoneAnchor: Send + Sync {
    fn load(&self) -> std::io::Result<Option<LedgerCheckpoint>>;
    fn advance(&self, checkpoint: LedgerCheckpoint) -> std::io::Result<()>;
}

pub(crate) fn advance_anchor(
    anchor: &dyn ExternalMonotoneAnchor,
    checkpoint: LedgerCheckpoint,
) -> std::io::Result<()> {
    if let Some(old) = anchor.load()?
        && (old.generation > checkpoint.generation
            || (old.generation == checkpoint.generation && old.tag != checkpoint.tag))
    {
        return Err(std::io::Error::other(
            "external anchor rejects rolled-back state",
        ));
    }
    anchor.advance(checkpoint)
}

pub(crate) struct Ledger {
    genesis: LockedRecord,
    slots: [Option<LockedRecord>; 2],
    slot_seals: [[u8; 8]; 2],
    paths: [std::path::PathBuf; 2],
    key: [u8; 32],
    domain: &'static [u8],
    ledger_id: [u8; 32],
    checkpoint: LedgerCheckpoint,
    failed: bool,
}
const LIMIT: usize = 16 * 1024 * 1024;
type Records = BTreeMap<Vec<u8>, Vec<u8>>;
impl Drop for Ledger {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.key);
    }
}
fn slot_paths(path: &std::path::Path) -> [std::path::PathBuf; 2] {
    [".slot_a", ".slot_b"].map(|suffix| {
        let mut name = path.as_os_str().to_os_string();
        name.push(suffix);
        name.into()
    })
}
impl Ledger {
    pub(crate) fn create(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
        domain: &'static [u8],
    ) -> Result<Self, ()> {
        use std::io::Read;
        let path = path.into();
        let genesis = LockedRecord::create_new(path.clone()).map_err(|_| ())?;
        let paths = slot_paths(&path);
        let slots = [
            LockedRecord::create_new(&paths[0]).map_err(|_| ())?,
            LockedRecord::create_new(&paths[1]).map_err(|_| ())?,
        ];
        let slot_seals = slots.each_ref().map(LockedRecord::lock_seal);
        let slots = slots.map(Some);
        let mut ledger_id = [0; 32];
        std::fs::File::open("/dev/urandom")
            .map_err(|_| ())?
            .read_exact(&mut ledger_id)
            .map_err(|_| ())?;
        let mut this = Self {
            genesis,
            slots,
            slot_seals,
            paths,
            key,
            domain,
            ledger_id,
            checkpoint: LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
            failed: false,
        };
        // Provision both slot sidecars before sealing genesis. An interrupted genesis
        // never becomes a usable authority and cannot be silently reprovisioned.
        this.slots[1]
            .as_ref()
            .ok_or(())?
            .replace(&[])
            .map_err(|_| ())?;
        this.genesis
            .replace(&this.genesis_bytes())
            .map_err(|_| ())?;
        this.write(&Records::new(), 0)?;
        Ok(this)
    }
    pub(crate) fn open(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
        domain: &'static [u8],
        checkpoint: LedgerCheckpoint,
    ) -> Result<Self, ()> {
        let path = path.into();
        let genesis = LockedRecord::open_existing(&path).map_err(|_| ())?;
        let bytes = genesis.read().map_err(|_| ())?;
        if bytes.len() != 88 || &bytes[..8] != b"QSAGLDG2" {
            return Err(());
        }
        let ledger_id = bytes[8..40].try_into().map_err(|_| ())?;
        let paths = slot_paths(&path);
        // acquire retains existing sidecars even when a slot file is missing. The
        // genesis seal below rejects replacement or recreation of either sidecar.
        let slot_seals = [
            bytes[40..48].try_into().map_err(|_| ())?,
            bytes[48..56].try_into().map_err(|_| ())?,
        ];
        // One damaged slot must not hide the other authenticated snapshot. A
        // missing/replaced sidecar makes that slot unavailable for future writes;
        // recovery can still read the surviving generation under the genesis lock.
        let slots = core::array::from_fn(|i| {
            LockedRecord::acquire(&paths[i])
                .ok()
                .filter(|slot| slot.lock_seal() == slot_seals[i])
        });
        let mut this = Self {
            genesis,
            slots,
            slot_seals,
            paths,
            key,
            domain,
            ledger_id,
            checkpoint,
            failed: false,
        };
        this.check_genesis()?;
        let mut best = None;
        for slot in 0..2 {
            if let Ok((candidate, _)) = this.read_slot(slot) {
                if candidate.generation < checkpoint.generation {
                    continue;
                }
                if candidate.generation == checkpoint.generation
                    && !ct_eq_bytes32(&candidate.tag, &checkpoint.tag)
                {
                    continue;
                }
                if best.is_none_or(|old: LedgerCheckpoint| candidate.generation > old.generation) {
                    best = Some(candidate);
                }
            }
        }
        this.checkpoint = best.ok_or(())?;
        Ok(this)
    }
    pub(crate) fn checkpoint(&self) -> LedgerCheckpoint {
        self.checkpoint
    }
    fn tag(&self, purpose: &[u8], bytes: &[u8]) -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.LEDGER.MAC/v2");
        xof.absorb(&(self.domain.len() as u64).to_le_bytes());
        xof.absorb(self.domain);
        xof.absorb(&self.key);
        xof.absorb(&self.genesis.lock_seal());
        xof.absorb(&self.ledger_id);
        xof.absorb(purpose);
        xof.absorb(bytes);
        let mut tag = [0; 32];
        xof.squeeze(&mut tag);
        tag
    }
    fn genesis_bytes(&self) -> Vec<u8> {
        let mut bytes = b"QSAGLDG2".to_vec();
        bytes.extend_from_slice(&self.ledger_id);
        for seal in &self.slot_seals {
            bytes.extend_from_slice(seal);
        }
        bytes.extend_from_slice(&self.tag(b"genesis", &bytes));
        bytes
    }
    fn check_genesis(&self) -> Result<(), ()> {
        if self.failed || self.genesis.read().map_err(|_| ())? != self.genesis_bytes() {
            return Err(());
        }
        Ok(())
    }
    fn read_slot(&self, slot: usize) -> Result<(LedgerCheckpoint, Records), ()> {
        let meta = std::fs::symlink_metadata(&self.paths[slot]).map_err(|_| ())?;
        if !meta.is_file() || meta.len() > (LIMIT + 16) as u64 {
            return Err(());
        }
        let bytes = self.slots[slot]
            .as_ref()
            .ok_or(())?
            .read()
            .map_err(|_| ())?;
        if bytes.len() < 48 || bytes.len() > LIMIT {
            return Err(());
        }
        let end = bytes.len() - 32;
        let tag: [u8; 32] = bytes[end..].try_into().map_err(|_| ())?;
        if !ct_eq_bytes32(&tag, &self.tag(b"snapshot", &bytes[..end])) {
            return Err(());
        }
        let generation = u64::from_le_bytes(bytes[..8].try_into().map_err(|_| ())?);
        if generation % 2 != slot as u64 {
            return Err(());
        }
        let count = u64::from_le_bytes(bytes[8..16].try_into().map_err(|_| ())?);
        if count > ((end - 16) / 8) as u64 {
            return Err(());
        }
        let mut cur = 16;
        let mut records = Records::new();
        for _ in 0..count {
            if end - cur < 8 {
                return Err(());
            }
            let k = u32::from_le_bytes(bytes[cur..cur + 4].try_into().map_err(|_| ())?) as usize;
            let v =
                u32::from_le_bytes(bytes[cur + 4..cur + 8].try_into().map_err(|_| ())?) as usize;
            cur += 8;
            let size = k.checked_add(v).ok_or(())?;
            if size > end - cur {
                return Err(());
            }
            if records
                .insert(
                    bytes[cur..cur + k].to_vec(),
                    bytes[cur + k..cur + size].to_vec(),
                )
                .is_some()
            {
                return Err(());
            }
            cur += size;
        }
        if cur != end {
            return Err(());
        }
        Ok((LedgerCheckpoint { generation, tag }, records))
    }
    pub(crate) fn read(&self) -> Result<Records, ()> {
        self.check_genesis()?;
        let (checkpoint, records) = self.read_slot((self.checkpoint.generation % 2) as usize)?;
        if checkpoint != self.checkpoint {
            return Err(());
        }
        Ok(records)
    }
    pub(crate) fn commit(&mut self, records: &Records) -> Result<(), ()> {
        self.read()?;
        let generation = self.checkpoint.generation.checked_add(1).ok_or(())?;
        self.write(records, generation)
    }
    fn write(&mut self, records: &Records, generation: u64) -> Result<(), ()> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&generation.to_le_bytes());
        bytes.extend_from_slice(&(records.len() as u64).to_le_bytes());
        for (k, v) in records {
            let size = k
                .len()
                .checked_add(v.len())
                .and_then(|n| n.checked_add(8))
                .ok_or(())?;
            if size > LIMIT.saturating_sub(bytes.len() + 32) {
                return Err(());
            }
            bytes.extend_from_slice(&(k.len() as u32).to_le_bytes());
            bytes.extend_from_slice(&(v.len() as u32).to_le_bytes());
            bytes.extend_from_slice(k);
            bytes.extend_from_slice(v);
        }
        let tag = self.tag(b"snapshot", &bytes);
        bytes.extend_from_slice(&tag);
        self.failed = true;
        // replace syncs the temporary inode, renames it, then syncs its parent.
        // Never overwrite the active generation before its successor is durable.
        self.slots[(generation % 2) as usize]
            .as_ref()
            .ok_or(())?
            .replace(&bytes)
            .map_err(|_| ())?;
        self.checkpoint = LedgerCheckpoint { generation, tag };
        self.failed = false;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn directory() -> std::path::PathBuf {
        static NEXT: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
        let id = NEXT.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        let dir = std::env::temp_dir().join(std::format!(
            "qsag-ledger-{}-{id}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        dir
    }
    #[test]
    fn crash_boundaries_preserve_burns_and_first_signed_records() {
        use crate::baggy::{
            FirstSignedError, FirstSignedLedger, FirstSignedRecord, FsFirstSignedLedger,
            StaticKeyId,
        };
        use crate::pcg_dense::{FsSeedBurnTracker, SeedBurnError, SeedBurnTracker};
        for boundary in 0..3 {
            let dir = directory();
            let path = dir.join("burn");
            let key = [4; 32];
            let mut ledger = FsSeedBurnTracker::provision_genesis(&path, key).unwrap();
            ledger.burn(&[1; 32]).unwrap();
            let mut anchor = ledger.checkpoint();
            if boundary == 0 {
                // Crash before inactive slot sync: a partial temporary inode is ignored.
                std::fs::write(dir.join("burn.slot_a.tmp"), b"partial").unwrap();
            } else {
                ledger.burn(&[2; 32]).unwrap();
                if boundary == 2 {
                    anchor = ledger.checkpoint();
                }
            }
            drop(ledger);
            let mut recovered = FsSeedBurnTracker::open_existing(&path, key, anchor).unwrap();
            assert_eq!(
                recovered.checkpoint().generation,
                if boundary == 0 { 1 } else { 2 }
            );
            assert_eq!(recovered.burn(&[1; 32]), Err(SeedBurnError::AlreadyBurned));
            if boundary != 0 {
                assert_eq!(recovered.burn(&[2; 32]), Err(SeedBurnError::AlreadyBurned));
            }
            recovered.burn(&[3; 32]).unwrap();
            drop(recovered);
            let path = dir.join("signed");
            let mut ledger = FsFirstSignedLedger::provision_genesis(&path, key).unwrap();
            let anchor = ledger.checkpoint();
            let id = StaticKeyId {
                identity: [1; 32],
                layer: 0,
                tree: 1,
                key_pair: 2,
            };
            ledger
                .sync_record(&[FirstSignedRecord {
                    key: id,
                    digits: alloc::vec![1, 2, 3],
                }])
                .unwrap();
            drop(ledger);
            let mut recovered = FsFirstSignedLedger::open_existing(&path, key, anchor).unwrap();
            assert_eq!(
                recovered.first_signed(&id).unwrap(),
                Some(alloc::vec![1, 2, 3])
            );
            assert_eq!(
                recovered.sync_record(&[FirstSignedRecord {
                    key: id,
                    digits: alloc::vec![2]
                }]),
                Err(FirstSignedError::Conflict)
            );
            drop(recovered);
            std::fs::remove_dir_all(dir).unwrap();
        }
    }
    #[test]
    fn both_slots_authenticate_and_minimum_anchor_rejects_rollback() {
        let dir = directory();
        let path = dir.join("ledger");
        let key = [4; 32];
        let mut ledger = Ledger::create(&path, key, b"test").unwrap();
        let genesis = ledger.checkpoint();
        assert!(Ledger::open(&path, key, b"test", genesis).is_err());
        let old = std::fs::read(&ledger.paths[0]).unwrap();
        let mut records = Records::new();
        records.insert(alloc::vec![1], alloc::vec![2]);
        ledger.commit(&records).unwrap();
        ledger.commit(&records).unwrap();
        let latest = ledger.checkpoint();
        drop(ledger);
        assert!(Ledger::open(&path, [5; 32], b"test", latest).is_err());
        assert!(Ledger::open(&path, key, b"other", latest).is_err());
        // Slot A is restored to an authenticated old generation; B remains generation 1.
        std::fs::write(&slot_paths(&path)[0], old).unwrap();
        assert!(Ledger::open(&path, key, b"test", latest).is_err());
        let recovered = Ledger::open(&path, key, b"test", genesis).unwrap();
        assert_eq!(recovered.checkpoint().generation, 1);
        drop(recovered);
        // A missing or corrupt inactive snapshot does not strand a valid active one.
        std::fs::remove_file(&slot_paths(&path)[0]).unwrap();
        let recovered = Ledger::open(&path, key, b"test", genesis).unwrap();
        assert_eq!(recovered.read().unwrap(), records);
        drop(recovered);
        let mut missing_lock = slot_paths(&path)[0].as_os_str().to_os_string();
        missing_lock.push(".lock");
        std::fs::write(std::path::PathBuf::from(missing_lock), b"corrupt sidecar").unwrap();
        let recovered = Ledger::open(&path, key, b"test", genesis).unwrap();
        assert_eq!(recovered.read().unwrap(), records);
        drop(recovered);
        std::fs::write(&slot_paths(&path)[1], b"bad").unwrap();
        assert!(Ledger::open(&path, key, b"test", genesis).is_err());
        assert!(Ledger::create(&path, key, b"test").is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
