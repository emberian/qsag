//! Per-key serialized ceremony reservations in one authenticated, crash-atomic record.
//! Reserve before the first secret-derived network output. A lost permit burns resources;
//! it never rolls a reservation back. Disk snapshot rollback requires an external anchor.
use crate::sponge::Cshake256Xof;
use qsag_asm::durable::LockedRecord;
use std::{io, path::PathBuf};

/// All resources committed together before release authority is issued.
#[derive(Debug, PartialEq, Eq)]
pub struct CeremonyReservation {
    pub ceremony_id: [u8; 32],
    pub key_id: [u8; 32],
    pub epoch_or_codeword: [u8; 32],
    pub seed_burn_cursor: u64,
    pub hedge_generation: u64,
}

/// An owned, non-Clone authority. Only a successful durable transaction creates one.
#[derive(Debug)]
pub struct CeremonyReleasePermit {
    reservation: CeremonyReservation,
    seal: [u8; 8],
}

/// One exclusive authority per key; no mutable subordinate ledger escapes this object.
pub struct FsCeremonyJournal {
    record: LockedRecord,
    key_id: [u8; 32],
    mac_key: [u8; 32],
    entries: Vec<CeremonyReservation>,
}

fn invalid() -> io::Error { io::Error::new(io::ErrorKind::InvalidData, "invalid ceremony reservation") }

impl Drop for FsCeremonyJournal {
    fn drop(&mut self) { qsag_asm::volatile_fill(&mut self.mac_key, 0); }
}

impl FsCeremonyJournal {
    pub fn create_new(path: impl Into<PathBuf>, key_id: [u8; 32], mac_key: [u8; 32]) -> io::Result<Self> {
        let this = Self { record: LockedRecord::create_new(path)?, key_id, mac_key, entries: Vec::new() };
        this.record.replace(&this.encode(None))?;
        Ok(this)
    }

    pub fn open_existing(path: impl Into<PathBuf>, key_id: [u8; 32], mac_key: [u8; 32]) -> io::Result<Self> {
        let mut this = Self { record: LockedRecord::open_existing(path)?, key_id, mac_key, entries: Vec::new() };
        let bytes = this.record.read()?;
        if bytes.len() < 72 || &bytes[..8] != b"QSAGCRJ1" || bytes[8..40] != key_id
            || !(bytes.len() - 72).is_multiple_of(80) { return Err(invalid()); }
        let end = bytes.len() - 32;
        if !qsag_asm::ct_eq_32(&this.tag(&bytes[..end]), bytes[end..].try_into().map_err(|_| invalid())?) {
            return Err(invalid());
        }
        for chunk in bytes[40..end].as_chunks::<80>().0 {
            let reservation = CeremonyReservation {
                ceremony_id: chunk[..32].try_into().map_err(|_| invalid())?, key_id,
                epoch_or_codeword: chunk[32..64].try_into().map_err(|_| invalid())?,
                seed_burn_cursor: u64::from_be_bytes(chunk[64..72].try_into().map_err(|_| invalid())?),
                hedge_generation: u64::from_be_bytes(chunk[72..80].try_into().map_err(|_| invalid())?),
            };
            this.validate(&reservation)?;
            this.entries.push(reservation);
        }
        Ok(this)
    }

    fn tag(&self, bytes: &[u8]) -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.CEREMONY.JOURNAL.MAC/v1");
        xof.absorb(&self.mac_key);
        xof.absorb(&self.record.lock_seal());
        xof.absorb(bytes);
        let mut tag = [0; 32]; xof.squeeze(&mut tag); tag
    }

    fn encode(&self, next: Option<&CeremonyReservation>) -> Vec<u8> {
        let mut bytes = b"QSAGCRJ1".to_vec();
        bytes.extend_from_slice(&self.key_id);
        for r in self.entries.iter().chain(next) {
            bytes.extend_from_slice(&r.ceremony_id);
            bytes.extend_from_slice(&r.epoch_or_codeword);
            bytes.extend_from_slice(&r.seed_burn_cursor.to_be_bytes());
            bytes.extend_from_slice(&r.hedge_generation.to_be_bytes());
        }
        bytes.extend_from_slice(&self.tag(&bytes)); bytes
    }

    fn validate(&self, r: &CeremonyReservation) -> io::Result<()> {
        if r.key_id != self.key_id || self.entries.iter().any(|e| e.ceremony_id == r.ceremony_id
            || e.epoch_or_codeword == r.epoch_or_codeword)
            || self.entries.last().is_some_and(|e| r.seed_burn_cursor <= e.seed_burn_cursor
                || r.hedge_generation <= e.hedge_generation) { return Err(invalid()); }
        Ok(())
    }

    /// One fsynced replacement commits all reservations. Failure issues no permit.
    pub fn persist_before_release(&mut self, r: CeremonyReservation) -> io::Result<CeremonyReleasePermit> {
        self.validate(&r)?;
        if self.record.read()? != self.encode(None) { return Err(invalid()); }
        self.record.replace(&self.encode(Some(&r)))?;
        let permit = CeremonyReleasePermit { reservation: CeremonyReservation {
            ceremony_id: r.ceremony_id, key_id: r.key_id, epoch_or_codeword: r.epoch_or_codeword,
            seed_burn_cursor: r.seed_burn_cursor, hedge_generation: r.hedge_generation,
        }, seal: self.record.lock_seal() };
        self.entries.push(r);
        Ok(permit)
    }

    /// Consume current authority; advancing the journal invalidates older pending permits.
    /// Callers must perform this check before releasing their bound ceremony's output.
    pub fn consume_release(&self, permit: CeremonyReleasePermit) -> io::Result<CeremonyReservation> {
        if permit.seal != self.record.lock_seal() || self.entries.last() != Some(&permit.reservation)
            || self.record.read()? != self.encode(None) { return Err(invalid()); }
        Ok(permit.reservation)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn durable_release_paths_require_bound_single_use_permits() {
        use crate::baggy::{FirstSignedLedger, FsFirstSignedLedger};
        use crate::pcg_dense::{SeedBurnTracker, FsSeedBurnTracker};
        use crate::belt_latch::{DurableWal, FsBeltWal, BeltLatchRecord};
        let dir = std::env::temp_dir().join(format!("qsag-release-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        std::fs::create_dir(&dir).unwrap();
        let mut journal = FsCeremonyJournal::create_new(dir.join("journal"), [4; 32], [5; 32]).unwrap();
        let mut signed = FsFirstSignedLedger::provision_genesis(dir.join("signed"), [6; 32]).unwrap();
        let mut burns = FsSeedBurnTracker::provision_genesis(dir.join("burns"), [7; 32]).unwrap();
        let mut belt = FsBeltWal::provision_genesis(dir.join("belt"), [8; 32]).unwrap();
        let reservation = |i, codeword| CeremonyReservation { ceremony_id: [i; 32], key_id: [4; 32],
            epoch_or_codeword: codeword, seed_burn_cursor: u64::from(i), hedge_generation: u64::from(i) };
        assert!(signed.begin_release(&[4; 32], &[1; 32], &[1; 32]).is_err());
        let permit = journal.persist_before_release(reservation(1, [1; 32])).unwrap();
        signed.authorize_release(&journal, permit).unwrap();
        signed.begin_release(&[4; 32], &[1; 32], &[1; 32]).unwrap();
        assert!(signed.begin_release(&[4; 32], &[1; 32], &[1; 32]).is_err());
        let permit = journal.persist_before_release(reservation(2, [2; 32])).unwrap();
        signed.authorize_release(&journal, permit).unwrap();
        assert!(signed.begin_release(&[9; 32], &[2; 32], &[2; 32]).is_err());
        assert!(signed.begin_release(&[4; 32], &[2; 32], &[2; 32]).is_err());
        assert!(burns.begin_expansion(&[3; 32], &[3; 32]).is_err());
        let permit = journal.persist_before_release(reservation(3, [3; 32])).unwrap();
        burns.authorize_release(&journal, permit).unwrap();
        burns.begin_expansion(&[3; 32], &[3; 32]).unwrap();
        burns.burn(&[3; 32]).unwrap();
        assert!(burns.begin_expansion(&[3; 32], &[3; 32]).is_err());
        let record = BeltLatchRecord { epoch: 4, msg_digest: [1; 32], retry_salt: [2; 32], target_sum_digits: vec![1, 2] };
        assert!(belt.authorize_open(&record).is_err());
        let permit = journal.persist_before_release(reservation(4, record.binding())).unwrap();
        belt.authorize_release(&journal, permit).unwrap();
        belt.authorize_open(&record).unwrap();
        assert!(belt.authorize_open(&record).is_err());
        drop((journal, signed, burns, belt));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn atomic_reservation_recovery_and_stale_permit() {
        let path = std::env::temp_dir().join(format!("qsag-ceremony-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let r = |i| CeremonyReservation { ceremony_id: [i; 32], key_id: [4; 32],
            epoch_or_codeword: [i; 32], seed_burn_cursor: u64::from(i), hedge_generation: u64::from(i) };
        let mut journal = FsCeremonyJournal::create_new(&path, [4; 32], [5; 32]).unwrap();
        let stale = journal.persist_before_release(r(1)).unwrap();
        let current = journal.persist_before_release(r(2)).unwrap();
        assert!(journal.consume_release(stale).is_err());
        assert_eq!(journal.consume_release(current).unwrap(), r(2));
        drop(journal);
        let mut recovered = FsCeremonyJournal::open_existing(&path, [4; 32], [5; 32]).unwrap();
        assert!(recovered.persist_before_release(r(1)).is_err());
        assert!(recovered.persist_before_release(r(2)).is_err());
        assert!(recovered.persist_before_release(r(3)).is_ok());
        // Keep the permanent lock sidecar: test paths are unique.
    }
}
