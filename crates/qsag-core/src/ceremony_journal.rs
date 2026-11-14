//! Per-key serialized ceremony reservations in one authenticated, crash-atomic record.
//! Reserve before the first secret-derived network output. A lost permit burns resources;
//! it never rolls a reservation back. Disk snapshot rollback is detected when callers retain
//! [`crate::LedgerCheckpoint`] in an external monotonic anchor and recover via
//! [`FsCeremonyJournal::open_existing_at_least`].
use crate::LedgerCheckpoint;
use crate::sponge::Cshake256Xof;
use crate::wipe::{ct_eq_bytes32, wipe_bytes32};
use qsag_asm::durable::LockedRecord;
use std::{io, path::PathBuf};

const JOURNAL_MAGIC: &[u8; 8] = b"QSAGCRJ2";
const HEADER_LEN: usize = 8 + 32 + 8;
const ENTRY_LEN: usize = 32 + 32 + 8 + 8 + 1 + 8;
const TAG_LEN: usize = 32;

const FLAG_HAS_EPOCH: u8 = 0x01;
const FLAG_IS_RETRY: u8 = 0x02;

/// All resources committed together before release authority is issued.
#[derive(Debug, PartialEq, Eq)]
pub struct CeremonyReservation {
    pub ceremony_id: [u8; 32],
    pub key_id: [u8; 32],
    pub epoch_or_codeword: [u8; 32],
    pub seed_burn_cursor: u64,
    pub hedge_generation: u64,
}

#[derive(Debug, PartialEq, Eq)]
struct JournalEntry {
    ceremony_id: [u8; 32],
    epoch_or_codeword: [u8; 32],
    seed_burn_cursor: u64,
    hedge_generation: u64,
    bound_epoch: Option<u64>,
    is_retry: bool,
}

impl JournalEntry {
    fn from_reservation(r: &CeremonyReservation, bound_epoch: Option<u64>, is_retry: bool) -> Self {
        Self {
            ceremony_id: r.ceremony_id,
            epoch_or_codeword: r.epoch_or_codeword,
            seed_burn_cursor: r.seed_burn_cursor,
            hedge_generation: r.hedge_generation,
            bound_epoch,
            is_retry,
        }
    }

    fn matches_permit(&self, r: &CeremonyReservation, bound_epoch: Option<u64>, is_retry: bool) -> bool {
        ct_eq_bytes32(&self.ceremony_id, &r.ceremony_id)
            && ct_eq_bytes32(&self.epoch_or_codeword, &r.epoch_or_codeword)
            && self.seed_burn_cursor == r.seed_burn_cursor
            && self.hedge_generation == r.hedge_generation
            && self.bound_epoch == bound_epoch
            && self.is_retry == is_retry
    }
}

/// An owned, non-Clone authority. Only a successful durable transaction creates one.
#[derive(Debug)]
pub struct CeremonyReleasePermit {
    reservation: CeremonyReservation,
    bound_epoch: Option<u64>,
    is_retry: bool,
    generation: u64,
    seal: [u8; 8],
}

/// One exclusive authority per key; no mutable subordinate ledger escapes this object.
pub struct FsCeremonyJournal {
    record: LockedRecord,
    key_id: [u8; 32],
    mac_key: [u8; 32],
    checkpoint: LedgerCheckpoint,
    entries: Vec<JournalEntry>,
}

fn invalid() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "invalid ceremony reservation")
}

impl Drop for FsCeremonyJournal {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.mac_key);
    }
}

impl FsCeremonyJournal {
    /// Current authenticated checkpoint; persist outside the disk-snapshot rollback domain
    /// before releasing secret-derived ceremony outputs.
    pub const fn checkpoint(&self) -> LedgerCheckpoint {
        self.checkpoint
    }

    pub fn create_new(path: impl Into<PathBuf>, key_id: [u8; 32], mac_key: [u8; 32]) -> io::Result<Self> {
        let mut this = Self {
            record: LockedRecord::create_new(path)?,
            key_id,
            mac_key,
            checkpoint: LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
            entries: Vec::new(),
        };
        let (encoded, checkpoint) = this.encode(1, None);
        this.record.replace(&encoded)?;
        this.checkpoint = checkpoint;
        Ok(this)
    }

    /// Recover an existing journal while enforcing an externally retained minimum checkpoint.
    /// Rejects any snapshot older than `min_checkpoint.generation` or carrying a mismatched
    /// tag at `min_checkpoint.generation`.
    pub fn open_existing_at_least(
        path: impl Into<PathBuf>,
        key_id: [u8; 32],
        mac_key: [u8; 32],
        min_checkpoint: LedgerCheckpoint,
    ) -> io::Result<Self> {
        let mut this = Self {
            record: LockedRecord::open_existing(path)?,
            key_id,
            mac_key,
            checkpoint: LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
            entries: Vec::new(),
        };
        let bytes = this.record.read()?;
        if bytes.len() < HEADER_LEN + TAG_LEN
            || &bytes[..8] != JOURNAL_MAGIC
            || !ct_eq_bytes32(bytes[8..40].try_into().map_err(|_| invalid())?, &key_id)
            || !(bytes.len() - (HEADER_LEN + TAG_LEN)).is_multiple_of(ENTRY_LEN)
        {
            return Err(invalid());
        }
        let end = bytes.len() - TAG_LEN;
        let stored_tag: [u8; 32] = bytes[end..].try_into().map_err(|_| invalid())?;
        let computed_tag = this.tag(&bytes[..end]);
        if !ct_eq_bytes32(&computed_tag, &stored_tag) {
            return Err(invalid());
        }
        let generation = u64::from_be_bytes(bytes[40..48].try_into().map_err(|_| invalid())?);
        let entry_count = (end - HEADER_LEN) / ENTRY_LEN;
        let expected_gen = (entry_count as u64).checked_add(1).ok_or_else(invalid)?;
        if generation == 0 || generation != expected_gen {
            return Err(invalid());
        }
        if generation < min_checkpoint.generation {
            return Err(invalid());
        }
        if generation == min_checkpoint.generation && !ct_eq_bytes32(&stored_tag, &min_checkpoint.tag) {
            return Err(invalid());
        }
        for chunk in bytes[HEADER_LEN..end].chunks_exact(ENTRY_LEN) {
            let flags = chunk[80];
            if flags & !(FLAG_HAS_EPOCH | FLAG_IS_RETRY) != 0 {
                return Err(invalid());
            }
            let raw_epoch = u64::from_be_bytes(chunk[81..89].try_into().map_err(|_| invalid())?);
            let bound_epoch = if (flags & FLAG_HAS_EPOCH) != 0 {
                Some(raw_epoch)
            } else {
                if raw_epoch != 0 {
                    return Err(invalid());
                }
                None
            };
            let is_retry = (flags & FLAG_IS_RETRY) != 0;
            let reservation = CeremonyReservation {
                ceremony_id: chunk[..32].try_into().map_err(|_| invalid())?,
                key_id,
                epoch_or_codeword: chunk[32..64].try_into().map_err(|_| invalid())?,
                seed_burn_cursor: u64::from_be_bytes(chunk[64..72].try_into().map_err(|_| invalid())?),
                hedge_generation: u64::from_be_bytes(chunk[72..80].try_into().map_err(|_| invalid())?),
            };
            this.validate(&reservation, bound_epoch, is_retry)?;
            this.entries
                .push(JournalEntry::from_reservation(&reservation, bound_epoch, is_retry));
        }
        this.checkpoint = LedgerCheckpoint {
            generation,
            tag: stored_tag,
        };
        Ok(this)
    }

    /// Recover an existing journal without an external anchor. Callers defending against
    /// full disk-snapshot rollback should use [`Self::open_existing_at_least`].
    pub fn open_existing(
        path: impl Into<PathBuf>,
        key_id: [u8; 32],
        mac_key: [u8; 32],
    ) -> io::Result<Self> {
        Self::open_existing_at_least(
            path,
            key_id,
            mac_key,
            LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
        )
    }

    fn tag(&self, bytes: &[u8]) -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.CEREMONY.JOURNAL.MAC/v2");
        xof.absorb(&self.mac_key);
        xof.absorb(&self.record.lock_seal());
        xof.absorb(bytes);
        let mut tag = [0; 32];
        xof.squeeze(&mut tag);
        tag
    }

    fn encode(&self, generation: u64, next: Option<&JournalEntry>) -> (Vec<u8>, LedgerCheckpoint) {
        let mut bytes = Vec::with_capacity(
            HEADER_LEN + (self.entries.len() + usize::from(next.is_some())) * ENTRY_LEN + TAG_LEN,
        );
        bytes.extend_from_slice(JOURNAL_MAGIC);
        bytes.extend_from_slice(&self.key_id);
        bytes.extend_from_slice(&generation.to_be_bytes());
        for e in self.entries.iter().chain(next) {
            bytes.extend_from_slice(&e.ceremony_id);
            bytes.extend_from_slice(&e.epoch_or_codeword);
            bytes.extend_from_slice(&e.seed_burn_cursor.to_be_bytes());
            bytes.extend_from_slice(&e.hedge_generation.to_be_bytes());
            let mut flags = 0u8;
            if e.bound_epoch.is_some() {
                flags |= FLAG_HAS_EPOCH;
            }
            if e.is_retry {
                flags |= FLAG_IS_RETRY;
            }
            bytes.push(flags);
            bytes.extend_from_slice(&e.bound_epoch.unwrap_or(0).to_be_bytes());
        }
        let tag = self.tag(&bytes);
        bytes.extend_from_slice(&tag);
        (bytes, LedgerCheckpoint { generation, tag })
    }

    fn validate(
        &self,
        r: &CeremonyReservation,
        bound_epoch: Option<u64>,
        is_retry: bool,
    ) -> io::Result<()> {
        if !ct_eq_bytes32(&r.key_id, &self.key_id) {
            return Err(invalid());
        }
        if self
            .entries
            .iter()
            .any(|e| ct_eq_bytes32(&e.ceremony_id, &r.ceremony_id))
        {
            return Err(invalid());
        }
        if let Some(last) = self.entries.last()
            && (r.seed_burn_cursor <= last.seed_burn_cursor
                || r.hedge_generation <= last.hedge_generation)
        {
            return Err(invalid());
        }
        if is_retry {
            let Some(last) = self.entries.last() else {
                return Err(invalid());
            };
            if last.bound_epoch != bound_epoch
                || !ct_eq_bytes32(&last.epoch_or_codeword, &r.epoch_or_codeword)
            {
                return Err(invalid());
            }
        } else {
            if self
                .entries
                .iter()
                .any(|e| ct_eq_bytes32(&e.epoch_or_codeword, &r.epoch_or_codeword))
            {
                return Err(invalid());
            }
            if let Some(ep) = bound_epoch
                && self
                    .entries
                    .iter()
                    .filter_map(|e| e.bound_epoch)
                    .any(|prev_ep| ep <= prev_ep)
            {
                return Err(invalid());
            }
        }
        Ok(())
    }

    fn commit_internal(
        &mut self,
        r: CeremonyReservation,
        bound_epoch: Option<u64>,
        is_retry: bool,
    ) -> io::Result<CeremonyReleasePermit> {
        self.validate(&r, bound_epoch, is_retry)?;
        let (expected_on_disk, expected_ckpt) = self.encode(self.checkpoint.generation, None);
        if expected_ckpt != self.checkpoint || self.record.read()? != expected_on_disk {
            return Err(invalid());
        }
        let next_gen = self.checkpoint.generation.checked_add(1).ok_or_else(invalid)?;
        let entry = JournalEntry::from_reservation(&r, bound_epoch, is_retry);
        let (next_bytes, next_ckpt) = self.encode(next_gen, Some(&entry));
        self.record.replace(&next_bytes)?;
        self.checkpoint = next_ckpt;
        self.entries.push(entry);
        Ok(CeremonyReleasePermit {
            reservation: r,
            bound_epoch,
            is_retry,
            generation: next_gen,
            seal: self.record.lock_seal(),
        })
    }

    /// One fsynced replacement commits all reservations for an unbound ceremony (e.g. stateless
    /// codeword or PCG seed burn). Failure issues no permit.
    pub fn persist_before_release(
        &mut self,
        r: CeremonyReservation,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, None, false)
    }

    /// Commit a fresh stateful epoch reservation binding both the numeric `epoch` (which must
    /// strictly exceed every prior bound epoch in this journal) and `r.epoch_or_codeword`.
    pub fn persist_epoch_before_release(
        &mut self,
        epoch: u64,
        r: CeremonyReservation,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, Some(epoch), false)
    }

    /// Authorize a crash-recovery retry attempt for the currently in-flight unbound reservation.
    /// Requires the identical `epoch_or_codeword`, a fresh `ceremony_id`, and strictly advancing
    /// `seed_burn_cursor` and `hedge_generation`.
    pub fn commit_retry_attempt(
        &mut self,
        r: CeremonyReservation,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, None, true)
    }

    /// Authorize a crash-recovery retry attempt for the currently in-flight stateful `epoch`.
    /// Requires `epoch` and `r.epoch_or_codeword` to match the in-flight reservation identically,
    /// while `r.ceremony_id` is fresh and preprocessing/hedge cursors strictly advance.
    pub fn commit_epoch_retry_attempt(
        &mut self,
        epoch: u64,
        r: CeremonyReservation,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, Some(epoch), true)
    }

    fn verify_current_permit(&self, permit: &CeremonyReleasePermit) -> io::Result<()> {
        if permit.seal != self.record.lock_seal()
            || permit.generation != self.checkpoint.generation
            || !ct_eq_bytes32(&permit.reservation.key_id, &self.key_id)
        {
            return Err(invalid());
        }
        let Some(last) = self.entries.last() else {
            return Err(invalid());
        };
        if !last.matches_permit(&permit.reservation, permit.bound_epoch, permit.is_retry) {
            return Err(invalid());
        }
        let (expected_on_disk, expected_ckpt) = self.encode(self.checkpoint.generation, None);
        if expected_ckpt != self.checkpoint || self.record.read()? != expected_on_disk {
            return Err(invalid());
        }
        Ok(())
    }

    /// Consume current authority; advancing the journal invalidates older pending permits.
    /// Callers must perform this check before releasing their bound ceremony's output.
    pub fn consume_release(&self, permit: CeremonyReleasePermit) -> io::Result<CeremonyReservation> {
        self.verify_current_permit(&permit)?;
        Ok(permit.reservation)
    }

    /// Consume current epoch-bound authority for [`crate::belt_latch::FsBeltWal`].
    /// Refuses permits that were not committed with an explicit numeric `epoch`.
    pub(crate) fn consume_belt_release(
        &self,
        permit: CeremonyReleasePermit,
    ) -> io::Result<(CeremonyReservation, u64)> {
        self.verify_current_permit(&permit)?;
        let Some(epoch) = permit.bound_epoch else {
            return Err(invalid());
        };
        Ok((permit.reservation, epoch))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn durable_release_paths_require_bound_single_use_permits() {
        use crate::baggy::{FirstSignedLedger, FsFirstSignedLedger};
        use crate::belt_latch::{BeltLatchRecord, DurableWal, FsBeltWal};
        use crate::pcg_dense::{FsSeedBurnTracker, SeedBurnTracker};
        let dir = std::env::temp_dir().join(format!(
            "qsag-release-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let mut journal = FsCeremonyJournal::create_new(dir.join("journal"), [4; 32], [5; 32]).unwrap();
        let mut signed = FsFirstSignedLedger::provision_genesis(dir.join("signed"), [6; 32]).unwrap();
        let mut burns = FsSeedBurnTracker::provision_genesis(dir.join("burns"), [7; 32]).unwrap();
        let mut belt = FsBeltWal::provision_genesis(dir.join("belt"), [8; 32]).unwrap();
        let reservation = |i, codeword| CeremonyReservation {
            ceremony_id: [i; 32],
            key_id: [4; 32],
            epoch_or_codeword: codeword,
            seed_burn_cursor: u64::from(i),
            hedge_generation: u64::from(i),
        };
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
        let record = BeltLatchRecord {
            epoch: 4,
            msg_digest: [1; 32],
            retry_salt: [2; 32],
            target_sum_digits: vec![1, 2],
        };
        assert!(belt.authorize_open(&record).is_err());
        // Unbound permits cannot authorize FsBeltWal.
        let unbound_permit = journal.persist_before_release(reservation(4, [0x44; 32])).unwrap();
        assert!(belt.authorize_release(&journal, unbound_permit).is_err());
        let permit = journal
            .persist_epoch_before_release(record.epoch, reservation(5, record.binding()))
            .unwrap();
        belt.authorize_release(&journal, permit).unwrap();
        belt.authorize_open(&record).unwrap();
        assert!(belt.authorize_open(&record).is_err());
        drop((journal, signed, burns, belt));
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn atomic_reservation_recovery_and_stale_permit() {
        let path = std::env::temp_dir().join(format!(
            "qsag-ceremony-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let r = |i| CeremonyReservation {
            ceremony_id: [i; 32],
            key_id: [4; 32],
            epoch_or_codeword: [i; 32],
            seed_burn_cursor: u64::from(i),
            hedge_generation: u64::from(i),
        };
        let mut journal = FsCeremonyJournal::create_new(&path, [4; 32], [5; 32]).unwrap();
        let stale = journal.persist_before_release(r(1)).unwrap();
        let current = journal.persist_before_release(r(2)).unwrap();
        assert!(journal.consume_release(stale).is_err());
        assert_eq!(journal.consume_release(current).unwrap(), r(2));
        let ckpt_gen3 = journal.checkpoint();
        drop(journal);
        let mut recovered =
            FsCeremonyJournal::open_existing_at_least(&path, [4; 32], [5; 32], ckpt_gen3).unwrap();
        assert!(recovered.persist_before_release(r(1)).is_err());
        assert!(recovered.persist_before_release(r(2)).is_err());
        assert!(recovered.persist_before_release(r(3)).is_ok());
        // Keep the permanent lock sidecar: test paths are unique.
    }

    #[test]
    fn journal_checkpoint_rejects_snapshot_rollback_and_permits_safe_crash_retry() {
        use crate::belt_latch::{BeltLatchRecord, DurableWal, FsBeltWal};
        let dir = std::env::temp_dir().join(format!(
            "qsag-ceremony-rollback-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let jpath = dir.join("journal");
        let bpath = dir.join("belt");

        let mut journal = FsCeremonyJournal::create_new(&jpath, [4; 32], [5; 32]).unwrap();
        let mut belt = FsBeltWal::provision_genesis(&bpath, [8; 32]).unwrap();
        let snapshot_genesis = std::fs::read(&jpath).unwrap();

        let rec_a = BeltLatchRecord {
            epoch: 7,
            msg_digest: [0xA1; 32],
            retry_salt: [0xA2; 32],
            target_sum_digits: vec![3, 1, 0, 2],
        };
        let _initial_permit = journal
            .persist_epoch_before_release(
                rec_a.epoch,
                CeremonyReservation {
                    ceremony_id: [1; 32],
                    key_id: [4; 32],
                    epoch_or_codeword: rec_a.binding(),
                    seed_burn_cursor: 10,
                    hedge_generation: 10,
                },
            )
            .unwrap();
        let anchored_ckpt = journal.checkpoint();
        // Simulate crash before belt opening completes.
        drop((journal, belt));

        // 1. Snapshot rollback of journal file is rejected when anchored_ckpt is supplied.
        let current_bytes = std::fs::read(&jpath).unwrap();
        std::fs::write(&jpath, &snapshot_genesis).unwrap();
        assert!(
            FsCeremonyJournal::open_existing_at_least(&jpath, [4; 32], [5; 32], anchored_ckpt)
                .is_err()
        );
        std::fs::write(&jpath, &current_bytes).unwrap();

        // 2. Recovery succeeds at anchored_ckpt; fresh reservation of same epoch/binding fails,
        //    changed binding retry fails, non-advancing cursor retry fails, reused ceremony_id fails,
        //    and identical-binding retry with fresh ceremony_id & advanced cursors succeeds!
        let mut journal =
            FsCeremonyJournal::open_existing_at_least(&jpath, [4; 32], [5; 32], anchored_ckpt)
                .unwrap();
        let mut belt = FsBeltWal::open_existing(&bpath, [8; 32]).unwrap();

        let rec_b = BeltLatchRecord {
            epoch: 7,
            msg_digest: [0xB1; 32],
            retry_salt: [0xB2; 32],
            target_sum_digits: vec![0, 2, 3, 1],
        };
        // Even if belt rolled back and minted a new binding at epoch <= 7, journal rejects it!
        assert!(
            journal
                .persist_epoch_before_release(
                    7,
                    CeremonyReservation {
                        ceremony_id: [2; 32],
                        key_id: [4; 32],
                        epoch_or_codeword: rec_b.binding(),
                        seed_burn_cursor: 11,
                        hedge_generation: 11,
                    },
                )
                .is_err()
        );
        assert!(
            journal
                .persist_epoch_before_release(
                    3,
                    CeremonyReservation {
                        ceremony_id: [2; 32],
                        key_id: [4; 32],
                        epoch_or_codeword: rec_b.binding(),
                        seed_burn_cursor: 11,
                        hedge_generation: 11,
                    },
                )
                .is_err()
        );
        // Retry with changed binding is rejected.
        assert!(
            journal
                .commit_epoch_retry_attempt(
                    7,
                    CeremonyReservation {
                        ceremony_id: [2; 32],
                        key_id: [4; 32],
                        epoch_or_codeword: rec_b.binding(),
                        seed_burn_cursor: 11,
                        hedge_generation: 11,
                    },
                )
                .is_err()
        );
        // Retry with reused ceremony_id or non-advancing cursors is rejected.
        assert!(
            journal
                .commit_epoch_retry_attempt(
                    7,
                    CeremonyReservation {
                        ceremony_id: [1; 32],
                        key_id: [4; 32],
                        epoch_or_codeword: rec_a.binding(),
                        seed_burn_cursor: 11,
                        hedge_generation: 11,
                    },
                )
                .is_err()
        );
        assert!(
            journal
                .commit_epoch_retry_attempt(
                    7,
                    CeremonyReservation {
                        ceremony_id: [2; 32],
                        key_id: [4; 32],
                        epoch_or_codeword: rec_a.binding(),
                        seed_burn_cursor: 10,
                        hedge_generation: 11,
                    },
                )
                .is_err()
        );

        // Legitimate retry with identical binding, fresh ceremony_id, and advanced cursors succeeds!
        let retry_permit = journal
            .commit_epoch_retry_attempt(
                7,
                CeremonyReservation {
                    ceremony_id: [2; 32],
                    key_id: [4; 32],
                    epoch_or_codeword: rec_a.binding(),
                    seed_burn_cursor: 11,
                    hedge_generation: 11,
                },
            )
            .unwrap();
        belt.authorize_release(&journal, retry_permit).unwrap();
        // Lying about the epoch when opening fails closed!
        let mut wrong_epoch_rec = rec_a.clone();
        wrong_epoch_rec.epoch = 8;
        assert!(belt.authorize_open(&wrong_epoch_rec).is_err());

        let retry_permit2 = journal
            .commit_epoch_retry_attempt(
                7,
                CeremonyReservation {
                    ceremony_id: [3; 32],
                    key_id: [4; 32],
                    epoch_or_codeword: rec_a.binding(),
                    seed_burn_cursor: 12,
                    hedge_generation: 12,
                },
            )
            .unwrap();
        belt.authorize_release(&journal, retry_permit2).unwrap();
        belt.authorize_open(&rec_a).unwrap();

        drop((journal, belt));
        std::fs::remove_dir_all(dir).unwrap();
    }
}
