//! Per-key serialized ceremony reservations in one authenticated, crash-atomic record.
//! Reserve before the first secret-derived network output. A lost permit burns resources;
//! it never rolls a reservation back. Disk snapshot rollback is detected when callers retain
//! [`crate::LedgerCheckpoint`] in an external monotonic anchor and recover via
//! [`FsCeremonyJournal::open_existing_at_least`].
use crate::LedgerCheckpoint;
use crate::sponge::Cshake256Xof;
use crate::wipe::{ct_eq_bytes32, wipe_bytes32};
use core::sync::atomic::{AtomicBool, Ordering};
use qsag_asm::durable::LockedRecord;
use std::{io, path::PathBuf};

const JOURNAL_MAGIC: &[u8; 8] = b"QSAGCRJ3";
const HEADER_LEN: usize = 8 + 32 + 8;
const ENTRY_LEN: usize = 32 + 32 + 8 + 8 + 1 + 8 + 32 + 8 + 8;
const TAG_LEN: usize = 32;

const FLAG_HAS_EPOCH: u8 = 0x01;
const FLAG_IS_RETRY: u8 = 0x02;

/// Policy and MPC resources committed atomically with a reservation.
/// Legacy entry points use the all-zero context; policy-aware callers must use
/// `persist_with_context` and `consume_release_with_context`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CeremonyContext {
    pub policy_id: [u8; 32],
    pub spend_amount: u64,
    pub mpc_nonce_epoch: u64,
}

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
    context: CeremonyContext,
}

impl JournalEntry {
    fn from_reservation(
        r: &CeremonyReservation,
        bound_epoch: Option<u64>,
        is_retry: bool,
        context: CeremonyContext,
    ) -> Self {
        Self {
            ceremony_id: r.ceremony_id,
            epoch_or_codeword: r.epoch_or_codeword,
            seed_burn_cursor: r.seed_burn_cursor,
            hedge_generation: r.hedge_generation,
            bound_epoch,
            is_retry,
            context,
        }
    }

    fn matches_permit(
        &self,
        r: &CeremonyReservation,
        bound_epoch: Option<u64>,
        is_retry: bool,
    ) -> bool {
        ct_eq_bytes32(&self.ceremony_id, &r.ceremony_id)
            && ct_eq_bytes32(&self.epoch_or_codeword, &r.epoch_or_codeword)
            && self.seed_burn_cursor == r.seed_burn_cursor
            && self.hedge_generation == r.hedge_generation
            && self.bound_epoch == bound_epoch
            && self.is_retry == is_retry
    }
}

/// The cursors and binding of the newest committed reservation. A caller recovering from a
/// crash between [`FsCeremonyJournal::persist_before_release`] and its own ledger update
/// derives its next cursors from these (they must strictly exceed both) and, when
/// `epoch_or_codeword` is the identifier it is retrying, uses
/// [`FsCeremonyJournal::commit_retry_attempt`] instead of a fresh reservation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommittedReservation {
    pub epoch_or_codeword: [u8; 32],
    pub seed_burn_cursor: u64,
    pub hedge_generation: u64,
    pub bound_epoch: Option<u64>,
    pub is_retry: bool,
}

/// An owned, non-Clone authority. Only a successful durable transaction creates one.
#[derive(Debug)]
pub struct CeremonyReleasePermit {
    reservation: CeremonyReservation,
    bound_epoch: Option<u64>,
    is_retry: bool,
    generation: u64,
    context: CeremonyContext,
    seal: [u8; 8],
}

/// One exclusive authority per key; no mutable subordinate ledger escapes this object.
///
/// A failed replacement or a refused anchor advance leaves the disk, the anchor and this
/// handle in an unknown relation, so it fails the handle permanently: every later commit
/// and release check is refused, and only a fresh open (which re-verifies the record against
/// the anchor) continues.
pub struct FsCeremonyJournal {
    record: LockedRecord,
    key_id: [u8; 32],
    mac_key: [u8; 32],
    checkpoint: LedgerCheckpoint,
    entries: Vec<JournalEntry>,
    anchor: Option<Box<dyn crate::ExternalMonotoneAnchor>>,
    failed: AtomicBool,
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

    /// The newest committed reservation, if any (see [`CommittedReservation`]).
    pub fn last_committed(&self) -> Option<CommittedReservation> {
        self.entries.last().map(|e| CommittedReservation {
            epoch_or_codeword: e.epoch_or_codeword,
            seed_burn_cursor: e.seed_burn_cursor,
            hedge_generation: e.hedge_generation,
            bound_epoch: e.bound_epoch,
            is_retry: e.is_retry,
        })
    }

    /// Whether an earlier write or anchor advance failed on this handle.
    pub fn is_failed(&self) -> bool {
        self.failed.load(Ordering::SeqCst)
    }

    fn ensure_usable(&self) -> io::Result<()> {
        if self.is_failed() {
            return Err(io::Error::other("ceremony journal handle failed; reopen"));
        }
        Ok(())
    }

    fn read_or_fail(&self) -> io::Result<Vec<u8>> {
        self.record.read().inspect_err(|_| {
            self.failed.store(true, Ordering::SeqCst);
        })
    }

    fn advance_anchor_or_fail(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        if let Some(anchor) = &self.anchor
            && let Err(e) = crate::durable_ledger::advance_anchor(&**anchor, checkpoint)
        {
            self.failed.store(true, Ordering::SeqCst);
            return Err(e);
        }
        Ok(())
    }

    pub fn create_new_anchored(
        path: impl Into<PathBuf>,
        key_id: [u8; 32],
        mac_key: [u8; 32],
        anchor: Box<dyn crate::ExternalMonotoneAnchor>,
    ) -> io::Result<Self> {
        if anchor.load()?.is_some() {
            return Err(invalid());
        }
        let mut journal = Self::create_new(path, key_id, mac_key)?;
        crate::durable_ledger::advance_anchor(&*anchor, journal.checkpoint)?;
        journal.anchor = Some(anchor);
        Ok(journal)
    }

    pub fn open_existing_anchored(
        path: impl Into<PathBuf>,
        key_id: [u8; 32],
        mac_key: [u8; 32],
        anchor: Box<dyn crate::ExternalMonotoneAnchor>,
    ) -> io::Result<Self> {
        let mut journal = match anchor.load()? {
            Some(minimum) => Self::open_existing_at_least(path, key_id, mac_key, minimum)?,
            // `create_new_anchored` wrote genesis but its anchor advance failed. No permit can
            // exist without an anchored commit, so only an empty genesis journal is adopted.
            None => {
                let journal = Self::open_existing(path, key_id, mac_key)?;
                if journal.checkpoint.generation != 1 || !journal.entries.is_empty() {
                    return Err(invalid());
                }
                journal
            }
        };
        crate::durable_ledger::advance_anchor(&*anchor, journal.checkpoint)?;
        journal.anchor = Some(anchor);
        Ok(journal)
    }

    pub fn create_new(
        path: impl Into<PathBuf>,
        key_id: [u8; 32],
        mac_key: [u8; 32],
    ) -> io::Result<Self> {
        let mut this = Self {
            record: LockedRecord::create_new(path)?,
            key_id,
            mac_key,
            checkpoint: LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
            entries: Vec::new(),
            anchor: None,
            failed: AtomicBool::new(false),
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
            anchor: None,
            failed: AtomicBool::new(false),
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
        if generation == min_checkpoint.generation
            && !ct_eq_bytes32(&stored_tag, &min_checkpoint.tag)
        {
            return Err(invalid());
        }
        for chunk in bytes[HEADER_LEN..end].as_chunks::<ENTRY_LEN>().0 {
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
                seed_burn_cursor: u64::from_be_bytes(
                    chunk[64..72].try_into().map_err(|_| invalid())?,
                ),
                hedge_generation: u64::from_be_bytes(
                    chunk[72..80].try_into().map_err(|_| invalid())?,
                ),
            };
            let context = CeremonyContext {
                policy_id: chunk[89..121].try_into().map_err(|_| invalid())?,
                spend_amount: u64::from_be_bytes(
                    chunk[121..129].try_into().map_err(|_| invalid())?,
                ),
                mpc_nonce_epoch: u64::from_be_bytes(
                    chunk[129..137].try_into().map_err(|_| invalid())?,
                ),
            };
            this.validate(&reservation, bound_epoch, is_retry, context)?;
            this.entries.push(JournalEntry::from_reservation(
                &reservation,
                bound_epoch,
                is_retry,
                context,
            ));
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
        let mut xof = Cshake256Xof::new(b"QSAG.CEREMONY.JOURNAL.MAC/v3");
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
            bytes.extend_from_slice(&e.context.policy_id);
            bytes.extend_from_slice(&e.context.spend_amount.to_be_bytes());
            bytes.extend_from_slice(&e.context.mpc_nonce_epoch.to_be_bytes());
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
        context: CeremonyContext,
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
        if let Some(last) = self.entries.last()
            && (context != CeremonyContext::default() || last.context != CeremonyContext::default())
            && context.mpc_nonce_epoch <= last.context.mpc_nonce_epoch
        {
            return Err(invalid());
        }
        if is_retry {
            let Some(last) = self.entries.last() else {
                return Err(invalid());
            };
            if last.context.policy_id != context.policy_id
                || last.context.spend_amount != context.spend_amount
                || last.bound_epoch != bound_epoch
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
        context: CeremonyContext,
    ) -> io::Result<CeremonyReleasePermit> {
        self.ensure_usable()?;
        self.validate(&r, bound_epoch, is_retry, context)?;
        let (expected_on_disk, expected_ckpt) = self.encode(self.checkpoint.generation, None);
        if expected_ckpt != self.checkpoint || self.read_or_fail()? != expected_on_disk {
            self.failed.store(true, Ordering::SeqCst);
            return Err(invalid());
        }
        let next_gen = self
            .checkpoint
            .generation
            .checked_add(1)
            .ok_or_else(invalid)?;
        let entry = JournalEntry::from_reservation(&r, bound_epoch, is_retry, context);
        let (next_bytes, next_ckpt) = self.encode(next_gen, Some(&entry));
        if let Err(e) = self.record.replace(&next_bytes) {
            self.failed.store(true, Ordering::SeqCst);
            return Err(e);
        }
        self.advance_anchor_or_fail(next_ckpt)?;
        self.checkpoint = next_ckpt;
        self.entries.push(entry);
        Ok(CeremonyReleasePermit {
            reservation: r,
            bound_epoch,
            is_retry,
            generation: next_gen,
            context,
            seal: self.record.lock_seal(),
        })
    }

    /// One fsynced replacement commits all reservations for an unbound ceremony (e.g. stateless
    /// codeword or PCG seed burn). Failure issues no permit.
    pub fn persist_before_release(
        &mut self,
        r: CeremonyReservation,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, None, false, CeremonyContext::default())
    }

    /// Commit a fresh stateful epoch reservation binding both the numeric `epoch` (which must
    /// strictly exceed every prior bound epoch in this journal) and `r.epoch_or_codeword`.
    pub fn persist_epoch_before_release(
        &mut self,
        epoch: u64,
        r: CeremonyReservation,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, Some(epoch), false, CeremonyContext::default())
    }

    /// Authorize a crash-recovery retry attempt for the currently in-flight unbound reservation.
    /// Requires the identical `epoch_or_codeword`, a fresh `ceremony_id`, and strictly advancing
    /// `seed_burn_cursor` and `hedge_generation`.
    pub fn commit_retry_attempt(
        &mut self,
        r: CeremonyReservation,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, None, true, CeremonyContext::default())
    }

    /// Authorize a crash-recovery retry attempt for the currently in-flight stateful `epoch`.
    /// Requires `epoch` and `r.epoch_or_codeword` to match the in-flight reservation identically,
    /// while `r.ceremony_id` is fresh and preprocessing/hedge cursors strictly advance.
    pub fn commit_epoch_retry_attempt(
        &mut self,
        epoch: u64,
        r: CeremonyReservation,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, Some(epoch), true, CeremonyContext::default())
    }

    /// Commit policy, spend and fresh MPC nonce atomically with the key reservation.
    /// A retry retains policy/spend and binding but advances the nonce and burn cursors.
    pub fn persist_with_context(
        &mut self,
        r: CeremonyReservation,
        epoch: Option<u64>,
        retry: bool,
        context: CeremonyContext,
    ) -> io::Result<CeremonyReleasePermit> {
        self.commit_internal(r, epoch, retry, context)
    }

    /// Check the caller's expected policy resources before consuming release authority.
    pub fn consume_release_with_context(
        &self,
        permit: CeremonyReleasePermit,
        expected: CeremonyContext,
    ) -> io::Result<CeremonyReservation> {
        if permit.context != expected {
            return Err(invalid());
        }
        self.consume_release(permit)
    }

    fn verify_current_permit(&self, permit: &CeremonyReleasePermit) -> io::Result<()> {
        self.ensure_usable()?;
        self.advance_anchor_or_fail(self.checkpoint)?;
        if permit.seal != self.record.lock_seal()
            || permit.generation != self.checkpoint.generation
            || !ct_eq_bytes32(&permit.reservation.key_id, &self.key_id)
        {
            return Err(invalid());
        }
        let Some(last) = self.entries.last() else {
            return Err(invalid());
        };
        if last.context != permit.context
            || !last.matches_permit(&permit.reservation, permit.bound_epoch, permit.is_retry)
        {
            return Err(invalid());
        }
        let (expected_on_disk, expected_ckpt) = self.encode(self.checkpoint.generation, None);
        if expected_ckpt != self.checkpoint || self.read_or_fail()? != expected_on_disk {
            self.failed.store(true, Ordering::SeqCst);
            return Err(invalid());
        }
        Ok(())
    }

    /// Consume current authority; advancing the journal invalidates older pending permits.
    /// Callers must perform this check before releasing their bound ceremony's output.
    pub fn consume_release(
        &self,
        permit: CeremonyReleasePermit,
    ) -> io::Result<CeremonyReservation> {
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
    #[derive(Clone, Default)]
    struct TestAnchor(std::sync::Arc<std::sync::Mutex<(Option<LedgerCheckpoint>, bool)>>);
    impl crate::ExternalMonotoneAnchor for TestAnchor {
        fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
            Ok(self.0.lock().unwrap().0)
        }
        fn advance(&self, next: LedgerCheckpoint) -> io::Result<()> {
            let mut state = self.0.lock().unwrap();
            if state.1
                || state.0.is_some_and(|old| {
                    old.generation > next.generation
                        || (old.generation == next.generation && old.tag != next.tag)
                })
            {
                return Err(invalid());
            }
            state.0 = Some(next);
            Ok(())
        }
    }

    #[test]
    fn belt_anchor_blocks_rollback_and_failed_advancement() {
        use crate::belt_latch::{BeltLatchState, DurableWal, FsBeltWal};
        fn assert_send<T: Send>() {}
        assert_send::<FsBeltWal>();
        assert_send::<FsCeremonyJournal>();
        let dir = std::env::temp_dir().join(format!(
            "qsag-belt-anchor-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("belt");
        let anchor = TestAnchor::default();
        let mut wal =
            FsBeltWal::provision_genesis_anchored(&path, [3; 32], Box::new(anchor.clone()))
                .unwrap();
        let snapshot = std::fs::read(&path).unwrap();
        wal.sync_persist(&BeltLatchState::default()).unwrap();
        assert_eq!(anchor.0.lock().unwrap().0, Some(wal.checkpoint()));
        anchor.0.lock().unwrap().1 = true;
        assert!(wal.sync_persist(&BeltLatchState::default()).is_err());
        drop(wal);
        anchor.0.lock().unwrap().1 = false;
        let wal =
            FsBeltWal::open_existing_anchored(&path, [3; 32], Box::new(anchor.clone())).unwrap();
        assert_eq!(anchor.0.lock().unwrap().0, Some(wal.checkpoint()));
        drop(wal);
        std::fs::write(&path, snapshot).unwrap();
        assert!(FsBeltWal::open_existing_anchored(&path, [3; 32], Box::new(anchor)).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    fn scratch_dir(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "qsag-{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        dir
    }

    fn reservation(n: u8) -> CeremonyReservation {
        CeremonyReservation {
            ceremony_id: [n; 32],
            key_id: [1; 32],
            epoch_or_codeword: [n; 32],
            seed_burn_cursor: u64::from(n),
            hedge_generation: u64::from(n),
        }
    }

    #[test]
    fn a_refused_anchor_advance_fails_the_journal_handle_for_good() {
        let dir = scratch_dir("journal-sticky");
        let path = dir.join("journal");
        let anchor = TestAnchor::default();
        let mut journal = FsCeremonyJournal::create_new_anchored(
            &path,
            [1; 32],
            [2; 32],
            Box::new(anchor.clone()),
        )
        .unwrap();
        let held = journal.persist_before_release(reservation(1)).unwrap();
        let before = journal.checkpoint();
        let committed_before = journal.last_committed();
        anchor.0.lock().unwrap().1 = true;
        assert!(journal.persist_before_release(reservation(2)).is_err());
        assert_eq!(journal.checkpoint(), before);
        assert_eq!(journal.last_committed(), committed_before);
        assert!(journal.is_failed());
        anchor.0.lock().unwrap().1 = false;
        // The anchor accepts again, but this handle's relation to it is unknown: it neither
        // commits (and so cannot climb past the anchor) nor honours a permit.
        assert!(journal.persist_before_release(reservation(3)).is_err());
        assert!(journal.consume_release(held).is_err());
        drop(journal);
        let mut journal =
            FsCeremonyJournal::open_existing_anchored(&path, [1; 32], [2; 32], Box::new(anchor))
                .unwrap();
        assert!(!journal.is_failed());
        let permit = journal.persist_before_release(reservation(3)).unwrap();
        assert_eq!(journal.consume_release(permit).unwrap(), reservation(3));
        drop(journal);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_refused_belt_anchor_advance_survives_latch_recovery_from_the_same_handle() {
        use crate::belt_latch::{BeltLatch, BeltLatchError, DurableWal, FsBeltWal, WalError};
        let dir = scratch_dir("belt-sticky");
        let path = dir.join("belt");
        let anchor = TestAnchor::default();
        let wal = FsBeltWal::provision_genesis_anchored(&path, [3; 32], Box::new(anchor.clone()))
            .unwrap();
        let mut latch = BeltLatch::recover(wal, 20).unwrap();
        anchor.0.lock().unwrap().1 = true;
        assert_eq!(
            latch.bind(0, &[1; 32], &[2; 32], &[1, 2]),
            Err(BeltLatchError::Wal(WalError::Io))
        );
        anchor.0.lock().unwrap().1 = false;
        let wal = latch.into_wal();
        assert!(wal.is_failed());
        assert!(BeltLatch::recover(wal, 20).is_err());
        let wal =
            FsBeltWal::open_existing_anchored(&path, [3; 32], Box::new(anchor.clone())).unwrap();
        assert!(!wal.is_failed());
        assert!(wal.load().unwrap().is_some());
        assert_eq!(anchor.0.lock().unwrap().0, Some(wal.checkpoint()));
        drop(wal);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_genesis_whose_anchor_advance_failed_is_adopted_and_nothing_later_is() {
        use crate::belt_latch::{BeltLatchState, DurableWal, FsBeltWal};
        let dir = scratch_dir("anchor-genesis");
        let anchor = TestAnchor::default();
        anchor.0.lock().unwrap().1 = true;
        let jpath = dir.join("journal");
        let bpath = dir.join("belt");
        assert!(
            FsCeremonyJournal::create_new_anchored(
                &jpath,
                [1; 32],
                [2; 32],
                Box::new(anchor.clone())
            )
            .is_err()
        );
        assert!(
            FsBeltWal::provision_genesis_anchored(&bpath, [3; 32], Box::new(anchor.clone()))
                .is_err()
        );
        anchor.0.lock().unwrap().1 = false;
        let journal_anchor = TestAnchor::default();
        let mut journal = FsCeremonyJournal::open_existing_anchored(
            &jpath,
            [1; 32],
            [2; 32],
            Box::new(journal_anchor.clone()),
        )
        .unwrap();
        assert_eq!(journal.checkpoint().generation, 1);
        assert_eq!(
            journal_anchor.0.lock().unwrap().0,
            Some(journal.checkpoint())
        );
        journal.persist_before_release(reservation(1)).unwrap();
        drop(journal);
        let mut wal =
            FsBeltWal::open_existing_anchored(&bpath, [3; 32], Box::new(anchor.clone())).unwrap();
        assert_eq!(anchor.0.lock().unwrap().0, Some(wal.checkpoint()));
        wal.sync_persist(&BeltLatchState {
            next_epoch: 1,
            in_flight: None,
        })
        .unwrap();
        drop(wal);
        // Past genesis, an unenrolled anchor is a lost anchor, not a fresh one.
        assert!(
            FsCeremonyJournal::open_existing_anchored(
                &jpath,
                [1; 32],
                [2; 32],
                Box::new(TestAnchor::default())
            )
            .is_err()
        );
        assert!(
            FsBeltWal::open_existing_anchored(&bpath, [3; 32], Box::new(TestAnchor::default()))
                .is_err()
        );
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_crash_after_the_reservation_is_recovered_through_the_committed_cursors() {
        let dir = scratch_dir("journal-cursor");
        let path = dir.join("journal");
        let mut journal = FsCeremonyJournal::create_new(&path, [1; 32], [2; 32]).unwrap();
        assert_eq!(journal.last_committed(), None);
        // The caller's own burn ledger stands at generation 4 and reserves cursor 5 for seed
        // `[9; 32]`; the process dies before that ledger advances.
        let seed_id = [9; 32];
        journal
            .persist_before_release(CeremonyReservation {
                ceremony_id: [1; 32],
                key_id: [1; 32],
                epoch_or_codeword: seed_id,
                seed_burn_cursor: 5,
                hedge_generation: 5,
            })
            .unwrap();
        drop(journal);
        let mut journal = FsCeremonyJournal::open_existing(&path, [1; 32], [2; 32]).unwrap();
        // Recomputing the cursor from the stale burn ledger reuses 5 and is refused.
        assert!(
            journal
                .persist_before_release(CeremonyReservation {
                    ceremony_id: [2; 32],
                    key_id: [1; 32],
                    epoch_or_codeword: seed_id,
                    seed_burn_cursor: 5,
                    hedge_generation: 5,
                })
                .is_err()
        );
        let last = journal.last_committed().unwrap();
        assert_eq!(
            last,
            CommittedReservation {
                epoch_or_codeword: seed_id,
                seed_burn_cursor: 5,
                hedge_generation: 5,
                bound_epoch: None,
                is_retry: false,
            }
        );
        let burn_ledger_next = 5;
        let cursor = burn_ledger_next.max(last.seed_burn_cursor) + 1;
        let hedge = last.hedge_generation + 1;
        let retry = CeremonyReservation {
            ceremony_id: [3; 32],
            key_id: [1; 32],
            epoch_or_codeword: seed_id,
            seed_burn_cursor: cursor,
            hedge_generation: hedge,
        };
        let permit = journal.commit_retry_attempt(retry).unwrap();
        assert_eq!(journal.consume_release(permit).unwrap().seed_burn_cursor, 6);
        assert!(journal.last_committed().unwrap().is_retry);
        drop(journal);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn policy_context_and_external_anchor_survive_restart_and_fail_closed() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-context-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("journal");
        let anchor = TestAnchor::default();
        let mut journal = FsCeremonyJournal::create_new_anchored(
            &path,
            [1; 32],
            [2; 32],
            Box::new(anchor.clone()),
        )
        .unwrap();
        let snapshot = std::fs::read(&path).unwrap();
        let reservation = |n| CeremonyReservation {
            ceremony_id: [n; 32],
            key_id: [1; 32],
            epoch_or_codeword: [3; 32],
            seed_burn_cursor: u64::from(n),
            hedge_generation: u64::from(n),
        };
        let context = CeremonyContext {
            policy_id: [4; 32],
            spend_amount: 50,
            mpc_nonce_epoch: 1,
        };
        let permit = journal
            .persist_with_context(reservation(1), Some(7), false, context)
            .unwrap();
        let changed = CeremonyContext {
            spend_amount: 51,
            ..context
        };
        assert!(
            journal
                .consume_release_with_context(permit, changed)
                .is_err()
        );
        drop(journal);
        let mut journal = FsCeremonyJournal::open_existing_anchored(
            &path,
            [1; 32],
            [2; 32],
            Box::new(anchor.clone()),
        )
        .unwrap();
        assert!(
            journal
                .persist_with_context(reservation(2), Some(7), true, context)
                .is_err()
        );
        assert!(
            journal
                .persist_with_context(
                    reservation(2),
                    Some(7),
                    true,
                    CeremonyContext {
                        mpc_nonce_epoch: 2,
                        ..changed
                    }
                )
                .is_err()
        );
        let next = CeremonyContext {
            mpc_nonce_epoch: 2,
            ..context
        };
        let permit = journal
            .persist_with_context(reservation(2), Some(7), true, next)
            .unwrap();
        assert_eq!(
            journal
                .consume_release_with_context(permit, next)
                .unwrap()
                .seed_burn_cursor,
            2
        );
        anchor.0.lock().unwrap().1 = true;
        assert!(
            journal
                .persist_with_context(
                    reservation(3),
                    Some(7),
                    true,
                    CeremonyContext {
                        mpc_nonce_epoch: 3,
                        ..context
                    }
                )
                .is_err()
        );
        drop(journal);
        anchor.0.lock().unwrap().1 = false;
        // The durable successor is recoverable after anchor failure, but the old snapshot is not.
        let journal = FsCeremonyJournal::open_existing_anchored(
            &path,
            [1; 32],
            [2; 32],
            Box::new(anchor.clone()),
        )
        .unwrap();
        drop(journal);
        let latest = std::fs::read(&path).unwrap();
        std::fs::write(&path, snapshot).unwrap();
        assert!(
            FsCeremonyJournal::open_existing_anchored(&path, [1; 32], [2; 32], Box::new(anchor))
                .is_err()
        );
        let mut tampered = latest;
        tampered[HEADER_LEN + 121] ^= 1; // spend amount is MAC-covered
        std::fs::write(&path, tampered).unwrap();
        assert!(FsCeremonyJournal::open_existing(&path, [1; 32], [2; 32]).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

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
        let mut journal =
            FsCeremonyJournal::create_new(dir.join("journal"), [4; 32], [5; 32]).unwrap();
        let mut signed =
            FsFirstSignedLedger::provision_genesis(dir.join("signed"), [6; 32]).unwrap();
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
        let permit = journal
            .persist_before_release(reservation(1, [1; 32]))
            .unwrap();
        signed.authorize_release(&journal, permit).unwrap();
        signed.begin_release(&[4; 32], &[1; 32], &[1; 32]).unwrap();
        assert!(signed.begin_release(&[4; 32], &[1; 32], &[1; 32]).is_err());
        let permit = journal
            .persist_before_release(reservation(2, [2; 32]))
            .unwrap();
        signed.authorize_release(&journal, permit).unwrap();
        assert!(signed.begin_release(&[9; 32], &[2; 32], &[2; 32]).is_err());
        assert!(signed.begin_release(&[4; 32], &[2; 32], &[2; 32]).is_err());
        assert!(burns.begin_expansion(&[3; 32], &[3; 32]).is_err());
        let permit = journal
            .persist_before_release(reservation(3, [3; 32]))
            .unwrap();
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
        let unbound_permit = journal
            .persist_before_release(reservation(4, [0x44; 32]))
            .unwrap();
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
        let belt = FsBeltWal::provision_genesis(&bpath, [8; 32]).unwrap();
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
