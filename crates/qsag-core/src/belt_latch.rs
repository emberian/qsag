//! `BeltLatch`: the durable one-time-leaf latch that gates every stateful `Jorts` opening.
//!
//! A one-time WOTS leaf (an *epoch*) may reveal chain nodes for exactly one digit vector. The
//! latch enforces that in three steps, and the chain shares can only be opened with the
//! [`OpenPermit`] the last step returns:
//!
//! 1. **Bind before open.** [`BeltLatch::bind`] writes `(epoch, msg_digest, retry_salt,
//!    target_sum_digits)` through [`DurableWal::sync_persist`] and only then updates memory.
//!    An epoch below the persisted high-water mark that is not the in-flight record is never
//!    bound again, so a crash can lose a leaf but cannot reuse one.
//! 2. **Replay, never re-roll.** A retry of the in-flight epoch must present the same message
//!    digest, the same salt and the same digits. A different message digest is refused with
//!    [`BeltLatchError::EpochAlreadyBound`], a different salt with
//!    [`BeltLatchError::RetrySaltMismatch`]: a fresh salt would select a second digit vector
//!    on the same leaf.
//! 3. **Peer echo.** [`BeltLatch::verify_peer_echoes`] requires the [`BeltEcho`] of *both*
//!    other signers and compares each with the local record. A corrupted signer that shows
//!    two honest signers different messages for one epoch is caught here, because the two
//!    honest signers exchange echoes directly.
//!
//! All three signers take part in every signature (the threshold is on the secret sharing,
//! not on attendance), so step 3 always has both echoes available. A signer that holds a
//! record its peers lack cannot prove the salt came from a coin flip; the caller's remedy is
//! to burn the epoch and sign at the next one, never to adopt a claimed salt.
//!
//! ### Echo authentication
//! An echo is addressed to one receiver and carries a `cSHAKE256` MAC over
//! `(sender, receiver, epoch, msg_digest, retry_salt, binding)` under a key held only by that
//! sender and that receiver ([`EchoMacKeys`]). The receiver recomputes the tag with the key
//! it shares with the claimed sender and compares in constant time; a mismatch is
//! [`BeltLatchError::EchoMacInvalid`]. The third signer does not hold that key, so it cannot
//! produce an echo "from" one honest signer that the other accepts, whatever the transport.
//! The MAC does not stop a replay of a genuine echo; a replayed echo carries its original
//! epoch and binding and is compared with the local record like any other.
//!
//! Where the keys come from is the caller's decision. [`derive_echo_mac_key`] hashes
//! secret material held by exactly one pair into a key used for nothing else. `Jorts` feeds
//! it the replicated key ceremony's share slots: slot `s` is held by parties `s` and
//! `s + 2 (mod 3)` and by nobody else, so each pair owns one slot. A latch recovered with
//! [`BeltLatch::recover`] has no keys; it can bind (for callers that authenticate their own
//! acknowledgements) but [`BeltLatch::echo_for`] and [`BeltLatch::verify_peer_echoes`]
//! refuse with [`BeltLatchError::EchoKeysMissing`].
//!
//! ### Epoch window
//! Sequential wallets accept fresh binds through `next_epoch + MAX_EPOCH_JUMP`.
//! Consensus signers use [`BeltLatch::recover_slot_indexed`] to bind any forward slot
//! within capacity. [`BeltLatch::bind_consensus_slot`] returns that slot as the leaf
//! index and permanently burns skipped indices. Only [`BeltLatch::bind`] permits
//! exact replay of the in-flight record during recovery.
//!
//! ### Log failure is terminal
//! If [`DurableWal::sync_persist`] fails, nothing is known about what reached storage. The
//! latch remains poisoned when it returns the error, and from then on `latched_salt`,
//! `bind`, `echo_for` and `verify_peer_echoes` return [`BeltLatchError::WalPoisoned`]. The
//! only way forward is a new latch recovered from the log.

use alloc::vec::Vec;
use core::fmt;
use qsag_verified::BeltLatchKernel;

use crate::sponge::keccak::{Cshake256Xof, cshake256_32, cshake256_32_multi_frame};
use crate::wipe::{ct_eq_bytes32, wipe_bytes32};

/// Largest permitted forward jump in sequential wallet mode.
pub const MAX_EPOCH_JUMP: u64 = 64;

/// Longest digit vector a record may carry: the bound of the verified transition kernel,
/// whose digit representation holds no more.
pub const MAX_TARGET_SUM_DIGITS: usize = qsag_verified::BELT_LATCH_MAX_DIGITS as usize;

const TAG_ECHO_KEY: &[u8] = b"QSAG.BELT.ECHO.KEY/v1";
const TAG_ECHO_MAC: &[u8] = b"QSAG.BELT.ECHO.MAC/v1";
#[cfg(feature = "std")]
const TAG_WAL_MAC: &[u8] = b"QSAG.BELT.LATCH.WAL.MAC/v3";
#[cfg(feature = "std")]
const TAG_WAL_TICKET: &[u8] = b"QSAG.BELT.LATCH.WAL.TICKET/v1";
#[cfg(feature = "std")]
const WAL_HEADER_LEN: usize = 8 + 32 + 32;

/// The durable binding of one epoch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BeltLatchRecord {
    pub epoch: u64,
    pub msg_digest: [u8; 32],
    pub retry_salt: [u8; 32],
    /// Base-`w` digits whose chain nodes this epoch may reveal.
    pub target_sum_digits: Vec<u8>,
}

impl BeltLatchRecord {
    /// Digest binding every field; this is what signers echo and what a permit carries.
    pub fn binding(&self) -> [u8; 32] {
        cshake256_32_multi_frame(
            b"QSAG.BELT.LATCH.BINDING/v1",
            &[
                &self.epoch.to_be_bytes(),
                &self.msg_digest,
                &self.retry_salt,
                &self.target_sum_digits,
            ],
        )
    }
}

/// Everything a write-ahead log must hold: the high-water mark and the in-flight record.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BeltLatchState {
    /// Every lower index is consumed, including indices skipped by a forward jump.
    pub next_epoch: u64,
    pub in_flight: Option<BeltLatchRecord>,
}

const STATE_MAGIC: &[u8; 8] = b"QSAGBLT1";

impl BeltLatchState {
    /// Canonical encoding with a trailing integrity digest.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(STATE_MAGIC);
        out.extend_from_slice(&self.next_epoch.to_be_bytes());
        match &self.in_flight {
            None => out.push(0),
            Some(rec) => {
                out.push(1);
                out.extend_from_slice(&rec.epoch.to_be_bytes());
                out.extend_from_slice(&rec.msg_digest);
                out.extend_from_slice(&rec.retry_salt);
                out.extend_from_slice(&(rec.target_sum_digits.len() as u32).to_be_bytes());
                out.extend_from_slice(&rec.target_sum_digits);
            }
        }
        let tag = cshake256_32(b"QSAG.BELT.LATCH.WAL/v1", &out);
        out.extend_from_slice(&tag);
        out
    }

    /// Strict decoder: any truncation, trailing byte or digest mismatch is `None`.
    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        if raw.len() < STATE_MAGIC.len() + 8 + 1 + 32 {
            return None;
        }
        let (body, tag) = raw.split_at(raw.len() - 32);
        let want = cshake256_32(b"QSAG.BELT.LATCH.WAL/v1", body);
        if !ct_eq_bytes32(&want, tag.try_into().ok()?) || &body[..8] != STATE_MAGIC {
            return None;
        }
        let next_epoch = u64::from_be_bytes(body[8..16].try_into().ok()?);
        let rest = &body[17..];
        let in_flight = match body[16] {
            0 if rest.is_empty() => None,
            1 if rest.len() >= 8 + 32 + 32 + 4 => {
                let epoch = u64::from_be_bytes(rest[..8].try_into().ok()?);
                let msg_digest: [u8; 32] = rest[8..40].try_into().ok()?;
                let retry_salt: [u8; 32] = rest[40..72].try_into().ok()?;
                let len = u32::from_be_bytes(rest[72..76].try_into().ok()?) as usize;
                if len > MAX_TARGET_SUM_DIGITS || rest.len() != 76 + len {
                    return None;
                }
                Some(BeltLatchRecord {
                    epoch,
                    msg_digest,
                    retry_salt,
                    target_sum_digits: rest[76..].to_vec(),
                })
            }
            _ => return None,
        };
        if let Some(rec) = &in_flight
            && rec.epoch >= next_epoch
        {
            return None;
        }
        Some(Self {
            next_epoch,
            in_flight,
        })
    }
}

/// Storage failure of a [`DurableWal`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalError {
    /// The write or its sync did not complete.
    Io,
    /// A stored state exists but does not decode.
    Corrupt,
}

/// Abstract durable storage for the latch state.
pub trait DurableWal {
    /// Authorize one release of the bound record after its durable journal transaction.
    fn authorize_open(&self, _record: &BeltLatchRecord) -> Result<(), WalError> {
        Err(WalError::Io)
    }

    /// Store `state` and return only once it would survive a power loss. On error nothing may
    /// be assumed about what was written; the latch then refuses to proceed.
    fn sync_persist(&mut self, state: &BeltLatchState) -> Result<(), WalError>;

    /// Load the last successfully persisted state; `Ok(None)` only for storage that was never
    /// written.
    fn load(&self) -> Result<Option<BeltLatchState>, WalError>;
}

/// Volatile [`DurableWal`] for tests and for hosts that supply their own durability one level
/// up. It is *not* durable: a process restart loses it.
///
/// Only a fresh, unpersisted `MemoryWal` may be cloned (e.g. `vec![MemoryWal::new(); n]`);
/// attempting to clone an active `MemoryWal` panics so tests and callers cannot accidentally
/// fork a live epoch-latch authority into two rollback views.
#[cfg(any(test, feature = "testing-ephemeral"))]
#[derive(Debug, Default)]
pub struct MemoryWal {
    stored: Option<Vec<u8>>,
    persists: u64,
    fail_next: bool,
}

#[cfg(any(test, feature = "testing-ephemeral"))]
impl Clone for MemoryWal {
    fn clone(&self) -> Self {
        assert!(
            self.stored.is_none() && self.persists == 0 && !self.fail_next,
            "MemoryWal: cloning an active volatile WAL authority is forbidden"
        );
        Self::new()
    }
}

#[cfg(any(test, feature = "testing-ephemeral"))]
impl MemoryWal {
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of successful persists.
    pub fn persist_count(&self) -> u64 {
        self.persists
    }

    /// Make the next [`DurableWal::sync_persist`] fail without storing anything.
    pub fn fail_next_persist(&mut self) {
        self.fail_next = true;
    }
}

#[cfg(any(test, feature = "testing-ephemeral"))]
impl DurableWal for MemoryWal {
    fn authorize_open(&self, _record: &BeltLatchRecord) -> Result<(), WalError> {
        Ok(())
    }
    fn sync_persist(&mut self, state: &BeltLatchState) -> Result<(), WalError> {
        if self.fail_next {
            self.fail_next = false;
            return Err(WalError::Io);
        }
        self.stored = Some(state.to_bytes());
        self.persists += 1;
        Ok(())
    }

    fn load(&self) -> Result<Option<BeltLatchState>, WalError> {
        match &self.stored {
            None => Ok(None),
            Some(raw) => BeltLatchState::from_bytes(raw)
                .map(Some)
                .ok_or(WalError::Corrupt),
        }
    }
}

/// File-backed [`DurableWal`]: exclusive process lock, write to a temporary file, `fsync`,
/// atomic rename, directory `fsync`.
///
/// The stored record is `generation.to_be_bytes() || reservation || nonce ||
/// BeltLatchState::to_bytes() || tag`, where `tag` is a `cSHAKE256` MAC over
/// `(wal_key, lock_seal, generation, reservation, nonce, state_bytes)` under a secret
/// `wal_key` the signer keeps apart from the log. `reservation` and `nonce` are the
/// [`crate::TicketSeal`] of the anchor ticket the record was committed under, all zero
/// without an anchor. Genesis and recovery are separate entry points:
///
/// * [`FsBeltWal::provision_genesis`] is for a newly enrolled key. It refuses a path whose
///   log or lock sidecar already exists, and durably writes an authenticated epoch-0 record
///   (`generation = 1`) before it returns.
/// * [`FsBeltWal::open_existing_at_least`] enforces an externally retained monotonic
///   [`crate::durable_ledger::LedgerCheckpoint`] so full disk-snapshot rollback is refused.
/// * [`FsBeltWal::open_existing`] is for unanchored recovery. A missing log, a missing lock
///   sidecar, or a record that fails the MAC is an error; nothing here ever falls back to
///   epoch 0, so [`DurableWal::load`] never returns `Ok(None)` for this type.
///
/// An anchored log commits every record under a single-use anchor ticket: it reserves the
/// successor of its checkpoint (a second contender is refused there, before writing),
/// replaces the record, then consumes the ticket, which settles the anchor on the new
/// record's checkpoint. Reopening after a crash in between either re-seals the unchanged
/// state under a fresh ticket (the record was not yet replaced) or settles the anchor on
/// the replaced record; the anchor refuses every other disk state.
///
/// A failed replacement, a refused reservation or a refused consumption fails the handle
/// permanently, including for a latch recovered from it through [`BeltLatch::into_wal`]:
/// a log whose relation to its anchor is unknown must be reopened from disk against the
/// anchor.
#[cfg(feature = "std")]
pub struct FsBeltWal {
    record: qsag_asm::durable::LockedRecord,
    wal_key: [u8; 32],
    checkpoint: crate::durable_ledger::LedgerCheckpoint,
    /// Reservation the record found at open was committed under.
    reservation: [u8; 32],
    anchor: Option<alloc::boxed::Box<dyn crate::ExternalMonotoneAnchor>>,
    release: core::cell::RefCell<Option<(crate::ceremony_journal::CeremonyReservation, u64)>>,
    failed: core::cell::Cell<Option<WalError>>,
}

#[cfg(feature = "std")]
impl fmt::Debug for FsBeltWal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FsBeltWal").finish_non_exhaustive()
    }
}

#[cfg(feature = "std")]
impl Drop for FsBeltWal {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.wal_key);
    }
}

#[cfg(feature = "std")]
impl FsBeltWal {
    /// Current authenticated checkpoint; persist in an external monotonic anchor before
    /// releasing chain openings to defend against full disk-snapshot rollback.
    pub const fn checkpoint(&self) -> crate::durable_ledger::LedgerCheckpoint {
        self.checkpoint
    }

    /// Whether an earlier write, read, authentication check, or anchor advance failed on this handle.
    pub fn is_failed(&self) -> bool {
        self.failed.get().is_some()
    }

    fn advance_anchor_or_fail(
        &self,
        checkpoint: crate::durable_ledger::LedgerCheckpoint,
    ) -> Result<(), WalError> {
        if let Some(anchor) = &self.anchor
            && crate::durable_ledger::advance_anchor(&**anchor, checkpoint).is_err()
        {
            self.failed.set(Some(WalError::Io));
            return Err(WalError::Io);
        }
        Ok(())
    }

    /// Open under an independently durable anchor and reconcile with it (see the type
    /// notes). An unenrolled anchor adopts only an untouched genesis log, the state
    /// [`Self::provision_genesis_anchored`] leaves when its anchor advance fails.
    pub fn open_existing_anchored(
        path: impl Into<std::path::PathBuf>,
        wal_key: [u8; 32],
        anchor: alloc::boxed::Box<dyn crate::ExternalMonotoneAnchor>,
    ) -> std::io::Result<Self> {
        use crate::durable_ledger::AnchorStanding;
        let mut wal = Self::open_existing(path, wal_key)?;
        let state = wal
            .load()
            .ok()
            .flatten()
            .ok_or_else(|| std::io::Error::other("belt latch log unreadable"))?;
        match anchor.reconcile(wal.checkpoint, &wal.reservation)? {
            AnchorStanding::Settled => {}
            AnchorStanding::Unenrolled => {
                if wal.checkpoint.generation != 1 || state != BeltLatchState::default() {
                    return Err(std::io::Error::other("missing belt anchor"));
                }
                crate::durable_ledger::advance_anchor(&*anchor, wal.checkpoint)?;
            }
            AnchorStanding::Reserved(abandoned) => {
                let (seal, checkpoint) = anchor.commit_with_ticket(
                    abandoned,
                    wal.checkpoint,
                    wal.ticket_context(&state),
                    |seal| wal.write(seal, &state),
                )?;
                wal.reservation = seal.reservation;
                wal.checkpoint = checkpoint;
            }
        }
        wal.anchor = Some(anchor);
        Ok(wal)
    }

    pub fn provision_genesis_anchored(
        path: impl Into<std::path::PathBuf>,
        wal_key: [u8; 32],
        anchor: alloc::boxed::Box<dyn crate::ExternalMonotoneAnchor>,
    ) -> std::io::Result<Self> {
        if anchor.load()?.is_some() {
            return Err(std::io::Error::other("belt anchor already enrolled"));
        }
        let mut wal = Self::provision_genesis(path, wal_key)?;
        crate::durable_ledger::advance_anchor(&*anchor, wal.checkpoint)?;
        wal.anchor = Some(anchor);
        Ok(wal)
    }

    /// Bind both numeric `epoch` and `epoch_or_codeword == BeltLatchRecord::binding()`.
    /// A permit authorizes only one opening attempt; crash recovery requires a fresh
    /// retry-attempt permit via [`crate::ceremony_journal::FsCeremonyJournal::commit_epoch_retry_attempt`].
    pub fn authorize_release(
        &mut self,
        journal: &crate::ceremony_journal::FsCeremonyJournal,
        permit: crate::ceremony_journal::CeremonyReleasePermit,
    ) -> std::io::Result<()> {
        *self.release.get_mut() = None;
        if self.is_failed() {
            return Err(std::io::Error::other(
                "belt latch log handle failed; reopen",
            ));
        }
        *self.release.get_mut() = Some(journal.consume_belt_release(permit)?);
        Ok(())
    }

    fn tag(
        wal_key: &[u8; 32],
        lock_seal: &[u8; 8],
        seal: &crate::TicketSeal,
        state_bytes: &[u8],
    ) -> [u8; 32] {
        cshake256_32_multi_frame(
            TAG_WAL_MAC,
            &[
                wal_key,
                lock_seal,
                &seal.generation.to_be_bytes(),
                &seal.reservation,
                &seal.nonce,
                state_bytes,
            ],
        )
    }

    fn seal(
        &self,
        seal: &crate::TicketSeal,
        state: &BeltLatchState,
    ) -> (Vec<u8>, crate::durable_ledger::LedgerCheckpoint) {
        let state_bytes = state.to_bytes();
        let tag = Self::tag(&self.wal_key, &self.record.lock_seal(), seal, &state_bytes);
        let mut out = Vec::with_capacity(WAL_HEADER_LEN + state_bytes.len() + 32);
        out.extend_from_slice(&seal.generation.to_be_bytes());
        out.extend_from_slice(&seal.reservation);
        out.extend_from_slice(&seal.nonce);
        out.extend_from_slice(&state_bytes);
        out.extend_from_slice(&tag);
        (
            out,
            crate::durable_ledger::LedgerCheckpoint {
                generation: seal.generation,
                tag,
            },
        )
    }

    fn unseal(
        &self,
        raw: &[u8],
    ) -> Option<(
        crate::durable_ledger::LedgerCheckpoint,
        crate::TicketSeal,
        BeltLatchState,
    )> {
        let (body, tag_slice) = raw.split_at_checked(raw.len().checked_sub(32)?)?;
        let (header, state_bytes) = body.split_at_checked(WAL_HEADER_LEN)?;
        let tag: [u8; 32] = tag_slice.try_into().ok()?;
        let seal = crate::TicketSeal {
            generation: u64::from_be_bytes(header[..8].try_into().ok()?),
            reservation: header[8..40].try_into().ok()?,
            nonce: header[40..].try_into().ok()?,
        };
        if seal.generation == 0 {
            return None;
        }
        let want = Self::tag(&self.wal_key, &self.record.lock_seal(), &seal, state_bytes);
        if !ct_eq_bytes32(&want, &tag) {
            return None;
        }
        let state = BeltLatchState::from_bytes(state_bytes)?;
        Some((
            crate::durable_ledger::LedgerCheckpoint {
                generation: seal.generation,
                tag,
            },
            seal,
            state,
        ))
    }

    /// What an anchor ticket for the record holding `state` is bound to: this log's
    /// identity and that state. The record's generation is bound by the ticket's epoch,
    /// and its MAC cannot be: it covers the ticket.
    fn ticket_context(&self, state: &BeltLatchState) -> [u8; 32] {
        cshake256_32_multi_frame(
            TAG_WAL_TICKET,
            &[&self.record.lock_seal(), &state.to_bytes()],
        )
    }

    fn write(
        &self,
        seal: &crate::TicketSeal,
        state: &BeltLatchState,
    ) -> std::io::Result<crate::durable_ledger::LedgerCheckpoint> {
        let (encoded, checkpoint) = self.seal(seal, state);
        self.record.replace(&encoded)?;
        Ok(checkpoint)
    }

    /// Provision the log of a newly enrolled key at `path` and write its authenticated
    /// epoch-0 record. Fails if a log or lock sidecar is already there.
    pub fn provision_genesis(
        path: impl Into<std::path::PathBuf>,
        wal_key: [u8; 32],
    ) -> std::io::Result<Self> {
        let mut wal = Self {
            record: qsag_asm::durable::LockedRecord::create_new(path)?,
            wal_key,
            checkpoint: crate::durable_ledger::LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
            reservation: [0; 32],
            anchor: None,
            release: core::cell::RefCell::new(None),
            failed: core::cell::Cell::new(None),
        };
        wal.checkpoint = wal.write(
            &crate::TicketSeal::unanchored(1),
            &BeltLatchState::default(),
        )?;
        Ok(wal)
    }

    /// Open (and lock) a log that [`Self::provision_genesis`] created while enforcing an
    /// externally retained minimum checkpoint. Rejects any record older than
    /// `min_checkpoint.generation` or carrying a mismatched tag at `min_checkpoint.generation`.
    pub fn open_existing_at_least(
        path: impl Into<std::path::PathBuf>,
        wal_key: [u8; 32],
        min_checkpoint: crate::durable_ledger::LedgerCheckpoint,
    ) -> std::io::Result<Self> {
        let mut wal = Self {
            record: qsag_asm::durable::LockedRecord::open_existing(path)?,
            wal_key,
            checkpoint: crate::durable_ledger::LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
            reservation: [0; 32],
            anchor: None,
            release: core::cell::RefCell::new(None),
            failed: core::cell::Cell::new(None),
        };
        let raw = wal.record.read()?;
        let Some((ckpt, seal, _)) = wal.unseal(&raw) else {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "belt latch log failed authentication",
            ));
        };
        if ckpt.generation < min_checkpoint.generation
            || (ckpt.generation == min_checkpoint.generation
                && !ct_eq_bytes32(&ckpt.tag, &min_checkpoint.tag))
        {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "belt latch log rolled back below checkpoint",
            ));
        }
        wal.checkpoint = ckpt;
        wal.reservation = seal.reservation;
        Ok(wal)
    }

    /// Open (and lock) a log that [`Self::provision_genesis`] created. Fails if the log or its
    /// lock sidecar is missing, or if the record does not verify under `wal_key`.
    /// Callers defending against full disk-snapshot rollback should use
    /// [`Self::open_existing_at_least`].
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        wal_key: [u8; 32],
    ) -> std::io::Result<Self> {
        Self::open_existing_at_least(
            path,
            wal_key,
            crate::durable_ledger::LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
        )
    }
}

#[cfg(feature = "std")]
impl DurableWal for FsBeltWal {
    fn authorize_open(&self, record: &BeltLatchRecord) -> Result<(), WalError> {
        if let Some(err) = self.failed.get() {
            return Err(err);
        }
        self.advance_anchor_or_fail(self.checkpoint)?;
        let (reservation, bound_epoch) = self.release.borrow_mut().take().ok_or(WalError::Io)?;
        if bound_epoch != record.epoch
            || !ct_eq_bytes32(&reservation.epoch_or_codeword, &record.binding())
        {
            return Err(WalError::Corrupt);
        }
        Ok(())
    }

    fn sync_persist(&mut self, state: &BeltLatchState) -> Result<(), WalError> {
        if let Some(err) = self.failed.get() {
            return Err(err);
        }
        let current_raw = self.record.read().map_err(|_| {
            self.failed.set(Some(WalError::Io));
            WalError::Io
        })?;
        let (on_disk_ckpt, _, _) = self.unseal(&current_raw).ok_or_else(|| {
            self.failed.set(Some(WalError::Corrupt));
            WalError::Corrupt
        })?;
        if on_disk_ckpt.generation != self.checkpoint.generation
            || !ct_eq_bytes32(&on_disk_ckpt.tag, &self.checkpoint.tag)
        {
            self.failed.set(Some(WalError::Corrupt));
            return Err(WalError::Corrupt);
        }
        let committed = match &self.anchor {
            Some(anchor) => anchor
                .commit_with_ticket(
                    self.checkpoint,
                    self.checkpoint,
                    self.ticket_context(state),
                    |seal| self.write(seal, state),
                )
                .map(|(_, checkpoint)| checkpoint),
            None => {
                let next_gen = self
                    .checkpoint
                    .generation
                    .checked_add(1)
                    .ok_or(WalError::Corrupt)?;
                self.write(&crate::TicketSeal::unanchored(next_gen), state)
            }
        };
        // A refused reservation, a failed replacement and a refused consumption all
        // leave this handle's relation to the disk or the anchor unknown.
        self.checkpoint = committed.map_err(|_| {
            self.failed.set(Some(WalError::Io));
            WalError::Io
        })?;
        Ok(())
    }

    fn load(&self) -> Result<Option<BeltLatchState>, WalError> {
        if let Some(err) = self.failed.get() {
            return Err(err);
        }
        match self.record.read() {
            Ok(raw) => {
                let (ckpt, _, state) = self.unseal(&raw).ok_or_else(|| {
                    self.failed.set(Some(WalError::Corrupt));
                    WalError::Corrupt
                })?;
                if ckpt.generation < self.checkpoint.generation
                    || (ckpt.generation == self.checkpoint.generation
                        && !ct_eq_bytes32(&ckpt.tag, &self.checkpoint.tag))
                {
                    self.failed.set(Some(WalError::Corrupt));
                    return Err(WalError::Corrupt);
                }
                Ok(Some(state))
            }
            Err(e)
                if matches!(
                    e.kind(),
                    std::io::ErrorKind::NotFound | std::io::ErrorKind::InvalidData
                ) =>
            {
                self.failed.set(Some(WalError::Corrupt));
                Err(WalError::Corrupt)
            }
            Err(_) => {
                self.failed.set(Some(WalError::Io));
                Err(WalError::Io)
            }
        }
    }
}

/// Errors of [`BeltLatch`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeltLatchError {
    /// `capacity_log2` is zero or above 62.
    InvalidCapacity,
    /// The epoch is at or beyond the key's capacity.
    Exhausted,
    /// The epoch is in flight for a different message digest.
    EpochAlreadyBound,
    /// The epoch is in flight with a different salt; the persisted salt must be replayed.
    RetrySaltMismatch,
    /// The epoch is in flight with different digits.
    DigitsMismatch,
    /// The digit vector is longer than [`MAX_TARGET_SUM_DIGITS`].
    DigitsTooLong,
    /// The epoch was bound earlier and is no longer the in-flight record.
    EpochConsumed,
    /// No record is in flight (nothing was bound).
    NothingBound,
    /// Some signers hold a persisted salt for this epoch and message and others do not; the
    /// epoch must be burned.
    RetrySaltUnavailable,
    /// An echo of a required peer is missing or duplicated.
    MissingEcho,
    /// A party index is not in `0..3`, or names the signer itself where a peer is required.
    InvalidParty,
    /// The latch was recovered without echo keys and can neither send nor check echoes.
    EchoKeysMissing,
    /// The tag of the echo claiming to come from `party` does not verify under the key
    /// shared with that party.
    EchoMacInvalid {
        party: usize,
    },
    /// A fresh epoch lies more than [`MAX_EPOCH_JUMP`] above the high-water mark.
    EpochJumpTooLarge,
    /// An earlier persist failed; this latch is unusable and a new one must be recovered
    /// from the log.
    WalPoisoned,
    /// A peer's echo differs from the local record: two views of one epoch exist.
    SplitView {
        party: usize,
    },
    /// A permit does not belong to the record being opened.
    PermitMismatch,
    Wal(WalError),
}

impl fmt::Display for BeltLatchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCapacity => f.write_str("invalid latch capacity"),
            Self::Exhausted => f.write_str("epoch space exhausted"),
            Self::EpochAlreadyBound => f.write_str("epoch already bound to another message"),
            Self::RetrySaltMismatch => f.write_str("retry must replay the persisted salt"),
            Self::DigitsMismatch => f.write_str("retry must replay the persisted digits"),
            Self::DigitsTooLong => f.write_str("digit vector exceeds the latch bound"),
            Self::EpochConsumed => f.write_str("epoch already consumed"),
            Self::NothingBound => f.write_str("no epoch is bound"),
            Self::RetrySaltUnavailable => {
                f.write_str("signers disagree on whether a salt is persisted; burn the epoch")
            }
            Self::MissingEcho => f.write_str("a required peer echo is missing or duplicated"),
            Self::InvalidParty => f.write_str("invalid party index"),
            Self::EchoKeysMissing => f.write_str("latch holds no echo keys"),
            Self::EchoMacInvalid { party } => {
                write!(f, "echo claiming party {party} fails authentication")
            }
            Self::EpochJumpTooLarge => f.write_str("epoch too far above the high-water mark"),
            Self::WalPoisoned => {
                f.write_str("a persist failed earlier; recover a new latch from the log")
            }
            Self::SplitView { party } => {
                write!(
                    f,
                    "split view: echo of party {party} differs from the local record"
                )
            }
            Self::PermitMismatch => f.write_str("open permit does not match the record"),
            Self::Wal(e) => write!(f, "write-ahead log failure: {e:?}"),
        }
    }
}

impl core::error::Error for BeltLatchError {}

/// Outcome of a successful [`BeltLatch::bind`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindOutcome {
    /// A new epoch was persisted.
    Fresh,
    /// The in-flight record already equals the request; nothing was written.
    Replay,
}

/// What a signer sends to one peer after binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BeltEcho {
    /// The sender.
    pub party: usize,
    /// The peer this echo is addressed to; the tag verifies for no other receiver.
    pub receiver: usize,
    pub epoch: u64,
    pub msg_digest: [u8; 32],
    pub retry_salt: [u8; 32],
    /// [`BeltLatchRecord::binding`], which also covers the digits.
    pub binding: [u8; 32],
    /// MAC over every field above under the key shared by `party` and `receiver`.
    pub tag: [u8; 32],
}

/// Derive the echo-MAC key of the pair `{a, b}` from secret material that exactly those two
/// parties hold. `context` is public and separates deployments (for example the public key).
/// The result is the same whichever of the two calls it, and is used only for echo tags.
pub fn derive_echo_mac_key(context: &[u8], a: usize, b: usize, pair_secrets: &[&[u8]]) -> [u8; 32] {
    let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
    let mut xof = Cshake256Xof::new(TAG_ECHO_KEY);
    let mut field = |bytes: &[u8]| {
        xof.absorb(&(bytes.len() as u64).to_be_bytes());
        xof.absorb(bytes);
    };
    field(context);
    field(&(lo as u64).to_be_bytes());
    field(&(hi as u64).to_be_bytes());
    for secret in pair_secrets {
        field(secret);
    }
    let mut key = [0u8; 32];
    xof.squeeze(&mut key);
    key
}

/// One signer's two pairwise echo-MAC keys. Not `Clone`; wiped on drop.
pub struct EchoMacKeys {
    party: usize,
    with_next: [u8; 32],
    with_prev: [u8; 32],
}

impl EchoMacKeys {
    /// `with_next` is the key `party` shares with `(party + 1) % 3`, `with_prev` the one it
    /// shares with `(party + 2) % 3`.
    pub fn new(
        party: usize,
        with_next: [u8; 32],
        with_prev: [u8; 32],
    ) -> Result<Self, BeltLatchError> {
        if party >= 3 {
            return Err(BeltLatchError::InvalidParty);
        }
        Ok(Self {
            party,
            with_next,
            with_prev,
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }

    fn key_for(&self, peer: usize) -> Result<&[u8; 32], BeltLatchError> {
        if peer == (self.party + 1) % 3 {
            Ok(&self.with_next)
        } else if peer == (self.party + 2) % 3 {
            Ok(&self.with_prev)
        } else {
            Err(BeltLatchError::InvalidParty)
        }
    }
}

impl fmt::Debug for EchoMacKeys {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "EchoMacKeys(party={}, [REDACTED])", self.party)
    }
}

impl Drop for EchoMacKeys {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.with_next);
        wipe_bytes32(&mut self.with_prev);
    }
}

/// Tag of an echo from `sender` to `receiver`. Every field has a fixed width, so the
/// concatenation is unambiguous; the key is absorbed first.
fn echo_tag(
    key: &[u8; 32],
    sender: usize,
    receiver: usize,
    epoch: u64,
    msg_digest: &[u8; 32],
    retry_salt: &[u8; 32],
    binding: &[u8; 32],
) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(TAG_ECHO_MAC);
    xof.absorb(key);
    xof.absorb(&(sender as u64).to_be_bytes());
    xof.absorb(&(receiver as u64).to_be_bytes());
    xof.absorb(&epoch.to_be_bytes());
    xof.absorb(msg_digest);
    xof.absorb(retry_salt);
    xof.absorb(binding);
    let mut tag = [0u8; 32];
    xof.squeeze(&mut tag);
    tag
}

/// Proof that one signer persisted a record and saw matching echoes from both peers.
/// Not `Clone`; constructible only by [`BeltLatch::verify_peer_echoes`].
#[derive(Debug, PartialEq, Eq)]
pub struct OpenPermit {
    party: usize,
    epoch: u64,
    binding: [u8; 32],
}

impl OpenPermit {
    pub fn party(&self) -> usize {
        self.party
    }

    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    pub fn binding(&self) -> &[u8; 32] {
        &self.binding
    }
}

/// Check that `permits` are one per party and all carry `record`'s binding.
pub fn permits_authorise(
    permits: &[OpenPermit; 3],
    record: &BeltLatchRecord,
) -> Result<(), BeltLatchError> {
    let binding = record.binding();
    for (party, permit) in permits.iter().enumerate() {
        if permit.party != party
            || permit.epoch != record.epoch
            || !ct_eq_bytes32(&permit.binding, &binding)
        {
            return Err(BeltLatchError::PermitMismatch);
        }
    }
    Ok(())
}

/// How a signer allocates leaves within the enrolled tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum BeltIndexingMode {
    /// Advance at most `MAX_EPOCH_JUMP` beyond the next wallet epoch.
    #[default]
    SequentialBounded,
    /// Use the consensus slot as the leaf index, burning every intervening leaf.
    SlotIndexed,
}

fn kernel_digits(bytes: &[u8]) -> qsag_verified::BeltLatchDigits {
    let mut padded = [0u8; MAX_TARGET_SUM_DIGITS];
    padded[..bytes.len()].copy_from_slice(bytes);
    qsag_verified::BeltLatchDigits {
        len: bytes.len() as u8,
        row0: padded[0..32].try_into().unwrap(),
        row1: padded[32..64].try_into().unwrap(),
        row2: padded[64..96].try_into().unwrap(),
        row3: padded[96..128].try_into().unwrap(),
    }
}

fn kernel_error(e: qsag_verified::BeltLatchKernelError) -> BeltLatchError {
    use qsag_verified::BeltLatchKernelError as E;
    match e {
        E::InvalidCapacity => BeltLatchError::InvalidCapacity,
        E::Exhausted => BeltLatchError::Exhausted,
        E::EpochAlreadyBound => BeltLatchError::EpochAlreadyBound,
        E::RetrySaltMismatch => BeltLatchError::RetrySaltMismatch,
        E::DigitsMismatch => BeltLatchError::DigitsMismatch,
        E::EpochConsumed => BeltLatchError::EpochConsumed,
        E::EpochJumpTooLarge => BeltLatchError::EpochJumpTooLarge,
        E::WalPoisoned | E::WalPersistFailed => BeltLatchError::WalPoisoned,
    }
}

/// One signer's latch (see the module documentation). Not `Clone`.
pub struct BeltLatch<W: DurableWal> {
    indexing_mode: BeltIndexingMode,
    wal: W,
    kernel: Option<BeltLatchKernel>,
    state: BeltLatchState,
    echo_keys: Option<EchoMacKeys>,
}

impl<W: DurableWal> fmt::Debug for BeltLatch<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BeltLatch")
            .field("indexing_mode", &self.indexing_mode)
            .field("next_epoch", &self.state.next_epoch)
            .field(
                "in_flight_epoch",
                &self.state.in_flight.as_ref().map(|r| r.epoch),
            )
            .field("party", &self.echo_keys.as_ref().map(EchoMacKeys::party))
            .field("wal_poisoned", &self.is_wal_poisoned())
            .finish()
    }
}

impl<W: DurableWal> BeltLatch<W> {
    /// Recover a latch without echo keys from `wal` (an unwritten log starts at epoch 0).
    /// It binds and replays, but cannot send or check echoes.
    pub fn recover(wal: W, capacity_log2: usize) -> Result<Self, BeltLatchError> {
        Self::recover_inner(
            wal,
            capacity_log2,
            None,
            BeltIndexingMode::SequentialBounded,
        )
    }

    /// Recover the latch of party `echo_keys.party()` from `wal`, able to exchange echoes.
    pub fn recover_with_echo_keys(
        wal: W,
        capacity_log2: usize,
        echo_keys: EchoMacKeys,
    ) -> Result<Self, BeltLatchError> {
        Self::recover_inner(
            wal,
            capacity_log2,
            Some(echo_keys),
            BeltIndexingMode::SequentialBounded,
        )
    }

    /// Recover the highest bound consensus slot from the durable high-water mark.
    pub fn recover_slot_indexed(wal: W, capacity_log2: usize) -> Result<Self, BeltLatchError> {
        Self::recover_inner(wal, capacity_log2, None, BeltIndexingMode::SlotIndexed)
    }

    /// Recover a consensus signer with authenticated peer echoes.
    pub fn recover_slot_indexed_with_echo_keys(
        wal: W,
        capacity_log2: usize,
        echo_keys: EchoMacKeys,
    ) -> Result<Self, BeltLatchError> {
        Self::recover_inner(
            wal,
            capacity_log2,
            Some(echo_keys),
            BeltIndexingMode::SlotIndexed,
        )
    }

    pub const fn indexing_mode(&self) -> BeltIndexingMode {
        self.indexing_mode
    }

    pub fn last_signed_slot(&self) -> Option<u64> {
        self.state.next_epoch.checked_sub(1)
    }

    /// Reserve one leaf exactly once. An identical crash replay goes through `bind`.
    pub fn bind_consensus_slot(
        &mut self,
        slot: u64,
        msg_digest: &[u8; 32],
        retry_salt: &[u8; 32],
        target_sum_digits: &[u8],
    ) -> Result<u64, BeltLatchError> {
        self.ensure_usable()?;
        if target_sum_digits.len() > MAX_TARGET_SUM_DIGITS {
            return Err(BeltLatchError::DigitsTooLong);
        }
        let capacity_limit = self
            .kernel
            .as_ref()
            .ok_or(BeltLatchError::WalPoisoned)?
            .capacity_limit();
        if slot >= capacity_limit {
            return Err(BeltLatchError::Exhausted);
        }
        if self.latched_salt(slot, msg_digest)?.is_some() {
            return Err(BeltLatchError::EpochConsumed);
        }
        self.bind(slot, msg_digest, retry_salt, target_sum_digits)?;
        Ok(slot)
    }

    fn recover_inner(
        wal: W,
        capacity_log2: usize,
        echo_keys: Option<EchoMacKeys>,
        indexing_mode: BeltIndexingMode,
    ) -> Result<Self, BeltLatchError> {
        if capacity_log2 == 0 || capacity_log2 > 62 {
            return Err(BeltLatchError::InvalidCapacity);
        }
        let capacity = 1u64 << capacity_log2;
        let state = wal.load().map_err(BeltLatchError::Wal)?.unwrap_or_default();
        let kernel = if state.next_epoch == 0 && state.in_flight.is_none() {
            BeltLatchKernel::new_empty(capacity).map_err(kernel_error)?
        } else {
            let current = state.in_flight.as_ref();
            if current.is_some_and(|r| r.target_sum_digits.len() > MAX_TARGET_SUM_DIGITS) {
                return Err(BeltLatchError::DigitsTooLong);
            }
            let record = qsag_verified::BeltLatchKernelRecord {
                epoch: current.map_or(0, |r| r.epoch),
                msg_digest: current.map_or([0; 32], |r| r.msg_digest),
                retry_salt: current.map_or([0; 32], |r| r.retry_salt),
                digits: kernel_digits(current.map_or(&[], |r| &r.target_sum_digits)),
            };
            BeltLatchKernel::recover(capacity, state.next_epoch, current.is_some(), record)
                .map_err(kernel_error)?
        };
        Ok(Self {
            indexing_mode,
            wal,
            kernel: Some(kernel),
            state,
            echo_keys,
        })
    }

    /// Whether a persist has failed on this latch (see the module documentation).
    pub fn is_wal_poisoned(&self) -> bool {
        self.kernel
            .as_ref()
            .is_none_or(BeltLatchKernel::is_wal_poisoned)
    }

    fn ensure_usable(&self) -> Result<(), BeltLatchError> {
        if self.is_wal_poisoned() {
            Err(BeltLatchError::WalPoisoned)
        } else {
            Ok(())
        }
    }

    pub fn next_epoch(&self) -> u64 {
        self.state.next_epoch
    }

    pub fn in_flight(&self) -> Option<&BeltLatchRecord> {
        self.state.in_flight.as_ref()
    }

    /// Give the log back (for a simulated restart in tests, or a controlled shutdown).
    pub fn into_wal(self) -> W {
        self.wal
    }

    pub fn wal(&self) -> &W {
        &self.wal
    }

    pub fn wal_mut(&mut self) -> &mut W {
        &mut self.wal
    }

    /// The salt a retry of `(epoch, msg_digest)` must replay, if this signer persisted one.
    /// `Ok(None)` means the epoch was never bound here, lies inside the epoch window, and a
    /// fresh salt may be drawn for it.
    pub fn latched_salt(
        &self,
        epoch: u64,
        msg_digest: &[u8; 32],
    ) -> Result<Option<[u8; 32]>, BeltLatchError> {
        self.ensure_usable()?;
        let kernel = self.kernel.as_ref().ok_or(BeltLatchError::WalPoisoned)?;
        if kernel.has_in_flight()
            && let Some(rec) = &self.state.in_flight
            && rec.epoch == epoch
        {
            return if ct_eq_bytes32(&rec.msg_digest, msg_digest) {
                Ok(Some(rec.retry_salt))
            } else {
                Err(BeltLatchError::EpochAlreadyBound)
            };
        }
        if epoch < kernel.next_epoch() {
            return Err(BeltLatchError::EpochConsumed);
        }
        if epoch >= kernel.capacity_limit() {
            return Err(BeltLatchError::Exhausted);
        }
        // `epoch >= next_epoch` here, and `next_epoch <= 2^62`, so the sum cannot overflow.
        if self.indexing_mode == BeltIndexingMode::SequentialBounded
            && epoch > kernel.next_epoch() + MAX_EPOCH_JUMP
        {
            return Err(BeltLatchError::EpochJumpTooLarge);
        }
        Ok(None)
    }

    /// Persist the binding of `epoch`, or confirm that the identical binding is in flight.
    /// Skipped epochs burn their leaf indices. Only sequential wallets enforce
    /// [`MAX_EPOCH_JUMP`]. A failed persist poisons the latch.
    pub fn bind(
        &mut self,
        epoch: u64,
        msg_digest: &[u8; 32],
        retry_salt: &[u8; 32],
        target_sum_digits: &[u8],
    ) -> Result<BindOutcome, BeltLatchError> {
        let replay = self.latched_salt(epoch, msg_digest)?;
        if target_sum_digits.len() > MAX_TARGET_SUM_DIGITS {
            // Preserve poison and replay error precedence without truncating the kernel's digit input.
            if let Some(salt) = replay {
                return Err(if !ct_eq_bytes32(&salt, retry_salt) {
                    BeltLatchError::RetrySaltMismatch
                } else {
                    BeltLatchError::DigitsMismatch
                });
            }
            return Err(BeltLatchError::DigitsTooLong);
        }
        let kernel = self.kernel.take().ok_or(BeltLatchError::WalPoisoned)?;
        let prev_capacity = kernel.capacity_limit();
        let prev_next_epoch = kernel.next_epoch();
        let prev_has_in_flight = kernel.has_in_flight();
        let prev_in_flight = kernel.in_flight();
        let kernel = if self.indexing_mode == BeltIndexingMode::SlotIndexed
            && !kernel.is_wal_poisoned()
            && epoch > prev_next_epoch
            && epoch < prev_capacity
        {
            BeltLatchKernel::recover(prev_capacity, epoch, prev_has_in_flight, prev_in_flight)
                .map_err(kernel_error)?
        } else {
            kernel
        };
        let next = replay.is_none().then(|| BeltLatchState {
            next_epoch: epoch + 1,
            in_flight: Some(BeltLatchRecord {
                epoch,
                msg_digest: *msg_digest,
                retry_salt: *retry_salt,
                target_sum_digits: target_sum_digits.to_vec(),
            }),
        });
        let persisted = match &next {
            Some(state) => self.wal.sync_persist(state),
            None => Ok(()),
        };
        let (kernel, outcome) = kernel.bind(qsag_verified::BeltLatchBindRequest {
            epoch,
            msg_digest: *msg_digest,
            retry_salt: *retry_salt,
            digits: kernel_digits(target_sum_digits),
            persist_ok: persisted.is_ok(),
        });
        self.kernel = Some(kernel);
        persisted.map_err(BeltLatchError::Wal)?;
        match outcome.map_err(kernel_error)? {
            qsag_verified::BeltLatchBindOutcome::Fresh => {
                self.state = next.expect("fresh binding persisted");
                Ok(BindOutcome::Fresh)
            }
            qsag_verified::BeltLatchBindOutcome::Replay => Ok(BindOutcome::Replay),
        }
    }

    /// The echo of the in-flight record addressed to peer `receiver`, sent after
    /// [`Self::bind`]. Each of the two peers gets its own echo.
    pub fn echo_for(&self, receiver: usize) -> Result<BeltEcho, BeltLatchError> {
        self.ensure_usable()?;
        let keys = self
            .echo_keys
            .as_ref()
            .ok_or(BeltLatchError::EchoKeysMissing)?;
        let key = keys.key_for(receiver)?;
        let rec = self
            .state
            .in_flight
            .as_ref()
            .ok_or(BeltLatchError::NothingBound)?;
        let binding = rec.binding();
        Ok(BeltEcho {
            party: keys.party,
            receiver,
            epoch: rec.epoch,
            msg_digest: rec.msg_digest,
            retry_salt: rec.retry_salt,
            binding,
            tag: echo_tag(
                key,
                keys.party,
                receiver,
                rec.epoch,
                &rec.msg_digest,
                &rec.retry_salt,
                &binding,
            ),
        })
    }

    /// Authenticate the echoes that both other signers addressed to this one, compare them
    /// with the in-flight record and, if they all agree, return the permit that authorises
    /// opening this epoch's chain shares. Echoes addressed to other receivers are ignored.
    pub fn verify_peer_echoes(&self, echoes: &[BeltEcho]) -> Result<OpenPermit, BeltLatchError> {
        self.ensure_usable()?;
        let keys = self
            .echo_keys
            .as_ref()
            .ok_or(BeltLatchError::EchoKeysMissing)?;
        let own_party = keys.party;
        let rec = self
            .state
            .in_flight
            .as_ref()
            .ok_or(BeltLatchError::NothingBound)?;
        let binding = rec.binding();
        for peer in (0..3).filter(|p| *p != own_party) {
            let mut seen = echoes
                .iter()
                .filter(|e| e.party == peer && e.receiver == own_party);
            let (Some(echo), None) = (seen.next(), seen.next()) else {
                return Err(BeltLatchError::MissingEcho);
            };
            // Authenticate what the echo claims before comparing it with the local record,
            // so a split view is only ever attributed to a party that vouched for it.
            let want = echo_tag(
                keys.key_for(peer)?,
                peer,
                own_party,
                echo.epoch,
                &echo.msg_digest,
                &echo.retry_salt,
                &echo.binding,
            );
            if !ct_eq_bytes32(&want, &echo.tag) {
                return Err(BeltLatchError::EchoMacInvalid { party: peer });
            }
            let same = echo.epoch == rec.epoch
                && ct_eq_bytes32(&echo.msg_digest, &rec.msg_digest)
                && ct_eq_bytes32(&echo.retry_salt, &rec.retry_salt)
                && ct_eq_bytes32(&echo.binding, &binding);
            if !same {
                return Err(BeltLatchError::SplitView { party: peer });
            }
        }
        self.wal.authorize_open(rec).map_err(BeltLatchError::Wal)?;
        Ok(OpenPermit {
            party: own_party,
            epoch: rec.epoch,
            binding,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DIGITS_A: [u8; 4] = [3, 0, 2, 1];
    const DIGITS_B: [u8; 4] = [1, 2, 0, 3];

    fn latch() -> BeltLatch<MemoryWal> {
        BeltLatch::recover(MemoryWal::new(), 20).unwrap()
    }

    /// Test key of the pair `{a, b}`; the three pairs get three different keys.
    fn pair_key(a: usize, b: usize) -> [u8; 32] {
        derive_echo_mac_key(b"belt-latch-tests", a, b, &[&[0x50 + (a + b) as u8; 32]])
    }

    fn keys_of(party: usize) -> EchoMacKeys {
        EchoMacKeys::new(
            party,
            pair_key(party, (party + 1) % 3),
            pair_key(party, (party + 2) % 3),
        )
        .unwrap()
    }

    fn latch_of(party: usize) -> BeltLatch<MemoryWal> {
        BeltLatch::recover_with_echo_keys(MemoryWal::new(), 20, keys_of(party)).unwrap()
    }

    /// Every party's echo to each of its two peers.
    fn all_echoes(latches: &[BeltLatch<MemoryWal>]) -> Vec<BeltEcho> {
        let mut out = Vec::new();
        for l in latches {
            let own = l.echo_keys.as_ref().unwrap().party();
            for receiver in (0..3).filter(|r| *r != own) {
                out.push(l.echo_for(receiver).unwrap());
            }
        }
        out
    }

    #[test]
    fn tooth_consensus_skips_reopen_and_echo() {
        let mut latches: Vec<_> = (0..3)
            .map(|p| {
                BeltLatch::recover_slot_indexed_with_echo_keys(MemoryWal::new(), 14, keys_of(p))
                    .unwrap()
            })
            .collect();
        for slot in [0, 500, 12_345] {
            for l in &mut latches {
                assert_eq!(
                    l.bind_consensus_slot(slot, &[7; 32], &[8; 32], &[1]),
                    Ok(slot)
                );
            }
            latches = latches
                .into_iter()
                .enumerate()
                .map(|(p, l)| {
                    BeltLatch::recover_slot_indexed_with_echo_keys(l.into_wal(), 14, keys_of(p))
                        .unwrap()
                })
                .collect();
            let echoes = all_echoes(&latches);
            for l in &mut latches {
                assert_eq!(l.verify_peer_echoes(&echoes).unwrap().epoch(), slot);
                assert_eq!(
                    l.bind_consensus_slot(slot, &[1; 32], &[8; 32], &[1]),
                    Err(BeltLatchError::EpochAlreadyBound)
                );
                assert_eq!(
                    l.bind_consensus_slot(slot, &[7; 32], &[8; 32], &[1]),
                    Err(BeltLatchError::EpochConsumed)
                );
                assert_eq!(
                    l.bind(slot, &[7; 32], &[8; 32], &[1]),
                    Ok(BindOutcome::Replay)
                );
            }
        }
        assert_eq!(
            latches[0].bind_consensus_slot(501, &[7; 32], &[8; 32], &[1]),
            Err(BeltLatchError::EpochConsumed)
        );
    }

    #[test]
    fn state_encoding_round_trips_and_rejects_every_corruption() {
        let state = BeltLatchState {
            next_epoch: 8,
            in_flight: Some(BeltLatchRecord {
                epoch: 7,
                msg_digest: [1; 32],
                retry_salt: [2; 32],
                target_sum_digits: DIGITS_A.to_vec(),
            }),
        };
        let raw = state.to_bytes();
        assert_eq!(BeltLatchState::from_bytes(&raw), Some(state));
        let empty = BeltLatchState::default();
        assert_eq!(BeltLatchState::from_bytes(&empty.to_bytes()), Some(empty));
        for i in 0..raw.len() {
            let mut bad = raw.clone();
            bad[i] ^= 0x01;
            assert_eq!(BeltLatchState::from_bytes(&bad), None, "byte {i}");
        }
        assert_eq!(BeltLatchState::from_bytes(&raw[..raw.len() - 1]), None);
        let mut longer = raw;
        longer.push(0);
        assert_eq!(BeltLatchState::from_bytes(&longer), None);
    }

    #[test]
    fn digit_vectors_beyond_the_kernel_bound_are_never_bound_or_decoded() {
        let at_bound = [1u8; MAX_TARGET_SUM_DIGITS];
        let over = [1u8; MAX_TARGET_SUM_DIGITS + 1];
        let mut l = latch();
        assert_eq!(
            l.bind(0, &[1; 32], &[9; 32], &over),
            Err(BeltLatchError::DigitsTooLong)
        );
        assert!(!l.is_wal_poisoned());
        assert_eq!(l.wal_mut().persist_count(), 0);
        assert_eq!((l.in_flight(), l.next_epoch()), (None, 0));
        assert_eq!(
            l.bind(0, &[1; 32], &[9; 32], &at_bound),
            Ok(BindOutcome::Fresh)
        );
        // A replay with an over-long vector differs from the stored one.
        assert_eq!(
            l.bind(0, &[1; 32], &[9; 32], &over),
            Err(BeltLatchError::DigitsMismatch)
        );

        let state = |digits: &[u8]| BeltLatchState {
            next_epoch: 1,
            in_flight: Some(BeltLatchRecord {
                epoch: 0,
                msg_digest: [1; 32],
                retry_salt: [2; 32],
                target_sum_digits: digits.to_vec(),
            }),
        };
        assert_eq!(
            BeltLatchState::from_bytes(&state(&at_bound).to_bytes()),
            Some(state(&at_bound))
        );
        assert_eq!(BeltLatchState::from_bytes(&state(&over).to_bytes()), None);
    }

    #[test]
    fn failed_forward_slot_write_preserves_the_durable_epoch() {
        let mut latch = BeltLatch::recover_slot_indexed(MemoryWal::new(), 20).unwrap();
        latch.bind(3, &[1; 32], &[2; 32], &DIGITS_A).unwrap();
        latch.wal_mut().fail_next_persist();
        assert_eq!(
            latch.bind(100_000, &[3; 32], &[4; 32], &DIGITS_B),
            Err(BeltLatchError::Wal(WalError::Io))
        );
        assert!(latch.kernel.as_ref().unwrap().is_wal_poisoned());
        assert_eq!(latch.next_epoch(), 4);
        let recovered = BeltLatch::recover_slot_indexed(latch.into_wal(), 20).unwrap();
        assert_eq!(recovered.in_flight().unwrap().epoch, 3);
        assert_eq!(recovered.next_epoch(), 4);
    }

    #[test]
    fn a_failed_persist_binds_nothing_and_poisons_the_latch_until_recovery() {
        let mut l = latch_of(0);
        assert_eq!(l.echo_for(1), Err(BeltLatchError::NothingBound));
        l.wal_mut().fail_next_persist();
        assert_eq!(
            l.bind(0, &[1; 32], &[9; 32], &DIGITS_A),
            Err(BeltLatchError::Wal(WalError::Io))
        );
        assert!(l.kernel.as_ref().unwrap().is_wal_poisoned());
        assert!(l.is_wal_poisoned());
        assert_eq!(l.in_flight(), None);
        assert_eq!(l.next_epoch(), 0);

        // The log would accept the next write, but the latch no longer offers one: every
        // method on the way to an opening is refused.
        assert_eq!(
            l.bind(0, &[1; 32], &[9; 32], &DIGITS_A),
            Err(BeltLatchError::WalPoisoned)
        );
        assert_eq!(
            l.bind(1, &[2; 32], &[8; 32], &DIGITS_B),
            Err(BeltLatchError::WalPoisoned)
        );
        assert_eq!(
            l.latched_salt(0, &[1; 32]),
            Err(BeltLatchError::WalPoisoned)
        );
        assert_eq!(l.echo_for(1), Err(BeltLatchError::WalPoisoned));
        assert_eq!(l.verify_peer_echoes(&[]), Err(BeltLatchError::WalPoisoned));
        assert_eq!(l.wal_mut().persist_count(), 0);

        // Recovery from the log: nothing was bound, and the new latch works.
        let mut l = BeltLatch::recover_with_echo_keys(l.into_wal(), 20, keys_of(0)).unwrap();
        assert!(!l.is_wal_poisoned());
        assert_eq!(l.in_flight(), None);
        assert_eq!(l.next_epoch(), 0);
        assert_eq!(
            l.bind(0, &[1; 32], &[9; 32], &DIGITS_A),
            Ok(BindOutcome::Fresh)
        );
        assert_eq!(l.wal_mut().persist_count(), 1);
        assert!(l.echo_for(1).is_ok());
    }

    /// A latch that already holds a record keeps it out of reach once a later persist fails.
    #[test]
    fn poison_also_blocks_the_record_that_was_already_in_flight() {
        let mut latches = [latch_of(0), latch_of(1), latch_of(2)];
        for l in &mut latches {
            l.bind(0, &[1; 32], &[9; 32], &DIGITS_A).unwrap();
        }
        let echoes = all_echoes(&latches);
        assert!(latches[0].verify_peer_echoes(&echoes).is_ok());
        latches[0].wal_mut().fail_next_persist();
        assert_eq!(
            latches[0].bind(1, &[2; 32], &[8; 32], &DIGITS_B),
            Err(BeltLatchError::Wal(WalError::Io))
        );
        assert_eq!(
            latches[0].verify_peer_echoes(&echoes),
            Err(BeltLatchError::WalPoisoned)
        );
        assert_eq!(latches[0].echo_for(1), Err(BeltLatchError::WalPoisoned));
        assert_eq!(
            latches[0].bind(0, &[1; 32], &[9; 32], &DIGITS_A),
            Err(BeltLatchError::WalPoisoned)
        );
    }

    #[test]
    fn a_fresh_bind_is_limited_to_the_epoch_window() {
        let mut l = latch();
        let capacity = 1u64 << 20;
        // One request for the last leaf of a fresh key is refused and consumes nothing.
        assert_eq!(
            l.bind(capacity - 1, &[1; 32], &[9; 32], &DIGITS_A),
            Err(BeltLatchError::EpochJumpTooLarge)
        );
        assert_eq!(
            l.latched_salt(capacity - 1, &[1; 32]),
            Err(BeltLatchError::EpochJumpTooLarge)
        );
        assert_eq!(
            l.bind(MAX_EPOCH_JUMP + 1, &[1; 32], &[9; 32], &DIGITS_A),
            Err(BeltLatchError::EpochJumpTooLarge)
        );
        assert_eq!(l.next_epoch(), 0);
        assert_eq!(l.in_flight(), None);
        assert_eq!(l.wal_mut().persist_count(), 0);

        // A jump of exactly the window is accepted, and the window moves with the mark.
        assert_eq!(
            l.bind(MAX_EPOCH_JUMP, &[1; 32], &[9; 32], &DIGITS_A),
            Ok(BindOutcome::Fresh)
        );
        let next = l.next_epoch();
        assert_eq!(next, MAX_EPOCH_JUMP + 1);
        assert_eq!(
            l.bind(next + MAX_EPOCH_JUMP + 1, &[2; 32], &[8; 32], &DIGITS_B),
            Err(BeltLatchError::EpochJumpTooLarge)
        );
        assert_eq!(l.next_epoch(), next);
        // The in-flight epoch still replays; the window applies to fresh epochs only.
        assert_eq!(
            l.bind(MAX_EPOCH_JUMP, &[1; 32], &[9; 32], &DIGITS_A),
            Ok(BindOutcome::Replay)
        );
        assert_eq!(
            l.bind(next + MAX_EPOCH_JUMP, &[2; 32], &[8; 32], &DIGITS_B),
            Ok(BindOutcome::Fresh)
        );
    }

    #[test]
    fn crash_replay_is_idempotent_and_never_re_rolls_the_salt() {
        let mut l = latch();
        assert_eq!(
            l.bind(5, &[1; 32], &[9; 32], &DIGITS_A),
            Ok(BindOutcome::Fresh)
        );
        assert_eq!(l.next_epoch(), 6);

        // Crash: only the log survives.
        let wal = l.into_wal();
        let mut l = BeltLatch::recover(wal, 20).unwrap();
        assert_eq!(l.next_epoch(), 6);
        assert_eq!(l.latched_salt(5, &[1; 32]), Ok(Some([9; 32])));

        // Same request: replay, with no further write.
        let before = l.wal_mut().persist_count();
        assert_eq!(
            l.bind(5, &[1; 32], &[9; 32], &DIGITS_A),
            Ok(BindOutcome::Replay)
        );
        assert_eq!(l.wal_mut().persist_count(), before);

        // Any change on the latched epoch is refused.
        assert_eq!(
            l.bind(5, &[2; 32], &[9; 32], &DIGITS_A),
            Err(BeltLatchError::EpochAlreadyBound)
        );
        assert_eq!(
            l.latched_salt(5, &[2; 32]),
            Err(BeltLatchError::EpochAlreadyBound)
        );
        assert_eq!(
            l.bind(5, &[1; 32], &[8; 32], &DIGITS_A),
            Err(BeltLatchError::RetrySaltMismatch)
        );
        assert_eq!(
            l.bind(5, &[1; 32], &[9; 32], &DIGITS_B),
            Err(BeltLatchError::DigitsMismatch)
        );

        // Epochs below the high-water mark that are not in flight are gone for good,
        // including the ones skipped on the way to epoch 5.
        for burned in 0..5 {
            assert_eq!(
                l.bind(burned, &[1; 32], &[9; 32], &DIGITS_A),
                Err(BeltLatchError::EpochConsumed)
            );
        }
        // Moving on consumes epoch 5 as well, across another crash.
        assert_eq!(
            l.bind(6, &[3; 32], &[7; 32], &DIGITS_B),
            Ok(BindOutcome::Fresh)
        );
        let mut l = BeltLatch::recover(l.into_wal(), 20).unwrap();
        assert_eq!(
            l.bind(5, &[1; 32], &[9; 32], &DIGITS_A),
            Err(BeltLatchError::EpochConsumed)
        );
        assert_eq!(
            l.bind(6, &[3; 32], &[7; 32], &DIGITS_B),
            Ok(BindOutcome::Replay)
        );
    }

    #[test]
    fn capacity_is_enforced() {
        assert_eq!(
            BeltLatch::recover(MemoryWal::new(), 0).unwrap_err(),
            BeltLatchError::InvalidCapacity
        );
        let mut l = BeltLatch::recover(MemoryWal::new(), 2).unwrap();
        assert_eq!(
            l.bind(3, &[1; 32], &[9; 32], &DIGITS_A),
            Ok(BindOutcome::Fresh)
        );
        assert_eq!(
            l.bind(4, &[1; 32], &[9; 32], &DIGITS_A),
            Err(BeltLatchError::Exhausted)
        );
    }

    #[test]
    fn matching_echoes_from_both_peers_yield_permits_that_authorise_only_that_record() {
        let mut latches = [latch_of(0), latch_of(1), latch_of(2)];
        for l in &mut latches {
            l.bind(2, &[1; 32], &[9; 32], &DIGITS_A).unwrap();
        }
        let echoes = all_echoes(&latches);
        let permits: [OpenPermit; 3] =
            core::array::from_fn(|p| latches[p].verify_peer_echoes(&echoes).unwrap());
        let record = latches[0].in_flight().unwrap().clone();
        assert_eq!(permits_authorise(&permits, &record), Ok(()));
        let mut other = record.clone();
        other.target_sum_digits = DIGITS_B.to_vec();
        assert_eq!(
            permits_authorise(&permits, &other),
            Err(BeltLatchError::PermitMismatch)
        );

        // One echo is not enough, and neither is the same peer twice.
        let to_0_from_1 = latches[1].echo_for(0).unwrap();
        let to_0_from_2 = latches[2].echo_for(0).unwrap();
        assert_eq!(
            latches[0].verify_peer_echoes(&[to_0_from_1]),
            Err(BeltLatchError::MissingEcho)
        );
        assert_eq!(
            latches[0].verify_peer_echoes(&[to_0_from_1, to_0_from_1, to_0_from_2]),
            Err(BeltLatchError::MissingEcho)
        );
        // An echo addressed to someone else does not count as one addressed to party 0.
        assert_eq!(
            latches[0].verify_peer_echoes(&[to_0_from_1, latches[2].echo_for(1).unwrap()]),
            Err(BeltLatchError::MissingEcho)
        );

        // A latch without keys binds but takes no part in the echo exchange, and a party
        // cannot address itself or an index outside the signer set.
        let mut bare = latch();
        bare.bind(2, &[1; 32], &[9; 32], &DIGITS_A).unwrap();
        assert_eq!(bare.echo_for(1), Err(BeltLatchError::EchoKeysMissing));
        assert_eq!(
            bare.verify_peer_echoes(&echoes),
            Err(BeltLatchError::EchoKeysMissing)
        );
        assert_eq!(latches[0].echo_for(0), Err(BeltLatchError::InvalidParty));
        assert_eq!(latches[0].echo_for(3), Err(BeltLatchError::InvalidParty));
        assert_eq!(
            EchoMacKeys::new(3, [0; 32], [0; 32]).unwrap_err(),
            BeltLatchError::InvalidParty
        );
    }

    #[test]
    fn pair_keys_are_symmetric_and_distinct_per_pair_and_context() {
        let secret: &[&[u8]] = &[&[7u8; 16], &[8u8; 16]];
        let k01 = derive_echo_mac_key(b"ctx", 0, 1, secret);
        assert_eq!(k01, derive_echo_mac_key(b"ctx", 1, 0, secret));
        assert_ne!(k01, derive_echo_mac_key(b"ctx", 0, 2, secret));
        assert_ne!(k01, derive_echo_mac_key(b"other", 0, 1, secret));
        assert_ne!(
            k01,
            derive_echo_mac_key(b"ctx", 0, 1, &[&[7u8; 16], &[9u8; 16]])
        );
        // Field boundaries are part of the input.
        assert_ne!(
            derive_echo_mac_key(b"ctx", 0, 1, &[&[1, 2], &[3]]),
            derive_echo_mac_key(b"ctx", 0, 1, &[&[1], &[2, 3]])
        );
    }

    /// Parties 0 and 1 are honest and bound different records for one epoch; party 2 is
    /// corrupted and relays between them. To get party 0 to open, party 2 needs an echo
    /// "from party 1" that matches party 0's record. It knows every public field of that
    /// echo and holds the keys of the pairs {2,0} and {1,2}, but not the key of {0,1}.
    #[test]
    fn a_forged_echo_in_an_honest_partys_name_is_rejected() {
        let (md_a, md_b) = ([0xAA; 32], [0xBB; 32]);
        let salt = [9; 32];
        let mut p0 = latch_of(0);
        let mut p1 = latch_of(1);
        p0.bind(4, &md_a, &salt, &DIGITS_A).unwrap();
        p1.bind(4, &md_b, &salt, &DIGITS_B).unwrap();
        // Party 2 binds party 0's view, so its own echo to party 0 is genuine and matches.
        let mut p2 = latch_of(2);
        p2.bind(4, &md_a, &salt, &DIGITS_A).unwrap();
        let from_2 = p2.echo_for(0).unwrap();
        let rec = p0.in_flight().unwrap().clone();
        let corrupt = keys_of(2);

        let forge = |tag: [u8; 32]| BeltEcho {
            party: 1,
            receiver: 0,
            epoch: rec.epoch,
            msg_digest: rec.msg_digest,
            retry_salt: rec.retry_salt,
            binding: rec.binding(),
            tag,
        };
        let tag_under = |key: &[u8; 32], sender: usize, receiver: usize| {
            echo_tag(
                key,
                sender,
                receiver,
                rec.epoch,
                &rec.msg_digest,
                &rec.retry_salt,
                &rec.binding(),
            )
        };
        let attempts = [
            // The right message under each key the corrupted party holds.
            forge(tag_under(corrupt.key_for(0).unwrap(), 1, 0)),
            forge(tag_under(corrupt.key_for(1).unwrap(), 1, 0)),
            // Its own valid tag for party 0, relabelled as coming from party 1.
            forge(from_2.tag),
            // The tag party 0 itself would send to party 1 for this record, reflected.
            forge(p0.echo_for(1).unwrap().tag),
            forge([0; 32]),
        ];
        for (i, forged) in attempts.into_iter().enumerate() {
            assert_eq!(
                p0.verify_peer_echoes(&[forged, from_2]),
                Err(BeltLatchError::EchoMacInvalid { party: 1 }),
                "attempt {i}"
            );
        }
        // Control: the same fields with the tag only the pair {0,1} can compute are accepted,
        // so the rejections above are due to the tag and nothing else.
        let genuine = forge(tag_under(&pair_key(0, 1), 1, 0));
        assert!(p0.verify_peer_echoes(&[genuine, from_2]).is_ok());

        // Party 1's real echo is authentic and exposes the split.
        assert_eq!(
            p0.verify_peer_echoes(&[p1.echo_for(0).unwrap(), from_2]),
            Err(BeltLatchError::SplitView { party: 1 })
        );
        // A genuine echo redirected to another receiver, or with a field changed after it
        // was tagged, fails authentication as well.
        let mut q1 = latch_of(1);
        q1.bind(4, &md_a, &salt, &DIGITS_A).unwrap();
        let redirected = BeltEcho {
            receiver: 0,
            ..q1.echo_for(2).unwrap()
        };
        assert_eq!(
            p0.verify_peer_echoes(&[redirected, from_2]),
            Err(BeltLatchError::EchoMacInvalid { party: 1 })
        );
        let honest = q1.echo_for(0).unwrap();
        assert!(p0.verify_peer_echoes(&[honest, from_2]).is_ok());
        for field in 0..4 {
            let mut bent = honest;
            match field {
                0 => bent.epoch ^= 1,
                1 => bent.msg_digest[0] ^= 1,
                2 => bent.retry_salt[0] ^= 1,
                _ => bent.binding[0] ^= 1,
            }
            assert_eq!(
                p0.verify_peer_echoes(&[bent, from_2]),
                Err(BeltLatchError::EchoMacInvalid { party: 1 }),
                "field {field}"
            );
        }
    }

    /// Party 2 is corrupted and shows party 0 one message and party 1 another for the same
    /// epoch. Each honest latch binds its own view, and the echo exchange between the two
    /// honest parties stops both before a permit exists.
    #[test]
    fn split_view_equivocation_is_rejected_by_both_honest_parties() {
        let (md_a, md_b) = ([0xAA; 32], [0xBB; 32]);
        let salt = [9; 32];
        let mut p0 = latch_of(0);
        let mut p1 = latch_of(1);
        assert_eq!(p0.bind(4, &md_a, &salt, &DIGITS_A), Ok(BindOutcome::Fresh));
        assert_eq!(p1.bind(4, &md_b, &salt, &DIGITS_B), Ok(BindOutcome::Fresh));
        // The corrupted party tells each honest party what it wants to hear, with valid tags:
        // it holds a pair key with each of them.
        let mut liar_a = latch_of(2);
        let mut liar_b = latch_of(2);
        liar_a.bind(4, &md_a, &salt, &DIGITS_A).unwrap();
        liar_b.bind(4, &md_b, &salt, &DIGITS_B).unwrap();
        let lie_to_0 = liar_a.echo_for(0).unwrap();
        let lie_to_1 = liar_b.echo_for(1).unwrap();
        assert_eq!(
            p0.verify_peer_echoes(&[p1.echo_for(0).unwrap(), lie_to_0]),
            Err(BeltLatchError::SplitView { party: 1 })
        );
        assert_eq!(
            p1.verify_peer_echoes(&[p0.echo_for(1).unwrap(), lie_to_1]),
            Err(BeltLatchError::SplitView { party: 0 })
        );

        // Same message but different salts (hence different digits) is a split view too.
        let mut q0 = latch_of(0);
        let mut q1 = latch_of(1);
        let mut q2 = latch_of(2);
        q0.bind(4, &md_a, &[1; 32], &DIGITS_A).unwrap();
        q1.bind(4, &md_a, &[2; 32], &DIGITS_B).unwrap();
        q2.bind(4, &md_a, &[1; 32], &DIGITS_A).unwrap();
        assert_eq!(
            q0.verify_peer_echoes(&[q1.echo_for(0).unwrap(), q2.echo_for(0).unwrap()]),
            Err(BeltLatchError::SplitView { party: 1 })
        );
        // A peer that binds the same message and salt but other digits differs only in the
        // binding, and is caught as well.
        let mut r1 = latch_of(1);
        r1.bind(4, &md_a, &[1; 32], &DIGITS_B).unwrap();
        assert_eq!(
            q0.verify_peer_echoes(&[r1.echo_for(0).unwrap(), q2.echo_for(0).unwrap()]),
            Err(BeltLatchError::SplitView { party: 1 })
        );
        // The honest parties stay bound: neither can be talked into the other message.
        assert_eq!(
            p0.bind(4, &md_b, &salt, &DIGITS_B),
            Err(BeltLatchError::EpochAlreadyBound)
        );
    }

    #[test]
    fn empty_memory_wal_clones_for_batch_init_while_active_memory_wal_clone_panics() {
        let fresh = alloc::vec![MemoryWal::new(); 3];
        assert_eq!(fresh.len(), 3);
    }

    #[test]
    #[should_panic(expected = "MemoryWal: cloning an active volatile WAL authority is forbidden")]
    fn cloning_persisted_memory_wal_panics() {
        let mut l = latch();
        l.bind(0, &[1; 32], &[9; 32], &DIGITS_A).unwrap();
        let wal = l.into_wal();
        let _forked = wal.clone();
    }

    #[test]
    #[should_panic(expected = "MemoryWal: cloning an active volatile WAL authority is forbidden")]
    fn cloning_armed_fail_next_memory_wal_panics() {
        let mut wal = MemoryWal::new();
        wal.fail_next_persist();
        let _forked = wal.clone();
    }
}

#[cfg(all(test, feature = "std"))]
mod fs_tests {
    use super::*;

    const KEY: [u8; 32] = [0x5a; 32];

    struct Scratch(std::path::PathBuf);

    impl Scratch {
        fn new(name: &str) -> Self {
            let dir = std::env::temp_dir()
                .join(std::format!("qsag-belt-wal-{}-{name}", std::process::id()));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).unwrap();
            Self(dir)
        }

        fn wal(&self) -> std::path::PathBuf {
            self.0.join("belt.wal")
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn bind_one(wal: FsBeltWal, epoch: u64) -> FsBeltWal {
        let mut latch = BeltLatch::recover(wal, 10).unwrap();
        latch
            .bind(epoch, &[7; 32], &[9; 32], &[3, 0, 2, 1])
            .unwrap();
        latch.into_wal()
    }

    #[test]
    fn tooth_consensus_disk_restart_burns_skipped_slots() {
        let dir = Scratch::new("consensus");
        drop(FsBeltWal::provision_genesis(dir.wal(), KEY).unwrap());
        for slot in [0, 500, 12_345] {
            let mut latch = BeltLatch::recover_slot_indexed(
                FsBeltWal::open_existing(dir.wal(), KEY).unwrap(),
                14,
            )
            .unwrap();
            assert_eq!(
                latch.bind_consensus_slot(slot, &[7; 32], &[8; 32], &[]),
                Ok(slot)
            );
        }
        let mut latch =
            BeltLatch::recover_slot_indexed(FsBeltWal::open_existing(dir.wal(), KEY).unwrap(), 14)
                .unwrap();
        assert_eq!(latch.last_signed_slot(), Some(12_345));
        for (slot, msg, err) in [
            (12_345, 1, BeltLatchError::EpochAlreadyBound),
            (12_345, 7, BeltLatchError::EpochConsumed),
            (501, 7, BeltLatchError::EpochConsumed),
        ] {
            assert_eq!(
                latch.bind_consensus_slot(slot, &[msg; 32], &[8; 32], &[]),
                Err(err)
            );
        }
    }

    #[test]
    fn recovery_refuses_a_log_that_was_never_provisioned() {
        let dir = Scratch::new("unprovisioned");
        assert_eq!(
            FsBeltWal::open_existing(dir.wal(), KEY).unwrap_err().kind(),
            std::io::ErrorKind::NotFound
        );
        // The refused open left nothing behind that a later genesis would trip over.
        drop(FsBeltWal::provision_genesis(dir.wal(), KEY).unwrap());
    }

    #[test]
    fn genesis_is_once_only_and_recovery_keeps_the_high_water_mark() {
        let dir = Scratch::new("once");
        let wal = FsBeltWal::provision_genesis(dir.wal(), KEY).unwrap();
        assert_eq!(wal.load().unwrap(), Some(BeltLatchState::default()));
        drop(bind_one(wal, 5));

        assert_eq!(
            FsBeltWal::provision_genesis(dir.wal(), KEY)
                .unwrap_err()
                .kind(),
            std::io::ErrorKind::AlreadyExists
        );
        let wal = FsBeltWal::open_existing(dir.wal(), KEY).unwrap();
        let latch = BeltLatch::recover(wal, 10).unwrap();
        assert_eq!(latch.next_epoch(), 6);
        assert_eq!(latch.in_flight().unwrap().epoch, 5);
    }

    #[test]
    fn a_deleted_log_is_rejected_instead_of_restarting_at_epoch_zero() {
        let dir = Scratch::new("deleted");
        drop(bind_one(
            FsBeltWal::provision_genesis(dir.wal(), KEY).unwrap(),
            5,
        ));
        std::fs::remove_file(dir.wal()).unwrap();

        assert_eq!(
            FsBeltWal::open_existing(dir.wal(), KEY).unwrap_err().kind(),
            std::io::ErrorKind::NotFound
        );
        // The lock sidecar outlives the log, so genesis cannot be replayed over it either.
        assert_eq!(
            FsBeltWal::provision_genesis(dir.wal(), KEY)
                .unwrap_err()
                .kind(),
            std::io::ErrorKind::AlreadyExists
        );
    }

    #[test]
    fn a_log_deleted_under_a_live_latch_fails_closed_on_load() {
        let dir = Scratch::new("live");
        let wal = FsBeltWal::provision_genesis(dir.wal(), KEY).unwrap();
        std::fs::remove_file(dir.wal()).unwrap();
        assert_eq!(wal.load(), Err(WalError::Corrupt));
        assert!(matches!(
            BeltLatch::recover(wal, 10),
            Err(BeltLatchError::Wal(WalError::Corrupt))
        ));
    }

    #[test]
    fn the_record_is_bound_to_the_wal_key() {
        let dir = Scratch::new("keyed");
        drop(bind_one(
            FsBeltWal::provision_genesis(dir.wal(), KEY).unwrap(),
            5,
        ));

        // Wrong key.
        assert_eq!(
            FsBeltWal::open_existing(dir.wal(), [0x5b; 32])
                .unwrap_err()
                .kind(),
            std::io::ErrorKind::InvalidData
        );
        // A well-formed epoch-0 state with a valid public digest but no MAC under the key:
        // what an attacker with file access but not the key can write.
        let mut forged = 1u64.to_be_bytes().to_vec();
        forged.extend_from_slice(&BeltLatchState::default().to_bytes());
        forged.extend_from_slice(&[0u8; 32]);
        std::fs::write(dir.wal(), &forged).unwrap();
        assert_eq!(
            FsBeltWal::open_existing(dir.wal(), KEY).unwrap_err().kind(),
            std::io::ErrorKind::InvalidData
        );
    }

    #[test]
    fn open_existing_at_least_rejects_snapshot_rollback() {
        let dir = Scratch::new("rollback");
        let wal0 = FsBeltWal::provision_genesis(dir.wal(), KEY).unwrap();
        let ckpt0 = wal0.checkpoint();
        let saved_genesis_bytes = std::fs::read(dir.wal()).unwrap();

        let wal1 = bind_one(wal0, 5);
        let ckpt1 = wal1.checkpoint();
        assert!(ckpt1.generation > ckpt0.generation);
        let saved_epoch5_bytes = std::fs::read(dir.wal()).unwrap();
        drop(wal1);

        // Restoring the pre-signing genesis snapshot while retaining ckpt1 is refused.
        std::fs::write(dir.wal(), &saved_genesis_bytes).unwrap();
        assert_eq!(
            FsBeltWal::open_existing_at_least(dir.wal(), KEY, ckpt1)
                .unwrap_err()
                .kind(),
            std::io::ErrorKind::InvalidData
        );

        // Restoring the genuine epoch-5 snapshot recovers cleanly at ckpt1 (and >= ckpt0).
        std::fs::write(dir.wal(), &saved_epoch5_bytes).unwrap();
        let recovered = FsBeltWal::open_existing_at_least(dir.wal(), KEY, ckpt1).unwrap();
        let latch = BeltLatch::recover(recovered, 10).unwrap();
        assert_eq!(latch.next_epoch(), 6);
        assert_eq!(latch.in_flight().unwrap().epoch, 5);
    }
}
