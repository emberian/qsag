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
//! A fresh bind is accepted only for `epoch <= next_epoch + MAX_EPOCH_JUMP`
//! ([`BeltLatchError::EpochJumpTooLarge`] otherwise), so one request can burn at most
//! [`MAX_EPOCH_JUMP`] leaves instead of the whole key. A signer whose log is further behind
//! its peers than the window cannot join them in one step.
//!
//! ### Log failure is terminal
//! If [`DurableWal::sync_persist`] fails, nothing is known about what reached storage. The
//! latch sets a poison flag before it returns the error, and from then on `latched_salt`,
//! `bind`, `echo_for` and `verify_peer_echoes` return [`BeltLatchError::WalPoisoned`]. The
//! only way forward is a new latch recovered from the log.

use alloc::vec::Vec;
use core::fmt;

use crate::sponge::keccak::{Cshake256Xof, cshake256_32, encode_multi_frame};
use crate::wipe::{ct_eq_bytes32, wipe_bytes32};

/// Largest distance above the high-water mark at which a fresh epoch may be bound.
pub const MAX_EPOCH_JUMP: u64 = 64;

const TAG_ECHO_KEY: &[u8] = b"QSAG.BELT.ECHO.KEY/v1";
const TAG_ECHO_MAC: &[u8] = b"QSAG.BELT.ECHO.MAC/v1";
#[cfg(feature = "std")]
const TAG_WAL_MAC: &[u8] = b"QSAG.BELT.LATCH.WAL.MAC/v1";

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
        cshake256_32(
            b"QSAG.BELT.LATCH.BINDING/v1",
            &encode_multi_frame(&[
                &self.epoch.to_be_bytes(),
                &self.msg_digest,
                &self.retry_salt,
                &self.target_sum_digits,
            ]),
        )
    }
}

/// Everything a write-ahead log must hold: the high-water mark and the in-flight record.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BeltLatchState {
    /// Every epoch below this value has been bound at least once.
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
                if rest.len() != 76 + len {
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
    fn authorize_open(&self, _record: &BeltLatchRecord) -> Result<(), WalError> { Err(WalError::Io) }

    /// Store `state` and return only once it would survive a power loss. On error nothing may
    /// be assumed about what was written; the latch then refuses to proceed.
    fn sync_persist(&mut self, state: &BeltLatchState) -> Result<(), WalError>;

    /// Load the last successfully persisted state; `Ok(None)` only for storage that was never
    /// written.
    fn load(&self) -> Result<Option<BeltLatchState>, WalError>;
}

/// Volatile [`DurableWal`] for tests and for hosts that supply their own durability one level
/// up. It is *not* durable: a process restart loses it.
#[derive(Clone, Debug, Default)]
pub struct MemoryWal {
    stored: Option<Vec<u8>>,
    persists: u64,
    fail_next: bool,
}

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

impl DurableWal for MemoryWal {
    fn authorize_open(&self, _record: &BeltLatchRecord) -> Result<(), WalError> { Ok(()) }
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
/// The stored record is `BeltLatchState::to_bytes() || tag`, where `tag` is a `cSHAKE256` MAC
/// under a secret `wal_key` the signer keeps apart from the log. Genesis and recovery are
/// separate entry points:
///
/// * [`FsBeltWal::provision_genesis`] is for a newly enrolled key. It refuses a path whose
///   log or lock sidecar already exists, and durably writes an authenticated epoch-0 record
///   before it returns.
/// * [`FsBeltWal::open_existing`] is for every later start. A missing log, a missing lock
///   sidecar, or a record that fails the MAC is an error; nothing here ever falls back to
///   epoch 0, so [`DurableWal::load`] never returns `Ok(None)` for this type.
#[cfg(feature = "std")]
pub struct FsBeltWal {
    record: qsag_asm::durable::LockedRecord,
    wal_key: [u8; 32],
    release: core::cell::RefCell<Option<crate::ceremony_journal::CeremonyReservation>>,
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
    /// Bind epoch_or_codeword to BeltLatchRecord::binding(). A permit authorizes
    /// only one opening attempt; recovery requires a fresh committed reservation.
    pub fn authorize_release(&mut self, journal: &crate::ceremony_journal::FsCeremonyJournal,
        permit: crate::ceremony_journal::CeremonyReleasePermit) -> std::io::Result<()> {
        *self.release.get_mut() = None;
        *self.release.get_mut() = Some(journal.consume_release(permit)?);
        Ok(())
    }

    fn tag(wal_key: &[u8; 32], body: &[u8]) -> [u8; 32] {
        cshake256_32(TAG_WAL_MAC, &encode_multi_frame(&[wal_key, body]))
    }

    fn seal(&self, state: &BeltLatchState) -> Vec<u8> {
        let mut out = state.to_bytes();
        let tag = Self::tag(&self.wal_key, &out);
        out.extend_from_slice(&tag);
        out
    }

    fn unseal(&self, raw: &[u8]) -> Option<BeltLatchState> {
        let (body, tag) = raw.split_at_checked(raw.len().checked_sub(32)?)?;
        if !ct_eq_bytes32(&Self::tag(&self.wal_key, body), tag.try_into().ok()?) {
            return None;
        }
        BeltLatchState::from_bytes(body)
    }

    /// Provision the log of a newly enrolled key at `path` and write its authenticated
    /// epoch-0 record. Fails if a log or lock sidecar is already there.
    pub fn provision_genesis(
        path: impl Into<std::path::PathBuf>,
        wal_key: [u8; 32],
    ) -> std::io::Result<Self> {
        let wal = Self {
            record: qsag_asm::durable::LockedRecord::create_new(path)?,
            wal_key,
            release: core::cell::RefCell::new(None),
        };
        wal.record.replace(&wal.seal(&BeltLatchState::default()))?;
        Ok(wal)
    }

    /// Open (and lock) a log that [`Self::provision_genesis`] created. Fails if the log or its
    /// lock sidecar is missing, or if the record does not verify under `wal_key`.
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        wal_key: [u8; 32],
    ) -> std::io::Result<Self> {
        let wal = Self {
            record: qsag_asm::durable::LockedRecord::open_existing(path)?,
            wal_key,
            release: core::cell::RefCell::new(None),
        };
        match wal.load() {
            Ok(Some(_)) => Ok(wal),
            Ok(None) | Err(WalError::Corrupt) => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "belt latch log failed authentication",
            )),
            Err(WalError::Io) => Err(std::io::Error::other("belt latch log unreadable")),
        }
    }
}

#[cfg(feature = "std")]
impl DurableWal for FsBeltWal {
    fn authorize_open(&self, record: &BeltLatchRecord) -> Result<(), WalError> {
        let reservation = self.release.borrow_mut().take().ok_or(WalError::Io)?;
        if reservation.epoch_or_codeword != record.binding() { return Err(WalError::Corrupt); }
        Ok(())
    }

    fn sync_persist(&mut self, state: &BeltLatchState) -> Result<(), WalError> {
        self.record
            .replace(&self.seal(state))
            .map_err(|_| WalError::Io)
    }

    fn load(&self) -> Result<Option<BeltLatchState>, WalError> {
        match self.record.read() {
            Ok(raw) => self.unseal(&raw).map(Some).ok_or(WalError::Corrupt),
            Err(e) if matches!(e.kind(), std::io::ErrorKind::NotFound | std::io::ErrorKind::InvalidData) => Err(WalError::Corrupt),
            Err(_) => Err(WalError::Io),
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
                write!(f, "split view: echo of party {party} differs from the local record")
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
pub fn derive_echo_mac_key(
    context: &[u8],
    a: usize,
    b: usize,
    pair_secrets: &[&[u8]],
) -> [u8; 32] {
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

/// One signer's latch (see the module documentation). Not `Clone`.
