//! Verifier-side challenges for [`crate::blind_vc`] presentations.
//!
//! A presentation proves a statement about one `(verifier_scope, verifier_challenge)`
//! pair. The proof stays valid forever, so whoever captures it can show it again. What
//! makes a presentation usable once is the verifier's own record of which challenges
//! it issued and has not yet accepted. [`crate::blind_vc::verify_presentation`] takes
//! that record as a [`PresentationChallenges`] and returns `true` only after the
//! presentation's challenge was consumed from it.
//!
//! * [`VerifierChallengeLedger`]: bounded, in memory, for a verifier that is one
//!   process. Its challenges end with the process: a restart refuses every earlier
//!   presentation, replayed or not.
//! * [`FsVerifierChallengeLedger`] (feature `std`): the same ledger in one exclusively
//!   locked file, committed on every issue and every consumption, for a verifier whose
//!   challenges are issued and consumed by different processes or must survive a
//!   restart. Stored state can be put back, so it takes an external monotone anchor
//!   to refuse a restored file.
//! * [`ReplayNotPrevented`]: the named opt-out for proof audit and proof-system tests.
//!
//! Only outstanding challenges are stored: consuming one removes it, and an expired
//! one is dropped at the next issue. A challenge that is not in the ledger is refused,
//! so the ledger never has to remember what it accepted.

use alloc::vec::Vec;

use qsag_accel::keccak::cshake256_framed_32;

/// Largest supported number of outstanding challenges in one ledger. The durable form
/// rewrites its whole record (72 bytes per outstanding challenge) on every operation.
pub const MAX_OUTSTANDING_CHALLENGES: usize = 65_536;

const CHALLENGE_TAG: &[u8] = b"QSAG.VC.VERIFIER.CHALLENGE.V1";
const SCOPE_TAG: &[u8] = b"QSAG.VC.VERIFIER.CHALLENGE.SCOPE.V1";

/// Why a challenge was not issued or not consumed. Every variant is a refusal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChallengeError {
    /// Not outstanding: never issued by this ledger, already consumed, or dropped
    /// after it expired.
    Unknown,
    /// Outstanding, but its lifetime has ended.
    Expired,
    /// Outstanding, but issued for another verifier scope. It stays outstanding.
    WrongScope,
    /// [`ReplayNotPrevented`]: the presentation answers another challenge than the
    /// one the caller expected.
    Unexpected,
    /// The ledger holds `capacity` live challenges, or its capacity is outside
    /// `1..=MAX_OUTSTANDING_CHALLENGES`. Nothing live is evicted to make room.
    LedgerFull,
    /// `ttl_seconds` is zero or `now + ttl_seconds` overflows.
    Lifetime,
    /// The durable record could not be committed, or this handle failed earlier. The
    /// operation did not succeed; reopen the ledger to learn which state is durable.
    Storage,
}

/// The verifier's record of challenges, as presentation verification uses it.
///
/// An implementation must make each challenge succeed at most once for the whole
/// acceptance domain of `verifier_scope`, and must fail closed on every error.
/// Returning `Ok` without durably removing the challenge from what will be accepted
/// later makes every presentation replayable.
pub trait PresentationChallenges {
    /// Cheap read-only admission check. A successful proof must still consume the challenge.
    fn is_live(&self, verifier_scope: &[u8], challenge: &[u8; 32]) -> bool;

    /// Called once per verification, after the proof and every statement check
    /// passed, with the scope the caller verified against and the challenge the
    /// presentation answers. Verification succeeds only if this returns `Ok`.
    fn consume(
        &mut self,
        verifier_scope: &[u8],
        challenge: &[u8; 32],
    ) -> Result<(), ChallengeError>;
}

/// Checks only that the presentation answers the challenge the caller expected.
/// Nothing is recorded and nothing is consumed: the same presentation verifies again,
/// for anyone who holds a copy of it, for as long as the issuer root is trusted.
///
/// This is for auditing a stored proof offline and for tests of the proof system. An
/// authorization decision made with it is replayable; a verifier that grants anything
/// on a presentation uses [`VerifierChallengeLedger`] or [`FsVerifierChallengeLedger`].
pub struct ReplayNotPrevented<'a>(pub &'a [u8; 32]);

impl PresentationChallenges for ReplayNotPrevented<'_> {
    fn is_live(&self, _: &[u8], challenge: &[u8; 32]) -> bool {
        self.0 == challenge
    }

    fn consume(&mut self, _: &[u8], challenge: &[u8; 32]) -> Result<(), ChallengeError> {
        if challenge == self.0 {
            Ok(())
        } else {
            Err(ChallengeError::Unexpected)
        }
    }
}

#[derive(Clone, Copy)]
struct Outstanding {
    challenge: [u8; 32],
    scope: [u8; 32],
    expires_at: u64,
}

fn scope_digest(verifier_scope: &[u8]) -> [u8; 32] {
    cshake256_framed_32(SCOPE_TAG, &[verifier_scope])
}

/// The bounded set of challenges one verifier has issued and not yet accepted.
///
/// `now` is the verifier's clock in seconds, supplied by the caller on every call. A
/// challenge issued at `now` with `ttl_seconds` is live while the clock reads less
/// than `now + ttl_seconds`. A clock that runs backwards can lengthen the life of a
/// challenge that is still outstanding; it cannot bring back a consumed one.
///
/// # Bound
/// At most `capacity` challenges are outstanding. Expired ones are dropped when the
/// next challenge is issued; a live one is never evicted, so a full ledger refuses to
/// issue until challenges are consumed or expire. Whoever can request challenges can
/// therefore fill the ledger and deny service for one lifetime: the application must
/// rate-limit issuance per client and keep lifetimes short. `capacity` is that bound.
///
/// # Lifetime
/// This ledger is process memory. Dropping it forgets every outstanding challenge:
/// presentations in flight then fail, and none is accepted twice. A challenge is
/// never accepted by a ledger that did not issue it, so a verifier that issues in one
/// process and verifies in another, or that must honour challenges across a restart,
/// needs [`FsVerifierChallengeLedger`].
pub struct VerifierChallengeLedger {
    /// Sorted by challenge.
    outstanding: Vec<Outstanding>,
    capacity: usize,
    /// Number of challenges ever issued; part of every challenge's derivation.
    issued: u64,
}

impl VerifierChallengeLedger {
    /// A capacity outside `1..=MAX_OUTSTANDING_CHALLENGES` refuses every issue.
    pub const fn new(capacity: usize) -> Self {
        Self {
            outstanding: Vec::new(),
            capacity,
            issued: 0,
        }
    }

    /// Number of challenges currently held, expired ones not yet dropped included.
    pub fn outstanding(&self) -> usize {
        self.outstanding.len()
    }

    /// Issue a challenge for `verifier_scope` that is live until `now + ttl_seconds`.
    ///
    /// `entropy` must be 32 fresh random bytes: it is what makes the challenge
    /// unpredictable to a holder who would precompute a presentation. The challenge
    /// is `cSHAKE256(entropy, verifier_scope, expiry, issue counter)`, so a repeated
    /// `entropy` still yields a new challenge for as long as this ledger's state
    /// lives, but one an observer of the earlier challenge's inputs could predict.
    pub fn issue(
        &mut self,
        verifier_scope: &[u8],
        now: u64,
        ttl_seconds: u64,
        entropy: [u8; 32],
    ) -> Result<[u8; 32], ChallengeError> {
        if self.capacity == 0 || self.capacity > MAX_OUTSTANDING_CHALLENGES {
            return Err(ChallengeError::LedgerFull);
        }
        if ttl_seconds == 0 {
            return Err(ChallengeError::Lifetime);
        }
        let expires_at = now
            .checked_add(ttl_seconds)
            .ok_or(ChallengeError::Lifetime)?;
        self.outstanding.retain(|entry| entry.expires_at > now);
        if self.outstanding.len() >= self.capacity {
            return Err(ChallengeError::LedgerFull);
        }
        let issued = self
            .issued
            .checked_add(1)
            .ok_or(ChallengeError::LedgerFull)?;
        let challenge = cshake256_framed_32(
            CHALLENGE_TAG,
            &[
                &entropy,
                verifier_scope,
                &expires_at.to_be_bytes(),
                &issued.to_be_bytes(),
            ],
        );
        // A digest equal to an outstanding one is a cSHAKE256 collision; refuse it
        // rather than let one entry stand for two issues.
        let index = match self
            .outstanding
            .binary_search_by(|entry| entry.challenge.cmp(&challenge))
        {
            Ok(_) => return Err(ChallengeError::Storage),
            Err(index) => index,
        };
        self.outstanding
            .try_reserve(1)
            .map_err(|_| ChallengeError::LedgerFull)?;
        self.outstanding.insert(
            index,
            Outstanding {
                challenge,
                scope: scope_digest(verifier_scope),
                expires_at,
            },
        );
        self.issued = issued;
        Ok(challenge)
    }

    /// This ledger as the [`PresentationChallenges`] of a verification at time `now`.
    pub fn at(&mut self, now: u64) -> impl PresentationChallenges + '_ {
        MemoryAt { ledger: self, now }
    }

    fn live_index(
        &self,
        verifier_scope: &[u8],
        challenge: &[u8; 32],
        now: u64,
    ) -> Result<usize, ChallengeError> {
        let index = self
            .outstanding
            .binary_search_by(|entry| entry.challenge.cmp(challenge))
            .map_err(|_| ChallengeError::Unknown)?;
        let entry = &self.outstanding[index];
        if entry.scope != scope_digest(verifier_scope) {
            return Err(ChallengeError::WrongScope);
        }
        if now >= entry.expires_at {
            return Err(ChallengeError::Expired);
        }
        Ok(index)
    }

    fn consume_at(
        &mut self,
        verifier_scope: &[u8],
        challenge: &[u8; 32],
        now: u64,
    ) -> Result<(), ChallengeError> {
        let index = self.live_index(verifier_scope, challenge, now)?;
        self.outstanding.remove(index);
        Ok(())
    }
}

struct MemoryAt<'a> {
    ledger: &'a mut VerifierChallengeLedger,
    now: u64,
}

impl PresentationChallenges for MemoryAt<'_> {
    fn is_live(&self, scope: &[u8], challenge: &[u8; 32]) -> bool {
        self.ledger.live_index(scope, challenge, self.now).is_ok()
    }

    fn consume(
        &mut self,
        verifier_scope: &[u8],
        challenge: &[u8; 32],
    ) -> Result<(), ChallengeError> {
        self.ledger.consume_at(verifier_scope, challenge, self.now)
    }
}

/// [`VerifierChallengeLedger`] in one crash-durable, exclusively locked file, so a
/// presentation accepted by one process is refused by the next one and after a
/// restart.
///
/// Every [`Self::issue`] and every successful consumption commits the record before
/// it returns. A commit that fails makes the operation fail and the handle refuse all
/// further use (the record may or may not have been replaced); reopen to continue.
/// All processes of one verifier open the same provisioned path. A competing open
/// fails while this handle holds the lock. `open_existing` never creates a ledger.
///
/// # Rollback
/// [`Self::create_new_anchored`] pins every commit in an
/// [`ExternalMonotoneAnchor`](qsag_core::ExternalMonotoneAnchor) (see
/// [`AnchoredSnapshot`](qsag_policy::AnchoredSnapshot)): a ledger whose file or
/// whole directory was put back to an earlier state is refused on open, so a
/// challenge consumed after that state cannot be accepted again. [`Self::create_new`]
/// has no anchor and gives crash recovery and process exclusion only: an
/// administrator, backup tool or volume snapshot that restores the file re-admits
/// every challenge that was outstanding in the restored state and consumed since,
/// until it expires.
///
/// # One challenge domain
/// An anchor does nothing for a second, independent copy of the service. Two replicas
/// with their own ledgers do not accept each other's challenges, but nothing local
/// can tell that a second ledger exists for the same verifier scope, or that a copy
/// of this file is being served elsewhere under its own anchor. A deployment has
/// exactly one challenge domain per verifier scope: one ledger on one host, or one
/// linearizable service behind [`PresentationChallenges`].
///
/// The bound and the rate-limiting duty of [`VerifierChallengeLedger`] apply.
#[cfg(feature = "std")]
pub struct FsVerifierChallengeLedger {
    snapshot: qsag_policy::AnchoredSnapshot,
    memory: VerifierChallengeLedger,
    failed: bool,
}

#[cfg(feature = "std")]
type Anchor = alloc::boxed::Box<dyn qsag_core::ExternalMonotoneAnchor>;

#[cfg(feature = "std")]
impl FsVerifierChallengeLedger {
    const MAGIC: [u8; 8] = *b"QSVCCH01";
    const PAYLOAD_HEADER_BYTES: usize = 16;
    const ENTRY_BYTES: usize = 72;

    fn check_capacity(capacity: usize) -> std::io::Result<()> {
        if capacity == 0 || capacity > MAX_OUTSTANDING_CHALLENGES {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "verifier challenge capacity outside supported range",
            ));
        }
        Ok(())
    }

    fn create(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
        anchor: Option<Anchor>,
    ) -> std::io::Result<Self> {
        Self::check_capacity(capacity)?;
        let memory = VerifierChallengeLedger::new(capacity);
        let snapshot = qsag_policy::AnchoredSnapshot::create_new(
            path,
            Self::MAGIC,
            &Self::encode(&memory),
            anchor,
        )?;
        Ok(Self {
            snapshot,
            memory,
            failed: false,
        })
    }

    fn open(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
        anchor: Option<Anchor>,
    ) -> std::io::Result<Self> {
        Self::check_capacity(capacity)?;
        let (snapshot, payload) = qsag_policy::AnchoredSnapshot::open_existing(
            path,
            Self::MAGIC,
            Self::PAYLOAD_HEADER_BYTES + Self::ENTRY_BYTES * capacity,
            anchor,
        )?;
        Ok(Self {
            snapshot,
            memory: Self::decode(&payload, capacity)?,
            failed: false,
        })
    }

    /// Provision an empty challenge domain with no rollback protection. Never use
    /// this to replace a lost ledger while its challenges may still be in flight.
    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
    ) -> std::io::Result<Self> {
        Self::create(path, capacity, None)
    }

    /// Provision an empty challenge domain pinned by `anchor`, which must be empty
    /// and must not share the ledger file's rollback domain.
    pub fn create_new_anchored(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
        anchor: Anchor,
    ) -> std::io::Result<Self> {
        Self::create(path, capacity, Some(anchor))
    }

    /// Recover an unanchored domain, requiring its original capacity and format.
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
    ) -> std::io::Result<Self> {
        Self::open(path, capacity, None)
    }

    /// Recover an anchored domain; a ledger older than `anchor` is refused.
    pub fn open_existing_anchored(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
        anchor: Anchor,
    ) -> std::io::Result<Self> {
        Self::open(path, capacity, Some(anchor))
    }

    pub fn is_anchored(&self) -> bool {
        self.snapshot.is_anchored()
    }

    /// Number of challenges currently held, expired ones not yet dropped included.
    pub fn outstanding(&self) -> usize {
        self.memory.outstanding()
    }

    /// [`VerifierChallengeLedger::issue`], committed before the challenge is returned.
    pub fn issue(
        &mut self,
        verifier_scope: &[u8],
        now: u64,
        ttl_seconds: u64,
        entropy: [u8; 32],
    ) -> Result<[u8; 32], ChallengeError> {
        if self.failed {
            return Err(ChallengeError::Storage);
        }
        let challenge = self
            .memory
            .issue(verifier_scope, now, ttl_seconds, entropy)?;
        self.commit()?;
        Ok(challenge)
    }

    /// This ledger as the [`PresentationChallenges`] of a verification at time `now`.
    pub fn at(&mut self, now: u64) -> impl PresentationChallenges + '_ {
        FsAt { ledger: self, now }
    }

    fn commit(&mut self) -> Result<(), ChallengeError> {
        self.snapshot
            .commit(&Self::encode(&self.memory))
            .map_err(|_| {
                self.failed = true;
                ChallengeError::Storage
            })
    }

    fn invalid() -> std::io::Error {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "invalid or unsupported verifier challenge record (expected QSVCCH01 and configured capacity)",
        )
    }

    fn encode(memory: &VerifierChallengeLedger) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(
            Self::PAYLOAD_HEADER_BYTES + Self::ENTRY_BYTES * memory.outstanding.len(),
        );
        bytes.extend_from_slice(&(memory.capacity as u32).to_be_bytes());
        bytes.extend_from_slice(&(memory.outstanding.len() as u32).to_be_bytes());
        bytes.extend_from_slice(&memory.issued.to_be_bytes());
        for entry in &memory.outstanding {
            bytes.extend_from_slice(&entry.challenge);
            bytes.extend_from_slice(&entry.scope);
            bytes.extend_from_slice(&entry.expires_at.to_be_bytes());
        }
        bytes
    }

    fn decode(payload: &[u8], capacity: usize) -> std::io::Result<VerifierChallengeLedger> {
        if payload.len() < Self::PAYLOAD_HEADER_BYTES {
            return Err(Self::invalid());
        }
        let stored_capacity = u32::from_be_bytes(payload[..4].try_into().unwrap()) as usize;
        let count = u32::from_be_bytes(payload[4..8].try_into().unwrap()) as usize;
        let issued = u64::from_be_bytes(payload[8..16].try_into().unwrap());
        let (entries, rest) = payload[Self::PAYLOAD_HEADER_BYTES..].as_chunks::<72>();
        if stored_capacity != capacity
            || count > capacity
            || count as u64 > issued
            || entries.len() != count
            || !rest.is_empty()
        {
            return Err(Self::invalid());
        }
        let mut memory = VerifierChallengeLedger::new(capacity);
        memory.issued = issued;
        memory
            .outstanding
            .try_reserve_exact(count)
            .map_err(std::io::Error::other)?;
        for entry in entries {
            let entry = Outstanding {
                challenge: entry[..32].try_into().unwrap(),
                scope: entry[32..64].try_into().unwrap(),
                expires_at: u64::from_be_bytes(entry[64..].try_into().unwrap()),
            };
            if memory
                .outstanding
                .last()
                .is_some_and(|prev| prev.challenge >= entry.challenge)
            {
                return Err(Self::invalid());
            }
            memory.outstanding.push(entry);
        }
        Ok(memory)
    }
}

#[cfg(feature = "std")]
struct FsAt<'a> {
    ledger: &'a mut FsVerifierChallengeLedger,
    now: u64,
}

#[cfg(feature = "std")]
impl PresentationChallenges for FsAt<'_> {
    fn is_live(&self, scope: &[u8], challenge: &[u8; 32]) -> bool {
        !self.ledger.failed
            && self
                .ledger
                .memory
                .live_index(scope, challenge, self.now)
                .is_ok()
    }

    fn consume(
        &mut self,
        verifier_scope: &[u8],
        challenge: &[u8; 32],
    ) -> Result<(), ChallengeError> {
        if self.ledger.failed {
            return Err(ChallengeError::Storage);
        }
        self.ledger
            .memory
            .consume_at(verifier_scope, challenge, self.now)?;
        self.ledger.commit()
    }
}

#[cfg(all(test, feature = "std", unix))]
pub(crate) mod test_support {
    use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, Mutex};
    use std::vec::Vec;

    /// A forked child holds copies of this process's lock descriptors until it execs,
    /// so a store dropped and reopened on one thread while another thread spawns a
    /// child can find its own lock still held. Tests that lock files or spawn take this.
    pub(crate) fn serial() -> std::sync::MutexGuard<'static, ()> {
        static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());
        SERIAL
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    /// An anchor outside the ledger's directory: it keeps what it was last given.
    #[derive(Clone, Default)]
    pub(crate) struct TestAnchor {
        cell: Arc<Mutex<Option<LedgerCheckpoint>>>,
        pub(crate) fail_next_advance: Arc<AtomicBool>,
    }

    impl ExternalMonotoneAnchor for TestAnchor {
        fn load(&self) -> std::io::Result<Option<LedgerCheckpoint>> {
            Ok(*self.cell.lock().unwrap())
        }
        fn advance(&self, checkpoint: LedgerCheckpoint) -> std::io::Result<()> {
            if self.fail_next_advance.swap(false, Ordering::SeqCst) {
                return Err(std::io::Error::other("anchor unreachable"));
            }
            let mut cell = self.cell.lock().unwrap();
            if let Some(old) = *cell
                && (old.generation > checkpoint.generation
                    || (old.generation == checkpoint.generation && old.tag != checkpoint.tag))
            {
                return Err(std::io::Error::other("anchor rejects rolled-back state"));
            }
            *cell = Some(checkpoint);
            Ok(())
        }
    }

    pub(crate) fn dir_files(dir: &std::path::Path) -> Vec<(PathBuf, Vec<u8>)> {
        let mut files: Vec<_> = std::fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .map(|p| {
                let bytes = std::fs::read(&p).unwrap();
                (p, bytes)
            })
            .collect();
        files.sort();
        files
    }

    pub(crate) fn temporary_directory(label: &str) -> PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(std::format!(
            "qsag-vc-challenges-{label}-{}-{nanos}",
            std::process::id()
        ));
        std::fs::create_dir(&path).unwrap();
        path
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_ledger_consumes_once_and_checks_scope_and_expiry() {
        let mut ledger = VerifierChallengeLedger::new(4);
        let a = ledger.issue(b"scope-a", 100, 60, [1; 32]).unwrap();
        let b = ledger.issue(b"scope-a", 100, 60, [2; 32]).unwrap();
        // Same entropy, scope and expiry: still a different challenge.
        let c = ledger.issue(b"scope-a", 100, 60, [2; 32]).unwrap();
        assert_ne!(a, b);
        assert_ne!(b, c);

        assert!(ledger.at(101).is_live(b"scope-a", &a));
        assert!(!ledger.at(101).is_live(b"scope-b", &a));
        assert!(!ledger.at(160).is_live(b"scope-a", &a));
        // Another scope is refused and leaves the challenge outstanding.
        assert_eq!(
            ledger.at(101).consume(b"scope-b", &a),
            Err(ChallengeError::WrongScope)
        );
        assert_eq!(ledger.at(101).consume(b"scope-a", &a), Ok(()));
        assert!(!ledger.at(101).is_live(b"scope-a", &a));
        assert_eq!(
            ledger.at(101).consume(b"scope-a", &a),
            Err(ChallengeError::Unknown)
        );
        assert_eq!(
            ledger.at(101).consume(b"scope-a", &[9; 32]),
            Err(ChallengeError::Unknown)
        );

        // The last live second is 159; expiry does not consume, so an earlier clock
        // reading still finds the challenge, once.
        assert_eq!(
            ledger.at(160).consume(b"scope-a", &b),
            Err(ChallengeError::Expired)
        );
        assert_eq!(
            ledger.at(u64::MAX).consume(b"scope-a", &b),
            Err(ChallengeError::Expired)
        );
        assert_eq!(ledger.at(159).consume(b"scope-a", &b), Ok(()));
        assert_eq!(
            ledger.at(159).consume(b"scope-a", &b),
            Err(ChallengeError::Unknown)
        );
        assert_eq!(ledger.outstanding(), 1);

        assert_eq!(
            ledger.issue(b"scope-a", 100, 0, [3; 32]),
            Err(ChallengeError::Lifetime)
        );
        assert_eq!(
            ledger.issue(b"scope-a", u64::MAX, 1, [3; 32]),
            Err(ChallengeError::Lifetime)
        );
        assert_eq!(ledger.outstanding(), 1);
    }

    #[test]
    fn memory_ledger_capacity_fails_closed_and_only_expiry_frees_room() {
        let mut ledger = VerifierChallengeLedger::new(2);
        let a = ledger.issue(b"s", 100, 10, [1; 32]).unwrap();
        let b = ledger.issue(b"s", 100, 50, [2; 32]).unwrap();
        // Full of live challenges: refused, and neither live one was evicted.
        assert_eq!(
            ledger.issue(b"s", 109, 10, [3; 32]),
            Err(ChallengeError::LedgerFull)
        );
        assert_eq!(ledger.outstanding(), 2);
        // `a` expires at 110: issuing then drops it and has room for exactly one.
        let c = ledger.issue(b"s", 110, 10, [3; 32]).unwrap();
        assert_eq!(
            ledger.issue(b"s", 110, 10, [4; 32]),
            Err(ChallengeError::LedgerFull)
        );
        assert_eq!(
            ledger.at(100).consume(b"s", &a),
            Err(ChallengeError::Unknown)
        );
        assert_eq!(ledger.at(111).consume(b"s", &b), Ok(()));
        assert_eq!(ledger.at(111).consume(b"s", &c), Ok(()));
        // Consumption frees room too.
        ledger.issue(b"s", 111, 10, [5; 32]).unwrap();

        for capacity in [0, MAX_OUTSTANDING_CHALLENGES + 1, usize::MAX] {
            assert_eq!(
                VerifierChallengeLedger::new(capacity).issue(b"s", 1, 1, [1; 32]),
                Err(ChallengeError::LedgerFull)
            );
        }
    }

    #[test]
    fn replay_not_prevented_only_compares_the_challenge() {
        let mut opt_out = ReplayNotPrevented(&[7; 32]);
        assert_eq!(opt_out.consume(b"any", &[7; 32]), Ok(()));
        assert_eq!(opt_out.consume(b"any", &[7; 32]), Ok(()));
        assert_eq!(
            opt_out.consume(b"any", &[8; 32]),
            Err(ChallengeError::Unexpected)
        );
    }

    #[cfg(all(feature = "std", unix))]
    #[test]
    fn fs_ledger_keeps_issues_and_consumptions_across_reopen() {
        let _serial = super::test_support::serial();
        let dir = test_support::temporary_directory("reopen");
        let path = dir.join("challenges");
        let mut ledger = FsVerifierChallengeLedger::create_new(&path, 2).unwrap();
        let a = ledger.issue(b"s", 100, 60, [1; 32]).unwrap();
        let b = ledger.issue(b"s", 100, 60, [2; 32]).unwrap();
        // The lock is exclusive while a handle lives.
        assert!(FsVerifierChallengeLedger::open_existing(&path, 2).is_err());
        drop(ledger);

        let mut ledger = FsVerifierChallengeLedger::open_existing(&path, 2).unwrap();
        assert_eq!(ledger.outstanding(), 2);
        assert_eq!(
            ledger.issue(b"s", 101, 60, [3; 32]),
            Err(ChallengeError::LedgerFull)
        );
        assert_eq!(
            ledger.at(101).consume(b"other", &a),
            Err(ChallengeError::WrongScope)
        );
        assert_eq!(ledger.at(101).consume(b"s", &a), Ok(()));
        drop(ledger);

        let mut ledger = FsVerifierChallengeLedger::open_existing(&path, 2).unwrap();
        assert_eq!(
            ledger.at(101).consume(b"s", &a),
            Err(ChallengeError::Unknown)
        );
        // The issue counter is durable: the entropy that made `a` makes another
        // challenge now, so the consumed one cannot be issued a second time.
        let again = ledger.issue(b"s", 100, 60, [1; 32]).unwrap();
        assert_ne!(again, a);
        assert_eq!(ledger.at(159).consume(b"s", &b), Ok(()));
        drop(ledger);

        assert!(FsVerifierChallengeLedger::open_existing(&path, 3).is_err());
        assert!(FsVerifierChallengeLedger::open_existing(dir.join("absent"), 2).is_err());
        assert!(FsVerifierChallengeLedger::create_new(&path, 2).is_err());
        for capacity in [0, MAX_OUTSTANDING_CHALLENGES + 1] {
            assert!(FsVerifierChallengeLedger::create_new(dir.join("bad"), capacity).is_err());
        }
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(all(feature = "std", unix))]
    #[test]
    fn fs_ledger_failed_commit_fails_closed_and_kills_the_handle() {
        let _serial = super::test_support::serial();
        use alloc::boxed::Box;
        use std::sync::atomic::Ordering;
        let dir = test_support::temporary_directory("failure");
        let path = dir.join("challenges");
        let mut ledger = FsVerifierChallengeLedger::create_new(&path, 4).unwrap();
        let a = ledger.issue(b"s", 100, 60, [1; 32]).unwrap();
        // A directory where atomic replacement needs its temporary file forces I/O
        // failure: no challenge is handed out, and the handle stays dead afterwards.
        std::fs::create_dir(dir.join("challenges.tmp")).unwrap();
        assert_eq!(
            ledger.issue(b"s", 100, 60, [2; 32]),
            Err(ChallengeError::Storage)
        );
        std::fs::remove_dir(dir.join("challenges.tmp")).unwrap();
        assert_eq!(
            ledger.issue(b"s", 100, 60, [3; 32]),
            Err(ChallengeError::Storage)
        );
        assert_eq!(
            ledger.at(101).consume(b"s", &a),
            Err(ChallengeError::Storage)
        );
        drop(ledger);
        // Nothing of the failed handle reached the record.
        let mut ledger = FsVerifierChallengeLedger::open_existing(&path, 4).unwrap();
        assert_eq!(ledger.outstanding(), 1);
        std::fs::create_dir(dir.join("challenges.tmp")).unwrap();
        assert_eq!(
            ledger.at(101).consume(b"s", &a),
            Err(ChallengeError::Storage)
        );
        std::fs::remove_dir(dir.join("challenges.tmp")).unwrap();
        drop(ledger);
        let mut ledger = FsVerifierChallengeLedger::open_existing(&path, 4).unwrap();
        assert_eq!(ledger.at(101).consume(b"s", &a), Ok(()));
        drop(ledger);

        // Anchored: the record is durable and the anchor write is lost. The
        // consumption is reported as failed, and it stays consumed after reopening.
        let anchored = dir.join("anchored");
        let anchor = test_support::TestAnchor::default();
        let mut ledger =
            FsVerifierChallengeLedger::create_new_anchored(&anchored, 4, Box::new(anchor.clone()))
                .unwrap();
        assert!(ledger.is_anchored());
        let b = ledger.issue(b"s", 100, 60, [4; 32]).unwrap();
        anchor.fail_next_advance.store(true, Ordering::SeqCst);
        assert_eq!(
            ledger.at(101).consume(b"s", &b),
            Err(ChallengeError::Storage)
        );
        assert_eq!(
            ledger.issue(b"s", 100, 60, [5; 32]),
            Err(ChallengeError::Storage)
        );
        drop(ledger);
        let mut ledger =
            FsVerifierChallengeLedger::open_existing_anchored(&anchored, 4, Box::new(anchor))
                .unwrap();
        assert_eq!(
            ledger.at(101).consume(b"s", &b),
            Err(ChallengeError::Unknown)
        );
        drop(ledger);
        // The anchor requirement cannot be dropped, and a foreign format is refused.
        assert!(FsVerifierChallengeLedger::open_existing(&anchored, 4).is_err());
        drop(qsag_policy::FsSealConsumptionStore::create_new(dir.join("seals"), 4).unwrap());
        assert!(FsVerifierChallengeLedger::open_existing(dir.join("seals"), 4).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
