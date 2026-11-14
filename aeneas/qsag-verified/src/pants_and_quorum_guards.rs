//! Quorum-Switching `BeltLatch` Guard, 256-Bit `WOTS+C` (`w = 4, v = 128, S = 192`) Verifier,
//! Sticky `Rss256Engine` Verification Poison Latch, and Static Ancestor `Waistband` Root Guard.
//!
//! All invariant-bearing state-machine structs keep every field module-private (with read-only
//! `const fn` getters) so safe Rust callers outside this module cannot forge or mutate internal
//! phases, verification flags, bound message tags, or poison latches directly.
//!
//! 1. `BeltQuorumCore`: enforces Byzantine quorum-switching parameters
//!    (`n > 0`, `f < t`, `t <= q`, `q <= n`, `2 * q > n + f`, and `q <= n - f` in global-liveness
//!    mode), bounded epoch jumps (`proposed_epoch <= next_epoch + max_jump_window`), irreversible
//!    `poisoned = true` latching on WAL failure or conflicting `(epoch, msg_tag)` equivocation,
//!    and `SharesAuthorized` transition strictly when `ack_count >= q && !poisoned`.
//! 2. `VerifiedWotsC256Guard` & `verified_wotsc256_verify_sum`: extracts all `128` base-4 digits
//!    (`0..=3`) from a `[u8; 32]` digest and verifies constant target sum `sum == 192`.
//! 3. `VerifiedRssPoisonLatch`: models `Rss256Engine` barrier state (`pending_relations`,
//!    `unverified`, `poisoned`), latching `poisoned = true` BEFORE clearing `pending_relations`
//!    on a failed check (`check_ok == false`) and gating `authorize_open()` behind
//!    `!poisoned && !unverified && pending_relations == 0`.
//! 4. `VerifiedWaistbandRootGuard`: checks `(cache_pk_tag == key_pk_tag) &&
//!    (cache_params_tag == key_params_tag) && (recomputed_child_root == expected_static_child_root)`
//!    plus durable first-signed ancestor codeword locking before permitting ancestor signing.

use crate::tower::ct_eq_bytes32;

/// Winternitz radix `w = 4` (`digits[i] in 0..=3`) for 256-bit `WOTS+C`.
pub const WOTSC256_BASE_W: u8 = 4;

/// Number of base-4 chains (`v = 128`) extracted from a 32-byte digest.
pub const WOTSC256_CHAINS: usize = 128;

/// Balanced constant target sum `S = 128 * (4 - 1) / 2 = 192` for 256-bit `WOTS+C`.
pub const WOTSC256_TARGET_SUM: u32 = 192;

/// Explicit refusal reasons emitted by the four guards in this module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PantsGuardError {
    InvalidBeltQuorumConfig,
    BeltGuardPoisoned,
    BeltWalSyncFailed,
    ConflictingEpochMsgTag,
    StaleEpochBelowNext,
    EpochJumpWindowExceeded,
    BeltEpochExhausted,
    NoEpochBound,
    EpochMismatch,
    AckCountExceedsCommittee,
    InsufficientQuorumAcks,
    SharesAlreadyAuthorized,
    InvalidWotsC256TargetSum,
    RssEnginePoisoned,
    ZeroRelationBatch,
    RelationCounterOverflow,
    RssVerificationCheckFailed,
    RssOpenBeforeCheck,
    WaistbandGuardPoisoned,
    WaistbandAddressMismatch,
    WaistbandCachePkMismatch,
    WaistbandCacheParamsMismatch,
    WaistbandChildRootMismatch,
    WaistbandCodewordEquivocation,
}

// ============================================================================
// 1. `BeltQuorumCore` (`2 * q > n + f` BFT Quorum-Switching + Poison)
// ============================================================================

/// Lifecycle phase of `BeltQuorumCore`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BeltQuorumPhase {
    Idle,
    EpochBoundPendingQuorum,
    SharesAuthorized,
    Poisoned,
}

/// Certified authorization token emitted when `BeltQuorumCore` reaches `SharesAuthorized`.
#[derive(Clone, Copy)]
pub struct BeltAuthorizationGrant {
    pub authorized_epoch: u64,
    pub msg_tag: [u8; 32],
    pub certified_acks: u32,
}

/// Observable input event for unified multi-turn stepping of `BeltQuorumCore`.
#[derive(Clone, Copy)]
#[allow(dead_code)]
pub(crate) enum BeltQuorumCoreInput {
    ProposeOrRetryEpoch {
        proposed_epoch: u64,
        msg_tag: [u8; 32],
        wal_sync_ok: bool,
    },
    RecordCustodianAck {
        ack_epoch: u64,
        ack_msg_tag: [u8; 32],
    },
    AuthorizeShares {
        req_epoch: u64,
        req_msg_tag: [u8; 32],
    },
}

/// Observable output emitted by a successful `BeltQuorumCore` transition.
#[derive(Clone, Copy)]
#[allow(dead_code)]
pub(crate) enum BeltQuorumCoreOutput {
    EpochBound,
    AckRecorded(u32),
    SharesAuthorized(BeltAuthorizationGrant),
}

/// Validate `(n, t, f, q)` quorum-switching parameters:
/// - `n > 0`, `f < t`, `t <= q`, `q <= n`,
/// - `2 * q > n + f` (overflow-free in `u64`, ensuring any two `q`-quorums share `>= f + 1` parties),
/// - `q <= n - f` when `require_global_liveness` is `true` (`n >= 3 * f + 1`).
#[inline]
pub const fn validate_belt_quorum_config(
    n: u32,
    t: u32,
    f: u32,
    q: u32,
    require_global_liveness: bool,
) -> bool {
    if n == 0 {
        return false;
    }
    if f >= t {
        return false;
    }
    if t > q {
        return false;
    }
    if q > n {
        return false;
    }
    let two_q: u64 = (q as u64) + (q as u64);
    let n_plus_f: u64 = (n as u64) + (f as u64);
    if two_q <= n_plus_f {
        return false;
    }
    if require_global_liveness && ((n as u64) < 3 * (f as u64) + 1 || q > n - f) {
        return false;
    }
    true
}

/// Non-`Clone` affine BFT quorum-switching epoch guard with private invariant-bearing fields.
pub(crate) struct BeltQuorumCore {
    n: u32,
    t: u32,
    f: u32,
    q: u32,
    global_liveness_mode: bool,
    next_epoch: u64,
    max_jump_window: u64,
    phase: BeltQuorumPhase,
    has_bound_epoch: bool,
    bound_epoch: u64,
    bound_msg_tag: [u8; 32],
    ack_count: u32,
    poisoned: bool,
}

#[inline]
const fn poison_belt_guard(st: BeltQuorumCore) -> BeltQuorumCore {
    BeltQuorumCore {
        n: st.n,
        t: st.t,
        f: st.f,
        q: st.q,
        global_liveness_mode: st.global_liveness_mode,
        next_epoch: st.next_epoch,
        max_jump_window: st.max_jump_window,
        phase: BeltQuorumPhase::Poisoned,
        has_bound_epoch: st.has_bound_epoch,
        bound_epoch: st.bound_epoch,
        bound_msg_tag: st.bound_msg_tag,
        ack_count: 0,
        poisoned: true,
    }
}

#[allow(dead_code)]
impl BeltQuorumCore {
    /// Construct a validated quorum-switching `BeltLatch` guard in `Idle` phase.
    pub fn new_validated(
        n: u32,
        t: u32,
        f: u32,
        q: u32,
        require_global_liveness: bool,
        initial_next_epoch: u64,
        max_jump_window: u64,
    ) -> Result<BeltQuorumCore, PantsGuardError> {
        if !validate_belt_quorum_config(n, t, f, q, require_global_liveness) {
            return Err(PantsGuardError::InvalidBeltQuorumConfig);
        }
        Ok(BeltQuorumCore {
            n,
            t,
            f,
            q,
            global_liveness_mode: require_global_liveness,
            next_epoch: initial_next_epoch,
            max_jump_window,
            phase: BeltQuorumPhase::Idle,
            has_bound_epoch: false,
            bound_epoch: 0,
            bound_msg_tag: [0u8; 32],
            ack_count: 0,
            poisoned: false,
        })
    }

    #[inline]
    pub const fn n(&self) -> u32 {
        self.n
    }

    #[inline]
    pub const fn t(&self) -> u32 {
        self.t
    }

    #[inline]
    pub const fn f(&self) -> u32 {
        self.f
    }

    #[inline]
    pub const fn q(&self) -> u32 {
        self.q
    }

    #[inline]
    pub const fn global_liveness_mode(&self) -> bool {
        self.global_liveness_mode
    }

    #[inline]
    pub const fn next_epoch(&self) -> u64 {
        self.next_epoch
    }

    #[inline]
    pub const fn max_jump_window(&self) -> u64 {
        self.max_jump_window
    }

    #[inline]
    pub const fn phase(&self) -> BeltQuorumPhase {
        self.phase
    }

    #[inline]
    pub const fn has_bound_epoch(&self) -> bool {
        self.has_bound_epoch
    }

    #[inline]
    pub const fn bound_epoch(&self) -> u64 {
        self.bound_epoch
    }

    #[inline]
    pub const fn bound_msg_tag(&self) -> [u8; 32] {
        self.bound_msg_tag
    }

    #[inline]
    pub const fn ack_count(&self) -> u32 {
        self.ack_count
    }

    #[inline]
    pub const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Bind a fresh epoch (`next_epoch <= proposed_epoch <= next_epoch + max_jump_window`) or
    /// idempotently retry the currently bound `(bound_epoch, bound_msg_tag)`.
    /// Permanently latches `poisoned = true` on WAL failure or conflicting `(epoch, msg_tag)`.
    pub fn propose_or_retry_epoch(
        self,
        proposed_epoch: u64,
        msg_tag: [u8; 32],
        wal_sync_ok: bool,
    ) -> (BeltQuorumCore, Result<(), PantsGuardError>) {
        if self.poisoned || matches!(self.phase, BeltQuorumPhase::Poisoned) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::BeltGuardPoisoned),
            );
        }
        if !validate_belt_quorum_config(self.n, self.t, self.f, self.q, self.global_liveness_mode) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::InvalidBeltQuorumConfig),
            );
        }
        if self.has_bound_epoch && self.bound_epoch >= self.next_epoch {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::BeltGuardPoisoned),
            );
        }
        if !wal_sync_ok {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::BeltWalSyncFailed),
            );
        }
        if self.has_bound_epoch && proposed_epoch == self.bound_epoch {
            if !ct_eq_bytes32(&self.bound_msg_tag, &msg_tag) {
                return (
                    poison_belt_guard(self),
                    Err(PantsGuardError::ConflictingEpochMsgTag),
                );
            }
            return (self, Ok(()));
        }
        if proposed_epoch < self.next_epoch {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::StaleEpochBelowNext),
            );
        }
        if proposed_epoch - self.next_epoch > self.max_jump_window {
            return (self, Err(PantsGuardError::EpochJumpWindowExceeded));
        }
        if proposed_epoch == u64::MAX {
            return (self, Err(PantsGuardError::BeltEpochExhausted));
        }
        let next = BeltQuorumCore {
            n: self.n,
            t: self.t,
            f: self.f,
            q: self.q,
            global_liveness_mode: self.global_liveness_mode,
            next_epoch: proposed_epoch + 1,
            max_jump_window: self.max_jump_window,
            phase: BeltQuorumPhase::EpochBoundPendingQuorum,
            has_bound_epoch: true,
            bound_epoch: proposed_epoch,
            bound_msg_tag: msg_tag,
            ack_count: 0,
            poisoned: false,
        };
        (next, Ok(()))
    }

    /// Record one verified custodian acknowledgment for `(ack_epoch, ack_msg_tag)`.
    /// Permanently latches `poisoned = true` on conflicting `ack_msg_tag` for `bound_epoch`.
    pub fn record_custodian_ack(
        self,
        ack_epoch: u64,
        ack_msg_tag: [u8; 32],
    ) -> (BeltQuorumCore, Result<u32, PantsGuardError>) {
        if self.poisoned || matches!(self.phase, BeltQuorumPhase::Poisoned) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::BeltGuardPoisoned),
            );
        }
        if !validate_belt_quorum_config(self.n, self.t, self.f, self.q, self.global_liveness_mode) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::InvalidBeltQuorumConfig),
            );
        }
        if self.has_bound_epoch && self.bound_epoch >= self.next_epoch {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::BeltGuardPoisoned),
            );
        }
        if !self.has_bound_epoch {
            return (self, Err(PantsGuardError::NoEpochBound));
        }
        if ack_epoch != self.bound_epoch {
            return (self, Err(PantsGuardError::EpochMismatch));
        }
        if !ct_eq_bytes32(&self.bound_msg_tag, &ack_msg_tag) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::ConflictingEpochMsgTag),
            );
        }
        if self.ack_count >= self.n {
            return (self, Err(PantsGuardError::AckCountExceedsCommittee));
        }
        let next_acks = self.ack_count + 1;
        let next = BeltQuorumCore {
            n: self.n,
            t: self.t,
            f: self.f,
            q: self.q,
            global_liveness_mode: self.global_liveness_mode,
            next_epoch: self.next_epoch,
            max_jump_window: self.max_jump_window,
            phase: self.phase,
            has_bound_epoch: true,
            bound_epoch: self.bound_epoch,
            bound_msg_tag: self.bound_msg_tag,
            ack_count: next_acks,
            poisoned: false,
        };
        (next, Ok(next_acks))
    }

    /// Transition to `SharesAuthorized` strictly when `!poisoned`, config is valid (`2 * q > n + f`),
    /// `(req_epoch, req_msg_tag)` matches the bound record, and `ack_count >= q`.
    pub fn authorize_shares(
        self,
        req_epoch: u64,
        req_msg_tag: [u8; 32],
    ) -> (
        BeltQuorumCore,
        Result<BeltAuthorizationGrant, PantsGuardError>,
    ) {
        if self.poisoned || matches!(self.phase, BeltQuorumPhase::Poisoned) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::BeltGuardPoisoned),
            );
        }
        if !validate_belt_quorum_config(self.n, self.t, self.f, self.q, self.global_liveness_mode) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::InvalidBeltQuorumConfig),
            );
        }
        if self.has_bound_epoch && self.bound_epoch >= self.next_epoch {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::BeltGuardPoisoned),
            );
        }
        if !self.has_bound_epoch {
            return (self, Err(PantsGuardError::NoEpochBound));
        }
        if req_epoch != self.bound_epoch {
            return (self, Err(PantsGuardError::EpochMismatch));
        }
        if !ct_eq_bytes32(&self.bound_msg_tag, &req_msg_tag) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::ConflictingEpochMsgTag),
            );
        }
        if self.ack_count < self.q {
            return (self, Err(PantsGuardError::InsufficientQuorumAcks));
        }
        if matches!(self.phase, BeltQuorumPhase::SharesAuthorized) {
            return (self, Err(PantsGuardError::SharesAlreadyAuthorized));
        }
        let grant = BeltAuthorizationGrant {
            authorized_epoch: self.bound_epoch,
            msg_tag: self.bound_msg_tag,
            certified_acks: self.ack_count,
        };
        let next = BeltQuorumCore {
            n: self.n,
            t: self.t,
            f: self.f,
            q: self.q,
            global_liveness_mode: self.global_liveness_mode,
            next_epoch: self.next_epoch,
            max_jump_window: self.max_jump_window,
            phase: BeltQuorumPhase::SharesAuthorized,
            has_bound_epoch: true,
            bound_epoch: self.bound_epoch,
            bound_msg_tag: self.bound_msg_tag,
            ack_count: self.ack_count,
            poisoned: false,
        };
        (next, Ok(grant))
    }

    /// Unified affine transition function dispatching any safe-Rust `BeltQuorumCoreInput`.
    pub fn step(
        self,
        input: BeltQuorumCoreInput,
    ) -> (
        BeltQuorumCore,
        Result<BeltQuorumCoreOutput, PantsGuardError>,
    ) {
        match input {
            BeltQuorumCoreInput::ProposeOrRetryEpoch {
                proposed_epoch,
                msg_tag,
                wal_sync_ok,
            } => {
                let (next, res) = self.propose_or_retry_epoch(proposed_epoch, msg_tag, wal_sync_ok);
                match res {
                    Ok(()) => (next, Ok(BeltQuorumCoreOutput::EpochBound)),
                    Err(e) => (next, Err(e)),
                }
            }
            BeltQuorumCoreInput::RecordCustodianAck {
                ack_epoch,
                ack_msg_tag,
            } => {
                let (next, res) = self.record_custodian_ack(ack_epoch, ack_msg_tag);
                match res {
                    Ok(c) => (next, Ok(BeltQuorumCoreOutput::AckRecorded(c))),
                    Err(e) => (next, Err(e)),
                }
            }
            BeltQuorumCoreInput::AuthorizeShares {
                req_epoch,
                req_msg_tag,
            } => {
                let (next, res) = self.authorize_shares(req_epoch, req_msg_tag);
                match res {
                    Ok(g) => (next, Ok(BeltQuorumCoreOutput::SharesAuthorized(g))),
                    Err(e) => (next, Err(e)),
                }
            }
        }
    }
}

// ============================================================================
// 2. `VerifiedWotsC256Guard` (256-Bit `WOTS+C`: `w = 4, chains = 128, sum = 192`)
// ============================================================================

/// Extract base-4 digit `chain_idx in 0..128` (`0..=3`) from big-endian 2-bit pairs of `digest[chain_idx / 4]`.
#[inline]
pub const fn wotsc256_extract_digit(digest: &[u8; 32], chain_idx: usize) -> u8 {
    let b = digest[chain_idx / 4];
    match chain_idx % 4 {
        0 => (b >> 6) & 0x03,
        1 => (b >> 4) & 0x03,
        2 => (b >> 2) & 0x03,
        _ => b & 0x03,
    }
}

/// Extract all `128` base-4 digits (`0..=3`) from a 32-byte `WOTS+C` digest.
pub fn verified_wotsc256_extract_digits(digest: &[u8; 32]) -> [u8; 128] {
    let mut digits = [0u8; 128];
    let mut i: usize = 0;
    while i < WOTSC256_CHAINS {
        digits[i] = wotsc256_extract_digit(digest, i);
        i += 1;
    }
    digits
}

/// Extract `128` base-4 digits (`0..=3`) from `digest` and verify exact constant sum `sum == 192`.
pub fn verified_wotsc256_verify_sum(digest: &[u8; 32]) -> bool {
    let mut sum: u32 = 0;
    let mut i: usize = 0;
    while i < WOTSC256_CHAINS {
        let d = wotsc256_extract_digit(digest, i) as u32;
        if sum > 0xFFFF_FFFFu32 - d {
            return false;
        }
        sum += d;
        i += 1;
    }
    sum == WOTSC256_TARGET_SUM
}

/// Non-`Clone` validated 256-bit `WOTS+C` codeword capability with private fields.
pub struct VerifiedWotsC256Guard {
    validated_digest: [u8; 32],
    digits: [u8; 128],
    verified_sum: u32,
}

impl VerifiedWotsC256Guard {
    /// Construct a `VerifiedWotsC256Guard` iff the 128 base-4 digits of `digest` sum to `192`.
    pub fn from_digest_verified(
        digest: [u8; 32],
    ) -> Result<VerifiedWotsC256Guard, PantsGuardError> {
        if !verified_wotsc256_verify_sum(&digest) {
            return Err(PantsGuardError::InvalidWotsC256TargetSum);
        }
        let digits = verified_wotsc256_extract_digits(&digest);
        Ok(VerifiedWotsC256Guard {
            validated_digest: digest,
            digits,
            verified_sum: WOTSC256_TARGET_SUM,
        })
    }

    #[inline]
    pub const fn validated_digest(&self) -> [u8; 32] {
        self.validated_digest
    }

    #[inline]
    pub const fn digits(&self) -> [u8; 128] {
        self.digits
    }

    #[inline]
    pub const fn verified_sum(&self) -> u32 {
        self.verified_sum
    }

    #[inline]
    pub const fn digit_at(&self, chain_idx: usize) -> Option<u8> {
        if chain_idx >= WOTSC256_CHAINS {
            None
        } else {
            Some(self.digits[chain_idx])
        }
    }
}

// ============================================================================
// 3. `VerifiedRssPoisonLatch` (Sticky Terminal Verification-Failure Latch)
// ============================================================================

/// Capability token returned ONLY when `VerifiedRssPoisonLatch::authorize_open` succeeds.
#[derive(Debug, PartialEq, Eq)]
pub struct RssOpenPermit {
    verified_clean: bool,
}

/// Observable input event for multi-turn stepping of `VerifiedRssPoisonLatch`.
#[derive(Clone, Copy, Debug)]
pub enum RssLatchStepInput {
    StageRelations { count: u64 },
    RecordCheckResult { check_ok: bool },
    AuthorizeOpen,
}

/// Observable output emitted by a successful `VerifiedRssPoisonLatch` transition.
#[derive(Debug, PartialEq, Eq)]
pub enum RssLatchStepOutput {
    RelationsStaged(u64),
    CheckVerified,
    OpenAuthorized(RssOpenPermit),
}

/// Non-`Clone` affine guard modeling `Rss256Engine` verification barrier state with private fields:
/// latches `poisoned = true` BEFORE clearing `pending_relations` on any failed check so a second
/// `record_check_result(true)` on `pending_relations == 0` can never re-enable `authorize_open()`.
pub struct VerifiedRssPoisonLatch {
    pending_relations: u64,
    unverified: bool,
    poisoned: bool,
}

#[inline]
const fn poison_rss_latch() -> VerifiedRssPoisonLatch {
    VerifiedRssPoisonLatch {
        pending_relations: 0,
        unverified: true,
        poisoned: true,
    }
}

impl VerifiedRssPoisonLatch {
    /// Initialize a clean `Rss256Engine` verification latch (`pending_relations = 0, unverified = false, poisoned = false`).
    #[inline]
    pub const fn new_clean() -> VerifiedRssPoisonLatch {
        VerifiedRssPoisonLatch {
            pending_relations: 0,
            unverified: false,
            poisoned: false,
        }
    }

    #[inline]
    pub const fn pending_relations(&self) -> u64 {
        self.pending_relations
    }

    #[inline]
    pub const fn is_unverified(&self) -> bool {
        self.unverified
    }

    #[inline]
    pub const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Stage `count > 0` unverified multiplication/opening relation words, setting `unverified = true`.
    pub fn stage_relations(
        self,
        count: u64,
    ) -> (VerifiedRssPoisonLatch, Result<u64, PantsGuardError>) {
        if self.poisoned {
            return (poison_rss_latch(), Err(PantsGuardError::RssEnginePoisoned));
        }
        if count == 0 {
            return (self, Err(PantsGuardError::ZeroRelationBatch));
        }
        if count > u64::MAX - self.pending_relations {
            return (
                poison_rss_latch(),
                Err(PantsGuardError::RelationCounterOverflow),
            );
        }
        let next_pending = self.pending_relations + count;
        let next = VerifiedRssPoisonLatch {
            pending_relations: next_pending,
            unverified: true,
            poisoned: false,
        };
        (next, Ok(next_pending))
    }

    /// Record the outcome of a verification barrier check:
    /// - If already `poisoned`, stays irreversibly `poisoned`.
    /// - If `check_ok == false`, sets `poisoned = true` and `unverified = true` BEFORE clearing
    ///   `pending_relations = 0`, returning `Err(RssVerificationCheckFailed)`.
    /// - If `check_ok == true` (while `!poisoned`), clears `pending_relations = 0` and `unverified = false`.
    pub fn record_check_result(
        self,
        check_ok: bool,
    ) -> (VerifiedRssPoisonLatch, Result<(), PantsGuardError>) {
        if self.poisoned {
            return (poison_rss_latch(), Err(PantsGuardError::RssEnginePoisoned));
        }
        if !check_ok {
            let mut failed = self;
            failed.poisoned = true;
            failed.unverified = true;
            failed.pending_relations = 0;
            return (failed, Err(PantsGuardError::RssVerificationCheckFailed));
        }
        let verified = VerifiedRssPoisonLatch {
            pending_relations: 0,
            unverified: false,
            poisoned: false,
        };
        (verified, Ok(()))
    }

    /// Authorize plane opening strictly when `!poisoned && !unverified && pending_relations == 0`.
    pub fn authorize_open(
        self,
    ) -> (
        VerifiedRssPoisonLatch,
        Result<RssOpenPermit, PantsGuardError>,
    ) {
        if self.poisoned {
            return (poison_rss_latch(), Err(PantsGuardError::RssEnginePoisoned));
        }
        if self.unverified || self.pending_relations != 0 {
            return (self, Err(PantsGuardError::RssOpenBeforeCheck));
        }
        (
            self,
            Ok(RssOpenPermit {
                verified_clean: true,
            }),
        )
    }

    /// Unified multi-turn transition dispatching any safe-Rust `RssLatchStepInput`.
    pub fn step(
        self,
        input: RssLatchStepInput,
    ) -> (
        VerifiedRssPoisonLatch,
        Result<RssLatchStepOutput, PantsGuardError>,
    ) {
        match input {
            RssLatchStepInput::StageRelations { count } => {
                let (next, res) = self.stage_relations(count);
                match res {
                    Ok(n) => (next, Ok(RssLatchStepOutput::RelationsStaged(n))),
                    Err(e) => (next, Err(e)),
                }
            }
            RssLatchStepInput::RecordCheckResult { check_ok } => {
                let (next, res) = self.record_check_result(check_ok);
                match res {
                    Ok(()) => (next, Ok(RssLatchStepOutput::CheckVerified)),
                    Err(e) => (next, Err(e)),
                }
            }
            RssLatchStepInput::AuthorizeOpen => {
                let (next, res) = self.authorize_open();
                match res {
                    Ok(p) => (next, Ok(RssLatchStepOutput::OpenAuthorized(p))),
                    Err(e) => (next, Err(e)),
                }
            }
        }
    }
}

// ============================================================================
// 4. `VerifiedWaistbandRootGuard` (Static Ancestor Child-Root & First-Signed Guard)
// ============================================================================

/// Input request for deriving/opening an ancestor WOTS signature above a cached `Waistband` layer.
#[derive(Clone, Copy)]
pub struct WaistbandDerivationRequest {
    pub req_layer: u32,
    pub req_tree: u64,
    pub req_kp: u32,
    pub cache_pk_tag: [u8; 32],
    pub cache_params_tag: [u8; 32],
    pub recomputed_child_root: [u8; 32],
    pub candidate_ancestor_codeword_tag: [u8; 32],
}

/// Permit emitted only when cache identity tags, static intermediate child root, and first-signed
/// codeword lock all match.
#[derive(Clone, Copy)]
pub struct WaistbandAncestorPermit {
    pub layer: u32,
    pub tree: u64,
    pub kp: u32,
    pub verified_child_root: [u8; 32],
    pub authorized_codeword_tag: [u8; 32],
}

/// Non-`Clone` affine static-ancestor `Waistband` guard with private invariant-bearing fields.
pub struct VerifiedWaistbandRootGuard {
    key_pk_tag: [u8; 32],
    key_params_tag: [u8; 32],
    ancestor_layer: u32,
    ancestor_tree: u64,
    ancestor_kp: u32,
    expected_static_child_root: [u8; 32],
    has_locked_codeword: bool,
    locked_ancestor_codeword_tag: [u8; 32],
    poisoned: bool,
}

#[inline]
const fn poison_waistband_guard(st: VerifiedWaistbandRootGuard) -> VerifiedWaistbandRootGuard {
    VerifiedWaistbandRootGuard {
        key_pk_tag: st.key_pk_tag,
        key_params_tag: st.key_params_tag,
        ancestor_layer: st.ancestor_layer,
        ancestor_tree: st.ancestor_tree,
        ancestor_kp: st.ancestor_kp,
        expected_static_child_root: st.expected_static_child_root,
        has_locked_codeword: st.has_locked_codeword,
        locked_ancestor_codeword_tag: st.locked_ancestor_codeword_tag,
        poisoned: true,
    }
}

impl VerifiedWaistbandRootGuard {
    /// Enroll an unpoisoned static ancestor WOTS coordinate bound to `(key_pk_tag, key_params_tag)`
    /// and its authenticated static child subtree root `expected_static_child_root`.
    #[inline]
    pub const fn new_enrolled(
        key_pk_tag: [u8; 32],
        key_params_tag: [u8; 32],
        ancestor_layer: u32,
        ancestor_tree: u64,
        ancestor_kp: u32,
        expected_static_child_root: [u8; 32],
    ) -> VerifiedWaistbandRootGuard {
        VerifiedWaistbandRootGuard {
            key_pk_tag,
            key_params_tag,
            ancestor_layer,
            ancestor_tree,
            ancestor_kp,
            expected_static_child_root,
            has_locked_codeword: false,
            locked_ancestor_codeword_tag: [0u8; 32],
            poisoned: false,
        }
    }

    #[inline]
    pub const fn key_pk_tag(&self) -> [u8; 32] {
        self.key_pk_tag
    }

    #[inline]
    pub const fn key_params_tag(&self) -> [u8; 32] {
        self.key_params_tag
    }

    #[inline]
    pub const fn ancestor_layer(&self) -> u32 {
        self.ancestor_layer
    }

    #[inline]
    pub const fn ancestor_tree(&self) -> u64 {
        self.ancestor_tree
    }

    #[inline]
    pub const fn ancestor_kp(&self) -> u32 {
        self.ancestor_kp
    }

    #[inline]
    pub const fn expected_static_child_root(&self) -> [u8; 32] {
        self.expected_static_child_root
    }

    #[inline]
    pub const fn has_locked_codeword(&self) -> bool {
        self.has_locked_codeword
    }

    #[inline]
    pub const fn locked_ancestor_codeword_tag(&self) -> [u8; 32] {
        self.locked_ancestor_codeword_tag
    }

    #[inline]
    pub const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Fail-closed ancestor digit-derivation barrier:
    /// verifies `(cache_pk_tag == key_pk_tag) && (cache_params_tag == key_params_tag) &&
    /// (recomputed_child_root == expected_static_child_root)` and enforces single-codeword
    /// locking before returning `Ok(WaistbandAncestorPermit)`.
    pub fn authorize_ancestor_derivation(
        self,
        req: WaistbandDerivationRequest,
    ) -> (
        VerifiedWaistbandRootGuard,
        Result<WaistbandAncestorPermit, PantsGuardError>,
    ) {
        if self.poisoned {
            return (
                poison_waistband_guard(self),
                Err(PantsGuardError::WaistbandGuardPoisoned),
            );
        }
        if req.req_layer != self.ancestor_layer
            || req.req_tree != self.ancestor_tree
            || req.req_kp != self.ancestor_kp
        {
            return (
                poison_waistband_guard(self),
                Err(PantsGuardError::WaistbandAddressMismatch),
            );
        }
        if !ct_eq_bytes32(&req.cache_pk_tag, &self.key_pk_tag) {
            return (
                poison_waistband_guard(self),
                Err(PantsGuardError::WaistbandCachePkMismatch),
            );
        }
        if !ct_eq_bytes32(&req.cache_params_tag, &self.key_params_tag) {
            return (
                poison_waistband_guard(self),
                Err(PantsGuardError::WaistbandCacheParamsMismatch),
            );
        }
        if !ct_eq_bytes32(&req.recomputed_child_root, &self.expected_static_child_root) {
            return (
                poison_waistband_guard(self),
                Err(PantsGuardError::WaistbandChildRootMismatch),
            );
        }
        if self.has_locked_codeword
            && !ct_eq_bytes32(
                &req.candidate_ancestor_codeword_tag,
                &self.locked_ancestor_codeword_tag,
            )
        {
            return (
                poison_waistband_guard(self),
                Err(PantsGuardError::WaistbandCodewordEquivocation),
            );
        }
        let permit = WaistbandAncestorPermit {
            layer: self.ancestor_layer,
            tree: self.ancestor_tree,
            kp: self.ancestor_kp,
            verified_child_root: self.expected_static_child_root,
            authorized_codeword_tag: req.candidate_ancestor_codeword_tag,
        };
        let next = VerifiedWaistbandRootGuard {
            key_pk_tag: self.key_pk_tag,
            key_params_tag: self.key_params_tag,
            ancestor_layer: self.ancestor_layer,
            ancestor_tree: self.ancestor_tree,
            ancestor_kp: self.ancestor_kp,
            expected_static_child_root: self.expected_static_child_root,
            has_locked_codeword: true,
            locked_ancestor_codeword_tag: req.candidate_ancestor_codeword_tag,
            poisoned: false,
        };
        (next, Ok(permit))
    }
}

#[cfg(test)]
mod core_tests {
    use super::*;
    #[test]
    fn belt_core_transitions() {
        // Under-threshold q = t = 2 for (n=5, t=3, f=2): 2*q = 4 <= n + f = 7 -> REJECT
        assert!(!validate_belt_quorum_config(5, 3, 2, 2, false));
        // (n=5, t=3, f=2, q=4): 2*q = 8 > 7, safety-only mode -> ACCEPT; global liveness q <= n-f=3 -> REJECT
        assert!(validate_belt_quorum_config(5, 3, 2, 4, false));
        assert!(!validate_belt_quorum_config(5, 3, 2, 4, true));
        // BFT global-liveness sweet spot (n=7, t=3, f=2, q=5): 2*q = 10 > 9 AND q = 5 <= 7 - 2 = 5 -> ACCEPT
        assert!(validate_belt_quorum_config(7, 3, 2, 5, true));
        // Unanimous 2-of-3 safety mode (n=3, t=2, f=1, q=3): 2*q = 6 > 4 -> ACCEPT
        assert!(validate_belt_quorum_config(3, 2, 1, 3, false));

        match BeltQuorumCore::new_validated(5, 3, 2, 3, false, 10, 4) {
            Ok(_) => panic!("2*q = 6 <= n+f = 7 must be rejected"),
            Err(e) => assert_eq!(e, PantsGuardError::InvalidBeltQuorumConfig),
        }

        let g0 = match BeltQuorumCore::new_validated(7, 3, 2, 5, true, 10, 4) {
            Ok(g) => g,
            Err(e) => panic!("valid BFT config rejected: {e:?}"),
        };
        assert_eq!(g0.n(), 7);
        assert_eq!(g0.t(), 3);
        assert_eq!(g0.f(), 2);
        assert_eq!(g0.q(), 5);
        assert!(g0.global_liveness_mode());
        assert_eq!(g0.next_epoch(), 10);
        assert_eq!(g0.max_jump_window(), 4);
        assert_eq!(g0.phase(), BeltQuorumPhase::Idle);
        assert!(!g0.has_bound_epoch());
        assert!(!g0.is_poisoned());

        // Jump window exceeded (15 > 10 + 4) refuses cleanly without poisoning
        let msg_a = [0x41u8; 32];
        let msg_b = [0x42u8; 32];
        let (g1, jump_err) = g0.propose_or_retry_epoch(15, msg_a, true);
        assert_eq!(jump_err, Err(PantsGuardError::EpochJumpWindowExceeded));
        assert!(!g1.is_poisoned());

        // Bounded jump to epoch 12 (10 <= 12 <= 14) binds epoch 12 and advances next_epoch = 13
        let (g2, bind_ok) = g1.propose_or_retry_epoch(12, msg_a, true);
        assert_eq!(bind_ok, Ok(()));
        assert_eq!(g2.phase(), BeltQuorumPhase::EpochBoundPendingQuorum);
        assert!(g2.has_bound_epoch());
        assert_eq!(g2.bound_epoch(), 12);
        assert_eq!(g2.bound_msg_tag(), msg_a);
        assert_eq!(g2.next_epoch(), 13);

        // Idempotent retry on (12, msg_a) succeeds without resetting acks
        let (mut g_cur, ack1) = g2.record_custodian_ack(12, msg_a);
        assert_eq!(ack1, Ok(1));
        let (g_retry, retry_ok) = g_cur.propose_or_retry_epoch(12, msg_a, true);
        assert_eq!(retry_ok, Ok(()));
        assert_eq!(g_retry.ack_count(), 1);
        g_cur = g_retry;

        // Insufficient acks (< q = 5) refuses authorization!
        for expected in 2..=4 {
            let (gn, r) = g_cur.record_custodian_ack(12, msg_a);
            assert_eq!(r, Ok(expected));
            g_cur = gn;
        }
        let (g_under, under_err) = g_cur.authorize_shares(12, msg_a);
        assert_eq!(
            under_err.err(),
            Some(PantsGuardError::InsufficientQuorumAcks)
        );
        assert_eq!(g_under.phase(), BeltQuorumPhase::EpochBoundPendingQuorum);

        // 5th ack reaches q = 5 -> SharesAuthorized!
        let (g5, ack5) = g_under.record_custodian_ack(12, msg_a);
        assert_eq!(ack5, Ok(5));
        let (g_auth, auth_res) = g5.step(BeltQuorumCoreInput::AuthorizeShares {
            req_epoch: 12,
            req_msg_tag: msg_a,
        });
        match auth_res {
            Ok(BeltQuorumCoreOutput::SharesAuthorized(grant)) => {
                assert_eq!(grant.authorized_epoch, 12);
                assert_eq!(grant.msg_tag, msg_a);
                assert_eq!(grant.certified_acks, 5);
            }
            other => panic!("expected SharesAuthorized grant, got {:?}", other.err()),
        }
        assert_eq!(g_auth.phase(), BeltQuorumPhase::SharesAuthorized);
        let (g_auth, repeated) = g_auth.authorize_shares(12, msg_a);
        assert_eq!(repeated.err(), Some(PantsGuardError::SharesAlreadyAuthorized));
        let (g_auth, retry) = g_auth.propose_or_retry_epoch(12, msg_a, true);
        assert!(retry.is_ok());
        let (g_auth, repeated) = g_auth.authorize_shares(12, msg_a);
        assert_eq!(repeated.err(), Some(PantsGuardError::SharesAlreadyAuthorized));

        // Conflicting msg_tag on bound epoch 12 permanently poisons the guard!
        let (g_eqv, eqv_err) = g_auth.propose_or_retry_epoch(12, msg_b, true);
        assert_eq!(eqv_err, Err(PantsGuardError::ConflictingEpochMsgTag));
        assert!(g_eqv.is_poisoned());
        assert_eq!(g_eqv.phase(), BeltQuorumPhase::Poisoned);
        let (_g_dead, after_poison) = g_eqv.authorize_shares(12, msg_a);
        assert_eq!(after_poison.err(), Some(PantsGuardError::BeltGuardPoisoned));

        // WAL sync failure also permanently poisons the guard!
        let gw0 = match BeltQuorumCore::new_validated(3, 2, 1, 3, false, 0, 2) {
            Ok(g) => g,
            Err(_) => unreachable!(),
        };
        let (gw1, wal_err) = gw0.propose_or_retry_epoch(0, msg_a, false);
        assert_eq!(wal_err, Err(PantsGuardError::BeltWalSyncFailed));
        assert!(gw1.is_poisoned());
        let (_gw2, retry_after_wal) = gw1.propose_or_retry_epoch(0, msg_a, true);
        assert_eq!(retry_after_wal, Err(PantsGuardError::BeltGuardPoisoned));
    }
}
