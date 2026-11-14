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
    if require_global_liveness && q > n - f {
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
            return (poison_belt_guard(self), Err(PantsGuardError::BeltGuardPoisoned));
        }
        if !validate_belt_quorum_config(
            self.n,
            self.t,
            self.f,
            self.q,
            self.global_liveness_mode,
        ) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::InvalidBeltQuorumConfig),
            );
        }
        if self.has_bound_epoch && self.bound_epoch >= self.next_epoch {
            return (poison_belt_guard(self), Err(PantsGuardError::BeltGuardPoisoned));
        }
        if !wal_sync_ok {
            return (poison_belt_guard(self), Err(PantsGuardError::BeltWalSyncFailed));
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
            return (poison_belt_guard(self), Err(PantsGuardError::BeltGuardPoisoned));
        }
        if !validate_belt_quorum_config(
            self.n,
            self.t,
            self.f,
            self.q,
            self.global_liveness_mode,
        ) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::InvalidBeltQuorumConfig),
            );
        }
        if self.has_bound_epoch && self.bound_epoch >= self.next_epoch {
            return (poison_belt_guard(self), Err(PantsGuardError::BeltGuardPoisoned));
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
    ) -> (BeltQuorumCore, Result<BeltAuthorizationGrant, PantsGuardError>) {
        if self.poisoned || matches!(self.phase, BeltQuorumPhase::Poisoned) {
            return (poison_belt_guard(self), Err(PantsGuardError::BeltGuardPoisoned));
        }
        if !validate_belt_quorum_config(
            self.n,
            self.t,
            self.f,
            self.q,
            self.global_liveness_mode,
        ) {
            return (
                poison_belt_guard(self),
                Err(PantsGuardError::InvalidBeltQuorumConfig),
            );
        }
        if self.has_bound_epoch && self.bound_epoch >= self.next_epoch {
            return (poison_belt_guard(self), Err(PantsGuardError::BeltGuardPoisoned));
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
    ) -> (BeltQuorumCore, Result<BeltQuorumCoreOutput, PantsGuardError>) {
        match input {
            BeltQuorumCoreInput::ProposeOrRetryEpoch {
                proposed_epoch,
                msg_tag,
                wal_sync_ok,
            } => {
                let (next, res) =
                    self.propose_or_retry_epoch(proposed_epoch, msg_tag, wal_sync_ok);
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
