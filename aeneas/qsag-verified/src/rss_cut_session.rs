//! 2-of-3 RSS / SPDZ Cut-the-Hash Anti-DFA Per-Party Protocol State Machine.
//!
//! Enforces the strict four-phase protocol progression:
//! `Round1MaskCommitted -> Round2ChiEvaluated -> Round3ConsistencyVerified -> CutOpened`
//! on a non-`Clone` affine session handle (`RssCutGateSession`). Any out-of-order call,
//! session-ID mismatch, Round-1 mask-commitment mismatch, or non-zero SPDZ / BBCGGI19
//! consistency residual irreversibly poisons the session and zeroes its candidate cut bytes,
//! ensuring unverified Keccak-`chi` cut shares can never be extracted in safe Rust.

use crate::keccak::Shake256Sponge;
use crate::tower::ct_eq_bytes32;

/// Protocol phase of a per-party 2-of-3 RSS Cut-the-Hash gate session.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RssCutPhase {
    Round1MaskCommitted,
    Round2ChiEvaluated,
    Round3ConsistencyVerified,
    CutOpened,
    Poisoned,
}

/// Explicit refusal reasons emitted by `RssCutGateSession` transitions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RssCutError {
    SessionPoisoned,
    SessionIdMismatch,
    InvalidPhaseTransition,
    MaskCommitmentMismatch,
    ConsistencyCheckFailed,
}

/// Observable input event for unified multi-turn stepping of `RssCutGateSession`.
#[derive(Clone, Copy)]
pub enum RssCutStepInput {
    AdvanceRound2Chi {
        req_session_id: [u8; 32],
        recomputed_mask_commitment: [u8; 32],
        chi_cut_candidate: [u8; 32],
    },
    AdvanceRound3VerifyConsistency {
        req_session_id: [u8; 32],
        spdz_mac_residual_lo: u128,
        spdz_mac_residual_hi: u128,
        bbcggi_dzk_residual: u64,
    },
    OpenVerifiedCut {
        req_session_id: [u8; 32],
    },
}

/// Observable output emitted by a successful `RssCutGateSession` transition.
#[derive(Clone, Copy)]
pub enum RssCutStepOutput {
    Round2Ready,
    Round3Verified,
    CutReleased([u8; 32]),
}

/// Non-`Clone` affine per-party state machine gating Cut-the-Hash boundary opening
/// behind Round-1 mask commitment binding and Round-3 SPDZ + BBCGGI19 zero-residual checks.
///
/// `phase`, `consistency_verified` and `poisoned` are private: outside this module they
/// change only through the transition methods, so a caller cannot mark a session verified
/// or clear its poison by assignment. Read them through [`RssCutGateSession::phase`],
/// [`RssCutGateSession::is_consistency_verified`] and [`RssCutGateSession::is_poisoned`].
///
/// External callers cannot reset the authorization state.
/// ```compile_fail,E0616
/// use qsag_verified::RssCutGateSession;
/// let mut guard = RssCutGateSession::new_round1_committed([0; 32], [0; 32]);
/// guard.mask_commitment = [0; 32];
/// ```
pub struct RssCutGateSession {
    session_id: [u8; 32],
    phase: RssCutPhase,
    mask_commitment: [u8; 32],
    candidate_cut_bytes: [u8; 32],
    consistency_verified: bool,
    poisoned: bool,
}

/// Domain-separated SHAKE256 commitment to a party's Round-1 cut mask share.
pub fn compute_rss_mask_commitment(
    session_id: &[u8; 32],
    party_id: u8,
    mask_bytes: &[u8; 32],
    salt_nonce: &[u8; 32],
) -> [u8; 32] {
    let domain_tag: [u8; 16] = [
        0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x53, 0x53, // "QSAG.RSS"
        0x43, 0x55, 0x54, 0x2E, 0x4D, 0x53, 0x4B, 0x31, // "CUT.MSK1"
    ];
    let party_buf: [u8; 1] = [party_id];
    let mut sp = Shake256Sponge::new_shake256();
    sp.absorb(&domain_tag);
    sp.absorb(session_id);
    sp.absorb(&party_buf);
    sp.absorb(mask_bytes);
    sp.absorb(salt_nonce);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

#[inline]
const fn poison_rss_cut_session(
    session_id: [u8; 32],
    mask_commitment: [u8; 32],
) -> RssCutGateSession {
    RssCutGateSession {
        session_id,
        phase: RssCutPhase::Poisoned,
        mask_commitment,
        candidate_cut_bytes: [0u8; 32],
        consistency_verified: false,
        poisoned: true,
    }
}

impl RssCutGateSession {
    /// Read-only state observation.
    pub const fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    /// Read-only state observation.
    pub const fn mask_commitment(&self) -> [u8; 32] {
        self.mask_commitment
    }

    /// Initialize a fresh Round-1 session bound to `session_id` and `mask_commitment`.
    #[inline]
    pub const fn new_round1_committed(
        session_id: [u8; 32],
        mask_commitment: [u8; 32],
    ) -> RssCutGateSession {
        RssCutGateSession {
            session_id,
            phase: RssCutPhase::Round1MaskCommitted,
            mask_commitment,
            candidate_cut_bytes: [0u8; 32],
            consistency_verified: false,
            poisoned: false,
        }
    }

    /// Inspect whether the session has been irreversibly poisoned.
    #[inline]
    pub const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Current protocol phase.
    #[inline]
    pub const fn phase(&self) -> RssCutPhase {
        self.phase
    }

    /// True once the Round-3 consistency checks have accepted this session.
    #[inline]
    pub const fn is_consistency_verified(&self) -> bool {
        self.consistency_verified
    }

    /// Round 1 -> Round 2 transition: verify session binding and Round-1 mask commitment,
    /// recording the masked Keccak-`chi` cut candidate while keeping `consistency_verified = false`.
    pub fn advance_round2_chi(
        self,
        req_session_id: [u8; 32],
        recomputed_mask_commitment: [u8; 32],
        chi_cut_candidate: [u8; 32],
    ) -> (RssCutGateSession, Result<(), RssCutError>) {
        if self.poisoned {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::SessionPoisoned),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &req_session_id) {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::SessionIdMismatch),
            );
        }
        match self.phase {
            RssCutPhase::Round1MaskCommitted => {}
            _ => {
                return (
                    poison_rss_cut_session(self.session_id, self.mask_commitment),
                    Err(RssCutError::InvalidPhaseTransition),
                );
            }
        }
        if !ct_eq_bytes32(&self.mask_commitment, &recomputed_mask_commitment) {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::MaskCommitmentMismatch),
            );
        }
        let next = RssCutGateSession {
            session_id: self.session_id,
            phase: RssCutPhase::Round2ChiEvaluated,
            mask_commitment: self.mask_commitment,
            candidate_cut_bytes: chi_cut_candidate,
            consistency_verified: false,
            poisoned: false,
        };
        (next, Ok(()))
    }

    /// Round 2 -> Round 3 transition: enforce zero SPDZ 2-lane MAC residuals and zero
    /// BBCGGI19 distributed zero-knowledge residual before unlocking cut release.
    /// Any non-zero residual poisons the session and wipes `candidate_cut_bytes`.
    pub fn advance_round3_verify_consistency(
        self,
        req_session_id: [u8; 32],
        spdz_mac_residual_lo: u128,
        spdz_mac_residual_hi: u128,
        bbcggi_dzk_residual: u64,
    ) -> (RssCutGateSession, Result<(), RssCutError>) {
        if self.poisoned {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::SessionPoisoned),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &req_session_id) {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::SessionIdMismatch),
            );
        }
        match self.phase {
            RssCutPhase::Round2ChiEvaluated => {}
            _ => {
                return (
                    poison_rss_cut_session(self.session_id, self.mask_commitment),
                    Err(RssCutError::InvalidPhaseTransition),
                );
            }
        }
        if spdz_mac_residual_lo != 0 || spdz_mac_residual_hi != 0 || bbcggi_dzk_residual != 0 {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::ConsistencyCheckFailed),
            );
        }
        let next = RssCutGateSession {
            session_id: self.session_id,
            phase: RssCutPhase::Round3ConsistencyVerified,
            mask_commitment: self.mask_commitment,
            candidate_cut_bytes: self.candidate_cut_bytes,
            consistency_verified: true,
            poisoned: false,
        };
        (next, Ok(()))
    }

    /// Round 3 -> CutOpened transition: release the verified cut bytes at most once,
    /// wiping the internal buffer and sealing the session in `CutOpened`.
    pub fn open_verified_cut(
        self,
        req_session_id: [u8; 32],
    ) -> (RssCutGateSession, Result<[u8; 32], RssCutError>) {
        if self.poisoned {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::SessionPoisoned),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &req_session_id) {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::SessionIdMismatch),
            );
        }
        match self.phase {
            RssCutPhase::Round3ConsistencyVerified => {}
            _ => {
                return (
                    poison_rss_cut_session(self.session_id, self.mask_commitment),
                    Err(RssCutError::InvalidPhaseTransition),
                );
            }
        }
        if !self.consistency_verified {
            return (
                poison_rss_cut_session(self.session_id, self.mask_commitment),
                Err(RssCutError::ConsistencyCheckFailed),
            );
        }
        let released = self.candidate_cut_bytes;
        let next = RssCutGateSession {
            session_id: self.session_id,
            phase: RssCutPhase::CutOpened,
            mask_commitment: self.mask_commitment,
            candidate_cut_bytes: [0u8; 32],
            consistency_verified: true,
            poisoned: false,
        };
        (next, Ok(released))
    }

    /// Unified affine transition function dispatching a single `RssCutStepInput` event.
    pub fn step(
        self,
        input: RssCutStepInput,
    ) -> (RssCutGateSession, Result<RssCutStepOutput, RssCutError>) {
        match input {
            RssCutStepInput::AdvanceRound2Chi {
                req_session_id,
                recomputed_mask_commitment,
                chi_cut_candidate,
            } => {
                let (next, res) = self.advance_round2_chi(
                    req_session_id,
                    recomputed_mask_commitment,
                    chi_cut_candidate,
                );
                match res {
                    Ok(()) => (next, Ok(RssCutStepOutput::Round2Ready)),
                    Err(e) => (next, Err(e)),
                }
            }
            RssCutStepInput::AdvanceRound3VerifyConsistency {
                req_session_id,
                spdz_mac_residual_lo,
                spdz_mac_residual_hi,
                bbcggi_dzk_residual,
            } => {
                let (next, res) = self.advance_round3_verify_consistency(
                    req_session_id,
                    spdz_mac_residual_lo,
                    spdz_mac_residual_hi,
                    bbcggi_dzk_residual,
                );
                match res {
                    Ok(()) => (next, Ok(RssCutStepOutput::Round3Verified)),
                    Err(e) => (next, Err(e)),
                }
            }
            RssCutStepInput::OpenVerifiedCut { req_session_id } => {
                let (next, res) = self.open_verified_cut(req_session_id);
                match res {
                    Ok(cut) => (next, Ok(RssCutStepOutput::CutReleased(cut))),
                    Err(e) => (next, Err(e)),
                }
            }
        }
    }
}
