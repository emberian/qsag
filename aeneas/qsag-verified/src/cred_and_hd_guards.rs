//! `qsag-cred` & `qsag-hd` Threshold Protocol Security Guards:
//!
//! 1. `MlDsaReleaseGate` (non-`Clone`): holds a masked partial `ML-DSA` response `z_share`
//!    privately and releases it ONLY when `(z_norm_ok && r0_norm_ok && w1_match && u_com_bound)`
//!    all hold (`P0-06`), wiping `z_share` and aborting on any rejection!
//! 2. `toprf_majority_of_3_goldilocks(s0, s1, s2) -> Option<(u64, Option<u8>)>`:
//!    branch-clean 2-of-3 canonical Goldilocks replica majority decoder + faulty-party index
//!    pinpointing used in 2-of-5 Poseidon2 TOPRF evaluation.
//! 3. `HdCommittedZeroTest` (non-`Clone`): freezes peer residual commitments strictly before
//!    opening the local residual and irreversibly quarantines the derivation family on mismatch (`P0-10`).

use crate::goldilocks::GOLDILOCKS_PRIME;
use crate::tower::ct_eq_bytes32;

/// NIST FIPS 204 prime modulus `q = 8_380_417` (`2^23 - 2^13 + 1`).
pub const MLDSA_Q: u32 = 8_380_417;

/// NIST FIPS 204 ML-DSA-44 `gamma_1 - beta = 131_072 - 78 = 130_994` infinity-norm bound on `z`.
pub const MLDSA44_Z_NORM_BOUND: u32 = 130_994;

/// NIST FIPS 204 ML-DSA-44 `gamma_2 - beta = 95_232 - 78 = 95_154` low-bits bound on `r_0`.
pub const MLDSA44_R0_NORM_BOUND: u32 = 95_154;

/// NIST FIPS 204 ML-DSA-65 `gamma_1 - beta = 524_288 - 196 = 524_092` infinity-norm bound on `z`.
pub const MLDSA65_Z_NORM_BOUND: u32 = 524_092;

/// NIST FIPS 204 ML-DSA-65 `gamma_2 - beta = 261_888 - 196 = 261_692` low-bits bound on `r_0`.
pub const MLDSA65_R0_NORM_BOUND: u32 = 261_692;

/// Explicit refusal reasons for `MlDsaReleaseGate` and `HdCommittedZeroTest`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CredHdGuardError {
    GateAbortedOrReleased,
    SessionIdMismatch,
    AttemptMismatch,
    RejectionSamplingBarrierFailed,
    FamilyQuarantined,
    InvalidHdPhaseTransition,
    PeerCommitmentMismatchQuarantined,
    InvalidModulusOrResidualQuarantined,
    HdZeroTestMismatchQuarantined,
}

/// NIST FIPS 204 `RejBoundedPoly` (`eta = 2`) nibble rejection mapper (`b < 15 -> (2 - (b mod 5)) mod q`):
/// maps each accepted nibble `b in 0..15` with exact 3-to-1 multiplicity onto `{2, 1, 0, q - 1, q - 2}`
/// and rejects `b >= 15` (`None`).
#[inline]
pub const fn mldsa44_sample_eta2_nibble_mod_q(nibble: u8) -> Option<u32> {
    if nibble >= 15 {
        return None;
    }
    let rem = (nibble % 5) as u32;
    if rem <= 2 {
        Some(2 - rem)
    } else {
        Some(MLDSA_Q + 2 - rem)
    }
}

/// Evaluate NIST FIPS 204 ML-DSA-44 rejection-sampling norm predicates `(||z||_inf < gamma_1 - beta, ||r_0||_inf < gamma_2 - beta)`.
#[inline]
pub const fn check_mldsa44_norm_bounds(z_inf_norm: u32, r0_inf_norm: u32) -> (bool, bool) {
    let z_ok = if z_inf_norm < MLDSA44_Z_NORM_BOUND {
        true
    } else {
        false
    };
    let r0_ok = if r0_inf_norm < MLDSA44_R0_NORM_BOUND {
        true
    } else {
        false
    };
    (z_ok, r0_ok)
}

/// Evaluate NIST FIPS 204 ML-DSA-65 rejection-sampling norm predicates `(||z||_inf < gamma_1 - beta, ||r_0||_inf < gamma_2 - beta)`.
#[inline]
pub const fn check_mldsa65_norm_bounds(z_inf_norm: u32, r0_inf_norm: u32) -> (bool, bool) {
    let z_ok = if z_inf_norm < MLDSA65_Z_NORM_BOUND {
        true
    } else {
        false
    };
    let r0_ok = if r0_inf_norm < MLDSA65_R0_NORM_BOUND {
        true
    } else {
        false
    };
    (z_ok, r0_ok)
}

/// Conjunction of Round-3 threshold ML-DSA response release barrier checks (`P0-06`).
#[derive(Clone, Copy)]
pub struct MlDsaBarrierChecks {
    pub req_session_id: [u8; 32],
    pub req_attempt: u32,
    pub z_norm_ok: bool,
    pub r0_norm_ok: bool,
    pub w1_match: bool,
    pub u_com_bound: bool,
}

/// Non-`Clone` affine release gate holding a party's masked partial `z_share` privately
/// until all four threshold ML-DSA rejection-sampling & commitment checks pass (`P0-06`).
///
/// External callers cannot reset the authorization state.
/// ```compile_fail,E0616
/// use qsag_verified::MlDsaReleaseGate;
/// let mut guard = MlDsaReleaseGate::new_sealed([0; 32], 0, [0; 32]);
/// guard.released = false;
/// ```
pub struct MlDsaReleaseGate {
    session_id: [u8; 32],
    attempt: u32,
    z_share_masked: [u8; 32],
    released: bool,
    aborted: bool,
}

#[inline]
const fn abort_mldsa_gate(session_id: [u8; 32], attempt: u32) -> MlDsaReleaseGate {
    MlDsaReleaseGate {
        session_id,
        attempt,
        z_share_masked: [0u8; 32],
        released: false,
        aborted: true,
    }
}

impl MlDsaReleaseGate {
    /// Read-only state observation.
    pub const fn session_id(&self) -> [u8; 32] { self.session_id }

    /// Read-only state observation.
    pub const fn attempt(&self) -> u32 { self.attempt }

    /// Read-only state observation.
    pub const fn released(&self) -> bool { self.released }

    /// Read-only state observation.
    pub const fn aborted(&self) -> bool { self.aborted }


    /// Seal a masked partial response `z_share_masked` inside a fresh single-attempt release gate.
    #[inline]
    pub const fn new_sealed(
        session_id: [u8; 32],
        attempt: u32,
        z_share_masked: [u8; 32],
    ) -> MlDsaReleaseGate {
        MlDsaReleaseGate {
            session_id,
            attempt,
            z_share_masked,
            released: false,
            aborted: false,
        }
    }

    /// Release `z_share_masked` if and only if the gate is fresh, `(session_id, attempt)` match,
    /// and `(z_norm_ok && r0_norm_ok && w1_match && u_com_bound)` all hold.
    /// Any failed predicate wipes `z_share_masked` to `[0u8; 32]` and marks `aborted = true`.
    pub fn try_release_z_share(
        self,
        checks: MlDsaBarrierChecks,
    ) -> (MlDsaReleaseGate, Result<[u8; 32], CredHdGuardError>) {
        if self.aborted || self.released {
            return (
                abort_mldsa_gate(self.session_id, self.attempt),
                Err(CredHdGuardError::GateAbortedOrReleased),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &checks.req_session_id) {
            return (
                abort_mldsa_gate(self.session_id, self.attempt),
                Err(CredHdGuardError::SessionIdMismatch),
            );
        }
        if self.attempt != checks.req_attempt {
            return (
                abort_mldsa_gate(self.session_id, self.attempt),
                Err(CredHdGuardError::AttemptMismatch),
            );
        }
        if !(checks.z_norm_ok && checks.r0_norm_ok && checks.w1_match && checks.u_com_bound) {
            return (
                abort_mldsa_gate(self.session_id, self.attempt),
                Err(CredHdGuardError::RejectionSamplingBarrierFailed),
            );
        }
        let out = self.z_share_masked;
        let next = MlDsaReleaseGate {
            session_id: self.session_id,
            attempt: self.attempt,
            z_share_masked: [0u8; 32],
            released: true,
            aborted: false,
        };
        (next, Ok(out))
    }
}

/// Branch-clean 2-of-3 canonical Goldilocks replica agreement & cheater-index pinpointing
/// used across the 3 cross-term holders of each 2-of-5 Poseidon2 TOPRF multiplication gate:
/// - Rejects non-canonical field aliases (`>= GOLDILOCKS_PRIME`) on any agreed value,
/// - Returns `Some((v, None))` when all 3 replicas canonically agree on `v < GOLDILOCKS_PRIME`,
/// - Returns `Some((v, Some(idx)))` (`idx in {0, 1, 2}`) when 2 replicas canonically agree on `v`
///   and replica `idx` deviates (even with a non-canonical `u64 >= GOLDILOCKS_PRIME`),
/// - Returns `None` if no canonical 2-of-3 majority exists.
pub const fn toprf_majority_of_3_goldilocks(
    s0: u64,
    s1: u64,
    s2: u64,
) -> Option<(u64, Option<u8>)> {
    let c0 = if s0 < GOLDILOCKS_PRIME { true } else { false };
    let c1 = if s1 < GOLDILOCKS_PRIME { true } else { false };
    let c2 = if s2 < GOLDILOCKS_PRIME { true } else { false };
    let eq01 = if c0 && c1 {
        if s0 == s1 { true } else { false }
    } else {
        false
    };
    let eq02 = if c0 && c2 {
        if s0 == s2 { true } else { false }
    } else {
        false
    };
    let eq12 = if c1 && c2 {
        if s1 == s2 { true } else { false }
    } else {
        false
    };
    if eq01 && eq02 {
        Some((s0, None))
    } else if eq01 {
        Some((s0, Some(2u8)))
    } else if eq02 {
        Some((s0, Some(1u8)))
    } else if eq12 {
        Some((s1, Some(0u8)))
    } else {
        None
    }
}

/// Phase progression for `qsag-hd` committed zero-test evaluation (`P0-10`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HdZeroTestPhase {
    AwaitPeerCommitment,
    PeerCommitmentFrozen,
    LocalResidualOpened,
    VerifiedZero,
    FamilyQuarantined,
}

/// Non-`Clone` affine committed zero-test gate (`qsag-hd` `P0-10`):
/// freezes the peer's residual commitment strictly before exposing `local_residual` and
/// irreversibly quarantines the derivation family on any commitment or zero-sum mismatch.
pub struct HdCommittedZeroTest {
    session_id: [u8; 32],
    phase: HdZeroTestPhase,
    frozen_peer_commitment: [u8; 32],
    local_residual: u32,
    modulus_q: u32,
    family_quarantined: bool,
}

#[inline]
const fn quarantine_hd_family(
    session_id: [u8; 32],
    frozen_peer_commitment: [u8; 32],
    modulus_q: u32,
) -> HdCommittedZeroTest {
    HdCommittedZeroTest {
        session_id,
        phase: HdZeroTestPhase::FamilyQuarantined,
        frozen_peer_commitment,
        local_residual: 0,
        modulus_q,
        family_quarantined: true,
    }
}

impl HdCommittedZeroTest {
    /// Read-only state observation.
    pub const fn session_id(&self) -> [u8; 32] { self.session_id }

    /// Read-only state observation.
    pub const fn phase(&self) -> HdZeroTestPhase { self.phase }

    /// Read-only state observation.
    pub const fn frozen_peer_commitment(&self) -> [u8; 32] { self.frozen_peer_commitment }

    /// Read-only state observation.
    pub const fn modulus_q(&self) -> u32 { self.modulus_q }

    /// Read-only state observation.
    pub const fn family_quarantined(&self) -> bool { self.family_quarantined }


    /// Initialize a committed zero-test gate holding `local_residual` mod `modulus_q` privately.
    /// Immediately quarantines if `modulus_q == 0` or `local_residual >= modulus_q`.
    #[inline]
    pub const fn new_awaiting_peer_commit(
        session_id: [u8; 32],
        local_residual: u32,
        modulus_q: u32,
    ) -> HdCommittedZeroTest {
        if modulus_q == 0 || local_residual >= modulus_q {
            quarantine_hd_family(session_id, [0u8; 32], modulus_q)
        } else {
            HdCommittedZeroTest {
                session_id,
                phase: HdZeroTestPhase::AwaitPeerCommitment,
                frozen_peer_commitment: [0u8; 32],
                local_residual,
                modulus_q,
                family_quarantined: false,
            }
        }
    }

    /// Phase 1: Freeze `peer_commitment` before any local residual can be opened.
    pub fn freeze_peer_commitment(
        self,
        req_session_id: [u8; 32],
        peer_commitment: [u8; 32],
    ) -> (HdCommittedZeroTest, Result<(), CredHdGuardError>) {
        if self.family_quarantined {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::FamilyQuarantined),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &req_session_id) {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::SessionIdMismatch),
            );
        }
        match self.phase {
            HdZeroTestPhase::AwaitPeerCommitment => {}
            _ => {
                return (
                    quarantine_hd_family(
                        self.session_id,
                        self.frozen_peer_commitment,
                        self.modulus_q,
                    ),
                    Err(CredHdGuardError::InvalidHdPhaseTransition),
                );
            }
        }
        let next = HdCommittedZeroTest {
            session_id: self.session_id,
            phase: HdZeroTestPhase::PeerCommitmentFrozen,
            frozen_peer_commitment: peer_commitment,
            local_residual: self.local_residual,
            modulus_q: self.modulus_q,
            family_quarantined: false,
        };
        (next, Ok(()))
    }

    /// Phase 2: Open `local_residual` strictly AFTER `peer_commitment` has been frozen.
    /// Any attempt to open before freezing quarantines the family and wipes `local_residual`.
    pub fn open_local_residual(
        self,
        req_session_id: [u8; 32],
    ) -> (HdCommittedZeroTest, Result<u32, CredHdGuardError>) {
        if self.family_quarantined {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::FamilyQuarantined),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &req_session_id) {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::SessionIdMismatch),
            );
        }
        match self.phase {
            HdZeroTestPhase::PeerCommitmentFrozen => {}
            _ => {
                return (
                    quarantine_hd_family(
                        self.session_id,
                        self.frozen_peer_commitment,
                        self.modulus_q,
                    ),
                    Err(CredHdGuardError::InvalidHdPhaseTransition),
                );
            }
        }
        let opened = self.local_residual;
        let next = HdCommittedZeroTest {
            session_id: self.session_id,
            phase: HdZeroTestPhase::LocalResidualOpened,
            frozen_peer_commitment: self.frozen_peer_commitment,
            local_residual: self.local_residual,
            modulus_q: self.modulus_q,
            family_quarantined: false,
        };
        (next, Ok(opened))
    }

    /// Phase 3: Verify the peer's opened commitment and check `(local_residual + peer_residual) % q == 0`.
    /// Quarantines the derivation family and zeroes `local_residual` on any mismatch (`P0-10`).
    pub fn verify_peer_opening(
        self,
        req_session_id: [u8; 32],
        recomputed_peer_commitment: [u8; 32],
        peer_residual: u32,
    ) -> (HdCommittedZeroTest, Result<(), CredHdGuardError>) {
        if self.family_quarantined {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::FamilyQuarantined),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &req_session_id) {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::SessionIdMismatch),
            );
        }
        match self.phase {
            HdZeroTestPhase::LocalResidualOpened => {}
            _ => {
                return (
                    quarantine_hd_family(
                        self.session_id,
                        self.frozen_peer_commitment,
                        self.modulus_q,
                    ),
                    Err(CredHdGuardError::InvalidHdPhaseTransition),
                );
            }
        }
        if !ct_eq_bytes32(&self.frozen_peer_commitment, &recomputed_peer_commitment) {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::PeerCommitmentMismatchQuarantined),
            );
        }
        if self.modulus_q == 0 || self.local_residual >= self.modulus_q || peer_residual >= self.modulus_q {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::InvalidModulusOrResidualQuarantined),
            );
        }
        let sum = (self.local_residual as u64) + (peer_residual as u64);
        let q64 = self.modulus_q as u64;
        if sum % q64 != 0 {
            return (
                quarantine_hd_family(self.session_id, self.frozen_peer_commitment, self.modulus_q),
                Err(CredHdGuardError::HdZeroTestMismatchQuarantined),
            );
        }
        let next = HdCommittedZeroTest {
            session_id: self.session_id,
            phase: HdZeroTestPhase::VerifiedZero,
            frozen_peer_commitment: self.frozen_peer_commitment,
            local_residual: 0,
            modulus_q: self.modulus_q,
            family_quarantined: false,
        };
        (next, Ok(()))
    }
}
