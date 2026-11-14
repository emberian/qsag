//! `qsag-fts` 48-Round SPN Deferred-MAC Session & 1-Use `WOTS+CS` Leaf Epoch Guard.
//!
//! 1. `FtsEpochGuard` (non-`Clone`): enforces strict single-use WOTS+CS leaf burning
//!    (`used == 0 -> used = 1`), rejecting any second signing attempt on the same epoch (`P0-04`).
//! 2. `wots_cs_verify_68_w5_sum136`: verifies `68`-chain `w = 5` (`0..5`) constant-sum `S = 136`
//!    target-sum Winternitz codewords, guaranteeing componentwise incomparability.
//! 3. `FtsDeferredMacSession` (non-`Clone`): gates 48-round SPN output wire release strictly behind
//!    `intermediate_mac_verified == true` and quarantines + zeroes candidate wires on failure (`P0-03`).

use crate::tower::ct_eq_bytes32;

/// Required round count for the `qsag-fts` key-homomorphic SPN evaluation before deferred MAC check.
pub const FTS_SPN_REQUIRED_ROUNDS: u8 = 48;

/// Winternitz alphabet radix `w = 5` (`digits[i] in 0..5`) for `qsag-fts` WOTS+CS.
pub const WOTS_CS_BASE_W: u8 = 5;

/// Number of parallel WOTS+CS chains (`ell = 68`) per `qsag-fts` epoch leaf.
pub const WOTS_CS_CHAINS: usize = 68;

/// Canonical balanced constant target sum `S = 68 * (5 - 1) / 2 = 136` for `w = 5, ell = 68`.
pub const WOTS_CS_TARGET_SUM: u64 = 136;

/// Explicit refusal reasons for `FtsEpochGuard` and `FtsDeferredMacSession`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FtsGuardError {
    GuardPoisoned,
    KeyBindingMismatch,
    EpochMismatch,
    EpochOutOfBounds,
    EpochAlreadyUsed,
    SessionQuarantined,
    SessionIdMismatch,
    IncompleteSpnRounds,
    DuplicateMacCheck,
    IntermediateMacQuarantined,
    IntermediateMacNotVerified,
    OutputAlreadyReleased,
    InvalidWotsConstantSum,
}

/// Single-use authorization token emitted when an `FtsEpochGuard` transitions `used: 0 -> 1`.
pub struct FtsEpochPermit {
    key_id: [u8; 32],
    authorized_epoch: u32,
    msg_digest: [u8; 32],
}

impl FtsEpochPermit {
    /// Consume the authorization and recover its bound public identity.
    pub fn into_binding(self) -> ([u8; 32], u32, [u8; 32]) {
        (self.key_id, self.authorized_epoch, self.msg_digest)
    }
}

/// Non-`Clone` affine per-epoch WOTS+CS leaf guard enforcing at-most-one signature per epoch (`P0-04`).
///
/// External callers cannot reset the authorization state.
/// ```compile_fail,E0616
/// use qsag_verified::FtsEpochGuard;
/// let mut guard = FtsEpochGuard::new_unused([0; 32], 0, 10);
/// guard.used = 0;
/// ```
pub struct FtsEpochGuard {
    key_id: [u8; 32],
    epoch: u32,
    max_epochs: u32,
    used: u8,
    poisoned: bool,
}

impl FtsEpochGuard {
    /// Read-only state observation.
    pub const fn key_id(&self) -> [u8; 32] {
        self.key_id
    }

    /// Read-only state observation.
    pub const fn epoch(&self) -> u32 {
        self.epoch
    }

    /// Read-only state observation.
    pub const fn max_epochs(&self) -> u32 {
        self.max_epochs
    }

    /// Read-only state observation.
    pub const fn used(&self) -> u8 {
        self.used
    }

    /// Read-only state observation.
    pub const fn poisoned(&self) -> bool {
        self.poisoned
    }

    /// Construct an unused single-epoch leaf guard (`used = 0`).
    /// Immediately marks `poisoned = true` if `epoch >= max_epochs`.
    #[inline]
    pub const fn new_unused(key_id: [u8; 32], epoch: u32, max_epochs: u32) -> FtsEpochGuard {
        let poisoned = if epoch >= max_epochs { true } else { false };
        FtsEpochGuard {
            key_id,
            epoch,
            max_epochs,
            used: 0,
            poisoned,
        }
    }

    /// Consume the unused epoch leaf (`used == 0 -> used = 1`) to authorize at most one signature.
    /// Rejects any second attempt (`used != 0 -> EpochAlreadyUsed`) and poisons the guard.
    pub fn consume_epoch_once(
        self,
        req_key_id: [u8; 32],
        req_epoch: u32,
        msg_digest: [u8; 32],
    ) -> (FtsEpochGuard, Result<FtsEpochPermit, FtsGuardError>) {
        if self.poisoned {
            let next = FtsEpochGuard {
                key_id: self.key_id,
                epoch: self.epoch,
                max_epochs: self.max_epochs,
                used: self.used,
                poisoned: true,
            };
            return (next, Err(FtsGuardError::GuardPoisoned));
        }
        if !ct_eq_bytes32(&self.key_id, &req_key_id) {
            return (self, Err(FtsGuardError::KeyBindingMismatch));
        }
        if req_epoch != self.epoch {
            return (self, Err(FtsGuardError::EpochMismatch));
        }
        if self.epoch >= self.max_epochs {
            let next = FtsEpochGuard {
                key_id: self.key_id,
                epoch: self.epoch,
                max_epochs: self.max_epochs,
                used: self.used,
                poisoned: true,
            };
            return (next, Err(FtsGuardError::EpochOutOfBounds));
        }
        if self.used != 0 {
            let next = FtsEpochGuard {
                key_id: self.key_id,
                epoch: self.epoch,
                max_epochs: self.max_epochs,
                used: self.used,
                poisoned: true,
            };
            return (next, Err(FtsGuardError::EpochAlreadyUsed));
        }
        let next = FtsEpochGuard {
            key_id: self.key_id,
            epoch: self.epoch,
            max_epochs: self.max_epochs,
            used: 1,
            poisoned: false,
        };
        let permit = FtsEpochPermit {
            key_id: self.key_id,
            authorized_epoch: self.epoch,
            msg_digest,
        };
        (next, Ok(permit))
    }
}

/// Verify that `digits` has exact length `68`, every digit satisfies `d < 5` (`w = 5`),
/// and `sum_{i=0}^{67} digits[i] == 136` using overflow-free `u64` accumulation.
pub fn wots_cs_verify_68_w5_sum136(digits: &[u8]) -> bool {
    if digits.len() != WOTS_CS_CHAINS {
        return false;
    }
    let mut sum: u64 = 0;
    let mut i: usize = 0;
    while i < digits.len() {
        let d = digits[i];
        if d >= WOTS_CS_BASE_W {
            return false;
        }
        let d64 = d as u64;
        if sum > u64::MAX - d64 {
            return false;
        }
        sum += d64;
        i += 1;
    }
    sum == WOTS_CS_TARGET_SUM
}

/// Fixed-array wrapper around `wots_cs_verify_68_w5_sum136` for 68-chain WOTS+CS codewords.
#[inline]
pub fn wots_cs_verify_68_array(digits: &[u8; 68]) -> bool {
    wots_cs_verify_68_w5_sum136(digits)
}

/// Non-`Clone` affine session gating 48-round SPN output wire release behind deferred intermediate
/// MAC verification (`intermediate_mac_verified == true`) and quarantining on MAC failure (`P0-03`).
pub struct FtsDeferredMacSession {
    session_id: [u8; 32],
    spn_rounds_completed: u8,
    intermediate_mac_verified: bool,
    output_released: bool,
    quarantined: bool,
    candidate_output_lo: u128,
    candidate_output_hi: u128,
}

#[inline]
const fn quarantine_fts_session(
    session_id: [u8; 32],
    spn_rounds_completed: u8,
) -> FtsDeferredMacSession {
    FtsDeferredMacSession {
        session_id,
        spn_rounds_completed,
        intermediate_mac_verified: false,
        output_released: false,
        quarantined: true,
        candidate_output_lo: 0,
        candidate_output_hi: 0,
    }
}

impl FtsDeferredMacSession {
    /// Read-only state observation.
    pub const fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    /// Read-only state observation.
    pub const fn spn_rounds_completed(&self) -> u8 {
        self.spn_rounds_completed
    }

    /// Read-only state observation.
    pub const fn intermediate_mac_verified(&self) -> bool {
        self.intermediate_mac_verified
    }

    /// Read-only state observation.
    pub const fn output_released(&self) -> bool {
        self.output_released
    }

    /// Read-only state observation.
    pub const fn quarantined(&self) -> bool {
        self.quarantined
    }

    /// Construct a deferred-MAC session holding candidate 256-bit SPN output wires `(lo, hi)`.
    /// Immediately quarantines and zeroes the candidate wires if `spn_rounds_completed != 48`.
    #[inline]
    pub const fn new_spn48_evaluated(
        session_id: [u8; 32],
        spn_rounds_completed: u8,
        candidate_output_lo: u128,
        candidate_output_hi: u128,
    ) -> FtsDeferredMacSession {
        if spn_rounds_completed != FTS_SPN_REQUIRED_ROUNDS {
            quarantine_fts_session(session_id, spn_rounds_completed)
        } else {
            FtsDeferredMacSession {
                session_id,
                spn_rounds_completed,
                intermediate_mac_verified: false,
                output_released: false,
                quarantined: false,
                candidate_output_lo,
                candidate_output_hi,
            }
        }
    }

    /// Inspect whether the MAC context has been quarantined.
    #[inline]
    pub const fn is_quarantined(&self) -> bool {
        self.quarantined
    }

    /// Verify the 2-lane intermediate SPN BDOZ/SPDZ MAC residuals (`lane0 == 0 && lane1 == 0`).
    /// On any non-zero residual or protocol violation, quarantines the session and wipes output wires.
    pub fn verify_intermediate_mac(
        self,
        req_session_id: [u8; 32],
        mac_residual_lane0: u128,
        mac_residual_lane1: u128,
    ) -> (FtsDeferredMacSession, Result<(), FtsGuardError>) {
        if self.quarantined {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::SessionQuarantined),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &req_session_id) {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::SessionIdMismatch),
            );
        }
        if self.spn_rounds_completed != FTS_SPN_REQUIRED_ROUNDS {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::IncompleteSpnRounds),
            );
        }
        if self.output_released || self.intermediate_mac_verified {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::DuplicateMacCheck),
            );
        }
        if mac_residual_lane0 != 0 || mac_residual_lane1 != 0 {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::IntermediateMacQuarantined),
            );
        }
        let next = FtsDeferredMacSession {
            session_id: self.session_id,
            spn_rounds_completed: self.spn_rounds_completed,
            intermediate_mac_verified: true,
            output_released: false,
            quarantined: false,
            candidate_output_lo: self.candidate_output_lo,
            candidate_output_hi: self.candidate_output_hi,
        };
        (next, Ok(()))
    }

    /// Release the 256-bit SPN output wires `(lo, hi)` strictly after:
    /// 1. `!quarantined` and `!output_released`,
    /// 2. `spn_rounds_completed == 48`,
    /// 3. `intermediate_mac_verified == true`, and
    /// 4. valid 68-digit `w = 5` constant-sum `S = 136` WOTS+CS codeword check.
    pub fn release_spn_output(
        self,
        req_session_id: [u8; 32],
        wots_digits: &[u8],
    ) -> (FtsDeferredMacSession, Result<(u128, u128), FtsGuardError>) {
        if self.quarantined {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::SessionQuarantined),
            );
        }
        if !ct_eq_bytes32(&self.session_id, &req_session_id) {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::SessionIdMismatch),
            );
        }
        if self.output_released {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::OutputAlreadyReleased),
            );
        }
        if self.spn_rounds_completed != FTS_SPN_REQUIRED_ROUNDS {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::IncompleteSpnRounds),
            );
        }
        if !self.intermediate_mac_verified {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::IntermediateMacNotVerified),
            );
        }
        if !wots_cs_verify_68_w5_sum136(wots_digits) {
            return (
                quarantine_fts_session(self.session_id, self.spn_rounds_completed),
                Err(FtsGuardError::InvalidWotsConstantSum),
            );
        }
        let out_lo = self.candidate_output_lo;
        let out_hi = self.candidate_output_hi;
        let next = FtsDeferredMacSession {
            session_id: self.session_id,
            spn_rounds_completed: self.spn_rounds_completed,
            intermediate_mac_verified: true,
            output_released: true,
            quarantined: false,
            candidate_output_lo: 0,
            candidate_output_hi: 0,
        };
        (next, Ok((out_lo, out_hi)))
    }
}
