//! Dishonest-majority $t$-of-$n$ Shamir SPDZ `Poseidon2` MPC engine (`poseidon2_mpc.rs`) for
//! stateful `JortsPoseidon2` and stateless `Corduroy` / `Baggy` over `Poseidon2Suite`,
//! with authenticated arithmetic and checked output release.
//!
//! ### Security Architecture & Hardening Invariants
//! 1. **Zero Secret Reconstruction (`0` Omniscient RAM):** Key shares (`SK.seed`, `SK.prf`) arrive
//!    from `dkg.rs` as 256 Boolean-verified `Goldilocks` bit shares, are packed locally into 32
//!    canonical `[0, 255]` byte shares, and authenticated directly via dealerless
//!    [`spdz_authenticate_goldilocks_batch_ext2`] under a unified `GoldilocksExt2` SPDZ MAC key
//!    $\alpha \in \mathbb{F}_{p^2}$ (`|F_{p^2}| \approx 2^{128}`).
//! 2. **Exact 56-Bit Linear Sponge Packing:** Because `bytes_to_limbs56` packs 7 big-endian bytes
//!    into `< 2^{56} < p` without cross-byte carry or modular wraparound, injecting 32 secret
//!    byte shares `[0, 255]` into any `th_preimage` template is an exact $\mathbb{F}_p$-linear
//!    combination over `Goldilocks` (`0` input A2B circuits!).
//! 3. **1-Round Binomial $x^7$ S-Box (`118` Tuples / `poseidon2_perm12`):** Each S-box consumes one
//!    `AuthenticatedPower7Share` `([r], [r^2], ..., [r^7])`, opens $y = x + r$ (`degree < t`),
//!    queues `([x + r], [x_mac + r_mac], y)` for mandatory pre-cut SPDZ `MacCheck`, and evaluates
//!    $(y - r)^7$ linearly on shares and `GoldilocksExt2` MACs in 1 round.
//! 4. **Exact Canonical `< p` Arithmetic-to-Binary (`A2B`) for Unrevealed Chain Steps:** Unrevealed
//!    intermediate WOTS+C / FORS hashes convert `st[0..4]` into 32 canonical big-endian byte shares
//!    without opening `st[0..4]`: each lane masks $z = (x - r) \bmod p$ with a verified `< p`
//!    `CanonicalBitMask64Share`, runs dual 64-bit public+secret ripple adders on $z + r$ and
//!    $(z + 2^{32} - 1) + r$, and selects exact canonical bits via the $2^{64}$ carry flag (`0`
//!    modulo-$p$ wraparound bugs across `0, 1, 2^{32} - 1, 2^{32}, p - 1`).
//! 5. **Strict Two-Stage Pre-Cut SPDZ `MacCheck` + Immediate Vault Poisoning:** Every cut-boundary
//!    opening (`r_rand`, FORS revealed leaf/tree leaves, WOTS+C chain endpoints, subtree public
//!    keys) verifies all queued intermediate wires AND the cut wires themselves via committed
//!    zero-masked [`commit_and_open_spdz_goldilocks_batch_quorum`] **strictly before** revealing
//!    the cut digest; any failure immediately calls `poison_and_wipe()` on all vaults and key shares.
//! 6. **Committee-wide latch gate on stateful signing:** a one-time leaf must be bound to one
//!    message across the whole committee, not only inside the `m >= t` members that happen to
//!    sign. The stateful entry points therefore accept local latches alone only when all `n`
//!    members attend, and otherwise require an [`EpochLatchCertificate`]: evidence that `q`
//!    members with `2q > n + (t - 1)` reserved this `(key, epoch, message digest)`. The signer
//!    re-checks the inequality and the binding, and refuses before any latch moves and before any
//!    share is touched. Availability follows the latch quorum, not `t`: a `(2, 3)` committee needs
//!    all three latches for every signature (see [`crate::dkg::QuorumEpochLatchCluster`]).
//! 7. **No caller-chosen randomiser:** the stateless signers derive `R` under MPC from `SK.prf`,
//!    a fixed domain frame and the message digest, so `R` (and with it the FORS instance) is the
//!    same in every session for a given `(key, message)`.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::dkg::{
    EpochLatchAuthorityPublic, EpochLatchCertificate, EpochLatchError as QuorumLatchError,
    ShamirPoseidonSeedShare, epoch_latch_binding, latch_quorum_intersects_honestly,
};
use crate::field::goldilocks::{Goldilocks, GoldilocksExt2};
use crate::keccak_mpc::DkgCachedSubtrees;
use crate::preprocessing::{
    OtMesh, PartyPrivateRng, PreprocessError, PreprocessedPoseidonPartyVault,
    commit_and_open_spdz_goldilocks_batch_quorum,
    commit_and_open_spdz_goldilocks_batch_quorum_with_mesh, run_dealerless_pi_pow7_with_alpha,
    spdz_authenticate_goldilocks_batch_ext2, spdz_setup_alpha_goldilocks,
    validate_all_eval_points_goldilocks,
};
use crate::sponge::keccak::cshake256_32;
use crate::sponge::poseidon2::{
    POSEIDON2_CONST_IV, POSEIDON2_HALF_EXTERNAL_ROUNDS, POSEIDON2_INIT_STATE,
    POSEIDON2_INTERNAL_ROUNDS, bytes_to_limbs56, poseidon2_const_at, poseidon2_hash32,
    poseidon2_pad, poseidon2_perm12,
};
use crate::tsw_baggy::{
    AdrsKind, EpochLatchError, ForsTreeOpening, HashAdrs, LayerXmssSig, Poseidon2Suite,
    PqHashParams, PqHashSig, PqPublicKey, StatefulEpochLatch, TAG_PRF, TAG_TH_F,
    build_merkle_from_leaves_topdown, build_prf_msg_template, build_single_secret32_template,
    build_stateful_det_opt_domain, build_stateless_det_opt_domain,
    derive_stateless_leaf_and_fors_indices, grind_tsw_internal_counter, grind_tsw_leaf_counter,
    th_pre_hash, th_tweak_tl, verify_pq_hash_sig,
};
use crate::wipe::{
    SecretBuffer, SecretWipe, ct_eq_bytes32, secret_vec_push, secret_vec_reserve,
    secret_vecs_with_capacity, wipe_bytes32, wipe_ext2, wipe_goldilocks,
};

/// Number of $x^7$ S-boxes in one Width-12 `poseidon2_perm12` (`4 * 12 + 22 * 1 + 4 * 12 = 118`).
pub const POSEIDON2_SBOXES_PER_PERM: usize = 118;

/// Number of Beaver triples consumed by one 64-bit canonical `< p` A2B lane conversion
/// (`63` for `z + r` + `63` for `(z + 2^32 - 1) + r` + `64` for carry mux = `190`).
pub const POSEIDON2_BEAVER_PER_A2B_LANE: usize = 190;

/// Number of Beaver triples consumed by one 4-lane (`256`-bit) sponge output A2B conversion (`760`).
pub const POSEIDON2_BEAVER_PER_A2B_HASH32: usize = 4 * POSEIDON2_BEAVER_PER_A2B_LANE;

const GOLDILOCKS_EPSILON: u64 = (1u64 << 32) - 1; // 2^64 - p = 2^32 - 1

/// Errors returned by the dishonest-majority `Poseidon2` SPDZ engine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Poseidon2MpcError {
    InvalidParams,
    InvalidQuorum {
        t: usize,
        n: usize,
    },
    KeySharePoisoned {
        party_id: usize,
    },
    PublicSeedMismatch,
    Preprocess(PreprocessError),
    EpochLatch(EpochLatchError),
    TswGrindExhausted,
    PolicyRejected,
    SignatureSelfCheckFailed,
    /// A supplied top-subtree leaf cache does not belong to this `(params, pk)`: wrong layer, wrong
    /// public key, wrong leaf count, or leaves that do not hash to `pk_root`.
    CachedSubtreeMismatch,
    /// A stateful signature was requested from `signers < committee` members without a latch
    /// certificate. Local latches bind an epoch to a message only among the members present, so
    /// a different signing set could open the same one-time leaf for another message.
    LatchCertificateRequired {
        signers: usize,
        committee: usize,
    },
    /// The presented latch certificate does not authorise this `(committee, key, epoch, message)`.
    LatchCertificateRejected(QuorumLatchError),
    /// Signing was requested before the key shares were enrolled with a verified `(params, pk)` profile.
    KeyNotEnrolled,
    /// Key shares disagree on, or were invoked with a different, `(params, pk)` profile than enrolled.
    KeyProfileMismatch,
}

impl From<PreprocessError> for Poseidon2MpcError {
    fn from(e: PreprocessError) -> Self {
        Self::Preprocess(e)
    }
}

impl From<EpochLatchError> for Poseidon2MpcError {
    fn from(e: EpochLatchError) -> Self {
        Self::EpochLatch(e)
    }
}

mod hem;
mod hem_mpc;
mod signing;
mod spdz_eval;

pub use hem::*;
pub use hem_mpc::*;
pub use signing::*;
pub use spdz_eval::*;

#[cfg(test)]
mod signing_tests;
#[cfg(test)]
mod tests;
