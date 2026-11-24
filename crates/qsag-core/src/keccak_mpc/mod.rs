//! Actively secure distributed `Keccak-f[1600]`, `SHAKE256` / `cSHAKE256`, and sealed
//! NIST FIPS 205 / `Corduroy` / `Baggy` cut-boundary MPC engines:
//!
//! 1. **Active 2-of-3 Replicated Secret Sharing (`RSS`, Araki et al. CCS 2016 + Furukawa–Lindell CCS 2017)**:
//!    64-way cross-instance bitsliced `Keccak-f[1600]` (`64` parallel sponges per permutation) backed by
//!    two-pass polynomial-field verified RSS AND relations and per-cut commit-before-open replicated
//!    share-equality checks (inconsistent replicas emit [`RssSlashingReceipt`]; AND relations
//!    use the statistical field proof).
//! 2. **Dishonest-Majority $t$-of-$n$ SPDZ Shamir `Keccak-f[1600]` (`SpdzSlhMpcCluster`)**:
//!    `BitslicedGf256x64` (`PublicGf256Matrix` Four-Russians Lagrange/extrapolation scaling) paired with
//!    exact 2-lane `Tower128` SPDZ Shamir MAC propagation (`2^{-256}` soundness), single-block FIPS 205
//!    `PRF` / `F` sponge fast path, mandatory pre-cut `MacCheck` **strictly before** revealing cut-boundary
//!    shares (`[P0-08]`), and permanent `vault.poison_and_wipe()` on abort (`[P0-07]`).
//! 3. **Distributed `Corduroy` / `Baggy` Custody & `DkgCachedSubtrees::build_distributed`**:
//!    Zero `PqSecretKey` / `SlhSecretKey` reconstruction anywhere (`0` central RAM shortcuts).

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hint::black_box;
use core::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, Ordering};

use crate::dkg::ShamirSeedShare256;
use crate::field::tower::{
    BitslicedGf256x64, Tower128, TowerGf256, bs_gf256_extract_lane, bs_gf256_insert_lane,
    bs_gf256_mul_planes_ct, bs_gf256_xor, bs_gf256_xor_assign, lagrange_weights_zero_gf256,
    wipe_tower128,
};
use crate::fips205::{
    CutBoundaryMacToken, Fips205Adrs, Fips205AdrsType, Fips205Error, Fips205Params, SlhBlock,
    SlhMpcOracles, sealed_mpc_oracles, try_wots_base16_digits_and_csum,
};
use crate::preprocessing::{
    OtMesh, PartyPrivateRng, PreprocessError, PreprocessedKeccakPartyVault,
    run_commit_and_open_coin, spdz_authenticate_bs_gf256_words, validate_all_eval_points_gf256,
};
use crate::sponge::keccak::{
    Cshake256WordStream4, Cshake256Xof, KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS,
    SHAKE256_RATE_BYTES, cshake256_32, cshake256_32_multi_frame, encode_multi_frame,
};
use crate::tsw_baggy::{
    AdrsKind, Cshake256Suite, ForsTreeOpening, HashAdrs, LayerXmssSig, PQ_CSHAKE_SUITE_CUSTOM,
    PqHashParams, PqHashSig, PqPublicKey, TAG_PRF, TAG_TH_F, TweakableHashSuite,
    build_merkle_from_leaves_topdown, build_single_secret32_template, canonical_target_sum,
    check_target_sum, derive_stateless_leaf_and_fors_indices, extract_base_w_digits_checked,
    th_chain_f, th_hash_internal_node, th_pre_hash, th_tweak_tl, verify_pq_hash_sig,
    walk_merkle_auth_path,
};
use crate::wipe::{
    SecretBuffer, ct_eq_bytes, ct_eq_bytes32, ct_eq_u64, secret_vec_extend_from_slice,
    secret_vec_push, secret_vecs_with_capacity, wipe_bytes, wipe_bytes32, wipe_u64s, wipe_u128s,
};

/// Overflow-safe active-lane bitmask for 64-way bitsliced batches (`batch_len == 64 -> u64::MAX`,
/// `batch_len == 0 -> 0`, never executing `1u64 << 64`).
#[inline]
pub const fn batch_active_mask(batch_len: usize) -> u64 {
    if batch_len == 0 {
        0
    } else if batch_len >= 64 {
        u64::MAX
    } else {
        (1u64 << batch_len) - 1
    }
}

/// Errors emitted by distributed `Keccak-f[1600]` MPC execution (RSS and SPDZ Shamir).
type RssCutShares = ([[u64; 256]; 3], [[u64; 256]; 3]);
/// Lane-0 and lane-1 `Tower128` MAC shares of the 64 values packed in one word.
pub(crate) type SpdzMacWord = [[Tower128; 64]; 2];
/// Per-party instance-bitsliced shares and MAC shares, one word per bit position.
type SpdzBitShares = (Vec<Vec<BitslicedGf256x64>>, Vec<Vec<SpdzMacWord>>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeccakMpcError {
    InvalidBatchSize(usize),
    InvalidParameters,
    Preprocess(PreprocessError),
    RssCommitMismatch {
        accused_party: usize,
    },
    RssShareEqualityFailed(RssSlashingReceipt),
    RssSacrificeFailed,
    SpdzMacAbort,
    SubtreeCacheCapExceeded {
        requested: usize,
        max_allowed: usize,
    },
    GrindExhausted,
    PostVerifyFailed,
    /// An earlier verification, coin flip, commitment or replica check of this engine or
    /// relation accumulator failed. The state is permanent: nothing is evaluated, verified
    /// or opened afterwards.
    Poisoned,
    /// The key shares are not bound to the supplied public key and parameter set (or are
    /// not bound at all, or disagree with each other).
    KeyBindingMismatch,
}

impl From<PreprocessError> for KeccakMpcError {
    fn from(e: PreprocessError) -> Self {
        Self::Preprocess(e)
    }
}

impl fmt::Display for KeccakMpcError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBatchSize(n) => write!(f, "invalid Keccak MPC batch size {}", n),
            Self::InvalidParameters => write!(f, "invalid Keccak MPC threshold/key parameters"),
            Self::Preprocess(e) => write!(f, "preprocessing/SPDZ error: {}", e),
            Self::RssCommitMismatch { accused_party } => {
                write!(
                    f,
                    "RSS share opening commitment mismatch from party {}",
                    accused_party
                )
            }
            Self::RssShareEqualityFailed(rec) => write!(
                f,
                "RSS replicated share mismatch on slot {} between primary party {} and secondary party {}",
                rec.share_slot, rec.primary_party, rec.secondary_party
            ),
            Self::RssSacrificeFailed => write!(f, "RSS Boolean-product consistency proof failed"),
            Self::SpdzMacAbort => write!(
                f,
                "SPDZ 2-lane Tower128 MacCheck aborted before cut opening"
            ),
            Self::SubtreeCacheCapExceeded {
                requested,
                max_allowed,
            } => write!(
                f,
                "distributed subtree cache leaf count {} exceeds cap {}",
                requested, max_allowed
            ),
            Self::GrindExhausted => write!(f, "TSW target-sum grind budget exhausted"),
            Self::PostVerifyFailed => write!(f, "post-MPC signature verification failed"),
            Self::Poisoned => write!(f, "RSS engine poisoned by an earlier failed check"),
            Self::KeyBindingMismatch => write!(
                f,
                "RSS key shares are not bound to this public key and parameter set"
            ),
        }
    }
}

impl core::error::Error for KeccakMpcError {}

/// Attributable fault receipt when two replicated holders of share slot `j in 0..3` broadcast
/// conflicting values after commitment lock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RssSlashingReceipt {
    pub share_slot: usize,
    pub primary_party: usize,
    pub secondary_party: usize,
}

mod rss_cluster;
mod rss_custody;
mod rss_dzk;
mod spdz;
mod tsw;

pub use rss_cluster::*;
pub use rss_custody::*;
pub(crate) use rss_dzk::*;
pub use spdz::*;
pub use tsw::*;

#[cfg(test)]
pub(crate) mod tests;
