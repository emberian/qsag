//! `qsag-verified` — Standalone `#![no_std]`, `#![forbid(unsafe_code)]`, zero-dependency
//! core cryptographic and state-machine primitives of `qsag`, extracted from actual `rustc` MIR
//! via `Charon` (`.llbc`) and `Aeneas` (`-backend lean`) for end-to-end Lean 4 verification.

#![no_std]
#![forbid(unsafe_code)]
// Charon + Aeneas `0-FunsExternal` MIR extraction intentionally uses explicit `match`/branch/scalar
// forms instead of `Try::branch` (`?`), closure `Option::map`, or `core::num::is_multiple_of`.
#![allow(
    clippy::collapsible_if,
    clippy::if_same_then_else,
    clippy::manual_is_multiple_of,
    clippy::manual_map,
    clippy::needless_bool,
    clippy::question_mark,
    clippy::too_many_arguments
)]

pub mod authenticated_belt;
pub use authenticated_belt::{
    BeltAuthError, BeltQuorumStepInput, BeltQuorumStepOutput, VerifiedBeltQuorumGuard,
    custodian_ack_tag, wal_receipt_tag,
};
pub mod belt_latch_kernel;
pub use belt_latch_kernel::{
    BELT_LATCH_MAX_CAPACITY_LIMIT, BELT_LATCH_MAX_DIGITS, BELT_LATCH_MAX_EPOCH_JUMP,
    BeltLatchBindOutcome, BeltLatchBindRequest, BeltLatchDigits, BeltLatchKernel,
    BeltLatchKernelError, BeltLatchKernelRecord, belt_latch_digits_eq,
};
pub mod cred_and_hd_guards;
pub mod fips205;
pub mod fts_spn_guard;
pub mod goldilocks;
pub mod keccak;
pub mod opening_guard;
pub mod pants_and_quorum_guards;
pub mod policy_and_addr;
pub mod rss_cut_session;
pub mod threshold;
pub mod tower;

pub use cred_and_hd_guards::{
    CredHdGuardError, HdCommittedZeroTest, HdZeroTestPhase, MLDSA_Q, MLDSA44_R0_NORM_BOUND,
    MLDSA44_Z_NORM_BOUND, MLDSA65_R0_NORM_BOUND, MLDSA65_Z_NORM_BOUND, MlDsaBarrierChecks,
    MlDsaReleaseGate, check_mldsa44_norm_bounds, check_mldsa65_norm_bounds,
    mldsa44_sample_eta2_nibble_mod_q, toprf_majority_of_3_goldilocks,
};
pub use fips205::{
    Fips205Adrs, Fips205AdrsType, decode_fips205_adrs, encode_fips205_adrs, fips205_f,
    fips205_wots_chain, fips205_wots_checksum, tsw_canonical_target_sum, tsw_check_target_sum,
    wots_checksum_base16, wots_extract_base16_digits,
};
pub use fts_spn_guard::{
    FTS_SPN_REQUIRED_ROUNDS, FtsDeferredMacSession, FtsEpochGuard, FtsEpochPermit, FtsGuardError,
    WOTS_CS_BASE_W, WOTS_CS_CHAINS, WOTS_CS_TARGET_SUM, wots_cs_verify_68_array,
    wots_cs_verify_68_w5_sum136,
};
pub use goldilocks::{
    CanonicalLiftError, GOLDILOCKS_EPSILON, GOLDILOCKS_NON_RESIDUE, GOLDILOCKS_PRIME, Goldilocks,
    GoldilocksExt2, goldilocks_add, goldilocks_canon, goldilocks_ext2_add, goldilocks_ext2_mul,
    goldilocks_ext2_neg, goldilocks_ext2_sub, goldilocks_from_canonical, goldilocks_inv,
    goldilocks_inv_or_zero, goldilocks_mul, goldilocks_neg, goldilocks_pow7, goldilocks_reduce128,
    goldilocks_square, goldilocks_sub,
};
pub use keccak::{
    KECCAK_ROUND_CONSTANTS, SHAKE256_RATE_BYTES, SHAKE256_RATE_LANES, Shake256Sponge, cshake256_32,
    keccak_f1600, keccak_f1600_round, shake256_32,
};
pub use opening_guard::{ConsumingOpeningGuard2Lane, OpeningReleasePermit};
pub use pants_and_quorum_guards::{
    BeltAuthorizationGrant, BeltQuorumPhase, PantsGuardError, RssLatchStepInput,
    RssLatchStepOutput, RssOpenPermit, VerifiedRssPoisonLatch, VerifiedWaistbandRootGuard,
    VerifiedWotsC256Guard, WOTSC256_BASE_W, WOTSC256_CHAINS, WOTSC256_TARGET_SUM,
    WaistbandAncestorPermit, WaistbandDerivationRequest, validate_belt_quorum_config,
    verified_wotsc256_extract_digits, verified_wotsc256_verify_sum, wotsc256_extract_digit,
};
pub use policy_and_addr::{
    CanonicalIntent128, HybridRoleTag, INTENT_V1_MAGIC, IntentAddressVersion, IntentIdentityKind,
    IntentSuiteTag, MAX_VELOCITY_U128, PolicyAddrError, SUITE_HYBRID_ED25519_MLDSA65,
    SUITE_HYBRID_SECP256K1_MLDSA44, StatefulVelocityGuard, VelocitySpendRequest,
    check_hybrid_domain_framing, decode_intent_128, derive_hybrid_transcript_digest,
    encode_intent_128,
};
pub use rss_cut_session::{
    RssCutError, RssCutGateSession, RssCutPhase, RssCutStepInput, RssCutStepOutput,
    compute_rss_mask_commitment,
};
pub use threshold::{
    BoundEpochRecord, EpochAuthGrant, EpochLatch, EpochLatchError, EpochRequest, EpochSignRequest,
    LastBoundEpoch, RssShare64, RssZeroSeeds64, ct_eq_bytes32,
    derive_jorts_legacy_v1_det_r_rand,
    dkg_beaver_frobenius_eval_gf256, dkg_beaver_frobenius_share_shamir_gf256,
    dkg_verify_key_shares_boolean_bdoz_gf256, dkg_verify_shamir_2of3_key_bit_gf256,
    epoch_latch_advance, rss_and_gate, rss_keccak_chi_lane, rss_not, rss_party_and_local,
    rss_reconstruct, rss_reshare_views, rss_xor, shamir_degree_reduce_2of3_gf256,
    shamir_eval_poly_gf256, shamir_eval_poly_goldilocks, shamir_lagrange_at_zero_gf256,
    shamir_lagrange_at_zero_goldilocks, shamir_lagrange_weight_zero_gf256,
    shamir_lagrange_weight_zero_goldilocks, shamir_validate_points_gf256,
};
pub use tower::{
    BdozCommittedBatchOpening2Lane, BdozVerifierSession2Lane, BdozWireOpening2Lane, Gf16, Gf256,
    Tower128, Tower256, bdoz_commit_masked_tag, bdoz_fold_masked_value, embed_gf256_to_tower128,
    gf16_add, gf16_mul, gf256_add, gf256_frobenius_residual, gf256_inv, gf256_inv_or_zero,
    gf256_is_boolean_frobenius, gf256_mul, tower128_add, tower128_mul, tower256_add, tower256_mul,
    verify_mac_2lane, verify_mac_2lane_with_burn,
};
