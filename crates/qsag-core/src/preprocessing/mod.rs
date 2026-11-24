//! 100% Dealerless Post-Quantum Active-Security Preprocessing (`0` trusted dealers, `0` single-seed
//! cleartext tuple generators):
//! 1. **`RlweBaseOt` (`RLWE_N = 1024, q = 12289, η = 1`)**: Fujisaki–Okamoto active-checked
//!    Ring-LWE 1-out-of-2 base OT over $R_q = \mathbb{Z}_{12289}\[X\]/(X^{1024} + 1)$ (`> 200`-bit PQ
//!    Core-SVP) with deterministic `(seed_b || rho_b)` re-encryption verification, `0` decryption
//!    failure ($\|(e_1 r_c - e_2 s_R + e_3)\|_\infty \le 2049 < 3072 = \lfloor q/4 \rfloor$), split
//!    per-party round state machines, and a post-Base-OT $512 \to 256$ 2-universal `[I_256 | R]`
//!    Leftover-Hash combiner + depth-2 GGM $\mathbb{F}_4$ 3-out-of-4 puncture eliminating
//!    Chou–Orlandi (`ePrint 2015/267`) selective-failure leakage to $< 2^{-128}$ ($2^{-129}$).
//! 2. **Interactive `SoftSpokenOT (n_C = 256, k = 2)` $\mathbb{F}_4$-VOLE Extension**: 3-message
//!    interactive challenge-response SoftSpokenOT (`KosOtUColsMsg` $\to$ `KosOtChallengeMsg` $\to$
//!    `OtExtProofMsg` / `KosOtProofMsg`) over `128` 2-bit $\mathbb{F}_4$ slices (`128` `u_cols` wire
//!    columns, `256` per-column `[X | I_256]` polynomial-basis $\mathbb{F}_{2^{128}}^2$ consistency
//!    equations via [`OtExtCheckKey`]), achieving Roy (`CRYPTO 2022` / `ePrint 2022/192` Thm 4.5)
//!    exact **$2^{-241}$** consistency soundness, **128-bit post-quantum Grover security** on
//!    $\Delta \in \mathbb{F}_2^{256}$, transcript-bound 256-bit single-block Keccak pad hashing,
//!    and an immediate shared `Arc<AtomicBool>` poison latch across all forked substreams.
//! 3. **Dealerless `Π_triple_f2` (`PreprocessedKeccakVault`)**: Authenticated pairwise OT
//!    products, recursive inner-product sacrifice, post-sacrifice adaptive bucket combining
//!    (including one discarded parity bucket), then degree-`<t` Shamir dealing and a two-lane
//!    `Tower128` SPDZ consistency check. Additive consumers stop before Shamir dealing.
//! 4. **Dealerless `Π_pow7` & Canonical `< p` A2B Bit-Masks (`PreprocessedPoseidonVault`)**:
//!    Joint `Π_rand` (`dealerless_joint_mask_uniform`) + pairwise 64-bit Gilboa `Goldilocks` OLE +
//!    `GoldilocksExt2` BDOZ MAC cross-terms + companion triple sacrifice (`pow7_sacrifice_sound`,
//!    cheating probability $1/p^2 < 2^{-127} < 2^{-125}$) + 3-round parallel Beaver power-tree
//!    (`evalPow7BeaverTree`: `[r], [r^2], ..., [r^7]`) + dealerless canonical `< p` 64-bit A2B masks
//!    verified via $b_k^2 - b_k = 0$ and exact `is_ge_p == 0` predicate opening.
//! 5. **Silent `pcg_dense` Vault Materialization (`materialize_silent_pcg_keccak_vaults` &
//!    `run_silent_pcg_keccak_vaults`)**: Callers can generate authenticated Shamir-SPDZ Beaver
//!    triples (`PreprocessedKeccakPartyVault`) and silent 384-bit OT correlations directly from
//!    locally expanded [`crate::pcg_dense::DensePcgExpandedVault`]s (`Depth15` expand-accumulate
//!    dual-LPN) alongside the interactive KOS/MASCOT [`run_dealerless_pi_triple_f2`] pool. The
//!    earlier sparse GGM/QC-LPN sketch below remains gated to unit-test regressions.

// Unit tests have a host runtime even when the production library is no_std.
#[cfg(all(test, not(feature = "std")))]
extern crate std;

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hint::black_box;

pub use crate::field::goldilocks::{
    Goldilocks, GoldilocksExt2, eval_poly_ext2_at_base, eval_poly_goldilocks,
    lagrange_weights_zero_goldilocks, wipe_ext2, wipe_goldilocks,
};
pub use crate::field::tower::{
    BitslicedGf256x64, PublicGf256Matrix, Tower128, TowerGf256, bs_gf256_extract_lane,
    bs_gf256_insert_lane, bs_gf256_mul_planes_ct, bs_gf256_scale_secret_ct, bs_gf256_xor,
    bs_gf256_xor_assign, eval_poly_gf256, lagrange_weights_zero_gf256, wipe_tower128,
};
use crate::sponge::keccak::{Cshake256Xof, cshake256_32_multi_frame, keccak_f1600};
use crate::wipe::{
    SecretBuffer, ct_eq_bytes32, secret_vec_extend_from_slice, secret_vec_push, wipe_bytes,
    wipe_bytes32, wipe_u16s, wipe_u64s, wipe_u128s,
};

mod coins_and_openings;
mod gf256_auth;
mod goldilocks_auth;
mod keccak_vault;
mod mac_blind;
mod ot_ext;
mod pcg_vault;
mod poseidon_vault;
mod rlwe_base_ot;
mod rlwe_poly;
mod rlwe_proof;
mod triple_f2;
pub(crate) use mac_blind::blind_open_tower128;
pub use mac_blind::{blind_open_additive_gf128_poly, blind_open_ext2};
use mac_blind::{blind_open_degree_ext2, blind_open_degree_tower128};

pub(crate) use coins_and_openings::fold_spdz_mac_words;
pub use coins_and_openings::{
    Gf256OpeningTables, GoldilocksOpeningTables, PartyCoinCommitState,
    commit_and_open_spdz_bs_gf256_quorum, commit_and_open_spdz_ext2_quorum,
    commit_and_open_spdz_goldilocks_quorum, open_and_check_degree_bs_gf256,
    open_and_check_degree_ext2, open_and_check_degree_gf256, open_and_check_degree_goldilocks,
    run_commit_and_open_coin, run_commit_and_open_coin_with_hook, validate_all_eval_points_gf256,
    validate_all_eval_points_goldilocks, verify_and_combine_coin_openings,
};
pub(crate) use gf256_auth::spdz_pimac_check_bs_gf256_words;
pub use gf256_auth::{
    authenticate_gf256_batch_two_lane, authenticate_gf256_shares_two_lane,
    commit_and_open_degree_tower128, spdz_authenticate_bs_gf256_words, spdz_setup_alpha_gf256,
    spdz_share_existing_alpha_gf256,
};
pub use goldilocks_auth::{
    commit_and_open_degree_ext2, commit_and_open_spdz_goldilocks_batch_quorum,
    commit_and_open_spdz_goldilocks_batch_quorum_with_mesh, pairwise_gilboa_ole_goldilocks,
    spdz_authenticate_goldilocks_batch_ext2, spdz_setup_alpha_goldilocks,
};
pub use keccak_vault::{
    AdditiveBoolTripleShares, KeccakBitTripleShare64, PreprocessedKeccakPartyVault,
    commit_and_open_spdz_bs_gf256_batch_quorum,
    commit_and_open_spdz_bs_gf256_batch_quorum_with_mesh, run_dealerless_pi_triple_f2,
    run_dealerless_pi_triple_f2_additive, run_dealerless_pi_triple_f2_additive_with_fault,
    run_dealerless_pi_triple_f2_with_alpha, run_dealerless_pi_triple_f2_with_fault,
    run_dealerless_pi_triple_f2_with_transcript,
};
pub(crate) use keccak_vault::{checked_boolean_product, derive_coin_permutation};
pub use ot_ext::{
    KosOtChallengeMsg, KosOtProofMsg, KosOtReceiverPending, KosOtSenderPending, KosOtUColsMsg,
    OtExtCheckKey, OtExtProofMsg, OtExtReceiverChannel, OtExtSenderChannel, OtMesh,
    establish_rlwe_ot_ext_channel, try_establish_rlwe_ot_ext_channel,
};
pub use pcg_vault::{
    PCG_DEFAULT_TREE_DEPTH, PCG_MAX_SEED_WIRE_BYTES, PCG_MAX_TREE_DEPTH, PCG_MIN_TREE_DEPTH,
    PCG_NUM_BOOL_TRIPLES, PCG_NUM_TOWER_TRIPLES, PCG_NUM_WORDS, PCG_TAPS_PER_TREE,
    PCG_TREES_PER_BUNDLE, PcgTreeDepth, SILENT_PCG_KECCAK_CHUNK_WORDS,
    expand_and_materialize_silent_pcg_keccak_vaults, materialize_silent_pcg_keccak_vaults,
    materialize_silent_pcg_keccak_vaults_with_alpha, run_dealerless_pcg_keccak_vaults,
    run_dealerless_pcg_keccak_vaults_with_alpha, run_silent_pcg_keccak_vaults,
    run_silent_pcg_keccak_vaults_with_alpha,
};
pub use poseidon_vault::{
    AuthenticatedPower7Share, CanonicalBitMask64Share, GoldilocksBeaverShare,
    PreprocessedPoseidonPartyVault, run_dealerless_pi_pow7, run_dealerless_pi_pow7_with_alpha,
    run_dealerless_pi_pow7_with_fault,
};
pub use rlwe_base_ot::{
    BaseOtCrsCommitMsg, BaseOtCrsOpenMsg, BaseOtCrsReceiverRound0, BaseOtCrsSenderRound0,
    BaseOtCrsShareMsg, BaseOtExtReceiverRound2, BaseOtExtSenderRound1, BaseOtExtSenderRound3,
    BaseOtRound1Msg, BaseOtRound2Msg, BaseOtRound3Msg, BaseOtRound4Msg, F4SliceReceiverSetup,
    RLWE_BASE_OT_BLOCKS, RLWE_BASE_OT_SLOTS_PER_BLOCK, batch_bdoz_gf2128_dot,
    softspoken_f4_slice_setup_receiver, softspoken_f4_slice_setup_sender_ct,
    softspoken_f4_zero_punctured_slot_ct,
};
pub use rlwe_poly::{
    OT_EXT_F4_SLICES, OT_EXT_PROOF_BYTES, OT_EXT_SACRIFICIAL_OTS, OT_EXT_SUBSPACE_BITS,
    RLWE_BASE_OT_COUNT, RLWE_BASE_OT_WORDS, RLWE_HALF_Q, RLWE_N, RLWE_N_INV, RLWE_OMEGA_1024,
    RLWE_OMEGA_INV_1024, RLWE_PSI_2048, RLWE_PSI_INV_2048, RLWE_Q, RlweOtReceiverMsg,
    RlweOtReceiverSecret, RlweOtSenderMsg, RlwePoly, RlwePolyNtt, rlwe_decode_bit_ct,
    rlwe_ot_choose, rlwe_ot_decrypt, rlwe_ot_transfer, try_rlwe_ot_transfer,
};
pub use rlwe_proof::{
    RLWE_ZKPOK_CHAL_BITS, RLWE_ZKPOK_PAIR_L2_SQ_BOUND, RLWE_ZKPOK_REPS, RlweReceiverZkPok,
};

/// Sender's two 384-bit correlation pads for one extended OT.
pub type OtPadPair = ([u8; 48], [u8; 48]);

/// Zeroizing sender OT pad batch (`!Clone`, volatile-wiped on normal and early-return `Drop`).
pub struct OtSendPads(pub(crate) Vec<OtPadPair>);

impl fmt::Debug for OtSendPads {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OtSendPads")
            .field("len", &self.0.len())
            .finish_non_exhaustive()
    }
}

impl core::ops::Deref for OtSendPads {
    type Target = [OtPadPair];
    #[inline]
    fn deref(&self) -> &[OtPadPair] {
        &self.0
    }
}

impl core::ops::DerefMut for OtSendPads {
    #[inline]
    fn deref_mut(&mut self) -> &mut [OtPadPair] {
        &mut self.0
    }
}

impl Drop for OtSendPads {
    fn drop(&mut self) {
        for (p0, p1) in &mut self.0 {
            wipe_bytes(p0);
            wipe_bytes(p1);
        }
        black_box(&mut self.0);
    }
}

/// Zeroizing receiver OT pad batch (`!Clone`, volatile-wiped on normal and early-return `Drop`).
pub struct OtRecvPads(pub(crate) Vec<[u8; 48]>);

impl fmt::Debug for OtRecvPads {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OtRecvPads")
            .field("len", &self.0.len())
            .finish_non_exhaustive()
    }
}

impl core::ops::Deref for OtRecvPads {
    type Target = [[u8; 48]];
    #[inline]
    fn deref(&self) -> &[[u8; 48]] {
        &self.0
    }
}

impl core::ops::DerefMut for OtRecvPads {
    #[inline]
    fn deref_mut(&mut self) -> &mut [[u8; 48]] {
        &mut self.0
    }
}

impl Drop for OtRecvPads {
    fn drop(&mut self) {
        for pad in &mut self.0 {
            wipe_bytes(pad);
        }
        black_box(&mut self.0);
    }
}

/// Pads for a complete correlated-OT batch, on both sides (`Drop`-wiped).
pub type OtBatchPads = (OtSendPads, OtRecvPads);
/// Party-major vectors of values of a given field/type.
pub type PartyValues<T> = Vec<Vec<T>>;
/// Two parallel 128-bit authentication lanes per party.
pub type TowerAlphaShares = Vec<[Tower128; 2]>;
/// Two-lane MACs indexed by verifier, sender and value.
pub type PairwiseTowerMacs = Vec<Vec<Vec<[Tower128; 2]>>>;
/// Value shares and two-lane MACs grouped by party.
pub type TowerMacMatrices = (PartyValues<[Tower128; 2]>, PartyValues<[Tower128; 2]>);
/// Authenticated Goldilocks Beaver material: a, b, c followed by their MACs.
pub type GoldilocksBeaverMaterial = (
    PartyValues<Goldilocks>,
    PartyValues<Goldilocks>,
    PartyValues<Goldilocks>,
    PartyValues<GoldilocksExt2>,
    PartyValues<GoldilocksExt2>,
    PartyValues<GoldilocksExt2>,
);
#[cfg(test)]
type SpcotPunctureOutput = (Vec<[u128; 2]>, Vec<([u8; 16], [u8; 16])>);

/// Preprocessing abort with deterministic attribution when a party deviates during OT, coin-flip,
/// polynomial degree verification, BDOZ/SPDZ MAC check, Booleanity check, or companion sacrifice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreprocessError {
    InvalidThreshold {
        t: usize,
        n: usize,
    },
    DuplicateOrZeroEvalPoint,
    CoinCommitMismatch {
        party_id: usize,
    },
    ShareCommitMismatch {
        phase: &'static str,
        party_id: usize,
    },
    BaseOtReceiverProofFailed {
        sender_id: usize,
        receiver_id: usize,
    },
    BaseOtFoCheckFailed {
        sender_id: usize,
        receiver_id: usize,
        ot_idx: u32,
    },
    KosOtCheckFailed {
        sender_id: usize,
        receiver_id: usize,
    },
    ChannelPoisoned {
        sender_id: usize,
        receiver_id: usize,
    },
    DegreeCheckFailed {
        phase: &'static str,
    },
    MacCheckFailed {
        phase: &'static str,
        accused_party: Option<usize>,
    },
    SacrificeResidualNonZero {
        phase: &'static str,
    },
    NonBooleanBitDetected {
        phase: &'static str,
    },
    VaultExhausted {
        kind: &'static str,
    },
    VaultPoisoned {
        kind: &'static str,
    },
    PcgDepthOutOfRange {
        depth: usize,
    },
    PcgInvalidWireSeed,
    ExperimentalSparsePcg,
    /// The wire seed carries the magic of an earlier, no longer accepted layout.
    PcgObsoleteWireSeedFormat,
    /// The seed's identity is already recorded as expanded; nothing was expanded.
    PcgSeedAlreadyBurned,
    /// The seed burn tracker could not record the burn; nothing was expanded.
    PcgSeedBurnNotRecorded,
}

impl fmt::Display for PreprocessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidThreshold { t, n } => {
                write!(f, "invalid threshold parameters t={}, n={}", t, n)
            }
            Self::DuplicateOrZeroEvalPoint => {
                write!(f, "duplicate or zero Shamir evaluation point")
            }
            Self::CoinCommitMismatch { party_id } => {
                write!(f, "commit-and-open coin mismatch from party {}", party_id)
            }
            Self::ShareCommitMismatch { phase, party_id } => {
                write!(
                    f,
                    "share commitment opening mismatch in {} from party {}",
                    phase, party_id
                )
            }
            Self::BaseOtReceiverProofFailed {
                sender_id,
                receiver_id,
            } => write!(
                f,
                "Ring-LWE Base-OT Receiver OR-Sigma ZKPoK failed (sender {}, receiver {})",
                sender_id, receiver_id
            ),
            Self::BaseOtFoCheckFailed {
                sender_id,
                receiver_id,
                ot_idx,
            } => write!(
                f,
                "Ring-LWE Base-OT Fujisaki-Okamoto re-encryption check failed (sender {}, receiver {}, idx {})",
                sender_id, receiver_id, ot_idx
            ),
            Self::KosOtCheckFailed {
                sender_id,
                receiver_id,
            } => write!(
                f,
                "interactive KOS OT extension correlation check failed between sender {} and receiver {}",
                sender_id, receiver_id
            ),
            Self::ChannelPoisoned {
                sender_id,
                receiver_id,
            } => write!(
                f,
                "OT extension channel ({} -> {}) permanently poisoned after prior abort",
                sender_id, receiver_id
            ),
            Self::DegreeCheckFailed { phase } => {
                write!(f, "Shamir degree < t check failed in {}", phase)
            }
            Self::MacCheckFailed {
                phase,
                accused_party,
            } => write!(
                f,
                "SPDZ/BDOZ MAC verification failed in {} (accused party {:?})",
                phase, accused_party
            ),
            Self::SacrificeResidualNonZero { phase } => {
                write!(f, "SPDZ companion sacrifice residual non-zero in {}", phase)
            }
            Self::NonBooleanBitDetected { phase } => {
                write!(f, "non-Boolean share b^2 != b detected in {}", phase)
            }
            Self::VaultExhausted { kind } => {
                write!(f, "preprocessed {} vault exhausted", kind)
            }
            Self::VaultPoisoned { kind } => {
                write!(
                    f,
                    "preprocessed {} vault permanently poisoned after MAC abort",
                    kind
                )
            }
            Self::PcgDepthOutOfRange { depth } => {
                write!(
                    f,
                    "PCG GGM tree depth {} out of supported range 14..=16",
                    depth
                )
            }
            Self::ExperimentalSparsePcg => write!(
                f,
                "compact PCG is unavailable: use uniform vault preprocessing"
            ),
            Self::PcgInvalidWireSeed => write!(f, "malformed or tampered PCG wire seed"),
            Self::PcgObsoleteWireSeedFormat => write!(
                f,
                "PCG wire seed uses the obsolete QSAGDPC1 layout; re-run setup to obtain a QSAGDPC2 seed"
            ),
            Self::PcgSeedAlreadyBurned => {
                write!(
                    f,
                    "PCG seed was already expanded once; refusing to expand it again"
                )
            }
            Self::PcgSeedBurnNotRecorded => {
                write!(f, "PCG seed burn could not be recorded; refusing to expand")
            }
        }
    }
}

/// Maximum accepted preprocessing frame (16 MiB), including all declared elements.
pub const MAX_FRAME_BUDGET: usize = 16 * 1024 * 1024;
pub(crate) fn validate_frame_count(
    count: usize,
    elem_bytes: usize,
    remaining: usize,
) -> Result<(), PreprocessError> {
    match count.checked_mul(elem_bytes) {
        Some(size) if size <= remaining && size <= MAX_FRAME_BUDGET => Ok(()),
        _ => Err(PreprocessError::PcgInvalidWireSeed),
    }
}

/// Secret-keyed transcript hedge. A restored counter is safe for a new transcript;
/// identical seed, counter, entropy and transcript necessarily reproduce the same bytes.
pub struct HedgedTranscriptRng {
    seed: [u8; 32],
    counter: u64,
}
impl Drop for HedgedTranscriptRng {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.seed);
    }
}
impl HedgedTranscriptRng {
    pub fn new(secret_hedge_seed: [u8; 32], monotonic_counter: u64) -> Self {
        Self {
            seed: secret_hedge_seed,
            counter: monotonic_counter,
        }
    }
    /// Fails before producing output on counter exhaustion. Variable inputs are length framed.
    pub fn fill_bytes(
        &mut self,
        caller_entropy: &[u8],
        session_and_msg_transcript: &[u8],
        out: &mut [u8],
    ) -> Result<(), PreprocessError> {
        let next = self
            .counter
            .checked_add(1)
            .ok_or(PreprocessError::PcgInvalidWireSeed)?;
        Self::derive(
            &self.seed,
            self.counter,
            caller_entropy,
            session_and_msg_transcript,
            out,
        );
        self.counter = next;
        Ok(())
    }
    pub(crate) fn derive(
        seed: &[u8; 32],
        counter: u64,
        caller_entropy: &[u8],
        session_and_msg_transcript: &[u8],
        out: &mut [u8],
    ) {
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"QSAG.HEDGED_RNG.V1");
        xof.absorb(seed);
        xof.absorb(&counter.to_le_bytes());
        xof.absorb(&(caller_entropy.len() as u64).to_le_bytes());
        xof.absorb(caller_entropy);
        xof.absorb(&(session_and_msg_transcript.len() as u64).to_le_bytes());
        xof.absorb(session_and_msg_transcript);
        xof.squeeze(out);
    }
}

/// Exact division by an enrolled public batch size without a hardware divider.
struct PublicDivisor {
    size: usize,
    reciprocal: usize,
}

impl PublicDivisor {
    fn new(size: usize) -> Self {
        assert!(size != 0);
        // Binary long division of MAX by the public size, once per batch.
        let mut remainder = usize::MAX;
        let mut reciprocal = 0;
        for shift in (0..=size.leading_zeros()).rev() {
            let part = size << shift;
            if remainder >= part {
                remainder -= part;
                reciprocal |= 1usize << shift;
            }
        }
        Self { size, reciprocal }
    }

    #[inline]
    fn split(&self, n: usize) -> (usize, usize) {
        // MAX/size rounded down underestimates the quotient by at most one.
        let q = ((n as u128 * self.reciprocal as u128) >> usize::BITS) as usize;
        let r = n - q * self.size;
        let adjust = usize::from(r >= self.size);
        (q + adjust, r - adjust * self.size)
    }

    fn ceil(&self, n: usize) -> usize {
        let (q, r) = self.split(n);
        q + usize::from(r != 0)
    }
}

#[cfg(test)]
#[test]
fn public_batch_division_matches_native_arithmetic() {
    for size in (1..1024).chain([usize::MAX / 2, usize::MAX / 2 + 1, usize::MAX]) {
        let divisor = PublicDivisor::new(size);
        for n in [
            0,
            1,
            size - 1,
            size,
            size.saturating_add(1),
            usize::MAX - 1,
            usize::MAX,
        ] {
            assert_eq!(divisor.split(n), (n / size, n % size));
            assert_eq!(divisor.ceil(n), n.div_ceil(size));
        }
    }
}

/// Reserve before exposing material. One cursor per material kind spans every quorum
/// and session using this non-cloneable vault; failed reservations leave it unchanged.
fn reserve_material(
    cursor: &mut usize,
    len: usize,
    count: usize,
    poisoned: bool,
    kind: &'static str,
) -> Result<core::ops::Range<usize>, PreprocessError> {
    if poisoned {
        return Err(PreprocessError::VaultPoisoned { kind });
    }
    let end = cursor
        .checked_add(count)
        .filter(|end| *end <= len)
        .ok_or(PreprocessError::VaultExhausted { kind })?;
    let start = *cursor;
    *cursor = end;
    Ok(start..end)
}

/// Deterministic per-party CSPRNG stream backed by `cSHAKE256("QSAG.PARTY.RNG/v1", ...)`.
/// Isolated strictly to a single party's private entropy seed; wiped on `Drop`.
pub struct PartyPrivateRng {
    seed: [u8; 32],
    counter: u64,
    buf: [u8; 8 * 136],
    off: usize,
}

impl fmt::Debug for PartyPrivateRng {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PartyPrivateRng([REDACTED])")
    }
}

impl Drop for PartyPrivateRng {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.seed);
        wipe_bytes(&mut self.buf);
    }
}

impl PartyPrivateRng {
    /// Seed from the operating system entropy source; failures are propagated.
    #[cfg(all(feature = "std", unix))]
    pub fn from_os_rng(domain_label: &[u8]) -> Result<Self, std::io::Error> {
        let mut seed = [0u8; 32];
        let result = qsag_asm::fill_os_random(&mut seed);
        if let Err(error) = result {
            wipe_bytes32(&mut seed);
            return Err(error);
        }
        let rng = Self::from_seed(seed, domain_label);
        wipe_bytes32(&mut seed);
        Ok(rng)
    }

    pub fn from_seed(party_seed: [u8; 32], domain_label: &[u8]) -> Self {
        let mut seed_copy = party_seed;
        let derived =
            cshake256_32_multi_frame(b"QSAG.PARTY.RNG.INIT/v1", &[&seed_copy, domain_label]);
        wipe_bytes32(&mut seed_copy);
        Self {
            seed: derived,
            counter: 0,
            buf: [0u8; 8 * 136],
            off: 8 * 136,
        }
    }

    /// Rekey the private mask stream with a public session/message transcript.
    /// Discards buffered bytes so no pre-transcript masks escape after this call.
    pub fn hedge_transcript(&mut self, transcript: &[u8]) {
        let mut entropy = self.next_bytes32();
        let mut seed = [0; 32];
        // Each rekey resets the counter under a fresh secret key.
        HedgedTranscriptRng::derive(&self.seed, 0, &entropy, transcript, &mut seed);
        wipe_bytes32(&mut self.seed);
        self.seed = seed;
        wipe_bytes32(&mut seed);
        wipe_bytes32(&mut entropy);
        wipe_bytes(&mut self.buf);
        self.counter = 0;
        self.off = self.buf.len();
    }

    fn refill(&mut self) {
        assert!(
            self.counter <= u64::MAX - 8,
            "PartyPrivateRng counter exhausted"
        );
        // Eight consecutive counter blocks preserve the exact scalar byte stream
        // while executing a single 8-way AVX-512 (or dual 4-way AVX2) permutation.
        let mut states = qsag_asm::KeccakState8x::default();
        states.0[0] = [u64::from_le_bytes(*b"QSAG.PRG"); 8];
        states.0[1] = [u64::from_le_bytes(*b"NG.BLK\x01\x00"); 8];
        for i in 0..4 {
            let word = u64::from_le_bytes(core::array::from_fn(|j| self.seed[8 * i + j]));
            states.0[2 + i] = [word; 8];
        }
        let base = self.counter;
        states.0[6] = core::array::from_fn(|k| base.wrapping_add(k as u64));
        self.counter = base.wrapping_add(8);
        states.0[7] = [0x1f; 8];
        states.0[16] = [0x8000_0000_0000_0000; 8];
        qsag_asm::keccak_f1600_x8(&mut states);
        for lane in 0..17 {
            let row = states.0[lane];
            for (block, &word) in row.iter().enumerate() {
                let offset = block * 136 + lane * 8;
                self.buf[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
            }
        }
        qsag_asm::volatile_fill(&mut states.0, [0u64; 8]);
        self.off = 0;
    }

    #[inline(always)]
    pub fn fill_bytes(&mut self, out: &mut [u8]) {
        if self.off + out.len() <= self.buf.len() {
            out.copy_from_slice(&self.buf[self.off..self.off + out.len()]);
            self.off += out.len();
            return;
        }
        let mut written = 0usize;
        while written < out.len() {
            if self.off == self.buf.len() {
                self.refill();
            }
            let avail = (self.buf.len() - self.off).min(out.len() - written);
            out[written..written + avail].copy_from_slice(&self.buf[self.off..self.off + avail]);
            self.off += avail;
            written += avail;
        }
    }

    #[inline(always)]
    pub fn next_u64(&mut self) -> u64 {
        if self.off + 8 <= self.buf.len() {
            let s = &self.buf[self.off..self.off + 8];
            let v = u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
            self.off += 8;
            return v;
        }
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }

    #[inline(always)]
    pub fn next_u128(&mut self) -> u128 {
        if self.off + 16 <= self.buf.len() {
            let s = &self.buf[self.off..self.off + 16];
            let v = u128::from_le_bytes([
                s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9], s[10], s[11], s[12],
                s[13], s[14], s[15],
            ]);
            self.off += 16;
            return v;
        }
        let lo = self.next_u64() as u128;
        let hi = self.next_u64() as u128;
        lo | (hi << 64)
    }

    #[inline]
    pub fn next_bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        self.fill_bytes(&mut out);
        out
    }

    /// Constant-time 192-bit (`24`-byte) reduction in $[0, p)$ (`< 2^{-192}` statistical distance, `0` branches).
    #[inline]
    pub fn next_goldilocks(&mut self) -> Goldilocks {
        let mut b = [0u8; 24];
        self.fill_bytes(&mut b);
        let g = Goldilocks::from_bytes24_unbiased(&b);
        wipe_bytes(&mut b);
        g
    }

    #[inline]
    pub fn next_ext2(&mut self) -> GoldilocksExt2 {
        GoldilocksExt2::new(self.next_goldilocks(), self.next_goldilocks())
    }

    #[inline]
    pub fn next_gf256(&mut self) -> TowerGf256 {
        if self.off < self.buf.len() {
            let b = self.buf[self.off];
            self.off += 1;
            return TowerGf256(b);
        }
        let mut b = [0u8; 1];
        self.fill_bytes(&mut b);
        TowerGf256(b[0])
    }

    #[inline(always)]
    pub fn next_tower128(&mut self) -> Tower128 {
        Tower128(self.next_u128())
    }
}
impl core::error::Error for PreprocessError {}

#[cfg(test)]
mod sparse_pcg;
#[cfg(test)]
mod tests_coins_and_rng;
#[cfg(test)]
mod tests_ot_ext;
#[cfg(test)]
mod tests_pcg;
#[cfg(test)]
mod tests_rlwe;
#[cfg(test)]
mod tests_vaults;

#[cfg(test)]
fn make_party_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
    (0..n)
        .map(|i| {
            let mut seed = [0u8; 32];
            seed[0] = tag;
            seed[1] = (i + 1) as u8;
            PartyPrivateRng::from_seed(seed, b"test")
        })
        .collect()
}
