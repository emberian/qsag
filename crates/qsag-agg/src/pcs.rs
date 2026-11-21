//! `Hem` Succinct Multilinear Polynomial Commitment Scheme (`WHIR` EUROCRYPT 2025 Rate-Escalation
//! over `GoldilocksExt4` + Steiner-Deduplicated `CANOPY_MIDSTATE` Merkle-Canopy Oracles).
//!
//! Commits to multilinear polynomials $W_i \in \mathbb{F}_p[X_0, \dots, X_{\ell-1}]$ and proves
//! evaluation claims over the quartic extension $\mathbb{F}_{p^4}$ (`GoldilocksExt4`,
//! $|\mathbb{F}_{p^4}| > 2^{255.99}$) via:
//! 1. Exact hypercube-to-monomial Möbius basis transform ($O(\ell 2^\ell)$),
//! 2. Multi-stage WHIR **rate escalation** (`whir_stage_schedule`): instead of folding an initial
//!    high-rate codeword passively at fixed rate across every round, each intermediate stage
//!    re-encodes the folded monomial witness at an **escalating Reed–Solomon blowup**
//!    (e.g. $B = (4, 16, 64)$, i.e. $\rho_0 = 1/4 \to \rho_1 = 1/16 \to \rho_2 = 1/64$ at
//!    $\ell = 20$), keeping intermediate evaluation domains bounded ($D_1 = 2^{19}, D_2 = 2^{18} \le 2^{20}$)
//!    with unconditional Johnson-radius QROM query counts $q = (258, 130, 88)$,
//! 3. **Out-of-Domain (OOD) List-Pinning & Shift-Query Accumulation:** every committed oracle
//!    $f^{(k)}$ is pinned at two independent $\mathbb{F}_{p^4}$ Kronecker point $\text{pow2}(z_{\text{ood},k})$
//!    before affine fold challenges are squeezed, and stage-$k$ fiber openings fold into shift claims
//!    $W^{(k+1)}(\text{pow2}(z_u)) = v_{\text{shift},u}$ batched into stage $k+1$'s sumcheck with
//!    independent $\mathbb{F}_{p^4}$ challenges,
//! 4. **Precomputed `CANOPY_MIDSTATE` + 4-Way SIMD `keccak_f1600_x4` Merkle-Canopy Trees** with
//!    canonical bottom-up **Steiner-deduplicated Merkle Multi-Proofs** (`CanopyMultiProof`),
//! 5. **Per-Stage 16-Bit Transcript Proof-of-Work** (`POW_MIDSTATE`) ground deterministically via
//!    4-way SIMD `cshake256_pow_u64_x4` before every stage's fiber query squeeze.
//!
//! # Soundness Accounting (`GoldilocksExt4` vs Legacy `GoldilocksExt2`)
//!
//! Query regimes and their assumptions are documented on [`whir_stage_schedule`].
//! Extension-field, OOD, proximity, and Fiat–Shamir reduction errors must be
//! accounted for separately; query exponents alone are not total security bits.
//!
//! # Batched commitments
//!
//! [`whir_commit_batch_owned`] commits $S \le$ [`MAX_BATCH_POLYS`] polynomials of equal size under
//! ONE Merkle-Canopy tree: Round-0 leaf $g$ holds coset fiber $g$ of every codeword.
//! [`whir_open_batch`] proves $W_i(p_i) = e_i$ for all $i \in [0, S)$ with one point-reduction
//! sumcheck over $\mathbb{F}_{p^4}$ followed by an asymmetric affine cascade [CWYZ26].

pub(crate) mod affine;
#[cfg(test)]
mod affine_schedule;
use affine::*;

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::GoldilocksOps as _;
use crate::field::{
    Goldilocks, GoldilocksExt4, build_eq_table_ext4, encode_rs_coset_ext4,
    encode_rs_coset_goldilocks_owned_cpu, encode_rs_coset_goldilocks_with_secret, eq_poly_ext4,
    eval_univariate_base_at_ext4_pair, eval_univariate_ext4, eval_univariate_ext4_at_base,
    fold_first_var_in_place_ext4, pow2_point_ext4,
};
use crate::sponge::{
    CANOPY_MIDSTATE, FiatShamirTranscript, InstanceBound, POW_MIDSTATE, TURBOSHAKE_CANOPY_MIDSTATE,
    TURBOSHAKE_POW_MIDSTATE, cshake256_from_midstate_16_x4, cshake256_from_midstate_16_x8,
    cshake256_from_midstate_32, cshake256_from_midstate_32_x4, cshake256_from_midstate_32_x8,
    cshake256_from_midstate_into, cshake256_pow_u64_single, cshake256_pow_u64_x8,
    poseidon2_pow_word, turboshake256_from_midstate_16_x4, turboshake256_from_midstate_16_x8,
    turboshake256_from_midstate_32, turboshake256_from_midstate_32_x4,
    turboshake256_from_midstate_32_x8, turboshake256_from_midstate_into,
    turboshake256_pow_u64_single, turboshake256_pow_u64_x8,
};

/// Default Stage-0 Reed–Solomon blowup factor ($1/\rho_0 = 4$ at $K = 8, 16, 32$).
/// Exact per-stage blowup factors are governed by [`whir_stage_schedule`].
pub const RS_BLOWUP: usize = 4;

/// Wire/parser query cap; active query counts are in WhirSchedule.
pub const NUM_PCS_QUERIES: usize = 512;

/// Per-stage Fiat–Shamir Proof-of-Work grinding difficulty in bits.
pub const PCS_POW_BITS: u32 = 16;

/// Early-stop variable count for the canonical $K = 8$ `JortsPoseidon2` shard ($\ell = 20 \implies 8$
/// variables = $256$ `GoldilocksExt4` evaluations), and hard cap across all schedules.
pub const EARLY_STOP_VARS: usize = 8;

/// Maximum variables folded inside a single WHIR stage ($2^6 = 64$ Radix-64 coset fiber).
pub const MAX_FOLD_STEP_VARS: usize = 6;

/// Maximum coset fiber arity ($2^{\text{MAX\_FOLD\_STEP\_VARS}} = 64$).
const MAX_FIBER_ARITY: usize = 1usize << MAX_FOLD_STEP_VARS;

/// Largest number of multilinear variables supported by the PCS (`28` -> $2^{28}$ witness entries;
/// the Stage-0 domain is then $2^{30}$, inside the $2^{31}$ cap of [`WhirSchedule::validate`]).
pub const MAX_PCS_NUM_VARS: usize = 28;

/// Largest `num_vars` the Vulkan WHIR session supports (`26` -> $K = 512$ signers in VRAM via 4-byte Kronecker tables).
#[cfg(feature = "vulkan")]
const MAX_GPU_PCS_NUM_VARS: usize = 26;

/// Largest number of polynomials committed jointly under one Round-0 Merkle-Canopy tree.
pub const MAX_BATCH_POLYS: usize = 16;

/// Largest number of base-field elements inside a single Round-0 batch leaf (`16 * 64 = 1024`).
const MAX_ROUND0_LEAF_VALS: usize = MAX_BATCH_POLYS * MAX_FIBER_ARITY;

/// Maximum number of WHIR stages across `2..=MAX_PCS_NUM_VARS` variables.
const MAX_WHIR_STAGES: usize = 4;

// Prefix-free 1-byte domain tags under `CANOPY_MIDSTATE` (`cSHAKE256("", ., "QSAG.PCS.CANOPY/v2")`):
const TAG_MERKLE_INTERNAL: u8 = qsag_whir_verified::TAG_CANOPY_MERKLE_INTERNAL;
const TAG_MERKLE_ROOT: u8 = 0x01;
const TAG_ROUND0_SALT: u8 = 0x02;
const TAG_ROUND0_SINGLE: u8 = 0x10;
const TAG_ROUND0_BATCH: u8 = 0x11;
const TAG_EXT4_STAGE_LEAF: u8 = 0x12;

// ============================================================================
// 1. WHIR Rate-Escalation Schedule (`num_vars` in `2..=28`)
// ============================================================================

/// Parameters for one WHIR folding & proximity-testing stage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WhirStageSpec {
    /// Reed–Solomon coset blowup $B_i = 1/\rho_i$ of this stage's committed oracle.
    pub blowup: usize,
    /// Number of multilinear variables $s_i \in [1, 6]$ folded during this stage's sumcheck.
    pub step_vars: usize,
    /// Target number of distinct coset fibers opened from this stage's oracle.
    /// If fewer fibers exist, every fiber is checked (exact consistency).
    pub num_queries: usize,
}

/// Johnson-radius query-accounting regimes (`BCIKS20`, agreement $\sqrt{\rho} + \eta$).
///
/// Capacity proximity-gap wire tags (`0`, `1`, `3`) are permanently retired and rejected on
/// deserialization (`Crites & Stewart 2025/2046`, `Krachun-Kazanin-Habock 2026/782`). These are
/// per-stage query bounds. The composed bounds (round-by-round errors with list sizes and
/// field errors, then BCS in the ROM and the QROM) are stated in `crates/qsag-agg/SECURITY.md` and
/// computed by `zk_hem::bounds::pcs_report`: with the 256-bit digests used here every
/// accepted regime gives 127 bits classically and 81 bits in the QROM.
///
/// The `Cdhz25*` regimes use the per-stage query tables of
/// `lean/Qsag/Protocol/Aggregation/QromSaltedMerkleStateRestoration.lean` (`HemOptimizedQromSchedule.minQueries`):
/// `Cdhz25Johnson*` is `cdhzPow16At2pow38` (pure query target `2^-200`, 16-bit PoW, stated there
/// for at most `2^38` oracle queries) and `Cdhz25ZeroPow*` is `unitaryZeroPow` (pure query target
/// `2^-214`, no PoW, stated for `Q + 1 <= 2^40`). The `Poseidon2*` variants use the same query
/// tables with the width-12 Poseidon2 Merkle-Canopy and Fiat–Shamir transcript in place of
/// `cSHAKE256`.
///
/// The `Qrom128` suffix on the CDHZ25 variants records a historical bounded-query target,
/// not a 128-bit nominal Grover work factor: the PoW profiles have 108 nominal bits and
/// require `Q <= 2^38`; the zero-PoW profiles have 107 nominal bits and require
/// `Q + 1 <= 2^40`. The bounded-query target credits grinding inside the CDHZ25 bound, which
/// no cited theorem supports; without that credit the public opening has error `2^-114.5`
/// at `Q = 2^38` (tags 5, 7, 10) and `2^-122.3` at `Q = 2^40` (tags 6, 8). No `Qrom128`
/// label, on any variant, is a 128-bit QROM security level (`crates/qsag-agg/SECURITY.md`,
/// section 0).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(u8)]
pub enum WhirSecurityRegime {
    /// `ceil(256/log2(B)) + 1` queries plus 16-bit PoW. Raw PCS tests only. Its weakest
    /// query round has error `2^-124.5` before grinding, not `2^-128`.
    BciksJohnsonClassical128 = 2,
    /// Default: `ceil(512/log2(B)) + 2` queries at the Johnson radius plus 16-bit PoW.
    /// Proven levels: 127 bits classical, 81 bits QROM (`crates/qsag-agg/SECURITY.md`).
    #[default]
    BciksJohnsonQrom128 = 4,
    /// `(202, 102, 70, 52)` queries at blowups `(4, 16, 64, 256)` plus 16-bit PoW, `cSHAKE256`.
    /// 108-bit nominal Grover work; bounded-query accounting assumes `Q <= 2^38`.
    Cdhz25JohnsonQrom128 = 5,
    /// `(216, 109, 74, 56)` queries at blowups `(4, 16, 64, 256)`, no PoW, `cSHAKE256`.
    /// 107-bit nominal Grover work; bounded-query accounting assumes `Q + 1 <= 2^40`.
    Cdhz25ZeroPowQrom128 = 6,
    /// [`Self::Cdhz25JohnsonQrom128`] query table over the Poseidon2 canopy and transcript.
    /// 108-bit nominal Grover work; bounded-query accounting assumes `Q <= 2^38`.
    Poseidon2Cdhz25JohnsonQrom128 = 7,
    /// [`Self::Cdhz25ZeroPowQrom128`] query table over the Poseidon2 canopy and transcript.
    /// 107-bit nominal Grover work; bounded-query accounting assumes `Q + 1 <= 2^40`.
    Poseidon2Cdhz25ZeroPowQrom128 = 8,
    /// [`Self::BciksJohnsonQrom128`] query table (`(258, 130, 88, 66)` + 16-bit PoW) over
    /// Role-1 12-round `TurboSHAKE256` Merkle-Canopy & PoW.
    TurboShakeBciksJohnsonQrom128 = 9,
    /// [`Self::Cdhz25JohnsonQrom128`] query table (`(202, 102, 70, 52)` + 16-bit PoW) over
    /// Role-1 12-round `TurboSHAKE256` Merkle-Canopy & PoW.
    /// 108-bit nominal Grover work; bounded-query accounting assumes `Q <= 2^38`.
    TurboShakeCdhz25JohnsonQrom128 = 10,
}

impl WhirSecurityRegime {
    /// Every wire-decodable regime.
    pub const ALL: [Self; 8] = [
        Self::BciksJohnsonClassical128,
        Self::BciksJohnsonQrom128,
        Self::Cdhz25JohnsonQrom128,
        Self::Cdhz25ZeroPowQrom128,
        Self::Poseidon2Cdhz25JohnsonQrom128,
        Self::Poseidon2Cdhz25ZeroPowQrom128,
        Self::TurboShakeBciksJohnsonQrom128,
        Self::TurboShakeCdhz25JohnsonQrom128,
    ];

    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            2 => Some(Self::BciksJohnsonClassical128),
            4 => Some(Self::BciksJohnsonQrom128),
            5 => Some(Self::Cdhz25JohnsonQrom128),
            6 => Some(Self::Cdhz25ZeroPowQrom128),
            7 => Some(Self::Poseidon2Cdhz25JohnsonQrom128),
            8 => Some(Self::Poseidon2Cdhz25ZeroPowQrom128),
            9 => Some(Self::TurboShakeBciksJohnsonQrom128),
            10 => Some(Self::TurboShakeCdhz25JohnsonQrom128),
            _ => None,
        }
    }

    /// Nominal single-round Grover search work is at least 128 bits.
    /// This is a per-round work estimate, not a security level: the proven QROM level of
    /// every regime is 81 bits (`crates/qsag-agg/SECURITY.md`, Theorem 3).
    /// Tag 2 has 72 bits, tags 4/9 have 136; tags 5/7/10 have 108 and 6/8 have 107.
    pub fn meets_unconditional_grover_128_floor(self) -> bool {
        self.qrom_grover_round_bits() >= 128
    }

    /// Uses a CDHZ25 bounded-query profile.
    /// The PoW profiles have 108-bit nominal Grover work and assume `Q <= 2^38`;
    /// the zero-PoW profiles have 107-bit nominal work and assume `Q + 1 <= 2^40`.
    /// This does not promise security at `2^64` queries or a composed security bound.
    pub fn is_bounded_query_profile(self) -> bool {
        matches!(
            self,
            Self::Cdhz25JohnsonQrom128
                | Self::Cdhz25ZeroPowQrom128
                | Self::Poseidon2Cdhz25JohnsonQrom128
                | Self::Poseidon2Cdhz25ZeroPowQrom128
                | Self::TurboShakeCdhz25JohnsonQrom128
        )
    }

    /// Accepted by the aggregate verifier's profile policy: either at least 128 bits of
    /// nominal single-round Grover work, or a CDHZ25 bounded-query profile (108 nominal
    /// bits at `Q <= 2^38`, or 107 at `Q + 1 <= 2^40`). Classical tag 2 is excluded.
    ///
    /// This is policy membership, not a security floor or a composed QROM theorem.
    /// Inspect [`Self::qrom_grover_round_bits`] and [`Self::is_bounded_query_profile`]
    /// when choosing assumptions.
    pub fn is_accepted_aggregate_profile(self) -> bool {
        self.meets_unconditional_grover_128_floor() || self.is_bounded_query_profile()
    }

    /// Merkle-Canopy trees and the Fiat–Shamir transcript use width-12 Poseidon2.
    pub fn uses_poseidon2_canopy(self) -> bool {
        matches!(
            self,
            Self::Poseidon2Cdhz25JohnsonQrom128 | Self::Poseidon2Cdhz25ZeroPowQrom128
        )
    }

    /// Role-1 outer WHIR Merkle-Canopy trees and PoW use 12-round `TurboSHAKE256` (RFC 9861).
    pub fn uses_turboshake_canopy(self) -> bool {
        matches!(
            self,
            Self::TurboShakeBciksJohnsonQrom128 | Self::TurboShakeCdhz25JohnsonQrom128
        )
    }

    /// Proof-of-Work grinding bits before every fold, stage and batch challenge squeeze.
    pub fn pow_bits(self) -> u32 {
        match self {
            Self::BciksJohnsonClassical128
            | Self::BciksJohnsonQrom128
            | Self::Cdhz25JohnsonQrom128
            | Self::Poseidon2Cdhz25JohnsonQrom128
            | Self::TurboShakeBciksJohnsonQrom128
            | Self::TurboShakeCdhz25JohnsonQrom128 => PCS_POW_BITS,
            Self::Cdhz25ZeroPowQrom128 | Self::Poseidon2Cdhz25ZeroPowQrom128 => 0,
        }
    }

    /// Exponent `t` the schedule targets: every non-exhaustive canonical stage is meant to
    /// have distinct-fiber query error below `2^-t` (checked against the finite witnesses in
    /// `pcs/affine_schedule.rs`). With the fold loss counted, tags 4 to 10 meet it at
    /// `2^17..2^24` cells; tag 2 does not (124.5 bits at worst, see
    /// `zk_hem::bounds::tests::stage_bounds_against_the_constants_asserted_by_the_regimes`).
    pub fn pure_query_target_bits(self) -> u32 {
        match self {
            Self::BciksJohnsonClassical128 => 128,
            Self::BciksJohnsonQrom128 | Self::TurboShakeBciksJohnsonQrom128 => 256,
            Self::Cdhz25JohnsonQrom128
            | Self::Poseidon2Cdhz25JohnsonQrom128
            | Self::TurboShakeCdhz25JohnsonQrom128 => 200,
            Self::Cdhz25ZeroPowQrom128 | Self::Poseidon2Cdhz25ZeroPowQrom128 => 214,
        }
    }

    /// Nominal query target plus PoW bits, before composed reduction accounting.
    /// This is not a lower bound on deployed round security: tag 2's fold-loss-adjusted
    /// query round reaches only 124.467 bits, so its nominal 144-bit figure is not attained.
    pub fn classical_fs_round_bits(self) -> u32 {
        match self {
            Self::BciksJohnsonClassical128 => 144,
            Self::BciksJohnsonQrom128 | Self::TurboShakeBciksJohnsonQrom128 => 272,
            _ => self.pure_query_target_bits() + self.pow_bits(),
        }
    }

    /// Nominal Grover round-search figure; total security requires separate reduction accounting.
    pub fn qrom_grover_round_bits(self) -> u32 {
        self.classical_fs_round_bits() / 2
    }

    fn minimum_queries(self, log_b: usize) -> usize {
        let by_blowup = |table: [usize; 4]| match log_b {
            0..=2 => table[0],
            3..=4 => table[1],
            5..=6 => table[2],
            _ => table[3],
        };
        match self {
            Self::BciksJohnsonClassical128 => 256usize.div_ceil(log_b) + 1,
            Self::BciksJohnsonQrom128 | Self::TurboShakeBciksJohnsonQrom128 => {
                512usize.div_ceil(log_b) + 2
            }
            Self::Cdhz25JohnsonQrom128
            | Self::Poseidon2Cdhz25JohnsonQrom128
            | Self::TurboShakeCdhz25JohnsonQrom128 => by_blowup([202, 102, 70, 52]),
            Self::Cdhz25ZeroPowQrom128 | Self::Poseidon2Cdhz25ZeroPowQrom128 => {
                by_blowup([216, 109, 74, 56])
            }
        }
    }

    pub fn schedule(self, num_vars: usize) -> WhirSchedule {
        let mut schedule = stage_geometry(num_vars);
        schedule.regime = self;
        for stage in &mut schedule.stages {
            stage.num_queries = self.minimum_queries(stage.blowup.trailing_zeros() as usize);
        }
        schedule
    }
}

/// Default schedule: Johnson QROM (`BciksJohnsonQrom128`), `ceil(512/log2(B)) + 2` queries plus
/// 16-bit PoW, i.e. `(258, 130, 88, 66)` at blowups `(4, 16, 64, 256)`. That puts the query
/// error of the public opening below $2^{-256}$ at a proven Johnson-radius threshold. Under
/// the scalar blend of zk-Hem the Stage-0 query error is $2^{-201}$. The composed bounds are
/// in `crates/qsag-agg/SECURITY.md` (`zk_hem::bounds`).
pub fn whir_stage_schedule(num_vars: usize) -> WhirSchedule {
    WhirSecurityRegime::default().schedule(num_vars)
}

/// Complete multi-stage WHIR rate-escalation schedule for a given `num_vars`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirSchedule {
    pub regime: WhirSecurityRegime,
    /// Remaining multilinear variables sent explicitly as `final_coeffs` (`1..=8`).
    pub early_stop_vars: usize,
    /// Ordered WHIR stages `0..M` (`1 <= M <= 4`), satisfying
    /// `early_stop_vars + sum_i stages[i].step_vars == num_vars`.
    pub stages: Vec<WhirStageSpec>,
}

// Folding geometry shared by all security regimes.
fn stage_geometry(num_vars: usize) -> WhirSchedule {
    assert!(
        (2..=MAX_PCS_NUM_VARS).contains(&num_vars),
        "unsupported PCS num_vars={num_vars}"
    );
    let sp = |blowup: usize, step_vars: usize| WhirStageSpec {
        blowup,
        step_vars,
        num_queries: 0,
    };

    if num_vars <= 6 {
        let es = if num_vars <= 3 { 1 } else { 2 };
        return WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: es,
            stages: vec![sp(16, num_vars - es)],
        };
    }
    if num_vars <= 11 {
        let es = if num_vars <= 8 { 3 } else { 4 };
        let rem = num_vars - es;
        let s0 = rem.div_ceil(2);
        let s1 = rem - s0;
        return WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: es,
            stages: vec![sp(4, s0), sp(16, s1)],
        };
    }
    if num_vars <= 16 {
        let es = if num_vars <= 13 {
            4
        } else if num_vars <= 15 {
            5
        } else {
            6
        };
        let rem = num_vars - es;
        let s0 = 4usize.min(rem - 4);
        let s1 = (rem - s0) / 2;
        let s2 = rem - s0 - s1;
        return WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: es,
            stages: vec![sp(4, s0), sp(16, s1), sp(64, s2)],
        };
    }
    if num_vars <= 20 {
        let es = num_vars - 12;
        return WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: es,
            stages: vec![sp(4, 5), sp(16, 3), sp(64, 4)],
        };
    }
    match num_vars {
        21 => WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: 8,
            stages: vec![sp(4, 6), sp(16, 3), sp(64, 4)],
        },
        22 => WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: 8,
            stages: vec![sp(4, 6), sp(16, 4), sp(64, 4)],
        },
        23 => WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: 7,
            stages: vec![sp(4, 6), sp(16, 4), sp(64, 3), sp(256, 3)],
        },
        24 => WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: 8,
            stages: vec![sp(4, 6), sp(16, 4), sp(64, 3), sp(256, 3)],
        },
        25 => WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: 8,
            stages: vec![sp(4, 6), sp(16, 4), sp(64, 4), sp(256, 3)],
        },
        26 => WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: 8,
            stages: vec![sp(4, 6), sp(16, 5), sp(64, 4), sp(256, 3)],
        },
        27 => WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: 8,
            stages: vec![sp(4, 6), sp(16, 5), sp(64, 4), sp(256, 4)],
        },
        28 => WhirSchedule {
            regime: WhirSecurityRegime::default(),
            early_stop_vars: 8,
            stages: vec![sp(4, 6), sp(16, 6), sp(64, 4), sp(256, 4)],
        },
        _ => unreachable!(),
    }
}

impl WhirSchedule {
    /// Aggregate authorization: canonical structure plus an accepted QROM profile.
    pub fn validate(&self, num_vars: usize) -> bool {
        self.validate_structural(num_vars) && self.regime.is_accepted_aggregate_profile()
    }

    /// Validate geometry, resource limits, and the canonical query table of the selected
    /// regime, without imposing aggregate authorization policy. Explicit low-level PCS
    /// callers may select classical tag 2; aggregate callers must use validate instead.
    pub fn validate_structural(&self, num_vars: usize) -> bool {
        if !(2..=MAX_PCS_NUM_VARS).contains(&num_vars)
            || !(1..=EARLY_STOP_VARS).contains(&self.early_stop_vars)
            || self.stages.is_empty()
            || self.stages.len() > MAX_WHIR_STAGES
        {
            return false;
        }
        let mut remaining = num_vars;
        for stage in &self.stages {
            if !matches!(stage.blowup, 4 | 16 | 64 | 256)
                || !(1..=MAX_FOLD_STEP_VARS).contains(&stage.step_vars)
                || stage.step_vars >= remaining
                || stage.num_queries > NUM_PCS_QUERIES
            {
                return false;
            }
            let log_b = stage.blowup.trailing_zeros() as usize;
            let min_q = self.regime.minimum_queries(log_b);
            if stage.num_queries < min_q {
                return false;
            }
            let Some(domain_u64) = 1u64
                .checked_shl(remaining as u32)
                .and_then(|n| n.checked_mul(stage.blowup as u64))
            else {
                return false;
            };
            // Bound stage domain to <= 2^31 so schedule validity is 100% deterministic across
            // 32-bit/wasm32 and 64-bit targets and stays within Goldilocks 2^32 two-adicity.
            if domain_u64 > (1u64 << 31)
                || usize::try_from(domain_u64).is_err()
                || domain_u64.trailing_zeros() > 32
            {
                return false;
            }
            remaining -= stage.step_vars;
        }
        remaining == self.early_stop_vars && self.is_canonical(num_vars)
    }

    /// Is this exactly the canonical schedule of its own regime for `num_vars`? Only canonical
    /// schedules are covered by the finite Johnson witnesses of `pcs/affine_schedule.rs`.
    pub fn is_canonical(&self, num_vars: usize) -> bool {
        (2..=MAX_PCS_NUM_VARS).contains(&num_vars) && *self == self.regime.schedule(num_vars)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![
            self.regime as u8,
            self.early_stop_vars as u8,
            self.stages.len() as u8,
        ];
        for stage in &self.stages {
            out.extend_from_slice(&(stage.blowup as u16).to_le_bytes());
            out.push(stage.step_vars as u8);
            out.extend_from_slice(&(stage.num_queries as u16).to_le_bytes());
        }
        out
    }

    pub fn from_bytes_canonical(bytes: &[u8], num_vars: usize) -> Option<(Self, usize)> {
        let regime = WhirSecurityRegime::from_u8(*bytes.first()?)?;
        let early_stop_vars = *bytes.get(1)? as usize;
        let count = *bytes.get(2)? as usize;
        if count > MAX_WHIR_STAGES {
            return None;
        }
        let mut stages = Vec::with_capacity(count);
        for chunk in bytes.get(3..3 + 5 * count)?.as_chunks::<5>().0 {
            stages.push(WhirStageSpec {
                blowup: u16::from_le_bytes([chunk[0], chunk[1]]) as usize,
                step_vars: chunk[2] as usize,
                num_queries: u16::from_le_bytes([chunk[3], chunk[4]]) as usize,
            });
        }
        let out = Self {
            regime,
            early_stop_vars,
            stages,
        };
        out.validate(num_vars).then_some((out, 3 + 5 * count))
    }
}

#[inline]
pub fn early_stop_vars_for(num_vars: usize) -> usize {
    whir_stage_schedule(num_vars).early_stop_vars
}

fn absorb_whir_schedule(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    sched: &WhirSchedule,
) {
    transcript.absorb(b"WHIR_PROTOCOL", b"AFFINE_MONOMIAL_V1");
    transcript.absorb(b"WHIR_SCHEDULE", &sched.to_bytes());
}

fn sample_stage_queries(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    stage_idx: usize,
    num_groups: usize,
    num_queries: usize,
) -> Vec<usize> {
    let target = num_queries.min(num_groups);
    let mut indices = BTreeSet::new();
    let mut label = *b"WHIR_QUERIES_S00";
    label[14] = b'0' + ((stage_idx / 10) as u8);
    label[15] = b'0' + ((stage_idx % 10) as u8);
    while indices.len() < target {
        for index in transcript.squeeze_query_indices(&label, num_groups, target - indices.len()) {
            indices.insert(index);
        }
    }
    indices.into_iter().collect()
}

// ============================================================================
// 2. Steiner-Deduplicated Merkle-Canopy Tree (`CANOPY_MIDSTATE` + 4x SIMD)
// ============================================================================

/// Compact commitment to a Merkle-Canopy tree: 32-byte `root` digest binding the tree's top node
/// to its depth `log_leaves`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CanopyCommitment {
    pub root: [u8; 32],
    pub log_leaves: u8,
}

impl CanopyCommitment {
    pub fn to_bytes(&self) -> [u8; 33] {
        let mut out = [0u8; 33];
        out[0..32].copy_from_slice(&self.root);
        out[32] = self.log_leaves;
        out
    }

    pub fn from_bytes_canonical(bytes: &[u8]) -> Option<(Self, usize)> {
        if bytes.len() < 33 {
            return None;
        }
        let log_leaves = bytes[32];
        if log_leaves > 28 {
            return None;
        }
        let mut root = [0u8; 32];
        root.copy_from_slice(&bytes[0..32]);
        Some((Self { root, log_leaves }, 33))
    }
}

/// Canonical Steiner-tree deduplicated Merkle multi-proof for a sorted set of leaf indices.
///
/// Emits solely the minimal frontier of sibling digests outside the induced binary Steiner subtree
/// spanned by the queried leaves. Near the root of the tree, queried paths coalesce and require
/// zero sibling hashes; `verify_canopy_multiproof` enforces exact consumption (`sib_cursor == len`)
/// so extra or unused sibling hashes are strictly rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanopyMultiProof {
    /// Canonical bottom-up Steiner-pruned authentication sibling digests.
    pub auth_siblings: Vec<[u8; 32]>,
}

impl CanopyMultiProof {
    pub fn push_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.auth_siblings.len() as u32).to_le_bytes());
        for h in &self.auth_siblings {
            out.extend_from_slice(h);
        }
    }

    pub fn from_bytes_canonical(bytes: &[u8]) -> Option<(Self, usize)> {
        let len_bytes = bytes.get(0..4)?;
        let sib_len =
            u32::from_le_bytes([len_bytes[0], len_bytes[1], len_bytes[2], len_bytes[3]]) as usize;
        if sib_len > NUM_PCS_QUERIES * 28 {
            return None;
        }
        let end = 4usize.checked_add(sib_len.checked_mul(32)?)?;
        let sib_bytes = bytes.get(4..end)?;
        let auth_siblings = sib_bytes.as_chunks::<32>().0.to_vec();
        Some((Self { auth_siblings }, end))
    }
}

/// Prover-side Merkle-Canopy tree (`nodes[1]` is top node; for `num_leaves >= 256`, stores only
/// internal nodes `0 .. num_leaves / 2` (`4x` lower RAM) and recomputes leaf/parent siblings on
/// opening).
pub struct MerkleCanopyTree {
    pub log_leaves: usize,
    pub is_compact: bool,
    pub is_turboshake: bool,
    pub nodes: Vec<[u8; 32]>,
    pub root: [u8; 32],
}

#[inline]
fn byte_canopy_into(turbo: bool, input: &[u8], out: &mut [u8]) {
    if turbo {
        turboshake256_from_midstate_into(&TURBOSHAKE_CANOPY_MIDSTATE, input, out);
    } else {
        cshake256_from_midstate_into(&CANOPY_MIDSTATE, input, out);
    }
}

#[inline]
fn byte_canopy_32(turbo: bool, input: &[u8]) -> [u8; 32] {
    if turbo {
        turboshake256_from_midstate_32(&TURBOSHAKE_CANOPY_MIDSTATE, input)
    } else {
        cshake256_from_midstate_32(&CANOPY_MIDSTATE, input)
    }
}

#[inline]
fn byte_canopy_32_x4(turbo: bool, inputs: [&[u8]; 4]) -> [[u8; 32]; 4] {
    if turbo {
        turboshake256_from_midstate_32_x4(&TURBOSHAKE_CANOPY_MIDSTATE, inputs)
    } else {
        cshake256_from_midstate_32_x4(&CANOPY_MIDSTATE, inputs)
    }
}

#[inline]
fn byte_canopy_32_x8(turbo: bool, inputs: [&[u8]; 8]) -> [[u8; 32]; 8] {
    if turbo {
        turboshake256_from_midstate_32_x8(&TURBOSHAKE_CANOPY_MIDSTATE, inputs)
    } else {
        cshake256_from_midstate_32_x8(&CANOPY_MIDSTATE, inputs)
    }
}

#[inline]
fn byte_canopy_16_x4(turbo: bool, inputs: [&[u8]; 4]) -> [[u8; 16]; 4] {
    if turbo {
        turboshake256_from_midstate_16_x4(&TURBOSHAKE_CANOPY_MIDSTATE, inputs)
    } else {
        cshake256_from_midstate_16_x4(&CANOPY_MIDSTATE, inputs)
    }
}

#[inline]
fn byte_canopy_16_x8(turbo: bool, inputs: [&[u8]; 8]) -> [[u8; 16]; 8] {
    if turbo {
        turboshake256_from_midstate_16_x8(&TURBOSHAKE_CANOPY_MIDSTATE, inputs)
    } else {
        cshake256_from_midstate_16_x8(&CANOPY_MIDSTATE, inputs)
    }
}

impl MerkleCanopyTree {
    pub fn build(leaf_hashes: Vec<[u8; 32]>) -> Self {
        let n = leaf_hashes.len();
        Self::build_from_fn(n, |i| leaf_hashes[i])
    }

    /// Build a 1-indexed `MerkleCanopyTree` from a scalar leaf hash closure.
    pub fn build_from_fn<F>(num_leaves: usize, leaf_fn: F) -> Self
    where
        F: Fn(usize) -> [u8; 32] + Sync,
    {
        if num_leaves >= 256 {
            return Self::build_from_fn_x4(num_leaves, |bl| {
                [
                    leaf_fn(bl),
                    leaf_fn(bl + 1),
                    leaf_fn(bl + 2),
                    leaf_fn(bl + 3),
                ]
            });
        }
        let n = num_leaves;
        assert!(n.is_power_of_two() && n >= 1);
        let log_leaves = n.trailing_zeros() as usize;
        let mut nodes = vec![[0u8; 32]; 2 * n];
        for i in 0..n {
            nodes[n + i] = leaf_fn(i);
        }
        for idx in (1..n).rev() {
            nodes[idx] = hash_merkle_internal(idx as u32, &nodes[2 * idx], &nodes[2 * idx + 1]);
        }
        let root = hash_tree_root(log_leaves as u8, &nodes[1]);
        Self {
            log_leaves,
            is_compact: false,
            is_turboshake: false,
            nodes,
            root,
        }
    }

    /// Build a 1-indexed `MerkleCanopyTree` using 4-way SIMD leaf hashing (`leaf_fn_x4(base_leaf)`
    /// hashes `base_leaf .. base_leaf + 4`) AND 4-way SIMD internal node hashing
    /// (`hash_merkle_internal_x4`), folding 16-leaf micro-subtrees in L1 registers.
    pub fn build_from_fn_x4<F4>(num_leaves: usize, leaf_fn_x4: F4) -> Self
    where
        F4: Fn(usize) -> [[u8; 32]; 4] + Sync,
    {
        Self::build_from_fn_x4_mode(false, num_leaves, leaf_fn_x4)
    }

    pub fn build_from_fn_x4_mode<F4>(turbo: bool, num_leaves: usize, leaf_fn_x4: F4) -> Self
    where
        F4: Fn(usize) -> [[u8; 32]; 4] + Sync,
    {
        let n = num_leaves;
        assert!(n.is_power_of_two() && n >= 4);
        let log_leaves = n.trailing_zeros() as usize;

        if n < 256 {
            let mut nodes = vec![[0u8; 32]; 2 * n];
            for bl in (0..n).step_by(4) {
                let h4 = leaf_fn_x4(bl);
                nodes[n + bl..n + bl + 4].copy_from_slice(&h4);
            }
            for depth in (2..log_leaves).rev() {
                let half = 1usize << depth;
                for idx in (half..2 * half).step_by(4) {
                    let p4 = hash_merkle_internal_x4_mode(
                        turbo,
                        idx as u32,
                        [
                            &nodes[2 * idx],
                            &nodes[2 * idx + 2],
                            &nodes[2 * idx + 4],
                            &nodes[2 * idx + 6],
                        ],
                        [
                            &nodes[2 * idx + 1],
                            &nodes[2 * idx + 3],
                            &nodes[2 * idx + 5],
                            &nodes[2 * idx + 7],
                        ],
                    );
                    nodes[idx..idx + 4].copy_from_slice(&p4);
                }
            }
            for idx in (1..4.min(n)).rev() {
                nodes[idx] = hash_merkle_internal_mode(
                    turbo,
                    idx as u32,
                    &nodes[2 * idx],
                    &nodes[2 * idx + 1],
                );
            }
            let root = hash_tree_root_mode(turbo, log_leaves as u8, &nodes[1]);
            return Self {
                log_leaves,
                is_compact: false,
                is_turboshake: turbo,
                nodes,
                root,
            };
        }

        // `n >= 256`: `q = n / 4 >= 64` (`q` is divisible by 4; `s16 = n / 16 >= 16` 16-leaf groups).
        let q = n / 4;
        let s16 = n / 16;
        let mut nodes = vec![[0u8; 32]; n / 2];

        let fold_16_leaves = |m: usize| -> [[u8; 32]; 4] {
            let bl = 16 * m;
            let k_base = (q + 4 * m) as u32;
            let l0 = leaf_fn_x4(bl);
            let l1 = leaf_fn_x4(bl + 4);
            let l2 = leaf_fn_x4(bl + 8);
            let l3 = leaf_fn_x4(bl + 12);
            let p_lo = hash_merkle_internal_x4_mode(
                turbo,
                2 * k_base,
                [&l0[0], &l0[2], &l1[0], &l1[2]],
                [&l0[1], &l0[3], &l1[1], &l1[3]],
            );
            let p_hi = hash_merkle_internal_x4_mode(
                turbo,
                2 * k_base + 4,
                [&l2[0], &l2[2], &l3[0], &l3[2]],
                [&l2[1], &l2[3], &l3[1], &l3[3]],
            );
            hash_merkle_internal_x4_mode(
                turbo,
                k_base,
                [&p_lo[0], &p_lo[2], &p_hi[0], &p_hi[2]],
                [&p_lo[1], &p_lo[3], &p_hi[1], &p_hi[3]],
            )
        };

        #[cfg(feature = "std")]
        if s16 >= 4 {
            let workers = crate::parallel_pow2_workers(s16);
            if workers > 1 {
                let m_chunk = s16 / workers;
                {
                    let quarter_slice = &mut nodes[q..2 * q];
                    let fold_ref = &fold_16_leaves;
                    std::thread::scope(|scope| {
                        for (t_idx, sub) in quarter_slice.chunks_mut(4 * m_chunk).enumerate() {
                            let base_m = t_idx * m_chunk;
                            crate::spawn_bounded(scope, move || {
                                for (off, dst4) in sub.as_chunks_mut::<4>().0.iter_mut().enumerate()
                                {
                                    *dst4 = fold_ref(base_m + off);
                                }
                            });
                        }
                    });
                }
                for depth in (2..=(log_leaves - 3)).rev() {
                    let half = 1usize << depth;
                    if half >= 256 {
                        let p_workers = crate::parallel_pow2_workers(half / 4);
                        let (upper, children) = nodes[..4 * half].split_at_mut(2 * half);
                        let parents = &mut upper[half..2 * half];
                        let p_chunk = half / p_workers;
                        std::thread::scope(|scope| {
                            for (t_idx, (p_sub, c_sub)) in parents
                                .chunks_mut(p_chunk)
                                .zip(children.chunks(2 * p_chunk))
                                .enumerate()
                            {
                                let base_node = half + t_idx * p_chunk;
                                crate::spawn_bounded(scope, move || {
                                    for (g, dst4) in
                                        p_sub.as_chunks_mut::<4>().0.iter_mut().enumerate()
                                    {
                                        let c = 8 * g;
                                        let out4 = hash_merkle_internal_x4_mode(
                                            turbo,
                                            (base_node + 4 * g) as u32,
                                            [
                                                &c_sub[c],
                                                &c_sub[c + 2],
                                                &c_sub[c + 4],
                                                &c_sub[c + 6],
                                            ],
                                            [
                                                &c_sub[c + 1],
                                                &c_sub[c + 3],
                                                &c_sub[c + 5],
                                                &c_sub[c + 7],
                                            ],
                                        );
                                        dst4.copy_from_slice(&out4);
                                    }
                                });
                            }
                        });
                    } else {
                        for idx in (half..2 * half).step_by(4) {
                            let out4 = hash_merkle_internal_x4_mode(
                                turbo,
                                idx as u32,
                                [
                                    &nodes[2 * idx],
                                    &nodes[2 * idx + 2],
                                    &nodes[2 * idx + 4],
                                    &nodes[2 * idx + 6],
                                ],
                                [
                                    &nodes[2 * idx + 1],
                                    &nodes[2 * idx + 3],
                                    &nodes[2 * idx + 5],
                                    &nodes[2 * idx + 7],
                                ],
                            );
                            nodes[idx..idx + 4].copy_from_slice(&out4);
                        }
                    }
                }
                for idx in [3usize, 2, 1] {
                    nodes[idx] = hash_merkle_internal_mode(
                        turbo,
                        idx as u32,
                        &nodes[2 * idx],
                        &nodes[2 * idx + 1],
                    );
                }
                let root = hash_tree_root_mode(turbo, log_leaves as u8, &nodes[1]);
                return Self {
                    log_leaves,
                    is_compact: true,
                    is_turboshake: turbo,
                    nodes,
                    root,
                };
            }
        }

        for m in 0..s16 {
            let out4 = fold_16_leaves(m);
            nodes[q + 4 * m..q + 4 * (m + 1)].copy_from_slice(&out4);
        }
        for depth in (2..=(log_leaves - 3)).rev() {
            let half = 1usize << depth;
            for idx in (half..2 * half).step_by(4) {
                let out4 = hash_merkle_internal_x4_mode(
                    turbo,
                    idx as u32,
                    [
                        &nodes[2 * idx],
                        &nodes[2 * idx + 2],
                        &nodes[2 * idx + 4],
                        &nodes[2 * idx + 6],
                    ],
                    [
                        &nodes[2 * idx + 1],
                        &nodes[2 * idx + 3],
                        &nodes[2 * idx + 5],
                        &nodes[2 * idx + 7],
                    ],
                );
                nodes[idx..idx + 4].copy_from_slice(&out4);
            }
        }
        for idx in [3usize, 2, 1] {
            nodes[idx] =
                hash_merkle_internal_mode(turbo, idx as u32, &nodes[2 * idx], &nodes[2 * idx + 1]);
        }
        let root = hash_tree_root_mode(turbo, log_leaves as u8, &nodes[1]);
        Self {
            log_leaves,
            is_compact: true,
            is_turboshake: turbo,
            nodes,
            root,
        }
    }

    /// Build a 1-indexed `MerkleCanopyTree` using 8-way SIMD leaf hashing (`leaf_fn_x8(base_leaf)`
    /// hashes `base_leaf .. base_leaf + 8`) and 8-way SIMD internal node hashing
    /// (`hash_merkle_internal_x8`), folding 16-leaf micro-subtrees in `3 × x8 + 1 × x4` vector calls.
    pub fn build_from_fn_x8<F8>(num_leaves: usize, leaf_fn_x8: F8) -> Self
    where
        F8: Fn(usize) -> [[u8; 32]; 8] + Sync,
    {
        Self::build_from_fn_x8_mode(false, num_leaves, leaf_fn_x8)
    }

    pub fn build_from_fn_x8_mode<F8>(turbo: bool, num_leaves: usize, leaf_fn_x8: F8) -> Self
    where
        F8: Fn(usize) -> [[u8; 32]; 8] + Sync,
    {
        let n = num_leaves;
        assert!(n.is_power_of_two() && n >= 8);
        let log_leaves = n.trailing_zeros() as usize;

        if n < 256 {
            let mut nodes = vec![[0u8; 32]; 2 * n];
            for bl in (0..n).step_by(8) {
                let h8 = leaf_fn_x8(bl);
                nodes[n + bl..n + bl + 8].copy_from_slice(&h8);
            }
            for depth in (3..log_leaves).rev() {
                let half = 1usize << depth;
                for idx in (half..2 * half).step_by(8) {
                    let p8 = hash_merkle_internal_x8_mode(
                        turbo,
                        idx as u32,
                        [
                            &nodes[2 * idx],
                            &nodes[2 * idx + 2],
                            &nodes[2 * idx + 4],
                            &nodes[2 * idx + 6],
                            &nodes[2 * idx + 8],
                            &nodes[2 * idx + 10],
                            &nodes[2 * idx + 12],
                            &nodes[2 * idx + 14],
                        ],
                        [
                            &nodes[2 * idx + 1],
                            &nodes[2 * idx + 3],
                            &nodes[2 * idx + 5],
                            &nodes[2 * idx + 7],
                            &nodes[2 * idx + 9],
                            &nodes[2 * idx + 11],
                            &nodes[2 * idx + 13],
                            &nodes[2 * idx + 15],
                        ],
                    );
                    nodes[idx..idx + 8].copy_from_slice(&p8);
                }
            }
            if n >= 8 {
                let p4 = hash_merkle_internal_x4_mode(
                    turbo,
                    4,
                    [&nodes[8], &nodes[10], &nodes[12], &nodes[14]],
                    [&nodes[9], &nodes[11], &nodes[13], &nodes[15]],
                );
                nodes[4..8].copy_from_slice(&p4);
            }
            for idx in [3usize, 2, 1] {
                nodes[idx] = hash_merkle_internal_mode(
                    turbo,
                    idx as u32,
                    &nodes[2 * idx],
                    &nodes[2 * idx + 1],
                );
            }
            let root = hash_tree_root_mode(turbo, log_leaves as u8, &nodes[1]);
            return Self {
                log_leaves,
                is_compact: false,
                is_turboshake: turbo,
                nodes,
                root,
            };
        }

        let q = n / 4;
        let s16 = n / 16;
        let mut nodes = vec![[0u8; 32]; n / 2];

        let fold_16_leaves = |m: usize| -> [[u8; 32]; 4] {
            let bl = 16 * m;
            let k_base = (q + 4 * m) as u32;
            let l0 = leaf_fn_x8(bl);
            let l1 = leaf_fn_x8(bl + 8);
            let p8 = hash_merkle_internal_x8_mode(
                turbo,
                2 * k_base,
                [
                    &l0[0], &l0[2], &l0[4], &l0[6], &l1[0], &l1[2], &l1[4], &l1[6],
                ],
                [
                    &l0[1], &l0[3], &l0[5], &l0[7], &l1[1], &l1[3], &l1[5], &l1[7],
                ],
            );
            hash_merkle_internal_x4_mode(
                turbo,
                k_base,
                [&p8[0], &p8[2], &p8[4], &p8[6]],
                [&p8[1], &p8[3], &p8[5], &p8[7]],
            )
        };

        #[cfg(feature = "std")]
        if s16 >= 4 {
            let workers = crate::parallel_pow2_workers(s16);
            if workers > 1 {
                let m_chunk = s16 / workers;
                {
                    let quarter_slice = &mut nodes[q..2 * q];
                    let fold_ref = &fold_16_leaves;
                    std::thread::scope(|scope| {
                        for (t_idx, sub) in quarter_slice.chunks_mut(4 * m_chunk).enumerate() {
                            let base_m = t_idx * m_chunk;
                            crate::spawn_bounded(scope, move || {
                                for (off, dst4) in sub.as_chunks_mut::<4>().0.iter_mut().enumerate()
                                {
                                    *dst4 = fold_ref(base_m + off);
                                }
                            });
                        }
                    });
                }
                for depth in (3..=(log_leaves - 3)).rev() {
                    let half = 1usize << depth;
                    if half >= 256 {
                        let p_workers = crate::parallel_pow2_workers(half / 8);
                        let (upper, children) = nodes[..4 * half].split_at_mut(2 * half);
                        let parents = &mut upper[half..2 * half];
                        let p_chunk = half / p_workers;
                        std::thread::scope(|scope| {
                            for (t_idx, (p_sub, c_sub)) in parents
                                .chunks_mut(p_chunk)
                                .zip(children.chunks(2 * p_chunk))
                                .enumerate()
                            {
                                let base_node = half + t_idx * p_chunk;
                                crate::spawn_bounded(scope, move || {
                                    for (g, dst8) in
                                        p_sub.as_chunks_mut::<8>().0.iter_mut().enumerate()
                                    {
                                        let c = 16 * g;
                                        let out8 = hash_merkle_internal_x8_mode(
                                            turbo,
                                            (base_node + 8 * g) as u32,
                                            [
                                                &c_sub[c],
                                                &c_sub[c + 2],
                                                &c_sub[c + 4],
                                                &c_sub[c + 6],
                                                &c_sub[c + 8],
                                                &c_sub[c + 10],
                                                &c_sub[c + 12],
                                                &c_sub[c + 14],
                                            ],
                                            [
                                                &c_sub[c + 1],
                                                &c_sub[c + 3],
                                                &c_sub[c + 5],
                                                &c_sub[c + 7],
                                                &c_sub[c + 9],
                                                &c_sub[c + 11],
                                                &c_sub[c + 13],
                                                &c_sub[c + 15],
                                            ],
                                        );
                                        dst8.copy_from_slice(&out8);
                                    }
                                });
                            }
                        });
                    } else {
                        for idx in (half..2 * half).step_by(8) {
                            let out8 = hash_merkle_internal_x8_mode(
                                turbo,
                                idx as u32,
                                [
                                    &nodes[2 * idx],
                                    &nodes[2 * idx + 2],
                                    &nodes[2 * idx + 4],
                                    &nodes[2 * idx + 6],
                                    &nodes[2 * idx + 8],
                                    &nodes[2 * idx + 10],
                                    &nodes[2 * idx + 12],
                                    &nodes[2 * idx + 14],
                                ],
                                [
                                    &nodes[2 * idx + 1],
                                    &nodes[2 * idx + 3],
                                    &nodes[2 * idx + 5],
                                    &nodes[2 * idx + 7],
                                    &nodes[2 * idx + 9],
                                    &nodes[2 * idx + 11],
                                    &nodes[2 * idx + 13],
                                    &nodes[2 * idx + 15],
                                ],
                            );
                            nodes[idx..idx + 8].copy_from_slice(&out8);
                        }
                    }
                }
                let out4 = hash_merkle_internal_x4_mode(
                    turbo,
                    4,
                    [&nodes[8], &nodes[10], &nodes[12], &nodes[14]],
                    [&nodes[9], &nodes[11], &nodes[13], &nodes[15]],
                );
                nodes[4..8].copy_from_slice(&out4);
                for idx in [3usize, 2, 1] {
                    nodes[idx] = hash_merkle_internal_mode(
                        turbo,
                        idx as u32,
                        &nodes[2 * idx],
                        &nodes[2 * idx + 1],
                    );
                }
                let root = hash_tree_root_mode(turbo, log_leaves as u8, &nodes[1]);
                return Self {
                    log_leaves,
                    is_compact: true,
                    is_turboshake: turbo,
                    nodes,
                    root,
                };
            }
        }

        for m in 0..s16 {
            let out4 = fold_16_leaves(m);
            nodes[q + 4 * m..q + 4 * (m + 1)].copy_from_slice(&out4);
        }
        for depth in (3..=(log_leaves - 3)).rev() {
            let half = 1usize << depth;
            for idx in (half..2 * half).step_by(8) {
                let out8 = hash_merkle_internal_x8_mode(
                    turbo,
                    idx as u32,
                    [
                        &nodes[2 * idx],
                        &nodes[2 * idx + 2],
                        &nodes[2 * idx + 4],
                        &nodes[2 * idx + 6],
                        &nodes[2 * idx + 8],
                        &nodes[2 * idx + 10],
                        &nodes[2 * idx + 12],
                        &nodes[2 * idx + 14],
                    ],
                    [
                        &nodes[2 * idx + 1],
                        &nodes[2 * idx + 3],
                        &nodes[2 * idx + 5],
                        &nodes[2 * idx + 7],
                        &nodes[2 * idx + 9],
                        &nodes[2 * idx + 11],
                        &nodes[2 * idx + 13],
                        &nodes[2 * idx + 15],
                    ],
                );
                nodes[idx..idx + 8].copy_from_slice(&out8);
            }
        }
        let out4 = hash_merkle_internal_x4_mode(
            turbo,
            4,
            [&nodes[8], &nodes[10], &nodes[12], &nodes[14]],
            [&nodes[9], &nodes[11], &nodes[13], &nodes[15]],
        );
        nodes[4..8].copy_from_slice(&out4);
        for idx in [3usize, 2, 1] {
            nodes[idx] =
                hash_merkle_internal_mode(turbo, idx as u32, &nodes[2 * idx], &nodes[2 * idx + 1]);
        }
        let root = hash_tree_root_mode(turbo, log_leaves as u8, &nodes[1]);
        Self {
            log_leaves,
            is_compact: true,
            is_turboshake: turbo,
            nodes,
            root,
        }
    }

    pub fn commitment(&self) -> CanopyCommitment {
        CanopyCommitment {
            root: self.root,
            log_leaves: self.log_leaves as u8,
        }
    }

    /// Generate a canonical Steiner-deduplicated multi-proof for `sorted_unique_indices`.
    pub fn open_multi_with_leaf_fn<F>(
        &self,
        sorted_unique_indices: &[usize],
        leaf_fn: F,
    ) -> CanopyMultiProof
    where
        F: Fn(usize) -> [u8; 32],
    {
        let n = 1usize << self.log_leaves;
        let turbo = self.is_turboshake;

        let get_node = |node_idx: usize| -> [u8; 32] {
            if !self.is_compact || node_idx < n / 2 {
                self.nodes[node_idx]
            } else if node_idx < n {
                let b = 2 * (node_idx - n / 2);
                let l0 = leaf_fn(b);
                let l1 = leaf_fn(b + 1);
                hash_merkle_internal_mode(turbo, node_idx as u32, &l0, &l1)
            } else {
                leaf_fn(node_idx - n)
            }
        };

        let mut auth_siblings = Vec::new();
        let mut active: Vec<usize> = sorted_unique_indices.iter().map(|&i| n + i).collect();
        let mut cur_depth = self.log_leaves;
        while cur_depth > 0 {
            let mut write = 0usize;
            let mut k = 0usize;
            while k < active.len() {
                let u = active[k];
                let sib = u ^ 1;
                if k + 1 < active.len() && active[k + 1] == sib {
                    k += 2;
                } else {
                    auth_siblings.push(get_node(sib));
                    k += 1;
                }
                active[write] = u >> 1;
                write += 1;
            }
            active.truncate(write);
            cur_depth -= 1;
        }
        CanopyMultiProof { auth_siblings }
    }
}

/// Verify a canonical Steiner-deduplicated `CanopyMultiProof` against `commitment` and
/// strictly ascending `(index, leaf_hash)` pairs.
pub fn verify_canopy_multiproof(
    commitment: &CanopyCommitment,
    sorted_leaves: &[(usize, [u8; 32])],
    proof: &CanopyMultiProof,
) -> bool {
    verify_canopy_multiproof_byte(false, commitment, sorted_leaves, proof)
}

fn verify_canopy_multiproof_byte(
    turbo: bool,
    commitment: &CanopyCommitment,
    sorted_leaves: &[(usize, [u8; 32])],
    proof: &CanopyMultiProof,
) -> bool {
    let _phase = crate::profile::span("verify_canopy_multiproof");
    let log_leaves = commitment.log_leaves as usize;
    if log_leaves > 28 {
        return false;
    }
    let n = 1usize << log_leaves;
    if sorted_leaves.is_empty() {
        return false;
    }
    for w in sorted_leaves.windows(2) {
        if w[0].0 >= w[1].0 {
            return false;
        }
    }
    if sorted_leaves.last().is_some_and(|leaf| leaf.0 >= n) {
        return false;
    }

    let mut active: Vec<(usize, [u8; 32])> =
        sorted_leaves.iter().map(|&(idx, h)| (n + idx, h)).collect();
    let mut sib_cursor = 0usize;
    let mut cur_depth = log_leaves;
    while cur_depth > 0 {
        let mut write = 0usize;
        let mut k = 0usize;
        while k < active.len() {
            let mut parents = [0u32; 8];
            let mut lefts = [[0u8; 32]; 8];
            let mut rights = [[0u8; 32]; 8];
            let mut lanes = 0;
            // Read up to 8 frontier parent steps before overwriting the in-place frontier.
            while lanes < 8 && k < active.len() {
                let (u, hu) = active[k];
                let sib = u ^ 1;
                let hsib = if k + 1 < active.len() && active[k + 1].0 == sib {
                    let coalesced = active[k + 1].1;
                    k += 2;
                    coalesced
                } else {
                    let Some(&supplied) = proof.auth_siblings.get(sib_cursor) else {
                        return false;
                    };
                    sib_cursor += 1;
                    k += 1;
                    supplied
                };
                let Some(pair) = qsag_whir_verified::step_merkle_pair_order(u as u64, 0, hu, hsib)
                else {
                    return false;
                };
                parents[lanes] = (u >> 1) as u32;
                lefts[lanes] = pair.left;
                rights[lanes] = pair.right;
                lanes += 1;
            }
            if lanes == 8 {
                let hashes =
                    hash_merkle_nodes_x8_mode(turbo, parents, lefts.each_ref(), rights.each_ref());
                for lane in 0..8 {
                    active[write + lane] = (parents[lane] as usize, hashes[lane]);
                }
            } else {
                let mut done = 0usize;
                if lanes >= 4 {
                    let p4 = [parents[0], parents[1], parents[2], parents[3]];
                    let l4 = [&lefts[0], &lefts[1], &lefts[2], &lefts[3]];
                    let r4 = [&rights[0], &rights[1], &rights[2], &rights[3]];
                    let hashes = hash_merkle_nodes_x4_mode(turbo, p4, l4, r4);
                    for lane in 0..4 {
                        active[write + lane] = (parents[lane] as usize, hashes[lane]);
                    }
                    done = 4;
                }
                for lane in done..lanes {
                    active[write + lane] = (
                        parents[lane] as usize,
                        hash_merkle_internal_mode(
                            turbo,
                            parents[lane],
                            &lefts[lane],
                            &rights[lane],
                        ),
                    );
                }
            }
            write += lanes;
        }
        active.truncate(write);
        cur_depth -= 1;
    }
    if sib_cursor != proof.auth_siblings.len() {
        return false;
    }
    matches!(active.as_slice(), [(1, top)] if hash_tree_root_mode(turbo, commitment.log_leaves, top) == commitment.root)
}

/// Zero-alloc fixed-frame internal node hash (`[0x00] || node_idx(4B) || left(32B) || right(32B)` = `69` bytes).
#[inline]
fn hash_merkle_internal_tagged_mode(
    turbo: bool,
    tag: u8,
    node_idx: u32,
    left: &[u8; 32],
    right: &[u8; 32],
) -> [u8; 32] {
    let mut buf = [0u8; 69];
    buf[0] = tag;
    buf[1..5].copy_from_slice(&node_idx.to_le_bytes());
    buf[5..37].copy_from_slice(left);
    buf[37..69].copy_from_slice(right);
    byte_canopy_32(turbo, &buf)
}

#[inline]
fn hash_merkle_internal_mode(
    turbo: bool,
    node_idx: u32,
    left: &[u8; 32],
    right: &[u8; 32],
) -> [u8; 32] {
    hash_merkle_internal_tagged_mode(turbo, TAG_MERKLE_INTERNAL, node_idx, left, right)
}

#[inline]
fn hash_merkle_internal(node_idx: u32, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    hash_merkle_internal_mode(false, node_idx, left, right)
}

/// 4-way SIMD internal node hash (`4` consecutive parent indices `base_node_idx .. base_node_idx + 4`).
#[inline]
fn hash_merkle_internal_x4_mode(
    turbo: bool,
    base_node_idx: u32,
    lefts: [&[u8; 32]; 4],
    rights: [&[u8; 32]; 4],
) -> [[u8; 32]; 4] {
    hash_merkle_nodes_x4_mode(
        turbo,
        core::array::from_fn(|k| base_node_idx + k as u32),
        lefts,
        rights,
    )
}

#[cfg(test)]
#[inline]
fn hash_merkle_internal_x4(
    base_node_idx: u32,
    lefts: [&[u8; 32]; 4],
    rights: [&[u8; 32]; 4],
) -> [[u8; 32]; 4] {
    hash_merkle_internal_x4_mode(false, base_node_idx, lefts, rights)
}

/// Hash four arbitrary frontier positions, preserving the node-index domain binding.
#[inline]
fn hash_merkle_nodes_x4_mode(
    turbo: bool,
    indices: [u32; 4],
    lefts: [&[u8; 32]; 4],
    rights: [&[u8; 32]; 4],
) -> [[u8; 32]; 4] {
    let mut bufs = [[0u8; 69]; 4];
    for k in 0..4 {
        bufs[k][0] = TAG_MERKLE_INTERNAL;
        bufs[k][1..5].copy_from_slice(&indices[k].to_le_bytes());
        bufs[k][5..37].copy_from_slice(lefts[k]);
        bufs[k][37..69].copy_from_slice(rights[k]);
    }
    byte_canopy_32_x4(turbo, [&bufs[0], &bufs[1], &bufs[2], &bufs[3]])
}

/// 8-way SIMD internal node hash (`8` consecutive parent indices `base_node_idx .. base_node_idx + 8`).
#[inline]
fn hash_merkle_internal_x8_mode(
    turbo: bool,
    base_node_idx: u32,
    lefts: [&[u8; 32]; 8],
    rights: [&[u8; 32]; 8],
) -> [[u8; 32]; 8] {
    hash_merkle_nodes_x8_mode(
        turbo,
        core::array::from_fn(|k| base_node_idx + k as u32),
        lefts,
        rights,
    )
}

#[cfg(test)]
#[inline]
fn hash_merkle_internal_x8(
    base_node_idx: u32,
    lefts: [&[u8; 32]; 8],
    rights: [&[u8; 32]; 8],
) -> [[u8; 32]; 8] {
    hash_merkle_internal_x8_mode(false, base_node_idx, lefts, rights)
}

/// Hash eight arbitrary frontier positions simultaneously.
#[inline]
fn hash_merkle_nodes_x8_mode(
    turbo: bool,
    indices: [u32; 8],
    lefts: [&[u8; 32]; 8],
    rights: [&[u8; 32]; 8],
) -> [[u8; 32]; 8] {
    let mut bufs = [[0u8; 69]; 8];
    for k in 0..8 {
        bufs[k][0] = TAG_MERKLE_INTERNAL;
        bufs[k][1..5].copy_from_slice(&indices[k].to_le_bytes());
        bufs[k][5..37].copy_from_slice(lefts[k]);
        bufs[k][37..69].copy_from_slice(rights[k]);
    }
    byte_canopy_32_x8(turbo, bufs.each_ref().map(|b| b.as_slice()))
}

/// Commitment digest of a tree: its top node bound to `log_leaves` (`34` bytes, `1` Keccak block).
#[inline]
fn hash_tree_root_mode(turbo: bool, log_leaves: u8, top_node: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 34];
    buf[0] = TAG_MERKLE_ROOT;
    buf[1] = log_leaves;
    buf[2..34].copy_from_slice(top_node);
    byte_canopy_32(turbo, &buf)
}

#[inline]
fn hash_tree_root(log_leaves: u8, top_node: &[u8; 32]) -> [u8; 32] {
    hash_tree_root_mode(false, log_leaves, top_node)
}

/// Deterministic Round-0 per-fiber 16-byte blinding salt (`37` bytes, `1` Keccak block).
#[inline]
fn derive_round0_salt_mode(turbo: bool, salt_seed: &[u8; 32], group_idx: u32) -> [u8; 16] {
    let mut buf = [0u8; 37];
    buf[0] = TAG_ROUND0_SALT;
    buf[1..33].copy_from_slice(salt_seed);
    buf[33..37].copy_from_slice(&group_idx.to_le_bytes());
    let mut out = [0u8; 16];
    byte_canopy_into(turbo, &buf, &mut out);
    out
}

#[inline]
fn derive_round0_salt(salt_seed: &[u8; 32], group_idx: u32) -> [u8; 16] {
    derive_round0_salt_mode(false, salt_seed, group_idx)
}

/// 4-way SIMD Round-0 salt derivation for fibers `base_group .. base_group + 4`.
#[inline]
fn derive_round0_salt_x4_mode(turbo: bool, salt_seed: &[u8; 32], base_group: u32) -> [[u8; 16]; 4] {
    let mut bufs = [[0u8; 37]; 4];
    for (k, buf) in bufs.iter_mut().enumerate() {
        buf[0] = TAG_ROUND0_SALT;
        buf[1..33].copy_from_slice(salt_seed);
        buf[33..37].copy_from_slice(&(base_group + k as u32).to_le_bytes());
    }
    byte_canopy_16_x4(turbo, [&bufs[0], &bufs[1], &bufs[2], &bufs[3]])
}

/// 8-way SIMD Round-0 salt derivation for fibers `base_group .. base_group + 8`.
#[inline]
fn derive_round0_salt_x8_mode(turbo: bool, salt_seed: &[u8; 32], base_group: u32) -> [[u8; 16]; 8] {
    let mut bufs = [[0u8; 37]; 8];
    for (k, buf) in bufs.iter_mut().enumerate() {
        buf[0] = TAG_ROUND0_SALT;
        buf[1..33].copy_from_slice(salt_seed);
        buf[33..37].copy_from_slice(&(base_group + k as u32).to_le_bytes());
    }
    byte_canopy_16_x8(turbo, bufs.each_ref().map(|b| b.as_slice()))
}

/// Zero-alloc single-polynomial Round-0 salted leaf hash (`arity` in `{2, 4, 8, 16, 32, 64}`).
#[inline]
fn hash_salted_base_group_mode(
    turbo: bool,
    leaf_idx: u32,
    salt: &[u8; 16],
    vals: &[Goldilocks],
) -> [u8; 32] {
    let arity = vals.len();
    debug_assert!(arity.is_power_of_two() && (2..=MAX_FIBER_ARITY).contains(&arity));
    let mut buf = [0u8; 22 + 8 * MAX_FIBER_ARITY];
    buf[0] = TAG_ROUND0_SINGLE;
    buf[1] = arity as u8;
    buf[2..6].copy_from_slice(&leaf_idx.to_le_bytes());
    buf[6..22].copy_from_slice(salt);
    for (i, v) in vals.iter().enumerate() {
        buf[22 + 8 * i..22 + 8 * (i + 1)].copy_from_slice(&v.to_le_bytes());
    }
    let used = 22 + 8 * arity;
    byte_canopy_32(turbo, &buf[..used])
}

/// Round-0 salted leaf hash across `num_polys` codewords.
fn hash_round0_leaf_mode(
    turbo: bool,
    leaf_idx: u32,
    salt: &[u8; 16],
    num_polys: usize,
    vals: &[Goldilocks],
) -> [u8; 32] {
    if num_polys == 1 {
        return hash_salted_base_group_mode(turbo, leaf_idx, salt, vals);
    }
    debug_assert!(num_polys <= MAX_BATCH_POLYS && vals.len() <= MAX_ROUND0_LEAF_VALS);
    let arity = vals.len() / num_polys;
    let used_bytes = 23 + 8 * vals.len();
    if vals.len() <= 128 {
        let mut buf = [0u8; 23 + 8 * 128];
        buf[0] = TAG_ROUND0_BATCH;
        buf[1] = arity as u8;
        buf[2] = num_polys as u8;
        buf[3..7].copy_from_slice(&leaf_idx.to_le_bytes());
        buf[7..23].copy_from_slice(salt);
        for (dst, v) in buf[23..used_bytes]
            .as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(vals)
        {
            *dst = v.to_le_bytes();
        }
        return byte_canopy_32(turbo, &buf[..used_bytes]);
    }
    let mut buf = [0u8; 23 + 8 * MAX_ROUND0_LEAF_VALS];
    buf[0] = TAG_ROUND0_BATCH;
    buf[1] = arity as u8;
    buf[2] = num_polys as u8;
    buf[3..7].copy_from_slice(&leaf_idx.to_le_bytes());
    buf[7..23].copy_from_slice(salt);
    for (dst, v) in buf[23..used_bytes]
        .as_chunks_mut::<8>()
        .0
        .iter_mut()
        .zip(vals)
    {
        *dst = v.to_le_bytes();
    }
    byte_canopy_32(turbo, &buf[..used_bytes])
}

/// Four arbitrary queried leaves, with exactly the scalar wire framing in every lane.
fn queried_round0_hash_x4_mode(
    turbo: bool,
    indices: &[usize],
    salts: &[[u8; 16]],
    num_polys: usize,
    vals: &[Goldilocks],
    per_query: usize,
) -> [[u8; 32]; 4] {
    if num_polys == 1 {
        let used = 22 + 8 * per_query;
        let mut bufs = [[0u8; 22 + 8 * MAX_FIBER_ARITY]; 4];
        for (lane, buf) in bufs.iter_mut().enumerate() {
            buf[0] = TAG_ROUND0_SINGLE;
            buf[1] = per_query as u8;
            buf[2..6].copy_from_slice(&(indices[lane] as u32).to_le_bytes());
            buf[6..22].copy_from_slice(&salts[lane]);
            for (dst, v) in buf[22..used]
                .as_chunks_mut::<8>()
                .0
                .iter_mut()
                .zip(&vals[lane * per_query..(lane + 1) * per_query])
            {
                *dst = v.to_le_bytes();
            }
        }
        return byte_canopy_32_x4(turbo, bufs.each_ref().map(|b| &b[..used]));
    }
    let mut bufs = [[0u8; 23 + 8 * MAX_ROUND0_LEAF_VALS]; 4];
    let header = 23;
    let used = header + 8 * per_query;
    for (lane, buf) in bufs.iter_mut().enumerate() {
        buf[0] = TAG_ROUND0_BATCH;
        buf[1] = (per_query / num_polys) as u8;
        buf[2] = num_polys as u8;
        buf[3..7].copy_from_slice(&(indices[lane] as u32).to_le_bytes());
        buf[7..header].copy_from_slice(&salts[lane]);
        for (dst, v) in buf[header..used]
            .as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(&vals[lane * per_query..(lane + 1) * per_query])
        {
            *dst = v.to_le_bytes();
        }
    }
    byte_canopy_32_x4(turbo, bufs.each_ref().map(|b| &b[..used]))
}

fn queried_ext4_hash_x4_mode(
    turbo: bool,
    stage: u8,
    indices: &[usize],
    vals: &[GoldilocksExt4],
    arity: usize,
) -> [[u8; 32]; 4] {
    let mut bufs = [[0u8; 7 + 32 * MAX_FIBER_ARITY]; 4];
    let used = 7 + 32 * arity;
    for (lane, buf) in bufs.iter_mut().enumerate() {
        buf[0] = TAG_EXT4_STAGE_LEAF;
        buf[1] = stage;
        buf[2] = arity as u8;
        buf[3..7].copy_from_slice(&(indices[lane] as u32).to_le_bytes());
        for (dst, v) in buf[7..used]
            .as_chunks_mut::<32>()
            .0
            .iter_mut()
            .zip(&vals[lane * arity..(lane + 1) * arity])
        {
            *dst = v.to_le_bytes();
        }
    }
    byte_canopy_32_x4(turbo, bufs.each_ref().map(|b| &b[..used]))
}

/// 4-way SIMD Round-0 salted leaf hash for 4 consecutive fibers `base_g .. base_g + 4`.
fn round0_leaf_hash_x4_mode(
    turbo: bool,
    codewords: &[Vec<Goldilocks>],
    salt_seed: &[u8; 32],
    base_g: usize,
    num_groups: usize,
    arity: usize,
) -> [[u8; 32]; 4] {
    let salts = derive_round0_salt_x4_mode(turbo, salt_seed, base_g as u32);
    if let [codeword] = codewords {
        let used = 22 + 8 * arity;
        let mut bufs = [[0u8; 22 + 8 * MAX_FIBER_ARITY]; 4];
        for lane in 0..4 {
            let g = base_g + lane;
            bufs[lane][0] = TAG_ROUND0_SINGLE;
            bufs[lane][1] = arity as u8;
            bufs[lane][2..6].copy_from_slice(&(g as u32).to_le_bytes());
            bufs[lane][6..22].copy_from_slice(&salts[lane]);
            for k in 0..arity {
                let v = codeword[g + k * num_groups];
                bufs[lane][22 + 8 * k..22 + 8 * (k + 1)].copy_from_slice(&v.to_le_bytes());
            }
        }
        return byte_canopy_32_x4(
            turbo,
            [
                &bufs[0][..used],
                &bufs[1][..used],
                &bufs[2][..used],
                &bufs[3][..used],
            ],
        );
    }

    let num_polys = codewords.len();
    let total_vals = num_polys * arity;
    let used = 23 + 8 * total_vals;
    if total_vals <= 128 {
        let mut bufs = [[0u8; 23 + 8 * 128]; 4];
        for lane in 0..4 {
            let g = base_g + lane;
            bufs[lane][0] = TAG_ROUND0_BATCH;
            bufs[lane][1] = arity as u8;
            bufs[lane][2] = num_polys as u8;
            bufs[lane][3..7].copy_from_slice(&(g as u32).to_le_bytes());
            bufs[lane][7..23].copy_from_slice(&salts[lane]);
            let mut pos = 23usize;
            for cw in codewords {
                for k in 0..arity {
                    bufs[lane][pos..pos + 8].copy_from_slice(&cw[g + k * num_groups].to_le_bytes());
                    pos += 8;
                }
            }
        }
        return byte_canopy_32_x4(
            turbo,
            [
                &bufs[0][..used],
                &bufs[1][..used],
                &bufs[2][..used],
                &bufs[3][..used],
            ],
        );
    }

    let mut bufs: Vec<Vec<u8>> = (0..4).map(|_| vec![0u8; used]).collect();
    for lane in 0..4 {
        let g = base_g + lane;
        bufs[lane][0] = TAG_ROUND0_BATCH;
        bufs[lane][1] = arity as u8;
        bufs[lane][2] = num_polys as u8;
        bufs[lane][3..7].copy_from_slice(&(g as u32).to_le_bytes());
        bufs[lane][7..23].copy_from_slice(&salts[lane]);
        let mut pos = 23usize;
        for cw in codewords {
            for k in 0..arity {
                bufs[lane][pos..pos + 8].copy_from_slice(&cw[g + k * num_groups].to_le_bytes());
                pos += 8;
            }
        }
    }
    byte_canopy_32_x4(turbo, [&bufs[0], &bufs[1], &bufs[2], &bufs[3]])
}

/// Scalar Round-0 leaf hash of fiber `g` (used during `open_multi_with_leaf_fn`).
fn round0_leaf_hash_mode(
    turbo: bool,
    codewords: &[Vec<Goldilocks>],
    salt_seed: &[u8; 32],
    g: usize,
    num_groups: usize,
    arity: usize,
) -> [u8; 32] {
    let salt = derive_round0_salt_mode(turbo, salt_seed, g as u32);
    if let [codeword] = codewords {
        let vals = collect_coset_group_base(codeword, g, num_groups, arity);
        return hash_salted_base_group_mode(turbo, g as u32, &salt, &vals[..arity]);
    }
    let used = codewords.len() * arity;
    let mut vals = [Goldilocks::ZERO; MAX_ROUND0_LEAF_VALS];
    for (chunk, codeword) in vals[..used].chunks_exact_mut(arity).zip(codewords) {
        for (k, slot) in chunk.iter_mut().enumerate() {
            *slot = codeword[g + k * num_groups];
        }
    }
    hash_round0_leaf_mode(turbo, g as u32, &salt, codewords.len(), &vals[..used])
}

/// Zero-alloc Stage `>= 1` `GoldilocksExt4` coset fiber leaf hash (`arity` in `{2, 4, 8, 16, 32, 64}`).
#[inline]
fn hash_ext4_group_mode(
    turbo: bool,
    stage_idx: u8,
    leaf_idx: u32,
    vals: &[GoldilocksExt4],
) -> [u8; 32] {
    let arity = vals.len();
    debug_assert!(arity.is_power_of_two() && (2..=MAX_FIBER_ARITY).contains(&arity));
    let mut buf = [0u8; 7 + 32 * MAX_FIBER_ARITY];
    buf[0] = TAG_EXT4_STAGE_LEAF;
    buf[1] = stage_idx;
    buf[2] = arity as u8;
    buf[3..7].copy_from_slice(&leaf_idx.to_le_bytes());
    for (i, v) in vals.iter().enumerate() {
        buf[7 + 32 * i..7 + 32 * (i + 1)].copy_from_slice(&v.to_le_bytes());
    }
    let used = 7 + 32 * arity;
    byte_canopy_32(turbo, &buf[..used])
}

/// 4-way SIMD Stage `>= 1` `GoldilocksExt4` coset fiber leaf hash for `base_g .. base_g + 4`.
fn hash_ext4_group_x4_mode(
    turbo: bool,
    stage_idx: u8,
    codeword: &[GoldilocksExt4],
    base_g: usize,
    num_groups: usize,
    arity: usize,
) -> [[u8; 32]; 4] {
    let used = 7 + 32 * arity;
    if arity <= 16 {
        let mut bufs = [[0u8; 7 + 32 * 16]; 4];
        for (lane, buf) in bufs.iter_mut().enumerate() {
            let g = base_g + lane;
            buf[0] = TAG_EXT4_STAGE_LEAF;
            buf[1] = stage_idx;
            buf[2] = arity as u8;
            buf[3..7].copy_from_slice(&(g as u32).to_le_bytes());
            for k in 0..arity {
                let b = codeword[g + k * num_groups].to_le_bytes();
                buf[7 + 32 * k..7 + 32 * (k + 1)].copy_from_slice(&b);
            }
        }
        return byte_canopy_32_x4(
            turbo,
            [
                &bufs[0][..used],
                &bufs[1][..used],
                &bufs[2][..used],
                &bufs[3][..used],
            ],
        );
    }
    let mut bufs = [[0u8; 7 + 32 * MAX_FIBER_ARITY]; 4];
    for (lane, buf) in bufs.iter_mut().enumerate() {
        let g = base_g + lane;
        buf[0] = TAG_EXT4_STAGE_LEAF;
        buf[1] = stage_idx;
        buf[2] = arity as u8;
        buf[3..7].copy_from_slice(&(g as u32).to_le_bytes());
        for k in 0..arity {
            let b = codeword[g + k * num_groups].to_le_bytes();
            buf[7 + 32 * k..7 + 32 * (k + 1)].copy_from_slice(&b);
        }
    }
    byte_canopy_32_x4(
        turbo,
        [
            &bufs[0][..used],
            &bufs[1][..used],
            &bufs[2][..used],
            &bufs[3][..used],
        ],
    )
}

/// 8-way SIMD Round-0 salted leaf hash for 8 consecutive fibers `base_g .. base_g + 8`.
fn round0_leaf_hash_x8_mode(
    turbo: bool,
    codewords: &[Vec<Goldilocks>],
    salt_seed: &[u8; 32],
    base_g: usize,
    num_groups: usize,
    arity: usize,
) -> [[u8; 32]; 8] {
    let salts = derive_round0_salt_x8_mode(turbo, salt_seed, base_g as u32);
    if let [codeword] = codewords {
        let used = 22 + 8 * arity;
        let mut bufs = [[0u8; 22 + 8 * MAX_FIBER_ARITY]; 8];
        for lane in 0..8 {
            let g = base_g + lane;
            bufs[lane][0] = TAG_ROUND0_SINGLE;
            bufs[lane][1] = arity as u8;
            bufs[lane][2..6].copy_from_slice(&(g as u32).to_le_bytes());
            bufs[lane][6..22].copy_from_slice(&salts[lane]);
            for k in 0..arity {
                let v = codeword[g + k * num_groups];
                bufs[lane][22 + 8 * k..22 + 8 * (k + 1)].copy_from_slice(&v.to_le_bytes());
            }
        }
        return byte_canopy_32_x8(turbo, bufs.each_ref().map(|b| &b[..used]));
    }

    let num_polys = codewords.len();
    let total_vals = num_polys * arity;
    let used = 23 + 8 * total_vals;
    if total_vals <= 128 {
        let mut bufs = [[0u8; 23 + 8 * 128]; 8];
        for lane in 0..8 {
            let g = base_g + lane;
            bufs[lane][0] = TAG_ROUND0_BATCH;
            bufs[lane][1] = arity as u8;
            bufs[lane][2] = num_polys as u8;
            bufs[lane][3..7].copy_from_slice(&(g as u32).to_le_bytes());
            bufs[lane][7..23].copy_from_slice(&salts[lane]);
            let mut pos = 23usize;
            for cw in codewords {
                for k in 0..arity {
                    bufs[lane][pos..pos + 8].copy_from_slice(&cw[g + k * num_groups].to_le_bytes());
                    pos += 8;
                }
            }
        }
        return byte_canopy_32_x8(turbo, bufs.each_ref().map(|b| &b[..used]));
    }

    let mut bufs: Vec<Vec<u8>> = (0..8).map(|_| vec![0u8; used]).collect();
    for lane in 0..8 {
        let g = base_g + lane;
        bufs[lane][0] = TAG_ROUND0_BATCH;
        bufs[lane][1] = arity as u8;
        bufs[lane][2] = num_polys as u8;
        bufs[lane][3..7].copy_from_slice(&(g as u32).to_le_bytes());
        bufs[lane][7..23].copy_from_slice(&salts[lane]);
        let mut pos = 23usize;
        for cw in codewords {
            for k in 0..arity {
                bufs[lane][pos..pos + 8].copy_from_slice(&cw[g + k * num_groups].to_le_bytes());
                pos += 8;
            }
        }
    }
    byte_canopy_32_x8(
        turbo,
        [
            &bufs[0], &bufs[1], &bufs[2], &bufs[3], &bufs[4], &bufs[5], &bufs[6], &bufs[7],
        ],
    )
}

/// 8-way SIMD Stage `>= 1` `GoldilocksExt4` coset fiber leaf hash for `base_g .. base_g + 8`.
fn hash_ext4_group_x8_mode(
    turbo: bool,
    stage_idx: u8,
    codeword: &[GoldilocksExt4],
    base_g: usize,
    num_groups: usize,
    arity: usize,
) -> [[u8; 32]; 8] {
    let used = 7 + 32 * arity;
    if arity <= 16 {
        let mut bufs = [[0u8; 7 + 32 * 16]; 8];
        for (lane, buf) in bufs.iter_mut().enumerate() {
            let g = base_g + lane;
            buf[0] = TAG_EXT4_STAGE_LEAF;
            buf[1] = stage_idx;
            buf[2] = arity as u8;
            buf[3..7].copy_from_slice(&(g as u32).to_le_bytes());
            for k in 0..arity {
                let b = codeword[g + k * num_groups].to_le_bytes();
                buf[7 + 32 * k..7 + 32 * (k + 1)].copy_from_slice(&b);
            }
        }
        return byte_canopy_32_x8(turbo, bufs.each_ref().map(|b| &b[..used]));
    }
    let mut bufs = [[0u8; 7 + 32 * MAX_FIBER_ARITY]; 8];
    for (lane, buf) in bufs.iter_mut().enumerate() {
        let g = base_g + lane;
        buf[0] = TAG_EXT4_STAGE_LEAF;
        buf[1] = stage_idx;
        buf[2] = arity as u8;
        buf[3..7].copy_from_slice(&(g as u32).to_le_bytes());
        for k in 0..arity {
            let b = codeword[g + k * num_groups].to_le_bytes();
            buf[7 + 32 * k..7 + 32 * (k + 1)].copy_from_slice(&b);
        }
    }
    byte_canopy_32_x8(turbo, bufs.each_ref().map(|b| &b[..used]))
}

// ============================================================================
// 2B. Poseidon2 & TurboSHAKE256 Merkle-Canopy
// ============================================================================

/// Merkle-Canopy hash backend of one committed oracle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CanopyHash {
    /// `CANOPY_MIDSTATE` 24-round `cSHAKE256` digests.
    Cshake256,
    /// `TURBOSHAKE_CANOPY_MIDSTATE` 12-round `TurboSHAKE256` digests.
    TurboShake256,
    /// Width-12 Poseidon2 digests (four canonical `Goldilocks` limbs, little-endian) for the
    /// oracle of WHIR stage `stage_idx`.
    Poseidon2 { stage_idx: u8 },
}

impl CanopyHash {
    /// Backend of the stage-`stage_idx` oracle under `regime`.
    pub fn for_stage(regime: WhirSecurityRegime, stage_idx: usize) -> Self {
        if regime.uses_poseidon2_canopy() {
            Self::Poseidon2 {
                stage_idx: stage_idx as u8,
            }
        } else if regime.uses_turboshake_canopy() {
            Self::TurboShake256
        } else {
            Self::Cshake256
        }
    }

    #[inline]
    fn byte_turbo_mode(self) -> Option<bool> {
        match self {
            Self::Cshake256 => Some(false),
            Self::TurboShake256 => Some(true),
            Self::Poseidon2 { .. } => None,
        }
    }
}

/// Node key of the Poseidon2 canopy tree of stage `stage_idx` with `2^log_leaves` leaves. The
/// trees carry no tree-level salt; blinding salts enter the Round-0 leaves.
#[inline]
pub fn poseidon2_canopy_key(stage_idx: u8, log_leaves: u8) -> [Goldilocks; 4] {
    crate::sponge::poseidon2_canopy_tree_key(stage_idx, log_leaves, [Goldilocks::ZERO; 4])
}

/// Poseidon2 internal node `node_idx` (1-indexed heap position) over two child digests.
/// `None` if a child is not four canonical limbs.
#[inline]
pub fn poseidon2_canopy_node(
    key: [Goldilocks; 4],
    node_idx: u32,
    left: &[u8; 32],
    right: &[u8; 32],
) -> Option<[u8; 32]> {
    let l = crate::sponge::bytes32_to_limbs4_le_canonical(left)?;
    let r = crate::sponge::bytes32_to_limbs4_le_canonical(right)?;
    Some(crate::sponge::limbs4_to_le_bytes32(
        crate::sponge::poseidon2_canopy_internal(node_idx, key, l, r),
    ))
}

/// Poseidon2 commitment digest binding the top node to `(stage_idx, log_leaves)`.
/// `None` if `top_node` is not four canonical limbs.
#[inline]
pub fn poseidon2_canopy_commitment_root(
    stage_idx: u8,
    log_leaves: u8,
    top_node: &[u8; 32],
) -> Option<[u8; 32]> {
    let top = crate::sponge::bytes32_to_limbs4_le_canonical(top_node)?;
    Some(crate::sponge::limbs4_to_le_bytes32(
        crate::sponge::poseidon2_canopy_root(stage_idx, log_leaves, [Goldilocks::ZERO; 4], top),
    ))
}

/// Poseidon2 Round-0 salted leaf: capacity `[leaf_idx, arity, num_polys, 0]`, rate stream
/// `[salt[0..7], salt[7..14], salt[14..16]] ++ vals` under the single- or batch-leaf domain tag.
pub fn poseidon2_round0_leaf(
    leaf_idx: u32,
    salt: &[u8; 16],
    num_polys: usize,
    vals: &[Goldilocks],
) -> [u8; 32] {
    debug_assert!((1..=MAX_BATCH_POLYS).contains(&num_polys) && vals.len() <= MAX_ROUND0_LEAF_VALS);
    let arity = vals.len() / num_polys;
    let mut limbs = [Goldilocks::ZERO; 3 + MAX_ROUND0_LEAF_VALS];
    for (dst, chunk) in limbs.iter_mut().zip(salt.chunks(7)) {
        let mut word = [0u8; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        *dst = Goldilocks::from_u64_reduced(u64::from_le_bytes(word));
    }
    limbs[3..3 + vals.len()].copy_from_slice(vals);
    let domain = if num_polys == 1 {
        crate::sponge::P2_DOMAIN_CANOPY_LEAF_R0
    } else {
        crate::sponge::P2_DOMAIN_CANOPY_LEAF_BATCH
    };
    let out = crate::sponge::poseidon2_sponge_hash_limbs(
        domain,
        [
            Goldilocks::from_u64_reduced(leaf_idx as u64),
            Goldilocks::from_u64_reduced(arity as u64),
            Goldilocks::from_u64_reduced(num_polys as u64),
            Goldilocks::ZERO,
        ],
        &limbs[..3 + vals.len()],
    );
    qsag_asm::volatile_fill(&mut limbs[..3 + vals.len()], Goldilocks::ZERO);
    crate::sponge::limbs4_to_le_bytes32(out)
}

/// Poseidon2 stage `>= 1` leaf over one `GoldilocksExt4` coset fiber: capacity
/// `[leaf_idx, arity, stage_idx, 0]`, rate stream the four limbs of every value in order.
pub fn poseidon2_ext4_leaf(stage_idx: u8, leaf_idx: u32, vals: &[GoldilocksExt4]) -> [u8; 32] {
    debug_assert!(vals.len() <= MAX_FIBER_ARITY);
    let mut limbs = [Goldilocks::ZERO; 4 * MAX_FIBER_ARITY];
    for (dst, v) in limbs.as_chunks_mut::<4>().0.iter_mut().zip(vals) {
        *dst = v.to_limbs();
    }
    crate::sponge::limbs4_to_le_bytes32(crate::sponge::poseidon2_sponge_hash_limbs(
        crate::sponge::P2_DOMAIN_CANOPY_LEAF_EXT4,
        [
            Goldilocks::from_u64_reduced(leaf_idx as u64),
            Goldilocks::from_u64_reduced(vals.len() as u64),
            Goldilocks::from_u64_reduced(stage_idx as u64),
            Goldilocks::ZERO,
        ],
        &limbs[..4 * vals.len()],
    ))
}

impl MerkleCanopyTree {
    /// Build the full (non-compact) Poseidon2 canopy tree of stage `stage_idx` from a leaf digest
    /// closure. `leaf_fn` must return canonical Poseidon2 digests.
    pub fn build_poseidon2<F>(num_leaves: usize, stage_idx: u8, leaf_fn: F) -> Self
    where
        F: Fn(usize) -> [u8; 32] + Sync,
    {
        let n = num_leaves;
        assert!(n.is_power_of_two() && n >= 1);
        let log_leaves = n.trailing_zeros() as usize;
        assert!(log_leaves <= 28);
        let key = poseidon2_canopy_key(stage_idx, log_leaves as u8);
        let mut nodes = vec![[0u8; 32]; 2 * n];
        fill_indexed(&mut nodes[n..], leaf_fn);
        #[cfg(feature = "vulkan")]
        if let Some((gpu_nodes, root)) =
            crate::acceleration::build_poseidon2_canopy_tree(&nodes[n..], stage_idx)
        {
            return Self {
                log_leaves,
                is_compact: false,
                is_turboshake: false,
                nodes: gpu_nodes,
                root,
            };
        }
        for depth in (0..log_leaves).rev() {
            let half = 1usize << depth;
            let (upper, children) = nodes[..4 * half].split_at_mut(2 * half);
            let children = &*children;
            fill_indexed(&mut upper[half..], |i| {
                match poseidon2_canopy_node(
                    key,
                    (half + i) as u32,
                    &children[2 * i],
                    &children[2 * i + 1],
                ) {
                    Some(parent) => parent,
                    None => panic!("non-canonical Poseidon2 canopy digest"),
                }
            });
        }
        let root = match poseidon2_canopy_commitment_root(stage_idx, log_leaves as u8, &nodes[1]) {
            Some(root) => root,
            None => panic!("non-canonical Poseidon2 canopy digest"),
        };
        Self {
            log_leaves,
            is_compact: false,
            is_turboshake: false,
            nodes,
            root,
        }
    }
}

/// Verify a canonical Steiner-deduplicated `CanopyMultiProof` under `hash` against `commitment`
/// and strictly ascending `(index, leaf_hash)` pairs.
pub fn verify_canopy_multiproof_with(
    hash: CanopyHash,
    commitment: &CanopyCommitment,
    sorted_leaves: &[(usize, [u8; 32])],
    proof: &CanopyMultiProof,
) -> bool {
    let stage_idx = match hash {
        CanopyHash::Cshake256 => {
            return verify_canopy_multiproof_byte(false, commitment, sorted_leaves, proof);
        }
        CanopyHash::TurboShake256 => {
            return verify_canopy_multiproof_byte(true, commitment, sorted_leaves, proof);
        }
        CanopyHash::Poseidon2 { stage_idx } => stage_idx,
    };
    let _phase = crate::profile::span("verify_canopy_multiproof_poseidon2");
    let log_leaves = commitment.log_leaves as usize;
    if log_leaves > 28 || sorted_leaves.is_empty() {
        return false;
    }
    let n = 1usize << log_leaves;
    if sorted_leaves.windows(2).any(|w| w[0].0 >= w[1].0)
        || sorted_leaves.last().is_some_and(|leaf| leaf.0 >= n)
    {
        return false;
    }
    let key = poseidon2_canopy_key(stage_idx, commitment.log_leaves);
    let mut active: Vec<(usize, [u8; 32])> =
        sorted_leaves.iter().map(|&(idx, h)| (n + idx, h)).collect();
    let mut sib_cursor = 0usize;
    for _ in 0..log_leaves {
        let mut write = 0usize;
        let mut k = 0usize;
        while k < active.len() {
            let (u, hu) = active[k];
            let sib = u ^ 1;
            let hsib = if k + 1 < active.len() && active[k + 1].0 == sib {
                let coalesced = active[k + 1].1;
                k += 2;
                coalesced
            } else {
                let Some(&supplied) = proof.auth_siblings.get(sib_cursor) else {
                    return false;
                };
                sib_cursor += 1;
                k += 1;
                supplied
            };
            let Some(pair) = qsag_whir_verified::step_merkle_pair_order(u as u64, 0, hu, hsib)
            else {
                return false;
            };
            let Some(parent) = poseidon2_canopy_node(key, (u >> 1) as u32, &pair.left, &pair.right)
            else {
                return false;
            };
            active[write] = (u >> 1, parent);
            write += 1;
        }
        active.truncate(write);
    }
    if sib_cursor != proof.auth_siblings.len() {
        return false;
    }
    matches!(
        active.as_slice(),
        [(1, top)] if poseidon2_canopy_commitment_root(stage_idx, commitment.log_leaves, top)
            == Some(commitment.root)
    )
}

/// Round-0 leaf digest of opened values under `hash`.
#[inline]
fn round0_leaf_digest(
    hash: CanopyHash,
    leaf_idx: u32,
    salt: &[u8; 16],
    num_polys: usize,
    vals: &[Goldilocks],
) -> [u8; 32] {
    match hash {
        CanopyHash::Cshake256 => hash_round0_leaf_mode(false, leaf_idx, salt, num_polys, vals),
        CanopyHash::TurboShake256 => hash_round0_leaf_mode(true, leaf_idx, salt, num_polys, vals),
        CanopyHash::Poseidon2 { .. } => poseidon2_round0_leaf(leaf_idx, salt, num_polys, vals),
    }
}

/// Poseidon2 Round-0 leaf digest of fiber `g` read from the committed codewords.
fn poseidon2_round0_leaf_from_codewords(
    codewords: &[Vec<Goldilocks>],
    salt_seed: &[u8; 32],
    g: usize,
    num_groups: usize,
    arity: usize,
) -> [u8; 32] {
    let salt = derive_round0_salt(salt_seed, g as u32);
    let used = codewords.len() * arity;
    let mut vals = [Goldilocks::ZERO; MAX_ROUND0_LEAF_VALS];
    for (chunk, codeword) in vals[..used].chunks_exact_mut(arity).zip(codewords) {
        for (k, slot) in chunk.iter_mut().enumerate() {
            *slot = codeword[g + k * num_groups];
        }
    }
    let out = poseidon2_round0_leaf(g as u32, &salt, codewords.len(), &vals[..used]);
    qsag_asm::volatile_fill(&mut vals[..used], Goldilocks::ZERO);
    out
}

/// Commit one `GoldilocksExt4` stage codeword under the canopy backend of `regime`.
fn build_ext4_stage_tree(
    regime: WhirSecurityRegime,
    stage_idx: u8,
    codeword: &[GoldilocksExt4],
    num_groups: usize,
    arity: usize,
) -> MerkleCanopyTree {
    if regime.uses_poseidon2_canopy() {
        return MerkleCanopyTree::build_poseidon2(num_groups, stage_idx, |g| {
            let fiber = collect_coset_group_ext4(codeword, g, num_groups, arity);
            poseidon2_ext4_leaf(stage_idx, g as u32, &fiber[..arity])
        });
    }
    let turbo = regime.uses_turboshake_canopy();
    if num_groups >= 8 {
        MerkleCanopyTree::build_from_fn_x8_mode(turbo, num_groups, |base_g| {
            hash_ext4_group_x8_mode(turbo, stage_idx, codeword, base_g, num_groups, arity)
        })
    } else {
        MerkleCanopyTree::build_from_fn_x4_mode(turbo, num_groups, |base_g| {
            hash_ext4_group_x4_mode(turbo, stage_idx, codeword, base_g, num_groups, arity)
        })
    }
}

/// Leaf digest of one `GoldilocksExt4` stage fiber under `hash`.
#[inline]
fn ext4_leaf_digest(
    hash: CanopyHash,
    stage_idx: u8,
    leaf_idx: u32,
    vals: &[GoldilocksExt4],
) -> [u8; 32] {
    match hash {
        CanopyHash::Cshake256 => hash_ext4_group_mode(false, stage_idx, leaf_idx, vals),
        CanopyHash::TurboShake256 => hash_ext4_group_mode(true, stage_idx, leaf_idx, vals),
        CanopyHash::Poseidon2 { .. } => poseidon2_ext4_leaf(stage_idx, leaf_idx, vals),
    }
}

// ============================================================================
// 3. `Hem` WHIR Proof Structures & Canonical Wire Serialization
// ============================================================================

/// Prover-side state for one commitment to `num_polys() >= 1` multilinear polynomials over
/// `Goldilocks`, all with `num_vars` variables.
pub struct HemWhirProverState {
    pub num_vars: usize,
    pub schedule: WhirSchedule,
    pub group_arity_0: usize,
    /// Boolean-hypercube evaluations, one table per committed polynomial.
    pub hypercube_evals: Vec<Vec<Goldilocks>>,
    /// Stage-0 Reed–Solomon codewords, one per committed polynomial.
    pub codewords_0: Vec<Vec<Goldilocks>>,
    /// Cached Stage-0 monomial coefficients for public CPU commits (empty in hiding/GPU mode).
    pub(crate) monomial_coeffs_0: Vec<Vec<Goldilocks>>,
    /// Whether the committed polynomials hold secret witness data requiring volatile zeroization.
    pub(crate) secret: bool,
    pub salt_seed: [u8; 32],
    pub tree_0: MerkleCanopyTree,
    /// GPU commits retain only a top-node stub; CPU commits retain opening-capable nodes.
    round0_tree_on_cpu: bool,
    #[cfg(feature = "vulkan")]
    pub(crate) gpu_session: Option<crate::acceleration::GpuWhirSession>,
}

impl Drop for HemWhirProverState {
    fn drop(&mut self) {
        if self.secret {
            for values in self
                .hypercube_evals
                .iter_mut()
                .chain(&mut self.codewords_0)
                .chain(&mut self.monomial_coeffs_0)
            {
                qsag_asm::volatile_fill(values, Goldilocks::ZERO);
            }
            qsag_asm::volatile_fill(&mut self.salt_seed, 0);
        }
    }
}

impl HemWhirProverState {
    #[inline]
    pub fn num_polys(&self) -> usize {
        self.hypercube_evals.len()
    }

    #[inline]
    pub fn commitment(&self) -> CanopyCommitment {
        self.tree_0.commitment()
    }

    #[inline]
    fn num_groups_0(&self) -> usize {
        ((1usize << self.num_vars) * self.schedule.stages[0].blowup) / self.group_arity_0
    }
}

/// Re-encoded intermediate WHIR stage oracle (`stage_idx` in `1..M`): carries the stage's
/// escalated-rate Merkle commitment, two independent OOD evaluations, 16-bit stage PoW nonce,
/// opened coset fibers, and Steiner-deduplicated Merkle multi-proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirStageProof {
    pub commitment: CanopyCommitment,
    pub stage_ood_evals: [GoldilocksExt4; 2],
    pub pow_nonce: u64,
    /// `arity` `GoldilocksExt4` values per queried fiber, in strictly ascending fiber order.
    pub opened_vals: Vec<GoldilocksExt4>,
    pub multiproof: CanopyMultiProof,
}

/// Complete `Hem` WHIR rate-escalated opening proof over `GoldilocksExt4` against one commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemWhirOpeningProof {
    /// Two independent out-of-domain evaluations of the Stage-0 polynomial.
    pub stage0_ood_evals: [GoldilocksExt4; 2],
    /// Affine bridge scalars `[sigma_even, tau_01, tau_10, c_F, c_G]` per fold.
    /// Cross terms precede phi; shifted claims precede the 16-bit fold PoW and theta/alpha/beta.
    pub fold_sumcheck_polys: Vec<[GoldilocksExt4; 5]>,
    /// 16-bit transcript Proof-of-Work nonces bound before each fold's `[theta, alpha, beta]`
    /// combiner squeeze (`whir_folding_pow_bits = 16`).
    pub fold_pow_nonces: Vec<u64>,
    /// Re-encoded escalated-rate WHIR stages `1..M`, each committed strictly before its stage's
    /// sumcheck challenges and Stage `k-1` shift queries are squeezed.
    pub folded_layers: Vec<WhirStageProof>,
    /// Terminal monomial coefficients: exactly `2^early_stop + 2` elements,
    /// including the two degree-overflow slots.
    pub final_coeffs: Vec<GoldilocksExt4>,
    /// 16-bit transcript Proof-of-Work nonce for Stage 0's fiber queries.
    pub pow_nonce: u64,
    /// 16-byte blinding salt of each queried Stage-0 leaf, in ascending leaf order.
    pub round0_salts: Vec<[u8; 16]>,
    /// Stage-0 leaf contents: per queried leaf, `group_arity_0` base-field values for each
    /// committed polynomial in commitment order.
    pub round0_vals: Vec<Goldilocks>,
    /// Steiner-deduplicated Merkle-Canopy multi-proof for Stage 0.
    pub round0_multiproof: CanopyMultiProof,
}

fn read_u32(bytes: &[u8], pos: &mut usize) -> Option<u32> {
    let chunk = bytes.get(*pos..pos.checked_add(4)?)?;
    *pos += 4;
    Some(u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]))
}

fn read_u64(bytes: &[u8], pos: &mut usize) -> Option<u64> {
    let chunk = bytes.get(*pos..pos.checked_add(8)?)?;
    let mut b = [0u8; 8];
    b.copy_from_slice(chunk);
    *pos += 8;
    Some(u64::from_le_bytes(b))
}

fn read_ext4(bytes: &[u8], pos: &mut usize) -> Option<GoldilocksExt4> {
    let chunk = bytes.get(*pos..pos.checked_add(32)?)?;
    let mut arr = [0u8; 32];
    arr.copy_from_slice(chunk);
    *pos += 32;
    GoldilocksExt4::from_le_bytes_canonical(arr)
}

fn read_sumcheck_wire_polys<const N: usize>(
    bytes: &[u8],
    pos: &mut usize,
    max_rounds: usize,
) -> Option<Vec<[GoldilocksExt4; N]>> {
    let n = read_u32(bytes, pos)? as usize;
    if n > max_rounds {
        return None;
    }
    let mut polys = Vec::with_capacity(n);
    for _ in 0..n {
        let mut wire = [GoldilocksExt4::ZERO; N];
        for v in &mut wire {
            *v = read_ext4(bytes, pos)?;
        }
        polys.push(wire);
    }
    Some(polys)
}

fn push_sumcheck_wire_polys<const N: usize>(polys: &[[GoldilocksExt4; N]], out: &mut Vec<u8>) {
    out.extend_from_slice(&(polys.len() as u32).to_le_bytes());
    for poly in polys {
        for v in poly {
            out.extend_from_slice(&v.to_le_bytes());
        }
    }
}

impl HemWhirOpeningProof {
    pub fn push_bytes(&self, out: &mut Vec<u8>) {
        assert_eq!(
            self.fold_sumcheck_polys.len(),
            self.fold_pow_nonces.len(),
            "fold sumcheck and fold PoW nonce lengths differ"
        );
        for v in self.stage0_ood_evals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        push_sumcheck_wire_polys(&self.fold_sumcheck_polys, out);
        for &nonce in &self.fold_pow_nonces {
            out.extend_from_slice(&nonce.to_le_bytes());
        }
        out.extend_from_slice(&(self.folded_layers.len() as u32).to_le_bytes());
        for layer in &self.folded_layers {
            out.extend_from_slice(&layer.commitment.to_bytes());
            for v in layer.stage_ood_evals {
                out.extend_from_slice(&v.to_le_bytes());
            }
            out.extend_from_slice(&layer.pow_nonce.to_le_bytes());
            out.extend_from_slice(&(layer.opened_vals.len() as u32).to_le_bytes());
            for v in &layer.opened_vals {
                out.extend_from_slice(&v.to_le_bytes());
            }
            layer.multiproof.push_bytes(out);
        }
        out.extend_from_slice(&(self.final_coeffs.len() as u32).to_le_bytes());
        for v in &self.final_coeffs {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&self.pow_nonce.to_le_bytes());
        out.extend_from_slice(&(self.round0_salts.len() as u32).to_le_bytes());
        for salt in &self.round0_salts {
            out.extend_from_slice(salt);
        }
        out.extend_from_slice(&(self.round0_vals.len() as u32).to_le_bytes());
        for v in &self.round0_vals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        self.round0_multiproof.push_bytes(out);
    }

    pub fn from_bytes_canonical(bytes: &[u8]) -> Option<(Self, usize)> {
        let mut pos = 0usize;
        let stage0_ood_evals = [read_ext4(bytes, &mut pos)?, read_ext4(bytes, &mut pos)?];
        let fold_sumcheck_polys = read_sumcheck_wire_polys(bytes, &mut pos, MAX_PCS_NUM_VARS)?;
        let mut fold_pow_nonces = Vec::with_capacity(fold_sumcheck_polys.len());
        for _ in 0..fold_sumcheck_polys.len() {
            fold_pow_nonces.push(read_u64(bytes, &mut pos)?);
        }

        let n_layers = read_u32(bytes, &mut pos)? as usize;
        if n_layers >= MAX_WHIR_STAGES {
            return None;
        }
        let mut folded_layers = Vec::with_capacity(n_layers);
        for _ in 0..n_layers {
            let (commitment, used_c) = CanopyCommitment::from_bytes_canonical(bytes.get(pos..)?)?;
            pos += used_c;
            let stage_ood_evals = [read_ext4(bytes, &mut pos)?, read_ext4(bytes, &mut pos)?];
            let layer_pow_nonce = read_u64(bytes, &mut pos)?;
            let n_vals = read_u32(bytes, &mut pos)? as usize;
            if n_vals == 0 || n_vals > NUM_PCS_QUERIES * MAX_FIBER_ARITY || (n_vals & 1) != 0 {
                return None;
            }
            let mut opened_vals = Vec::with_capacity(n_vals);
            for _ in 0..n_vals {
                opened_vals.push(read_ext4(bytes, &mut pos)?);
            }
            let (multiproof, used_mp) = CanopyMultiProof::from_bytes_canonical(bytes.get(pos..)?)?;
            pos += used_mp;
            folded_layers.push(WhirStageProof {
                commitment,
                stage_ood_evals,
                pow_nonce: layer_pow_nonce,
                opened_vals,
                multiproof,
            });
        }

        let n_final = read_u32(bytes, &mut pos)? as usize;
        if !(4..=((1usize << EARLY_STOP_VARS) + 2)).contains(&n_final)
            || !(n_final - 2).is_power_of_two()
        {
            return None;
        }
        let mut final_coeffs = Vec::with_capacity(n_final);
        for _ in 0..n_final {
            final_coeffs.push(read_ext4(bytes, &mut pos)?);
        }

        let pow_nonce = read_u64(bytes, &mut pos)?;

        let n_queries = read_u32(bytes, &mut pos)? as usize;
        if n_queries == 0 || n_queries > NUM_PCS_QUERIES {
            return None;
        }
        let salt_bytes = bytes.get(pos..pos.checked_add(16 * n_queries)?)?;
        let round0_salts: Vec<[u8; 16]> = salt_bytes.as_chunks::<16>().0.to_vec();
        pos += 16 * n_queries;

        let n_r0 = read_u32(bytes, &mut pos)? as usize;
        if n_r0 == 0 || !n_r0.is_multiple_of(n_queries) || n_r0 / n_queries > MAX_ROUND0_LEAF_VALS {
            return None;
        }
        let val_bytes = bytes.get(pos..pos.checked_add(8 * n_r0)?)?;
        let mut round0_vals = Vec::with_capacity(n_r0);
        for &lb in val_bytes.as_chunks::<8>().0 {
            round0_vals.push(Goldilocks::from_le_bytes_canonical(lb).ok()?);
        }
        pos += 8 * n_r0;

        let (round0_multiproof, used_r0_mp) =
            CanopyMultiProof::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += used_r0_mp;

        Some((
            Self {
                stage0_ood_evals,
                fold_sumcheck_polys,
                fold_pow_nonces,
                folded_layers,
                final_coeffs,
                pow_nonce,
                round0_salts,
                round0_vals,
                round0_multiproof,
            },
            pos,
        ))
    }
}

/// Batched opening proof for evaluation claims $W_i(p_i) = e_i$ across $S \ge 1$ polynomials
/// committed under one `CanopyCommitment`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemWhirBatchOpeningProof {
    /// Wire-compressed `[c_0, c_2]` point-reduction sumcheck polynomials, one per variable.
    /// Empty when $S = 1$.
    pub point_sumcheck_polys: Vec<[GoldilocksExt4; 2]>,
    /// Claimed evaluations $W_i(\rho)$ at the common `Ext4` point $\rho$. Empty when $S = 1$.
    pub common_point_evals: Vec<GoldilocksExt4>,
    /// Shifted monomial functional claims, absorbed before affine batching.
    pub shifted_evals: Vec<GoldilocksExt4>,
    /// 16-bit transcript Proof-of-Work nonce bound before squeezing `PCS_BATCH_AFFINE_THETA`
    /// (`0` when $S = 1$).
    pub batch_pow_nonce: u64,
    /// Single opening of the degree-preserving asymmetric affine cascade.
    pub opening: HemWhirOpeningProof,
}

impl HemWhirBatchOpeningProof {
    pub fn push_bytes(&self, out: &mut Vec<u8>) {
        assert_eq!(
            self.common_point_evals.len(),
            self.shifted_evals.len(),
            "batch evaluation lengths differ"
        );
        push_sumcheck_wire_polys(&self.point_sumcheck_polys, out);
        out.extend_from_slice(&(self.common_point_evals.len() as u32).to_le_bytes());
        for v in &self.common_point_evals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        for v in &self.shifted_evals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&self.batch_pow_nonce.to_le_bytes());
        self.opening.push_bytes(out);
    }

    pub fn from_bytes_canonical(bytes: &[u8]) -> Option<(Self, usize)> {
        let mut pos = 0usize;
        let point_sumcheck_polys = read_sumcheck_wire_polys(bytes, &mut pos, MAX_PCS_NUM_VARS)?;
        let n_evals = read_u32(bytes, &mut pos)? as usize;
        if n_evals > MAX_BATCH_POLYS {
            return None;
        }
        let mut common_point_evals = Vec::with_capacity(n_evals);
        for _ in 0..n_evals {
            common_point_evals.push(read_ext4(bytes, &mut pos)?);
        }
        let mut shifted_evals = Vec::with_capacity(n_evals);
        for _ in 0..n_evals {
            shifted_evals.push(read_ext4(bytes, &mut pos)?);
        }
        let batch_pow_nonce = read_u64(bytes, &mut pos)?;
        if n_evals == 0 && batch_pow_nonce != 0 {
            return None;
        }
        let (opening, used) = HemWhirOpeningProof::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += used;
        Some((
            Self {
                point_sumcheck_polys,
                common_point_evals,
                shifted_evals,
                batch_pow_nonce,
                opening,
            },
            pos,
        ))
    }
}

// ============================================================================
// 4. Möbius Basis Transforms, Fast Parallel Kernels & Fiber Folding
// ============================================================================

/// Blocks of `2^MOBIUS_CACHE_BLOCK_LOG` cells complete their low variables while cache-resident.
const MOBIUS_CACHE_BLOCK_LOG: usize = 13;

/// Möbius steps for variables `0..bits` of `a` (`a.len()` a multiple of `2^bits`): cache-resident
/// blocks first, then the remaining variables two per pass. Each step is the exact subtraction
/// `hi -= lo`, so the result does not depend on the blocking.
fn mobius_steps_blocked<T>(a: &mut [T], bits: usize)
where
    T: Copy + core::ops::SubAssign,
{
    let step = |a: &mut [T], bit: usize| {
        let stride = 1usize << bit;
        for block in a.chunks_exact_mut(2 * stride) {
            let (lo, hi) = block.split_at_mut(stride);
            for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                *h -= l;
            }
        }
    };
    let low = bits.min(MOBIUS_CACHE_BLOCK_LOG);
    for block in a.chunks_exact_mut(1usize << low) {
        for bit in 0..low {
            step(block, bit);
        }
    }
    let mut bit = low;
    while bit + 1 < bits {
        let stride = 1usize << bit;
        for block in a.chunks_exact_mut(4 * stride) {
            let (lo, hi) = block.split_at_mut(2 * stride);
            let (q0, q1) = lo.split_at_mut(stride);
            let (q2, q3) = hi.split_at_mut(stride);
            for k in 0..stride {
                q1[k] -= q0[k];
                q3[k] -= q2[k];
                q2[k] -= q0[k];
                q3[k] -= q1[k];
            }
        }
        bit += 2;
    }
    if bit < bits {
        step(a, bit);
    }
}

pub(crate) fn hypercube_to_monomial_in_place<T>(coeffs: &mut [T], parallel_min_len: usize)
where
    T: Copy + Send + Sync + core::ops::SubAssign,
{
    let ell = coeffs.len().trailing_zeros() as usize;
    #[cfg(feature = "std")]
    if coeffs.len() >= parallel_min_len {
        let threads = crate::parallel_pow2_workers(coeffs.len() / 2);
        let chunk_n = coeffs.len() / threads;
        let chunk_bits = chunk_n.trailing_zeros() as usize;
        std::thread::scope(|scope| {
            for sub in coeffs.chunks_mut(chunk_n) {
                crate::spawn_bounded(scope, move || mobius_steps_blocked(sub, chunk_bits));
            }
        });
        for bit in chunk_bits..ell {
            let stride = 1usize << bit;
            for block in coeffs.chunks_mut(stride * 2) {
                let (lo, hi) = block.split_at_mut(stride);
                let sub_len = (stride / threads).max(1);
                std::thread::scope(|scope| {
                    for (lo_c, hi_c) in lo.chunks(sub_len).zip(hi.chunks_mut(sub_len)) {
                        crate::spawn_bounded(scope, move || {
                            for (h, &l) in hi_c.iter_mut().zip(lo_c.iter()) {
                                *h -= l;
                            }
                        });
                    }
                });
            }
        }
        return;
    }
    #[cfg(not(feature = "std"))]
    let _ = parallel_min_len;
    mobius_steps_blocked(coeffs, ell);
}

/// Convert boolean-hypercube evaluations `evals[0..2^\ell]` into multilinear monomial coefficients.
pub fn hypercube_to_monomial_coeffs(evals: &[Goldilocks]) -> Vec<Goldilocks> {
    assert!(evals.len().is_power_of_two() && evals.len() >= 2);
    let mut coeffs = evals.to_vec();
    hypercube_to_monomial_in_place(&mut coeffs, 32_768);
    coeffs
}

/// Convert `GoldilocksExt4` boolean-hypercube evaluations into multilinear monomial coefficients.
pub fn hypercube_to_monomial_coeffs_ext4(evals: &[GoldilocksExt4]) -> Vec<GoldilocksExt4> {
    assert!(evals.len().is_power_of_two() && evals.len() >= 2);
    let mut coeffs = evals.to_vec();
    hypercube_to_monomial_in_place(&mut coeffs, 8_192);
    coeffs
}

/// Parallel `build_eq_table_ext4` for large variable counts (`>= 14`), bit-identical to
/// [`build_eq_table_ext4`].
fn build_eq_table_ext4_fast(r: &[GoldilocksExt4]) -> Vec<GoldilocksExt4> {
    #[cfg(feature = "std")]
    if r.len() >= 14 {
        let split = r.len() - 4;
        let top_weights = build_eq_table_ext4(&r[split..]);
        let bot = &r[..split];
        let sub_len = 1usize << split;
        let mut out = vec![GoldilocksExt4::ZERO; 1usize << r.len()];
        std::thread::scope(|scope| {
            for (t_idx, sub) in out.chunks_mut(sub_len).enumerate() {
                let init = top_weights[t_idx];
                crate::spawn_bounded(scope, move || {
                    sub[0] = init;
                    let mut cur_len = 1usize;
                    for &ri in bot.iter().rev() {
                        for idx in (0..cur_len).rev() {
                            let v = sub[idx];
                            let vr = v * ri;
                            sub[2 * idx] = v - vr;
                            sub[2 * idx + 1] = vr;
                        }
                        cur_len *= 2;
                    }
                });
            }
        });
        return out;
    }
    build_eq_table_ext4(r)
}

#[inline]
fn collect_coset_group_base(
    codeword: &[Goldilocks],
    group_idx: usize,
    num_groups: usize,
    arity: usize,
) -> [Goldilocks; MAX_FIBER_ARITY] {
    let mut out = [Goldilocks::ZERO; MAX_FIBER_ARITY];
    for (k, slot) in out.iter_mut().enumerate().take(arity) {
        *slot = codeword[group_idx + k * num_groups];
    }
    out
}

#[inline]
fn collect_coset_group_ext4(
    codeword: &[GoldilocksExt4],
    group_idx: usize,
    num_groups: usize,
    arity: usize,
) -> [GoldilocksExt4; MAX_FIBER_ARITY] {
    let mut out = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
    for (k, slot) in out.iter_mut().enumerate().take(arity) {
        *slot = codeword[group_idx + k * num_groups];
    }
    out
}

// The wire tower basis is [1, u², u, u³]; the extracted core uses polynomial order.
fn to_verified_ext4(x: GoldilocksExt4) -> qsag_whir_verified::Ext4 {
    let l = x.to_limbs();
    qsag_whir_verified::Ext4 {
        a: l[0].to_canonical_u64(),
        b: l[2].to_canonical_u64(),
        c: l[1].to_canonical_u64(),
        d: l[3].to_canonical_u64(),
    }
}
fn from_verified_ext4(x: qsag_whir_verified::Ext4) -> GoldilocksExt4 {
    GoldilocksExt4::from_limbs([x.a, x.c, x.b, x.d].map(Goldilocks::from_u64_reduced))
}

/// A coset fiber folded through every challenge but the last: the remaining duet
/// `(v0, v1)` at `±x`, with the base-field scalars the last extracted fold step consumes.
struct FiberLastDuet {
    v0: GoldilocksExt4,
    v1: GoldilocksExt4,
    inv_two_x: Goldilocks,
    x_sq: Goldilocks,
    chal: [GoldilocksExt4; 3],
}

impl FiberLastDuet {
    /// Last fold step, matching `qsag_whir_verified::cwyz_duet_fold` over `GoldilocksExt4`.
    #[inline]
    fn fold(&self, inv_two: Goldilocks) -> GoldilocksExt4 {
        let [theta, alpha, beta] = self.chal;
        let even = (self.v0 + self.v1).mul_base(inv_two);
        let odd = (self.v0 - self.v1).mul_base(self.inv_two_x);
        let mixed = even + theta * odd;
        let gamma = alpha + beta.mul_base(self.x_sq);
        odd + gamma * mixed
    }

    /// Extracted acceptance gate: the last fold step lands exactly on `claimed`.
    #[inline]
    fn accepts(&self, inv_two: Goldilocks, claimed: qsag_whir_verified::Ext4) -> bool {
        let [theta, alpha, beta] = self.chal;
        let algebraic_gate = crate::recursive_fold::DuetFoldStatement {
            v0: self.v0,
            v1: self.v1,
            theta,
            alpha,
            beta,
            inv_two,
            inv_two_x: self.inv_two_x,
            x_sq: self.x_sq,
            claimed: from_verified_ext4(qsag_whir_verified::Ext4 {
                a: claimed.a,
                b: claimed.b,
                c: claimed.c,
                d: claimed.d,
            }),
        };
        if !algebraic_gate.accepts() {
            return false;
        }
        #[cfg(all(test, feature = "std"))]
        crate::recursive_fold::capture_gate(&algebraic_gate);
        let odd = (self.v0 - self.v1).mul_base(self.inv_two_x);
        let gamma = alpha + beta.mul_base(self.x_sq);
        let affine_claim = from_verified_ext4(qsag_whir_verified::Ext4 {
            a: claimed.a,
            b: claimed.b,
            c: claimed.c,
            d: claimed.d,
        }) - gamma * theta * odd;
        qsag_whir_verified::verify_affine_duet_fold_step(
            to_verified_ext4(self.v0),
            to_verified_ext4(self.v1),
            self.inv_two_x.to_canonical_u64(),
            inv_two.to_canonical_u64(),
            to_verified_ext4(gamma),
            to_verified_ext4(affine_claim),
        ) && qsag_whir_verified::verify_cwyz_duet_fold_step(
            to_verified_ext4(self.v0),
            to_verified_ext4(self.v1),
            self.inv_two_x.to_canonical_u64(),
            inv_two.to_canonical_u64(),
            self.x_sq.to_canonical_u64(),
            to_verified_ext4(theta),
            to_verified_ext4(alpha),
            to_verified_ext4(beta),
            claimed,
        )
    }
}

const COSET_FOLD_ZETAS: [Goldilocks; MAX_FOLD_STEP_VARS + 1] = [
    Goldilocks::ONE,
    crate::field::gl_two_adic_generator(1),
    crate::field::gl_two_adic_generator(2),
    crate::field::gl_two_adic_generator(3),
    crate::field::gl_two_adic_generator(4),
    crate::field::gl_two_adic_generator(5),
    crate::field::gl_two_adic_generator(6),
];

/// Fold a coset fiber `vals` of size $A = 2^s \in \{2, 4, 8, 16, 32, 64\}$ at points
/// $x_k = y_0 \cdot \zeta_A^k$ across all but the last of `chals[0..s]`, leaving the final duet
/// for [`FiberLastDuet::accepts`] (`qsag_whir_verified::verify_cwyz_duet_fold_step`).
#[inline]
fn fold_coset_group_to_last_duet(
    vals: &[GoldilocksExt4],
    mut y0: Goldilocks,
    mut inv_y0: Goldilocks,
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    chals: &[[GoldilocksExt4; 3]],
) -> FiberLastDuet {
    let step = chals.len();
    assert!((1..=MAX_FOLD_STEP_VARS).contains(&step) && vals.len() == (1usize << step));
    let mut buf = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
    buf[..vals.len()].copy_from_slice(vals);
    let mut cur_len = vals.len();
    let mut inv_zeta = inv_zetas[step];
    let mut zeta = COSET_FOLD_ZETAS[step];
    for &[theta, alpha, beta] in &chals[..step - 1] {
        let half = cur_len / 2;
        let mut inv_two_xk = inv_two * inv_y0;
        let mut xk = y0;
        for k in 0..half {
            let v0 = buf[k];
            let v1 = buf[k + half];
            let even = (v0 + v1).mul_base(inv_two);
            let odd = (v0 - v1).mul_base(inv_two_xk);
            let mixed = even + theta * odd;
            let gamma = alpha + beta.mul_base(xk.square());
            buf[k] = odd + gamma * mixed;
            xk *= zeta;
            inv_two_xk *= inv_zeta;
        }
        cur_len = half;
        inv_y0 = inv_y0.square();
        inv_zeta = inv_zeta.square();
        y0 = y0.square();
        zeta = zeta.square();
    }
    FiberLastDuet {
        v0: buf[0],
        v1: buf[1],
        inv_two_x: inv_two * inv_y0,
        x_sq: y0.square(),
        chal: chals[step - 1],
    }
}

/// Base-field specialized counterpart to [`fold_coset_group_to_last_duet`] for single-polynomial
/// Round-0 fibers (`vals: &[Goldilocks]`), executing Round 0 directly over `Goldilocks` before
/// continuing in `GoldilocksExt4`.
#[inline]
fn fold_base_coset_group_to_last_duet(
    vals: &[Goldilocks],
    mut y0: Goldilocks,
    mut inv_y0: Goldilocks,
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    chals: &[[GoldilocksExt4; 3]],
) -> FiberLastDuet {
    let step = chals.len();
    assert!((1..=MAX_FOLD_STEP_VARS).contains(&step) && vals.len() == (1usize << step));
    if step == 1 {
        return FiberLastDuet {
            v0: GoldilocksExt4::from_base(vals[0]),
            v1: GoldilocksExt4::from_base(vals[1]),
            inv_two_x: inv_two * inv_y0,
            x_sq: y0.square(),
            chal: chals[0],
        };
    }
    let mut buf = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY / 2];
    let mut cur_len = vals.len() / 2;
    let mut inv_zeta = inv_zetas[step];
    let mut zeta = COSET_FOLD_ZETAS[step];
    {
        let [theta, alpha, beta] = chals[0];
        let mut inv_two_xk = inv_two * inv_y0;
        let mut xk = y0;
        for (k, slot) in buf[..cur_len].iter_mut().enumerate() {
            let v0 = vals[k];
            let v1 = vals[k + cur_len];
            let even_b = (v0 + v1) * inv_two;
            let odd_b = (v0 - v1) * inv_two_xk;
            let mixed = GoldilocksExt4::from_base(even_b) + theta.mul_base(odd_b);
            let gamma = alpha + beta.mul_base(xk.square());
            *slot = GoldilocksExt4::from_base(odd_b) + gamma * mixed;
            xk *= zeta;
            inv_two_xk *= inv_zeta;
        }
        inv_y0 = inv_y0.square();
        inv_zeta = inv_zeta.square();
        y0 = y0.square();
        zeta = zeta.square();
    }
    for &[theta, alpha, beta] in &chals[1..step - 1] {
        let half = cur_len / 2;
        let mut inv_two_xk = inv_two * inv_y0;
        let mut xk = y0;
        for k in 0..half {
            let v0 = buf[k];
            let v1 = buf[k + half];
            let even = (v0 + v1).mul_base(inv_two);
            let odd = (v0 - v1).mul_base(inv_two_xk);
            let mixed = even + theta * odd;
            let gamma = alpha + beta.mul_base(xk.square());
            buf[k] = odd + gamma * mixed;
            xk *= zeta;
            inv_two_xk *= inv_zeta;
        }
        cur_len = half;
        inv_y0 = inv_y0.square();
        inv_zeta = inv_zeta.square();
        y0 = y0.square();
        zeta = zeta.square();
    }
    FiberLastDuet {
        v0: buf[0],
        v1: buf[1],
        inv_two_x: inv_two * inv_y0,
        x_sq: y0.square(),
        chal: chals[step - 1],
    }
}

/// Fold a whole coset fiber, returning $W^{(s)}(\text{pow2}(y_0^{2^s}))$.
#[inline]
fn fold_coset_group_ext4(
    vals: &[GoldilocksExt4],
    y0: Goldilocks,
    inv_y0: Goldilocks,
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    chals: &[[GoldilocksExt4; 3]],
) -> GoldilocksExt4 {
    fold_coset_group_to_last_duet(vals, y0, inv_y0, inv_two, inv_zetas, chals).fold(inv_two)
}

/// Precompute shifted coset points `y0[i] = NON_RESIDUE * omega^{q_indices[i]}` via a 4-bit
/// stack nibble table and invert the entire stage query batch in one `Goldilocks::batch_inv`.
fn batch_coset_points_and_inverses(
    omega: Goldilocks,
    q_indices: &[usize],
) -> (Vec<Goldilocks>, Vec<Goldilocks>) {
    let max_g = q_indices.iter().copied().max().unwrap_or(0);
    let active_nibbles = if max_g == 0 {
        1
    } else {
        (usize::BITS as usize - max_g.leading_zeros() as usize).div_ceil(4)
    }
    .min(8);

    let mut nibbles = [[Goldilocks::ONE; 16]; 8];
    nibbles[0][0] = Goldilocks::NON_RESIDUE;
    for d in 1..16 {
        nibbles[0][d] = nibbles[0][d - 1] * omega;
    }
    let mut base = omega.pow(16);
    for row in nibbles.iter_mut().take(active_nibbles).skip(1) {
        for d in 1..16 {
            row[d] = row[d - 1] * base;
        }
        if active_nibbles > 2 {
            let b2 = base.square();
            let b4 = b2.square();
            let b8 = b4.square();
            base = b8.square();
        }
    }

    let mut y0s = Vec::with_capacity(q_indices.len());
    for &g in q_indices {
        debug_assert!((g >> 32) == 0);
        let mut acc = nibbles[0][g & 0xF];
        for (nib, row) in nibbles.iter().enumerate().take(active_nibbles).skip(1) {
            acc *= row[(g >> (4 * nib)) & 0xF];
        }
        y0s.push(acc);
    }
    let mut inv_y0s = y0s.clone();
    Goldilocks::batch_inv(&mut inv_y0s);
    (y0s, inv_y0s)
}

/// Does the fiber at `y0` fold exactly onto `final_coeffs(y0^{2^s})`? The last fold step is
/// checked by the extracted `verify_cwyz_duet_fold_step` against the extracted Horner value.
fn final_fiber_matches_terminal_poly(
    fiber: &[GoldilocksExt4],
    y0: Goldilocks,
    inv_y0: Goldilocks,
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    chals: &[[GoldilocksExt4; 3]],
    final_coeffs: &[qsag_whir_verified::Ext4],
) -> bool {
    let z_u = pow2_iter_base(y0, chals.len());
    fold_coset_group_to_last_duet(fiber, y0, inv_y0, inv_two, inv_zetas, chals).accepts(
        inv_two,
        qsag_whir_verified::eval_ext4_univariate_at_base(final_coeffs, z_u.to_canonical_u64()),
    )
}

/// Final-polynomial coefficients in the extracted core's representation.
fn to_verified_coeffs(coeffs: &[GoldilocksExt4]) -> Vec<qsag_whir_verified::Ext4> {
    coeffs.iter().copied().map(to_verified_ext4).collect()
}

#[inline]
fn build_inv_zetas() -> [Goldilocks; MAX_FOLD_STEP_VARS + 1] {
    [
        Goldilocks::ONE,
        Goldilocks::two_adic_generator(1).inv(),
        Goldilocks::two_adic_generator(2).inv(),
        Goldilocks::two_adic_generator(3).inv(),
        Goldilocks::two_adic_generator(4).inv(),
        Goldilocks::two_adic_generator(5).inv(),
        Goldilocks::two_adic_generator(6).inv(),
    ]
}

#[inline]
fn pow2_iter_base(mut y0: Goldilocks, steps: usize) -> Goldilocks {
    for _ in 0..steps {
        y0 = y0.square();
    }
    y0
}

pub(crate) fn fill_indexed<T, F>(out: &mut [T], f: F)
where
    T: Send,
    F: Fn(usize) -> T + Sync,
{
    #[cfg(feature = "std")]
    if out.len() >= 8_192 {
        let threads = crate::parallel_workers().min(out.len());
        let chunk = out.len().div_ceil(threads);
        let f_ref = &f;
        std::thread::scope(|scope| {
            for (t_idx, sub) in out.chunks_mut(chunk).enumerate() {
                crate::spawn_bounded(scope, move || {
                    for (off, dst) in sub.iter_mut().enumerate() {
                        *dst = f_ref(t_idx * chunk + off);
                    }
                });
            }
        });
        return;
    }
    for (i, dst) in out.iter_mut().enumerate() {
        *dst = f(i);
    }
}

/// Round-0 base-field -> `GoldilocksExt4` fold (`1` `mul_base` op per output instead of `2` full
/// `Ext4 * Ext4` muls!).
fn fold_base_first_var_ext4(table: &[Goldilocks], r: GoldilocksExt4) -> Vec<GoldilocksExt4> {
    let mut out = vec![GoldilocksExt4::ZERO; table.len() / 2];
    fill_indexed(&mut out, |k| {
        let a = table[2 * k];
        GoldilocksExt4::from_base(a) + r.mul_base(table[2 * k + 1] - a)
    });
    out
}

/// Fold first variable of `table` at `r` using reusable `scratch` storage when parallelizing.
fn fold_first_var_ext4_into(
    table: &mut Vec<GoldilocksExt4>,
    scratch: &mut Vec<GoldilocksExt4>,
    r: GoldilocksExt4,
) {
    #[cfg(feature = "std")]
    if table.len() >= 16_384 {
        let half = table.len() / 2;
        scratch.resize(half, GoldilocksExt4::ZERO);
        let src = table.as_slice();
        fill_indexed(&mut scratch[..half], |k| {
            let a = src[2 * k];
            a + r * (src[2 * k + 1] - a)
        });
        core::mem::swap(table, scratch);
        return;
    }
    #[cfg(not(feature = "std"))]
    let _ = scratch;
    fold_first_var_in_place_ext4(table, r);
}

fn dot_base_ext4_fast(base_tbl: &[Goldilocks], ext_tbl: &[GoldilocksExt4]) -> GoldilocksExt4 {
    debug_assert_eq!(base_tbl.len(), ext_tbl.len());
    #[cfg(feature = "std")]
    if base_tbl.len() >= 16_384 {
        let threads = crate::parallel_workers().min(base_tbl.len());
        let chunk = base_tbl.len().div_ceil(threads);
        return std::thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .filter_map(|t_idx| {
                    let start = t_idx * chunk;
                    (start < base_tbl.len()).then(|| {
                        let end = (start + chunk).min(base_tbl.len());
                        let b_sub = &base_tbl[start..end];
                        let e_sub = &ext_tbl[start..end];
                        crate::spawn_bounded(scope, move || {
                            let mut acc = GoldilocksExt4::ZERO;
                            for (&b, &e) in b_sub.iter().zip(e_sub.iter()) {
                                acc += e.mul_base(b);
                            }
                            acc
                        })
                    })
                })
                .collect();
            let mut sum = GoldilocksExt4::ZERO;
            for h in handles {
                sum += crate::join_worker(h);
            }
            sum
        });
    }
    let mut acc = GoldilocksExt4::ZERO;
    for (&b, &e) in base_tbl.iter().zip(ext_tbl.iter()) {
        acc += e.mul_base(b);
    }
    acc
}

fn dot_ext4_fast(a: &[GoldilocksExt4], b: &[GoldilocksExt4]) -> GoldilocksExt4 {
    debug_assert_eq!(a.len(), b.len());
    #[cfg(feature = "std")]
    if a.len() >= 16_384 {
        let threads = crate::parallel_workers().min(a.len());
        let chunk = a.len().div_ceil(threads);
        return std::thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .filter_map(|t_idx| {
                    let start = t_idx * chunk;
                    (start < a.len()).then(|| {
                        let end = (start + chunk).min(a.len());
                        let a_sub = &a[start..end];
                        let b_sub = &b[start..end];
                        crate::spawn_bounded(scope, move || {
                            let mut acc = GoldilocksExt4::ZERO;
                            for (&x, &y) in a_sub.iter().zip(b_sub.iter()) {
                                acc += x * y;
                            }
                            acc
                        })
                    })
                })
                .collect();
            let mut sum = GoldilocksExt4::ZERO;
            for h in handles {
                sum += crate::join_worker(h);
            }
            sum
        });
    }
    let mut acc = GoldilocksExt4::ZERO;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc += x * y;
    }
    acc
}

#[cfg(test)]
fn axpy_ext4_fast(dst: &mut [GoldilocksExt4], scale: GoldilocksExt4, src: &[GoldilocksExt4]) {
    debug_assert_eq!(dst.len(), src.len());
    #[cfg(feature = "std")]
    if dst.len() >= 16_384 {
        let threads = crate::parallel_workers().min(dst.len());
        let chunk = dst.len().div_ceil(threads);
        std::thread::scope(|scope| {
            for (d_sub, s_sub) in dst.chunks_mut(chunk).zip(src.chunks(chunk)) {
                crate::spawn_bounded(scope, move || {
                    for (d, &s) in d_sub.iter_mut().zip(s_sub.iter()) {
                        *d += scale * s;
                    }
                });
            }
        });
        return;
    }
    for (d, &s) in dst.iter_mut().zip(src.iter()) {
        *d += scale * s;
    }
}

const INV_TWO: Goldilocks = Goldilocks::from_u64_reduced(0x7FFF_FFFF_8000_0001);

#[inline]
fn pack_quadratic_wire(
    ev0: GoldilocksExt4,
    ev1: GoldilocksExt4,
    ev2: GoldilocksExt4,
) -> [GoldilocksExt4; 2] {
    let c2 = (ev2 - ev1 - ev1 + ev0).mul_base(INV_TWO);
    [ev0, c2]
}

#[inline]
fn eval_quadratic_wire(
    wire: &[GoldilocksExt4; 2],
    sum_claim: GoldilocksExt4,
    x: GoldilocksExt4,
) -> GoldilocksExt4 {
    from_verified_ext4(qsag_whir_verified::eval_quadratic_sumcheck_wire(
        to_verified_ext4(wire[0]),
        to_verified_ext4(wire[1]),
        to_verified_ext4(sum_claim),
        to_verified_ext4(x),
    ))
}

fn powers_of_ext4(base: GoldilocksExt4, count: usize) -> Vec<GoldilocksExt4> {
    let mut out = Vec::with_capacity(count);
    let mut cur = GoldilocksExt4::ONE;
    for _ in 0..count {
        out.push(cur);
        cur *= base;
    }
    out
}

// ============================================================================
// 5. Commit, Open & Verify (`whir_*`)
// ============================================================================

/// Commit to a base-field multilinear polynomial given its $2^\ell$ boolean-hypercube evaluations.
pub fn whir_commit_with_schedule(
    hypercube_evals: &[Goldilocks],
    salt_seed: &[u8; 32],
    schedule: &WhirSchedule,
) -> (CanopyCommitment, HemWhirProverState) {
    whir_commit_owned_with_schedule(hypercube_evals.to_vec(), salt_seed, schedule)
}

pub fn whir_commit_owned_with_schedule(
    hypercube_evals: Vec<Goldilocks>,
    salt_seed: &[u8; 32],
    schedule: &WhirSchedule,
) -> (CanopyCommitment, HemWhirProverState) {
    whir_commit_batch_owned_with_schedule(vec![hypercube_evals], salt_seed, schedule)
}

pub fn whir_commit(
    hypercube_evals: &[Goldilocks],
    salt_seed: &[u8; 32],
) -> (CanopyCommitment, HemWhirProverState) {
    whir_commit_owned(hypercube_evals.to_vec(), salt_seed)
}

/// Zero-copy commitment taking ownership of `hypercube_evals`.
pub fn whir_commit_owned(
    hypercube_evals: Vec<Goldilocks>,
    salt_seed: &[u8; 32],
) -> (CanopyCommitment, HemWhirProverState) {
    whir_commit_batch_owned(vec![hypercube_evals], salt_seed)
}

/// Commit to `1..=MAX_BATCH_POLYS` base-field multilinear polynomials of equal size under one
/// `CANOPY_MIDSTATE` Merkle-Canopy tree using the Stage-0 blowup of [`whir_stage_schedule`].
pub fn whir_commit_batch_owned(
    polys: Vec<Vec<Goldilocks>>,
    salt_seed: &[u8; 32],
) -> (CanopyCommitment, HemWhirProverState) {
    let schedule = whir_stage_schedule(
        polys
            .first()
            .map_or(0, |p| p.len().trailing_zeros() as usize),
    );
    whir_commit_batch_owned_with_schedule(polys, salt_seed, &schedule)
}

pub fn whir_commit_batch_owned_with_schedule(
    polys: Vec<Vec<Goldilocks>>,
    salt_seed: &[u8; 32],
    schedule: &WhirSchedule,
) -> (CanopyCommitment, HemWhirProverState) {
    whir_commit_batch_owned_with_schedule_inner(polys, salt_seed, schedule, 0, false)
}

pub(crate) fn whir_commit_batch_secret_with_schedule(
    polys: Vec<Vec<Goldilocks>>,
    salt_seed: &[u8; 32],
    schedule: &WhirSchedule,
) -> (CanopyCommitment, HemWhirProverState) {
    whir_commit_batch_owned_with_schedule_inner(polys, salt_seed, schedule, 0, true)
}

pub(crate) fn whir_commit_batch_owned_with_schedule_and_extra_vram(
    polys: Vec<Vec<Goldilocks>>,
    salt_seed: &[u8; 32],
    schedule: &WhirSchedule,
    extra_witness_words: usize,
) -> (CanopyCommitment, HemWhirProverState) {
    whir_commit_batch_owned_with_schedule_inner(
        polys,
        salt_seed,
        schedule,
        extra_witness_words,
        false,
    )
}

fn whir_commit_batch_owned_with_schedule_inner(
    polys: Vec<Vec<Goldilocks>>,
    salt_seed: &[u8; 32],
    schedule: &WhirSchedule,
    extra_witness_words: usize,
    secret: bool,
) -> (CanopyCommitment, HemWhirProverState) {
    let _phase = crate::profile::span("whir_commit_batch_owned_with_schedule");
    assert!(!polys.is_empty() && polys.len() <= MAX_BATCH_POLYS);
    let table_len = polys[0].len();
    assert!(table_len.is_power_of_two() && table_len >= 4);
    assert!(polys.iter().all(|p| p.len() == table_len));
    let num_vars = table_len.trailing_zeros() as usize;
    assert!(num_vars <= MAX_PCS_NUM_VARS);

    assert!(schedule.validate_structural(num_vars));
    let schedule = schedule.clone();
    let st0 = schedule.stages[0];
    let group_arity_0 = 1usize << st0.step_vars;

    #[cfg(feature = "vulkan")]
    if schedule.regime.uses_poseidon2_canopy() {
        crate::acceleration::report_cpu_poseidon_canopy();
    }
    #[cfg(feature = "vulkan")]
    if table_len >= 4_096
        && num_vars <= MAX_GPU_PCS_NUM_VARS
        && !schedule.regime.uses_poseidon2_canopy()
        && let Some(session) = crate::acceleration::try_acquire_whir_session_for(secret)
    {
        const PAR_CHUNK: usize = 262_144;
        const STAGING_CHUNK_WORDS: usize = 4 * 1024 * 1024;
        let turbo = schedule.regime.uses_turboshake_canopy();
        let mut wb_chunk = vec![0u64; STAGING_CHUNK_WORDS.min(table_len)];
        let (max_stage_dom, max_stage_grps) = max_intermediate_stage_dims(num_vars, &schedule);
        let domain_len = table_len * st0.blowup;
        let num_groups = domain_len / group_arity_0;

        let gpu_res = session.exec_verified(|raw, key, anchor| {
            raw.prover_whir_commit_round0_with_mode_and_receipt(
                key,
                anchor,
                turbo,
                polys.len(),
                qsag_accel::WhirRound0ReceiptParams {
                    salt_seed,
                    num_vars,
                    blowup: st0.blowup,
                    group_arity: group_arity_0,
                    max_stage1_domain_ext4: max_stage_dom,
                    max_stage1_groups: max_stage_grps,
                    extra_witness_words,
                },
                |poly_idx, pos, dst| {
                    let n = dst.len();
                    let src = &polys[poly_idx][pos..pos + n];
                    let wb = &mut wb_chunk[..n];
                    if n >= PAR_CHUNK && crate::parallel_workers() > 1 {
                        let workers = crate::parallel_workers().min(n.div_ceil(PAR_CHUNK));
                        let chunk_len = n.div_ceil(workers.max(1));
                        std::thread::scope(|scope| {
                            for (dst_chunk, src_chunk) in
                                wb.chunks_mut(chunk_len).zip(src.chunks(chunk_len))
                            {
                                crate::spawn_bounded(scope, move || {
                                    for (d, v) in dst_chunk.iter_mut().zip(src_chunk.iter()) {
                                        *d = v.to_canonical_u64();
                                    }
                                });
                            }
                        });
                    } else {
                        for (d, v) in wb.iter_mut().zip(src.iter()) {
                            *d = v.to_canonical_u64();
                        }
                    }
                    dst.copy_from_slice(wb);
                },
            )
        });
        if secret {
            qsag_asm::volatile_fill(&mut wb_chunk, 0u64);
        }
        match gpu_res {
            Ok(top_node)
                if session.record_stage(qsag_accel::ProverKernelSlot::WhirLdeCommitment) =>
            {
                let log_leaves = num_groups.trailing_zeros() as usize;
                let root = hash_tree_root_mode(turbo, log_leaves as u8, &top_node);
                let tree_0 = MerkleCanopyTree {
                    log_leaves,
                    is_compact: false,
                    is_turboshake: turbo,
                    nodes: vec![[0u8; 32], top_node],
                    root,
                };
                let comm = tree_0.commitment();
                return (
                    comm,
                    HemWhirProverState {
                        num_vars,
                        schedule,
                        group_arity_0,
                        hypercube_evals: polys,
                        codewords_0: Vec::new(),
                        monomial_coeffs_0: Vec::new(),
                        secret,
                        salt_seed: *salt_seed,
                        tree_0,
                        round0_tree_on_cpu: false,
                        gpu_session: Some(session),
                    },
                );
            }
            Ok(_) => session.record_fallback("whir_commit_round0", "prover kernel pin mismatch"),
            Err(err) => session.record_fallback("whir_commit_round0", err),
        }
    }
    #[cfg(not(feature = "vulkan"))]
    let _ = extra_witness_words;

    let (monomial_coeffs_0, codewords_0, tree_0) = build_cpu_round0(
        &polys,
        salt_seed,
        schedule.regime,
        st0.blowup,
        group_arity_0,
        secret,
    );
    let comm = tree_0.commitment();
    (
        comm,
        HemWhirProverState {
            num_vars,
            schedule,
            group_arity_0,
            hypercube_evals: polys,
            codewords_0,
            monomial_coeffs_0,
            secret,
            salt_seed: *salt_seed,
            tree_0,
            round0_tree_on_cpu: true,
            #[cfg(feature = "vulkan")]
            gpu_session: None,
        },
    )
}

fn build_cpu_round0(
    polys: &[Vec<Goldilocks>],
    salt_seed: &[u8; 32],
    regime: WhirSecurityRegime,
    blowup: usize,
    group_arity_0: usize,
    secret: bool,
) -> (Vec<Vec<Goldilocks>>, Vec<Vec<Goldilocks>>, MerkleCanopyTree) {
    let (monomial_coeffs_0, codewords_0) = build_cpu_round0_codewords(polys, blowup, secret, true);
    let tree_0 = build_cpu_round0_tree(&codewords_0, salt_seed, regime, group_arity_0);
    (monomial_coeffs_0, codewords_0, tree_0)
}

fn build_cpu_round0_codewords(
    polys: &[Vec<Goldilocks>],
    blowup: usize,
    secret: bool,
    cache_coefficients: bool,
) -> (Vec<Vec<Goldilocks>>, Vec<Vec<Goldilocks>>) {
    let encode = |evals: &Vec<Goldilocks>| {
        if evals.len() >= (1 << 22) {
            let domain_len = evals
                .len()
                .checked_mul(blowup)
                .expect("RS domain size overflow");
            let mut coeffs = Vec::with_capacity(domain_len);
            coeffs.extend_from_slice(evals);
            hypercube_to_monomial_in_place(&mut coeffs, 1 << 14);
            return (
                Vec::new(),
                encode_rs_coset_goldilocks_owned_cpu(coeffs, blowup),
            );
        }
        let mut coeffs = hypercube_to_monomial_coeffs(evals);
        let codeword = encode_rs_coset_goldilocks_with_secret(&coeffs, blowup, secret);
        if !cache_coefficients || secret {
            if secret {
                qsag_asm::volatile_fill(&mut coeffs, Goldilocks::ZERO);
            }
            (Vec::new(), codeword)
        } else {
            (coeffs, codeword)
        }
    };
    // Large polynomials use one owned domain buffer each and encode sequentially.
    #[cfg(feature = "std")]
    let pairs: Vec<(Vec<Goldilocks>, Vec<Goldilocks>)> =
        if polys.len() > 1 && polys[0].len() < (1 << 22) && crate::parallel_workers() > 1 {
            std::thread::scope(|scope| {
                let handles: Vec<_> = polys
                    .iter()
                    .map(|evals| crate::spawn_bounded(scope, move || encode(evals)))
                    .collect();
                handles.into_iter().map(crate::join_worker).collect()
            })
        } else {
            polys.iter().map(encode).collect()
        };
    #[cfg(not(feature = "std"))]
    let pairs: Vec<(Vec<Goldilocks>, Vec<Goldilocks>)> = polys.iter().map(encode).collect();
    let mut monomial_coeffs_0 = if secret || !cache_coefficients || polys[0].len() >= (1 << 22) {
        Vec::new()
    } else {
        Vec::with_capacity(pairs.len())
    };
    let mut codewords_0 = Vec::with_capacity(pairs.len());
    for (coeffs, cw) in pairs {
        if !coeffs.is_empty() {
            monomial_coeffs_0.push(coeffs);
        }
        codewords_0.push(cw);
    }
    (monomial_coeffs_0, codewords_0)
}

fn build_cpu_round0_tree(
    codewords_0: &[Vec<Goldilocks>],
    salt_seed: &[u8; 32],
    regime: WhirSecurityRegime,
    group_arity_0: usize,
) -> MerkleCanopyTree {
    let domain_len = codewords_0[0].len();
    let num_groups = domain_len / group_arity_0;
    let turbo = regime.uses_turboshake_canopy();

    let _phase = crate::profile::span("round0_merkle_tree");
    if regime.uses_poseidon2_canopy() {
        MerkleCanopyTree::build_poseidon2(num_groups, 0, |g| {
            poseidon2_round0_leaf_from_codewords(
                codewords_0,
                salt_seed,
                g,
                num_groups,
                group_arity_0,
            )
        })
    } else if num_groups >= 8 {
        MerkleCanopyTree::build_from_fn_x8_mode(turbo, num_groups, |base_g| {
            round0_leaf_hash_x8_mode(
                turbo,
                codewords_0,
                salt_seed,
                base_g,
                num_groups,
                group_arity_0,
            )
        })
    } else {
        MerkleCanopyTree::build_from_fn_x4_mode(turbo, num_groups, |base_g| {
            round0_leaf_hash_x4_mode(
                turbo,
                codewords_0,
                salt_seed,
                base_g,
                num_groups,
                group_arity_0,
            )
        })
    }
}

/// Produce a `[P0-01]`-hardened `Hem` WHIR opening proof over `GoldilocksExt4` for one evaluation
/// claim on a single-polynomial commitment.
pub fn whir_open(
    state: &HemWhirProverState,
    point: &[GoldilocksExt4],
    claimed_eval: GoldilocksExt4,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> HemWhirOpeningProof {
    absorb_whir_schedule(transcript, &state.schedule);
    assert_eq!(state.num_polys(), 1);
    assert_eq!(point.len(), state.num_vars);
    transcript.absorb(b"PCS_NUM_VARS", &(state.num_vars as u64).to_le_bytes());
    transcript.absorb(b"PCS_COMM0", &state.commitment().to_bytes());
    for &c in point {
        transcript.absorb_ext4(b"PCS_POINT_COORD", c);
    }
    transcript.absorb_ext4(b"PCS_CLAIMED_EVAL", claimed_eval);

    #[cfg(feature = "vulkan")]
    if let Some(session) = state.gpu_session.as_ref() {
        let mut gpu_tr = transcript.clone();
        match whir_open_single_gpu(state, session, point, claimed_eval, &mut gpu_tr) {
            Ok(opening) => {
                *transcript = gpu_tr;
                return opening;
            }
            Err(err) => session.record_fallback("whir_open", err),
        }
    }

    let kernel_table = monomial_table(point);
    whir_open_core(
        state,
        None,
        &[[GoldilocksExt4::ONE, GoldilocksExt4::ZERO]],
        kernel_table,
        claimed_eval,
        transcript,
    )
}

fn absorb_batch_statement(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    num_vars: usize,
    comm_0: &CanopyCommitment,
    points: &[&[GoldilocksExt4]],
    evals: &[GoldilocksExt4],
) {
    transcript.absorb(b"PCS_NUM_VARS", &(num_vars as u64).to_le_bytes());
    transcript.absorb(b"PCS_COMM0", &comm_0.to_bytes());
    transcript.absorb(b"PCS_BATCH_POLYS", &(points.len() as u64).to_le_bytes());
    for (point, &eval) in points.iter().zip(evals) {
        for &c in point.iter() {
            transcript.absorb_ext4(b"PCS_BATCH_POINT", c);
        }
        transcript.absorb_ext4(b"PCS_BATCH_EVAL", eval);
    }
}

/// Open every polynomial $W_i$ of `state` at its own `GoldilocksExt4` point: prove
/// $W_i(\text{points}[i]) = \text{evals}[i]$ for all $i$ with one `Hem` WHIR opening.
pub fn whir_open_batch(
    state: &HemWhirProverState,
    points: &[&[GoldilocksExt4]],
    evals: &[GoldilocksExt4],
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> HemWhirBatchOpeningProof {
    let _phase = crate::profile::span("whir_open_batch");
    absorb_whir_schedule(transcript, &state.schedule);
    let num_polys = state.num_polys();
    let num_vars = state.num_vars;
    assert_eq!(points.len(), num_polys);
    assert_eq!(evals.len(), num_polys);
    assert!(points.iter().all(|p| p.len() == num_vars));
    absorb_batch_statement(transcript, num_vars, &state.commitment(), points, evals);

    #[cfg(feature = "vulkan")]
    if let Some(session) = state.gpu_session.as_ref() {
        let mut gpu_tr = transcript.clone();
        match whir_open_batch_gpu(state, session, points, evals, &mut gpu_tr) {
            Ok(batch_proof) => {
                *transcript = gpu_tr;
                return batch_proof;
            }
            Err(err) => session.record_fallback("whir_open_batch", err),
        }
    }

    if num_polys == 1 {
        let kernel = monomial_table(points[0]);
        let opening = whir_open_core(
            state,
            None,
            &[[GoldilocksExt4::ONE, GoldilocksExt4::ZERO]],
            kernel,
            evals[0],
            transcript,
        );
        return HemWhirBatchOpeningProof {
            point_sumcheck_polys: Vec::new(),
            common_point_evals: Vec::new(),
            shifted_evals: Vec::new(),
            batch_pow_nonce: 0,
            opening,
        };
    }

    // Point reduction sumcheck over GoldilocksExt4:
    let lambda = transcript.squeeze_ext4(b"PCS_BATCH_LAMBDA");
    let lambda_pows = powers_of_ext4(lambda, num_polys);
    let mut claim = GoldilocksExt4::ZERO;
    for (&w, &e) in lambda_pows.iter().zip(evals) {
        claim += w * e;
    }
    let mut kernels: Vec<Vec<GoldilocksExt4>> =
        points.iter().map(|p| build_eq_table_ext4_fast(p)).collect();
    let mut tables: Vec<Vec<GoldilocksExt4>> = Vec::new();
    let mut fold_scratch: Vec<GoldilocksExt4> = Vec::new();
    let mut point_sumcheck_polys = Vec::with_capacity(num_vars);
    let mut rho = Vec::with_capacity(num_vars);

    for round in 0..num_vars {
        let mut ev0 = GoldilocksExt4::ZERO;
        let mut ev2 = GoldilocksExt4::ZERO;
        for i in 0..num_polys {
            let (p0, p2) = if round == 0 {
                sumcheck_round_evals_ext4(&state.hypercube_evals[i], &kernels[i], |k, w| {
                    k.mul_base(w)
                })
            } else {
                sumcheck_round_evals_ext4(&tables[i], &kernels[i], |k, w| k * w)
            };
            ev0 += lambda_pows[i] * p0;
            ev2 += lambda_pows[i] * p2;
        }
        let ev1 = claim - ev0;
        let wire = pack_quadratic_wire(ev0, ev1, ev2);
        transcript.absorb_ext4(b"PCS_BATCH_SC_C0", wire[0]);
        transcript.absorb_ext4(b"PCS_BATCH_SC_C2", wire[1]);
        point_sumcheck_polys.push(wire);

        let r = transcript.squeeze_ext4(b"PCS_BATCH_SC_CHAL");
        claim = eval_quadratic_wire(&wire, claim, r);
        if round == 0 {
            tables = state
                .hypercube_evals
                .iter()
                .map(|w| fold_base_first_var_ext4(w, r))
                .collect();
        } else {
            for table in &mut tables {
                fold_first_var_ext4_into(table, &mut fold_scratch, r);
            }
        }
        for kernel in &mut kernels {
            fold_first_var_ext4_into(kernel, &mut fold_scratch, r);
        }
        rho.push(r);
    }
    drop(fold_scratch);
    drop(kernels);
    let common_point_evals: Vec<GoldilocksExt4> = tables.iter().map(|t| t[0]).collect();
    drop(tables);
    for &e in &common_point_evals {
        transcript.absorb_ext4(b"PCS_BATCH_COMMON_EVAL", e);
    }

    let kernel = monomial_table(&rho);
    let computed_monomial_polys: Vec<Vec<Goldilocks>>;
    let monomial_polys: &[Vec<Goldilocks>] = if state.monomial_coeffs_0.len() == num_polys {
        &state.monomial_coeffs_0
    } else {
        #[cfg(feature = "std")]
        let derived = if state.hypercube_evals.len() > 1 && crate::parallel_workers() > 1 {
            std::thread::scope(|scope| {
                let handles: Vec<_> = state
                    .hypercube_evals
                    .iter()
                    .map(|w| crate::spawn_bounded(scope, move || hypercube_to_monomial_coeffs(w)))
                    .collect();
                handles.into_iter().map(crate::join_worker).collect()
            })
        } else {
            state
                .hypercube_evals
                .iter()
                .map(|w| hypercube_to_monomial_coeffs(w))
                .collect()
        };
        #[cfg(not(feature = "std"))]
        let derived = state
            .hypercube_evals
            .iter()
            .map(|w| hypercube_to_monomial_coeffs(w))
            .collect();
        computed_monomial_polys = derived;
        &computed_monomial_polys
    };
    let shifted_evals: Vec<_> = monomial_polys
        .iter()
        .map(|c| dot_base_ext4_fast(c, &kernel[1..1 + c.len()]))
        .collect();
    for &e in &shifted_evals {
        transcript.absorb_ext4(b"PCS_BATCH_SHIFT", e);
    }
    let batch_pow_nonce = grind_pcs_pow(transcript);
    transcript.absorb(b"PCS_BATCH_POW", &batch_pow_nonce.to_le_bytes());
    let weights = cascade_weights(num_polys, transcript);
    let combined_claim = combine_claims(&weights, &common_point_evals, &shifted_evals);
    let opening = whir_open_core(
        state,
        Some(monomial_polys),
        &weights,
        kernel,
        combined_claim,
        transcript,
    );
    HemWhirBatchOpeningProof {
        point_sumcheck_polys,
        common_point_evals,
        shifted_evals,
        batch_pow_nonce,
        opening,
    }
}

fn sumcheck_round_evals_ext4<W, M>(
    w: &[W],
    k: &[GoldilocksExt4],
    mul: M,
) -> (GoldilocksExt4, GoldilocksExt4)
where
    W: Copy + Send + Sync + core::ops::Add<Output = W> + core::ops::Sub<Output = W>,
    M: Fn(GoldilocksExt4, W) -> GoldilocksExt4 + Sync,
{
    debug_assert_eq!(w.len(), k.len());
    let half = w.len() / 2;
    let run = |j0: usize, j1: usize| {
        let mut a0 = GoldilocksExt4::ZERO;
        let mut a2 = GoldilocksExt4::ZERO;
        for j in j0..j1 {
            let w0 = w[2 * j];
            let w1 = w[2 * j + 1];
            let k0 = k[2 * j];
            let k1 = k[2 * j + 1];
            a0 += mul(k0, w0);
            let w2 = w1 + (w1 - w0);
            let k2 = k1 + (k1 - k0);
            a2 += mul(k2, w2);
        }
        (a0, a2)
    };

    #[cfg(feature = "std")]
    if half >= 4_096 {
        let threads = crate::parallel_workers().min(half);
        let chunk = half.div_ceil(threads);
        let run_ref = &run;
        let mut total = (GoldilocksExt4::ZERO, GoldilocksExt4::ZERO);
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .filter_map(|t_idx| {
                    let j0 = t_idx * chunk;
                    (j0 < half).then(|| {
                        let j1 = (j0 + chunk).min(half);
                        crate::spawn_bounded(scope, move || run_ref(j0, j1))
                    })
                })
                .collect();
            for h in handles {
                let (p0, p2) = crate::join_worker(h);
                total.0 += p0;
                total.1 += p2;
            }
        });
        return total;
    }
    run(0, half)
}

type ActiveStageOracle = (Vec<GoldilocksExt4>, MerkleCanopyTree, [GoldilocksExt4; 2]);

/// Core multi-stage `Hem` WHIR rate-escalated opening over `GoldilocksExt4`.
/// Table length from which a public opening folds its coefficient and kernel tables in
/// their own storage instead of through a second buffer of the same size.
const COMPACT_FOLD_MIN_LEN: usize = 1 << 22;

type CpuRound0Artifacts = (Vec<Vec<Goldilocks>>, Option<MerkleCanopyTree>);

fn whir_open_core(
    state: &HemWhirProverState,
    precomputed_monomial_polys: Option<&[Vec<Goldilocks>]>,
    weights: &[[GoldilocksExt4; 2]],
    mut cur_k: Vec<GoldilocksExt4>,
    mut cur_sum_claim: GoldilocksExt4,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> HemWhirOpeningProof {
    // A state without its Stage-0 Reed-Solomon cache re-encodes it, but only once the
    // Stage-0 queries need it: by then the coefficient and kernel tables have been folded
    // `2^step_vars`-fold, so the codewords never coexist with the full-size tables.
    let mut lazy_cpu_r0: Option<CpuRound0Artifacts> = None;
    let rebuild_round0 = || {
        let (_, codewords) = build_cpu_round0_codewords(
            &state.hypercube_evals,
            state.schedule.stages[0].blowup,
            state.secret,
            false,
        );
        let tree = (!state.round0_tree_on_cpu).then(|| {
            build_cpu_round0_tree(
                &codewords,
                &state.salt_seed,
                state.schedule.regime,
                state.group_arity_0,
            )
        });
        (codewords, tree)
    };
    let release_round0 = |lazy: &mut Option<CpuRound0Artifacts>| {
        if let Some((mut cws, _)) = lazy.take()
            && state.secret
        {
            for secret_vec in &mut cws {
                qsag_asm::volatile_fill(secret_vec, Goldilocks::ZERO);
            }
        }
    };

    let num_polys = state.num_polys();
    assert_eq!(weights.len(), num_polys);
    let single = num_polys == 1;
    let sched = &state.schedule;
    let turbo = sched.regime.uses_turboshake_canopy();
    let num_stages = sched.stages.len();
    let early_stop = sched.early_stop_vars;
    let fold_vars = state.num_vars - early_stop;
    absorb_whir_schedule(transcript, sched);
    let core_len = 1usize << state.num_vars;
    let pre_monos = precomputed_monomial_polys
        .or((state.monomial_coeffs_0.len() == num_polys)
            .then_some(state.monomial_coeffs_0.as_slice()));

    let direct_unit_base =
        !state.secret && single && weights[0] == [GoldilocksExt4::ONE, GoldilocksExt4::ZERO];
    let owned_unit_c: Vec<Goldilocks>;
    let unit_c0: Option<&[Goldilocks]> = if direct_unit_base {
        if let Some(pre) = pre_monos {
            Some(pre[0].as_slice())
        } else {
            owned_unit_c = hypercube_to_monomial_coeffs(&state.hypercube_evals[0]);
            Some(owned_unit_c.as_slice())
        }
    } else {
        None
    };

    let mut cur_coeffs = if unit_c0.is_some() {
        Vec::with_capacity(core_len / 2 + 2)
    } else {
        let _combine_phase = crate::profile::span("whir_open_combine_coeffs");
        let mut coeffs = vec![GoldilocksExt4::ZERO; core_len + 2];
        for (poly_idx, (w, table)) in weights.iter().zip(&state.hypercube_evals).enumerate() {
            let mut owned_c = Vec::new();
            let c: &[Goldilocks] = match pre_monos {
                Some(pre) => &pre[poly_idx],
                None => {
                    owned_c = hypercube_to_monomial_coeffs(table);
                    &owned_c
                }
            };
            coeffs[0] += w[0].mul_base(c[0]);
            #[cfg(feature = "std")]
            if core_len >= 16_384 {
                let workers = crate::parallel_workers();
                let chunk = (core_len - 1).div_ceil(workers);
                let c_ref = c;
                let w0 = w[0];
                let w1 = w[1];
                std::thread::scope(|scope| {
                    for (t_idx, sub) in coeffs[1..core_len].chunks_mut(chunk).enumerate() {
                        let base_i = 1 + t_idx * chunk;
                        crate::spawn_bounded(scope, move || {
                            for (off, dst) in sub.iter_mut().enumerate() {
                                let i = base_i + off;
                                *dst = (*dst + w1.mul_base(c_ref[i - 1])) + w0.mul_base(c_ref[i]);
                            }
                        });
                    }
                });
            } else {
                for i in 1..core_len {
                    coeffs[i] = (coeffs[i] + w[1].mul_base(c[i - 1])) + w[0].mul_base(c[i]);
                }
            }
            #[cfg(not(feature = "std"))]
            for i in 1..core_len {
                coeffs[i] = (coeffs[i] + w[1].mul_base(c[i - 1])) + w[0].mul_base(c[i]);
            }
            coeffs[core_len] += w[1].mul_base(c[core_len - 1]);
            if state.secret && !owned_c.is_empty() {
                qsag_asm::volatile_fill(&mut owned_c, Goldilocks::ZERO);
            }
        }
        coeffs
    };

    let ood_phase = crate::profile::span("whir_open_stage0_ood");
    let z_ood_0 = core::array::from_fn::<_, 2, _>(|_| transcript.squeeze_ext4(b"WHIR_OOD_CHAL"));
    let stage0_ood_evals = match unit_c0 {
        Some(c0) => eval_univariate_base_at_ext4_pair(c0, z_ood_0),
        None => z_ood_0.map(|z| eval_univariate_ext4(&cur_coeffs, z)),
    };
    for e in stage0_ood_evals {
        transcript.absorb_ext4(b"WHIR_OOD_EVAL", e);
    }
    for (z, e) in z_ood_0.into_iter().zip(stage0_ood_evals) {
        let xi = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
        add_geometric_scaled_in_place(&mut cur_k, xi, z);
        cur_sum_claim += xi * e;
    }
    drop(ood_phase);

    let inv_two = Goldilocks::TWO.inv();
    let inv_zetas = build_inv_zetas();

    let mut rem_vars = state.num_vars;
    let mut fold_sumcheck_polys = Vec::with_capacity(fold_vars);
    let mut fold_pow_nonces = Vec::with_capacity(fold_vars);
    let mut stage_pow_nonce_0: u64 = 0;
    let mut round0_salts: Vec<[u8; 16]> = Vec::new();
    let mut round0_vals: Vec<Goldilocks> = Vec::new();
    let mut round0_multiproof = CanopyMultiProof {
        auth_siblings: Vec::new(),
    };
    let mut c_scratch = Vec::with_capacity(core_len / 4 + 4);
    let mut k_scratch = Vec::with_capacity(cur_k.len() / 2 + 2);

    // Staged `Ext4` oracle currently active for `stage_idx >= 1`: `(cw, tree, ood_eval)`.
    let mut active_stage_oracle: Option<ActiveStageOracle> = None;
    let mut folded_layers: Vec<WhirStageProof> = Vec::with_capacity(num_stages.saturating_sub(1));

    for (stage_idx, st) in sched.stages.iter().enumerate() {
        let arity = 1usize << st.step_vars;
        release_round0(&mut lazy_cpu_r0);

        let mut stage_chals = [[GoldilocksExt4::ZERO; 3]; MAX_FOLD_STEP_VARS];
        for (fold_in_stage, slot) in stage_chals.iter_mut().take(st.step_vars).enumerate() {
            let compact = !state.secret && cur_coeffs.len() >= COMPACT_FOLD_MIN_LEN;
            let (wire, fold_pow_nonce, chals) = if stage_idx == 0
                && fold_in_stage == 0
                && let Some(c0) = unit_c0
            {
                prove_fold_from_base(
                    c0,
                    &mut cur_coeffs,
                    &mut cur_k,
                    &mut k_scratch,
                    &mut cur_sum_claim,
                    transcript,
                )
            } else {
                prove_fold_in_place(
                    &mut cur_coeffs,
                    &mut cur_k,
                    &mut c_scratch,
                    &mut k_scratch,
                    &mut cur_sum_claim,
                    transcript,
                    compact,
                )
            };
            fold_sumcheck_polys.push(wire);
            fold_pow_nonces.push(fold_pow_nonce);
            *slot = chals;
        }
        rem_vars -= st.step_vars;
        let chals_slice = &stage_chals[..st.step_vars];

        if stage_idx + 1 < num_stages {
            // 2A. Intermediate WHIR Rate-Escalation Transition (`stage_idx -> stage_idx + 1`):
            //     Re-encode `cur_coeffs` (`2^{rem_vars}` `Ext4` elements) at `stages[stage_idx + 1].blowup`
            //     and absorb `comm_next` + `ood_eval_next` BEFORE grinding/squeezing Stage `stage_idx`'s
            //     spot-check fiber queries!
            let next_spec = sched.stages[stage_idx + 1];
            let next_arity = 1usize << next_spec.step_vars;
            let cw_next = encode_overflow(&cur_coeffs, next_spec.blowup);
            let num_groups_next = cw_next.len() / next_arity;
            let next_stage_u8 = (stage_idx + 1) as u8;
            let _tree_phase = crate::profile::span("whir_open_stage_tree_and_queries");
            let tree_next = build_ext4_stage_tree(
                sched.regime,
                next_stage_u8,
                &cw_next,
                num_groups_next,
                next_arity,
            );
            let comm_next = tree_next.commitment();
            transcript.absorb(b"WHIR_NEXT_COMMIT", &comm_next.to_bytes());

            let z_ood_next =
                core::array::from_fn::<_, 2, _>(|_| transcript.squeeze_ext4(b"WHIR_OOD_CHAL"));
            let ood_eval_next = z_ood_next.map(|z| eval_univariate_ext4(&cur_coeffs, z));
            for e in ood_eval_next {
                transcript.absorb_ext4(b"WHIR_OOD_EVAL", e);
            }

            // Grind Stage `stage_idx`'s 16-bit PoW nonce and squeeze Stage `stage_idx`'s fiber queries!
            let pow_nonce = grind_pcs_pow(transcript);
            transcript.absorb(b"WHIR_STAGE_POW", &pow_nonce.to_le_bytes());

            let shift_claims = if stage_idx == 0 {
                stage_pow_nonce_0 = pow_nonce;
                if state.codewords_0.is_empty() {
                    lazy_cpu_r0 = Some(rebuild_round0());
                }
                let (codewords_0, tree_0): (&[Vec<Goldilocks>], &MerkleCanopyTree) =
                    match &lazy_cpu_r0 {
                        Some((codewords, tree)) => {
                            (codewords.as_slice(), tree.as_ref().unwrap_or(&state.tree_0))
                        }
                        None => (state.codewords_0.as_slice(), &state.tree_0),
                    };
                let num_groups_0 = state.num_groups_0();
                let domain_0 = codewords_0[0].len();
                let log_d0 = domain_0.trailing_zeros() as usize;
                let omega_0 = Goldilocks::two_adic_generator(log_d0);
                let zeta_0 = omega_0.pow(num_groups_0 as u64);
                let q_indices = sample_stage_queries(transcript, 0, num_groups_0, st.num_queries);
                let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega_0, &q_indices);

                round0_salts.reserve(q_indices.len());
                round0_vals.reserve(q_indices.len() * num_polys * arity);
                let mut claims = Vec::with_capacity(q_indices.len());
                for (q_pos, &g) in q_indices.iter().enumerate() {
                    let y0 = y0s[q_pos];
                    let inv_y0 = inv_y0s[q_pos];
                    round0_salts.push(derive_round0_salt_mode(turbo, &state.salt_seed, g as u32));
                    let mut fiber = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                    if single {
                        let cw0 = &codewords_0[0];
                        for k in 0..arity {
                            let v = cw0[g + k * num_groups_0];
                            round0_vals.push(v);
                            fiber[k] = GoldilocksExt4::from_base(v);
                        }
                    } else {
                        for (w, cw) in weights.iter().zip(codewords_0) {
                            let mut x = y0;
                            for k in 0..arity {
                                let v = cw[g + k * num_groups_0];
                                round0_vals.push(v);
                                fiber[k] += (w[0] + w[1].mul_base(x)).mul_base(v);
                                x *= zeta_0;
                            }
                        }
                    }
                    let v_shift = fold_coset_group_ext4(
                        &fiber[..arity],
                        y0,
                        inv_y0,
                        inv_two,
                        &inv_zetas,
                        chals_slice,
                    );
                    let z_u = pow2_iter_base(y0, st.step_vars);
                    claims.push((z_u, v_shift));
                }
                round0_multiproof = tree_0.open_multi_with_leaf_fn(&q_indices, |g| {
                    round0_leaf_hash_mode(
                        turbo,
                        codewords_0,
                        &state.salt_seed,
                        g,
                        num_groups_0,
                        arity,
                    )
                });
                claims
            } else {
                let (mut prev_cw, prev_tree, prev_ood) = match active_stage_oracle.take() {
                    Some(oracle) => oracle,
                    None => unreachable!("a noninitial stage follows a committed oracle"),
                };
                let domain_cur = prev_cw.len();
                let num_groups_cur = domain_cur / arity;
                let log_d = domain_cur.trailing_zeros() as usize;
                let omega = Goldilocks::two_adic_generator(log_d);
                let q_indices =
                    sample_stage_queries(transcript, stage_idx, num_groups_cur, st.num_queries);
                let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega, &q_indices);

                let mut opened_vals = Vec::with_capacity(q_indices.len() * arity);
                let mut claims = Vec::with_capacity(q_indices.len());
                for (q_pos, &g) in q_indices.iter().enumerate() {
                    let y0 = y0s[q_pos];
                    let inv_y0 = inv_y0s[q_pos];
                    let fiber = collect_coset_group_ext4(&prev_cw, g, num_groups_cur, arity);
                    opened_vals.extend_from_slice(&fiber[..arity]);
                    let v_shift = fold_coset_group_ext4(
                        &fiber[..arity],
                        y0,
                        inv_y0,
                        inv_two,
                        &inv_zetas,
                        chals_slice,
                    );
                    let z_u = pow2_iter_base(y0, st.step_vars);
                    claims.push((z_u, v_shift));
                }
                let stage_u8 = stage_idx as u8;
                let multiproof = prev_tree.open_multi_with_leaf_fn(&q_indices, |g| {
                    let fiber = collect_coset_group_ext4(&prev_cw, g, num_groups_cur, arity);
                    hash_ext4_group_mode(turbo, stage_u8, g as u32, &fiber[..arity])
                });
                if state.secret {
                    qsag_asm::volatile_fill(&mut prev_cw, GoldilocksExt4::ZERO);
                }
                folded_layers.push(WhirStageProof {
                    commitment: prev_tree.commitment(),
                    stage_ood_evals: prev_ood,
                    pow_nonce,
                    opened_vals,
                    multiproof,
                });
                claims
            };

            let mut shift_bytes = Vec::with_capacity(32 * shift_claims.len());
            for &(_, v_shift) in &shift_claims {
                shift_bytes.extend_from_slice(&v_shift.to_le_bytes());
            }
            transcript.absorb(b"WHIR_SHIFT_VALS", &shift_bytes);

            // Squeeze OOD & shift batching challenges and fold all new claims into `(cur_k, cur_sum_claim)`.
            for (z, e) in z_ood_next.into_iter().zip(ood_eval_next) {
                let xi = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
                add_geometric_scaled_in_place(&mut cur_k, xi, z);
                cur_sum_claim += xi * e;
            }
            let gamma_shift = transcript.squeeze_ext4(b"WHIR_SHIFT_GAMMA");

            accumulate_shift_claims_into_kernel(
                &mut cur_k,
                &mut cur_sum_claim,
                rem_vars,
                gamma_shift,
                &shift_claims,
            );

            active_stage_oracle = Some((cw_next, tree_next, ood_eval_next));
        } else {
            // 2B. Final WHIR Stage (`stage_idx + 1 == num_stages`, `rem_vars == early_stop`):
            debug_assert_eq!(rem_vars, early_stop);
            debug_assert_eq!(cur_coeffs.len(), (1usize << early_stop) + 2);

            let mut final_bytes = Vec::with_capacity(32 * cur_coeffs.len());
            for &v in &cur_coeffs {
                final_bytes.extend_from_slice(&v.to_le_bytes());
            }
            transcript.absorb(b"WHIR_FINAL_POLY", &final_bytes);

            let pow_nonce = grind_pcs_pow(transcript);
            transcript.absorb(b"WHIR_FINAL_POW", &pow_nonce.to_le_bytes());

            // The prover refuses to emit a final polynomial that disagrees with a fiber it
            // opens; the comparison runs through the extracted fold-step gate and Horner rule.
            let final_coeffs_v = to_verified_coeffs(&cur_coeffs);

            if stage_idx == 0 {
                stage_pow_nonce_0 = pow_nonce;
                if state.codewords_0.is_empty() {
                    lazy_cpu_r0 = Some(rebuild_round0());
                }
                let (codewords_0, tree_0): (&[Vec<Goldilocks>], &MerkleCanopyTree) =
                    match &lazy_cpu_r0 {
                        Some((codewords, tree)) => {
                            (codewords.as_slice(), tree.as_ref().unwrap_or(&state.tree_0))
                        }
                        None => (state.codewords_0.as_slice(), &state.tree_0),
                    };
                let num_groups_0 = state.num_groups_0();
                let domain_0 = codewords_0[0].len();
                let log_d0 = domain_0.trailing_zeros() as usize;
                let omega_0 = Goldilocks::two_adic_generator(log_d0);
                let zeta_0 = omega_0.pow(num_groups_0 as u64);
                let q_indices = sample_stage_queries(transcript, 0, num_groups_0, st.num_queries);
                let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega_0, &q_indices);
                round0_salts.reserve(q_indices.len());
                round0_vals.reserve(q_indices.len() * num_polys * arity);
                for (q_pos, &g) in q_indices.iter().enumerate() {
                    let y0 = y0s[q_pos];
                    let inv_y0 = inv_y0s[q_pos];
                    round0_salts.push(derive_round0_salt_mode(turbo, &state.salt_seed, g as u32));
                    let mut fiber = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                    if single {
                        let cw0 = &codewords_0[0];
                        for k in 0..arity {
                            let v = cw0[g + k * num_groups_0];
                            round0_vals.push(v);
                            fiber[k] = GoldilocksExt4::from_base(v);
                        }
                    } else {
                        for (w, cw) in weights.iter().zip(codewords_0) {
                            let mut x = y0;
                            for k in 0..arity {
                                let v = cw[g + k * num_groups_0];
                                round0_vals.push(v);
                                fiber[k] += (w[0] + w[1].mul_base(x)).mul_base(v);
                                x *= zeta_0;
                            }
                        }
                    }
                    assert!(
                        final_fiber_matches_terminal_poly(
                            &fiber[..arity],
                            y0,
                            inv_y0,
                            inv_two,
                            &inv_zetas,
                            chals_slice,
                            &final_coeffs_v,
                        ),
                        "final polynomial disagrees with an opened Round-0 fiber"
                    );
                }
                round0_multiproof = tree_0.open_multi_with_leaf_fn(&q_indices, |g| {
                    round0_leaf_hash_mode(
                        turbo,
                        codewords_0,
                        &state.salt_seed,
                        g,
                        num_groups_0,
                        arity,
                    )
                });
            } else {
                let (mut prev_cw, prev_tree, prev_ood) = match active_stage_oracle.take() {
                    Some(oracle) => oracle,
                    None => unreachable!("a noninitial stage follows a committed oracle"),
                };
                let domain_cur = prev_cw.len();
                let num_groups_cur = domain_cur / arity;
                let log_d = domain_cur.trailing_zeros() as usize;
                let omega = Goldilocks::two_adic_generator(log_d);
                let q_indices =
                    sample_stage_queries(transcript, stage_idx, num_groups_cur, st.num_queries);
                let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega, &q_indices);
                let mut opened_vals = Vec::with_capacity(q_indices.len() * arity);
                for (q_pos, &g) in q_indices.iter().enumerate() {
                    let fiber = collect_coset_group_ext4(&prev_cw, g, num_groups_cur, arity);
                    opened_vals.extend_from_slice(&fiber[..arity]);
                    assert!(
                        final_fiber_matches_terminal_poly(
                            &fiber[..arity],
                            y0s[q_pos],
                            inv_y0s[q_pos],
                            inv_two,
                            &inv_zetas,
                            chals_slice,
                            &final_coeffs_v,
                        ),
                        "final polynomial disagrees with an opened stage fiber"
                    );
                }
                let stage_u8 = stage_idx as u8;
                let multiproof = prev_tree.open_multi_with_leaf_fn(&q_indices, |g| {
                    let fiber = collect_coset_group_ext4(&prev_cw, g, num_groups_cur, arity);
                    hash_ext4_group_mode(turbo, stage_u8, g as u32, &fiber[..arity])
                });
                if state.secret {
                    qsag_asm::volatile_fill(&mut prev_cw, GoldilocksExt4::ZERO);
                }
                folded_layers.push(WhirStageProof {
                    commitment: prev_tree.commitment(),
                    stage_ood_evals: prev_ood,
                    pow_nonce,
                    opened_vals,
                    multiproof,
                });
            }
        }
    }

    release_round0(&mut lazy_cpu_r0);
    if state.secret {
        qsag_asm::volatile_fill(&mut c_scratch, GoldilocksExt4::ZERO);
    }

    HemWhirOpeningProof {
        stage0_ood_evals,
        fold_sumcheck_polys,
        fold_pow_nonces,
        folded_layers,
        final_coeffs: cur_coeffs,
        pow_nonce: stage_pow_nonce_0,
        round0_salts,
        round0_vals,
        round0_multiproof,
    }
}

#[cfg(feature = "vulkan")]
#[inline]
pub(crate) fn ext4_to_arr(e: GoldilocksExt4) -> [u64; 4] {
    e.to_limbs().map(Goldilocks::to_canonical_u64)
}

#[cfg(feature = "vulkan")]
#[inline]
fn word_to_gl_checked(w: u64) -> Result<Goldilocks, qsag_accel::VulkanError> {
    Goldilocks::from_canonical_u64(w).ok_or(qsag_accel::VulkanError::Accel(
        qsag_accel::AccelError::BackendFailure,
    ))
}

#[cfg(feature = "vulkan")]
#[inline]
pub(crate) fn arr_to_ext4_checked(a: [u64; 4]) -> Result<GoldilocksExt4, qsag_accel::VulkanError> {
    let mut limbs = [Goldilocks::ZERO; 4];
    for (&w, dst) in a.iter().zip(&mut limbs) {
        *dst = word_to_gl_checked(w)?;
    }
    Ok(GoldilocksExt4::from_limbs(limbs))
}

#[cfg(feature = "vulkan")]
fn max_intermediate_stage_dims(num_vars: usize, schedule: &WhirSchedule) -> (usize, usize) {
    let mut rem_vars = num_vars;
    let mut max_dom = 1usize;
    let mut max_grps = 1usize;
    for stage_idx in 0..schedule.stages.len().saturating_sub(1) {
        rem_vars -= schedule.stages[stage_idx].step_vars;
        let next_spec = schedule.stages[stage_idx + 1];
        let next_arity = 1usize << next_spec.step_vars;
        let dom = (1usize << rem_vars) * next_spec.blowup;
        let grps = dom / next_arity;
        max_dom = max_dom.max(dom);
        max_grps = max_grps.max(grps);
    }
    (max_dom, max_grps)
}

#[cfg(feature = "vulkan")]
fn eq_kronecker_1024(point: &[GoldilocksExt4]) -> [[u64; 4]; 1024] {
    let raw: Vec<[u64; 4]> = point.iter().copied().map(ext4_to_arr).collect();
    qsag_accel::eq_kronecker_1024(&raw)
}

#[cfg(feature = "vulkan")]
fn mono_kronecker_1024(point: &[GoldilocksExt4]) -> [[u64; 4]; 1024] {
    let raw: Vec<[u64; 4]> = point.iter().copied().map(ext4_to_arr).collect();
    qsag_accel::mono_kronecker_1024(&raw)
}

#[cfg(feature = "vulkan")]
fn pair_geometric_kronecker_2048(
    s0: GoldilocksExt4,
    z0: GoldilocksExt4,
    s1: GoldilocksExt4,
    z1: GoldilocksExt4,
) -> [[u64; 4]; 2048] {
    qsag_accel::pair_geometric_kronecker_2048(
        ext4_to_arr(s0),
        ext4_to_arr(z0),
        ext4_to_arr(s1),
        ext4_to_arr(z1),
    )
}

#[cfg(feature = "vulkan")]
fn collect_steiner_sibling_indices(log_leaves: usize, sorted_unique_indices: &[usize]) -> Vec<u64> {
    let n = 1usize << log_leaves;
    let mut sib_indices = Vec::with_capacity(sorted_unique_indices.len() * log_leaves);
    let mut active: Vec<usize> = sorted_unique_indices.iter().map(|&i| n + i).collect();
    for _ in 0..log_leaves {
        let mut write = 0usize;
        let mut k = 0usize;
        while k < active.len() {
            let u = active[k];
            let sib = u ^ 1;
            if k + 1 < active.len() && active[k + 1] == sib {
                k += 2;
            } else {
                sib_indices.push(sib as u64);
                k += 1;
            }
            active[write] = u >> 1;
            write += 1;
        }
        active.truncate(write);
    }
    sib_indices
}

#[cfg(feature = "vulkan")]
fn decode_merkle_siblings(words: &[u64]) -> Vec<[u8; 32]> {
    words
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| {
            let mut node = [0u8; 32];
            for (i, &w) in c.iter().enumerate() {
                node[8 * i..8 * (i + 1)].copy_from_slice(&w.to_le_bytes());
            }
            node
        })
        .collect()
}

#[cfg(feature = "vulkan")]
fn whir_open_single_gpu(
    state: &HemWhirProverState,
    session: &crate::acceleration::GpuWhirSession,
    point: &[GoldilocksExt4],
    claimed_eval: GoldilocksExt4,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> Result<HemWhirOpeningProof, qsag_accel::VulkanError> {
    let mono_kron = mono_kronecker_1024(point);
    session.exec_verified_unit(|raw, key, anchor| {
        raw.prover_whir_expand_monomial_and_dot_1024_with_receipt(
            key,
            anchor,
            &mono_kron,
            state.num_vars,
            1,
            &mut [],
        )
    })?;
    whir_open_core_gpu(
        state,
        session,
        &[[GoldilocksExt4::ONE, GoldilocksExt4::ZERO]],
        claimed_eval,
        transcript,
    )
}

#[cfg(feature = "vulkan")]
fn whir_open_batch_gpu(
    state: &HemWhirProverState,
    session: &crate::acceleration::GpuWhirSession,
    points: &[&[GoldilocksExt4]],
    evals: &[GoldilocksExt4],
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> Result<HemWhirBatchOpeningProof, qsag_accel::VulkanError> {
    let num_polys = state.num_polys();
    let num_vars = state.num_vars;

    if num_polys == 1 {
        let opening = whir_open_single_gpu(state, session, points[0], evals[0], transcript)?;
        return Ok(HemWhirBatchOpeningProof {
            point_sumcheck_polys: Vec::new(),
            common_point_evals: Vec::new(),
            shifted_evals: Vec::new(),
            batch_pow_nonce: 0,
            opening,
        });
    }

    let lambda = transcript.squeeze_ext4(b"PCS_BATCH_LAMBDA");
    let lambda_pows = powers_of_ext4(lambda, num_polys);
    let mut claim = GoldilocksExt4::ZERO;
    for (&w, &e) in lambda_pows.iter().zip(evals) {
        claim += w * e;
    }

    let mut eq_kron_flat = Vec::with_capacity(1024 * num_polys);
    for p in points {
        eq_kron_flat.extend_from_slice(&eq_kronecker_1024(p));
    }
    let lam_arr: Vec<[u64; 4]> = lambda_pows.iter().copied().map(ext4_to_arr).collect();
    session.exec_verified_unit(|raw, key, anchor| {
        raw.prover_whir_batch_sumcheck_init_with_receipt(
            key,
            anchor,
            &eq_kron_flat,
            &lam_arr,
            num_vars,
        )
    })?;

    let mut cur_len = 1usize << num_vars;
    let pp_hi = (num_polys * cur_len) as u32;
    let mut src_base = 0u32;
    let mut round = 0usize;
    let mut point_sumcheck_polys = Vec::with_capacity(num_vars);
    let mut rho = Vec::with_capacity(num_vars);

    while round < num_vars && (round == 0 || cur_len > 1_024) {
        let [ev0_arr, ev2_arr] = session.exec_verified(|raw, key, anchor| {
            raw.prover_whir_batch_sumcheck_eval_with_receipt(
                key, anchor, round, cur_len, num_polys, src_base,
            )
        })?;
        let ev0 = arr_to_ext4_checked(ev0_arr)?;
        let ev2 = arr_to_ext4_checked(ev2_arr)?;
        let ev1 = claim - ev0;
        let wire = pack_quadratic_wire(ev0, ev1, ev2);
        transcript.absorb_ext4(b"PCS_BATCH_SC_C0", wire[0]);
        transcript.absorb_ext4(b"PCS_BATCH_SC_C2", wire[1]);
        point_sumcheck_polys.push(wire);

        let r = transcript.squeeze_ext4(b"PCS_BATCH_SC_CHAL");
        claim = eval_quadratic_wire(&wire, claim, r);
        let dst_base = if src_base == 0 { pp_hi } else { 0 };
        session.exec_verified_unit(|raw, key, anchor| {
            raw.prover_whir_batch_sumcheck_fold_with_receipt(
                key,
                anchor,
                qsag_accel::WhirBatchSumcheckStep {
                    round,
                    cur_len,
                    num_polys,
                    src_base,
                    dst_base,
                },
                ext4_to_arr(r),
            )
        })?;
        cur_len /= 2;
        src_base = dst_base;
        rho.push(r);
        round += 1;
    }

    let mut raw_t = vec![[0u64; 4]; num_polys * cur_len];
    let mut raw_k = vec![[0u64; 4]; num_polys * cur_len];
    session.exec_verified_unit(|raw, key, anchor| {
        raw.prover_whir_batch_sumcheck_read_tail_with_receipt(
            key,
            anchor,
            qsag_accel::WhirBatchSumcheckStep {
                round: 0,
                cur_len,
                num_polys,
                src_base,
                dst_base: 0,
            },
            &mut raw_t,
            &mut raw_k,
        )
    })?;
    let mut tables: Vec<Vec<GoldilocksExt4>> = Vec::with_capacity(num_polys);
    let mut kernels: Vec<Vec<GoldilocksExt4>> = Vec::with_capacity(num_polys);
    for p in 0..num_polys {
        tables.push(
            raw_t[p * cur_len..(p + 1) * cur_len]
                .iter()
                .copied()
                .map(arr_to_ext4_checked)
                .collect::<Result<Vec<_>, _>>()?,
        );
        kernels.push(
            raw_k[p * cur_len..(p + 1) * cur_len]
                .iter()
                .copied()
                .map(arr_to_ext4_checked)
                .collect::<Result<Vec<_>, _>>()?,
        );
    }

    let mut fold_scratch = Vec::new();
    for _ in round..num_vars {
        let mut ev0 = GoldilocksExt4::ZERO;
        let mut ev2 = GoldilocksExt4::ZERO;
        for i in 0..num_polys {
            let (p0, p2) = sumcheck_round_evals_ext4(&tables[i], &kernels[i], |k, w| k * w);
            ev0 += lambda_pows[i] * p0;
            ev2 += lambda_pows[i] * p2;
        }
        let ev1 = claim - ev0;
        let wire = pack_quadratic_wire(ev0, ev1, ev2);
        transcript.absorb_ext4(b"PCS_BATCH_SC_C0", wire[0]);
        transcript.absorb_ext4(b"PCS_BATCH_SC_C2", wire[1]);
        point_sumcheck_polys.push(wire);

        let r = transcript.squeeze_ext4(b"PCS_BATCH_SC_CHAL");
        claim = eval_quadratic_wire(&wire, claim, r);
        for table in &mut tables {
            fold_first_var_ext4_into(table, &mut fold_scratch, r);
        }
        for kernel in &mut kernels {
            fold_first_var_ext4_into(kernel, &mut fold_scratch, r);
        }
        rho.push(r);
    }

    let common_point_evals: Vec<GoldilocksExt4> = tables.iter().map(|t| t[0]).collect();
    for &e in &common_point_evals {
        transcript.absorb_ext4(b"PCS_BATCH_COMMON_EVAL", e);
    }

    let mono_kron = mono_kronecker_1024(&rho);
    let mut shifted_raw = vec![[0u64; 4]; num_polys];
    session.exec_verified_unit(|raw, key, anchor| {
        raw.prover_whir_expand_monomial_and_dot_1024_with_receipt(
            key,
            anchor,
            &mono_kron,
            num_vars,
            1,
            &mut shifted_raw,
        )
    })?;
    let shifted_evals: Vec<GoldilocksExt4> = shifted_raw
        .into_iter()
        .map(arr_to_ext4_checked)
        .collect::<Result<Vec<_>, _>>()?;
    for &e in &shifted_evals {
        transcript.absorb_ext4(b"PCS_BATCH_SHIFT", e);
    }

    let batch_pow_nonce = grind_pcs_pow(transcript);
    transcript.absorb(b"PCS_BATCH_POW", &batch_pow_nonce.to_le_bytes());
    let weights = cascade_weights(num_polys, transcript);
    let combined_claim = combine_claims(&weights, &common_point_evals, &shifted_evals);
    let opening = whir_open_core_gpu(state, session, &weights, combined_claim, transcript)?;
    Ok(HemWhirBatchOpeningProof {
        point_sumcheck_polys,
        common_point_evals,
        shifted_evals,
        batch_pow_nonce,
        opening,
    })
}

#[cfg(feature = "vulkan")]
fn whir_open_core_gpu(
    state: &HemWhirProverState,
    session: &crate::acceleration::GpuWhirSession,
    weights: &[[GoldilocksExt4; 2]],
    mut cur_sum_claim: GoldilocksExt4,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> Result<HemWhirOpeningProof, qsag_accel::VulkanError> {
    let num_polys = state.num_polys();
    let single = num_polys == 1;
    let sched = &state.schedule;
    let num_stages = sched.stages.len();
    let early_stop = sched.early_stop_vars;
    let fold_vars = state.num_vars - early_stop;

    absorb_whir_schedule(transcript, sched);
    let core_len = 1usize << state.num_vars;
    let mut c_len = core_len + 2;
    let mut k_len = core_len + 2;
    let pp_ck = c_len as u32;

    let z_ood_0 = core::array::from_fn::<_, 2, _>(|_| transcript.squeeze_ext4(b"WHIR_OOD_CHAL"));
    let z_ood_0_kron = pair_geometric_kronecker_2048(
        GoldilocksExt4::ONE,
        z_ood_0[0],
        GoldilocksExt4::ONE,
        z_ood_0[1],
    );
    let weights_arr: Vec<[[u64; 4]; 2]> = weights
        .iter()
        .map(|w| [ext4_to_arr(w[0]), ext4_to_arr(w[1])])
        .collect();
    let ood0_raw = session.exec_verified(|raw, key, anchor| {
        raw.prover_whir_open_init_1024_with_receipt(
            key,
            anchor,
            state.num_vars,
            single,
            &weights_arr,
            &z_ood_0_kron,
        )
    })?;
    let stage0_ood_evals = [
        arr_to_ext4_checked(ood0_raw[0])?,
        arr_to_ext4_checked(ood0_raw[1])?,
    ];
    for e in stage0_ood_evals {
        transcript.absorb_ext4(b"WHIR_OOD_EVAL", e);
    }

    let xi_0 = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
    cur_sum_claim += xi_0 * stage0_ood_evals[0];
    let xi_1 = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
    cur_sum_claim += xi_1 * stage0_ood_evals[1];
    let xi_z_0_kron = pair_geometric_kronecker_2048(xi_0, z_ood_0[0], xi_1, z_ood_0[1]);
    session.exec_verified_unit(|raw, key, anchor| {
        raw.prover_whir_add_ood_claims_1024_with_receipt(key, anchor, k_len, 0, &xi_z_0_kron)
    })?;

    let inv_two = Goldilocks::TWO.inv();
    let inv_zetas = build_inv_zetas();
    let mut rem_vars = state.num_vars;
    let mut fold_sumcheck_polys = Vec::with_capacity(fold_vars);
    let mut fold_pow_nonces = Vec::with_capacity(fold_vars);
    let mut stage_pow_nonce_0: u64 = 0;
    let mut round0_salts: Vec<[u8; 16]> = Vec::new();
    let mut round0_vals: Vec<Goldilocks> = Vec::new();
    let mut round0_multiproof = CanopyMultiProof {
        auth_siblings: Vec::new(),
    };
    let mut active_gpu_stage: Option<(usize, CanopyCommitment, [GoldilocksExt4; 2])> = None;
    let mut folded_layers: Vec<WhirStageProof> = Vec::with_capacity(num_stages.saturating_sub(1));

    let mut c_base = 0u32;
    let mut k_base = 0u32;

    for (stage_idx, st) in sched.stages.iter().enumerate() {
        let arity = 1usize << st.step_vars;
        let mut stage_chals = [[GoldilocksExt4::ZERO; 3]; MAX_FOLD_STEP_VARS];

        for (step_idx, slot) in stage_chals.iter_mut().take(st.step_vars).enumerate() {
            let pairs_ck = (c_len / 2).min(k_len / 2);
            let pairs_c = c_len / 2;
            let k_half = (k_len / 2) as u32;
            let next_base = if c_base == 0 { pp_ck } else { 0 };

            let w012 = session.exec_verified(|raw, key, anchor| {
                raw.prover_whir_fold_pass_a_with_receipt(key, anchor, pairs_ck, c_base, k_base)
            })?;
            let mut wire = [GoldilocksExt4::ZERO; 5];
            wire[0] = arr_to_ext4_checked(w012[0])?;
            wire[1] = arr_to_ext4_checked(w012[1])?;
            wire[2] = arr_to_ext4_checked(w012[2])?;
            let phi = bridge_prefix(&wire, transcript);

            let w34 = session.exec_verified(|raw, key, anchor| {
                raw.prover_whir_fold_pass_b_with_receipt(
                    key,
                    anchor,
                    pairs_c,
                    c_base,
                    k_base,
                    k_half,
                    next_base,
                    ext4_to_arr(phi),
                )
            })?;
            wire[3] = arr_to_ext4_checked(w34[0])?;
            wire[4] = arr_to_ext4_checked(w34[1])?;
            k_len = k_half as usize + 1;

            let (fold_pow_nonce, next_claim, chals) =
                bridge_finish(&wire, cur_sum_claim, phi, transcript);
            cur_sum_claim = next_claim;

            let is_last_step = step_idx + 1 == st.step_vars;
            let norm_zero = is_last_step && next_base != 0;
            c_len = pairs_c + 1;
            let norm_len = c_len.max(k_len);
            session.exec_verified_unit(|raw, key, anchor| {
                raw.prover_whir_fold_pass_c_with_receipt(
                    key,
                    anchor,
                    pairs_c,
                    c_base,
                    next_base,
                    ext4_to_arr(chals[0]),
                    ext4_to_arr(chals[1]),
                    ext4_to_arr(chals[2]),
                    norm_zero,
                    norm_len,
                )
            })?;
            if norm_zero {
                c_base = 0;
                k_base = 0;
            } else {
                c_base = next_base;
                k_base = next_base;
            }

            fold_sumcheck_polys.push(wire);
            fold_pow_nonces.push(fold_pow_nonce);
            *slot = chals;
        }
        rem_vars -= st.step_vars;
        let chals_slice = &stage_chals[..st.step_vars];

        if stage_idx + 1 < num_stages {
            let next_spec = sched.stages[stage_idx + 1];
            let next_arity = 1usize << next_spec.step_vars;
            let next_domain = (1usize << rem_vars) * next_spec.blowup;
            let num_groups_next = next_domain / next_arity;
            let log_leaves_next = num_groups_next.trailing_zeros() as u8;

            let top_next = session.exec_verified(|raw, key, anchor| {
                raw.prover_whir_commit_stage_with_receipt(
                    key,
                    anchor,
                    stage_idx + 1,
                    c_len,
                    next_domain,
                    next_arity,
                )
            })?;
            if !session.record_stage(qsag_accel::ProverKernelSlot::WhirLdeCommitment) {
                return Err(qsag_accel::VulkanError::WorkspacePoisoned);
            }
            let turbo = sched.regime.uses_turboshake_canopy();
            let comm_next = CanopyCommitment {
                root: hash_tree_root_mode(turbo, log_leaves_next, &top_next),
                log_leaves: log_leaves_next,
            };
            transcript.absorb(b"WHIR_NEXT_COMMIT", &comm_next.to_bytes());

            let z_ood_next =
                core::array::from_fn::<_, 2, _>(|_| transcript.squeeze_ext4(b"WHIR_OOD_CHAL"));
            let z_ood_next_kron = pair_geometric_kronecker_2048(
                GoldilocksExt4::ONE,
                z_ood_next[0],
                GoldilocksExt4::ONE,
                z_ood_next[1],
            );
            let ood_raw = session.exec_verified(|raw, key, anchor| {
                raw.prover_whir_eval_univariate_2_1024_with_receipt(
                    key,
                    anchor,
                    c_len,
                    0,
                    &z_ood_next_kron,
                )
            })?;
            let ood_eval_next = [
                arr_to_ext4_checked(ood_raw[0])?,
                arr_to_ext4_checked(ood_raw[1])?,
            ];
            for e in ood_eval_next {
                transcript.absorb_ext4(b"WHIR_OOD_EVAL", e);
            }

            let pow_nonce = grind_pcs_pow(transcript);
            transcript.absorb(b"WHIR_STAGE_POW", &pow_nonce.to_le_bytes());

            let shift_claims = if stage_idx == 0 {
                stage_pow_nonce_0 = pow_nonce;
                let num_groups_0 = state.num_groups_0();
                let domain_0 = core_len * sched.stages[0].blowup;
                let log_d0 = domain_0.trailing_zeros() as usize;
                let log_leaves_0 = num_groups_0.trailing_zeros() as usize;
                let omega_0 = Goldilocks::two_adic_generator(log_d0);
                let zeta_0 = omega_0.pow(num_groups_0 as u64);
                let q_indices = sample_stage_queries(transcript, 0, num_groups_0, st.num_queries);
                let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega_0, &q_indices);
                let q_u64: Vec<u64> = q_indices.iter().map(|&i| i as u64).collect();
                let sib_indices = collect_steiner_sibling_indices(log_leaves_0, &q_indices);

                let salt_words = 2 * q_indices.len();
                let fiber_words = num_polys * arity * q_indices.len();
                let mut raw_q = vec![0u64; salt_words + fiber_words + 4 * sib_indices.len()];
                session.exec_verified_unit(|raw, key, anchor| {
                    raw.prover_whir_gather_queries_with_receipt(
                        key,
                        anchor,
                        0,
                        arity,
                        num_polys,
                        num_groups_0,
                        &q_u64,
                        &sib_indices,
                        &mut raw_q,
                    )
                })?;

                round0_salts.reserve(q_indices.len());
                round0_vals.reserve(fiber_words);
                for qi in 0..q_indices.len() {
                    let mut salt = [0u8; 16];
                    salt[0..8].copy_from_slice(&raw_q[2 * qi].to_le_bytes());
                    salt[8..16].copy_from_slice(&raw_q[2 * qi + 1].to_le_bytes());
                    round0_salts.push(salt);
                }
                let mut claims = Vec::with_capacity(q_indices.len());
                for q_pos in 0..q_indices.len() {
                    let f_base = salt_words + q_pos * (num_polys * arity);
                    let y0 = y0s[q_pos];
                    let inv_y0 = inv_y0s[q_pos];
                    let mut fiber = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                    if single {
                        for k in 0..arity {
                            let v = word_to_gl_checked(raw_q[f_base + k])?;
                            round0_vals.push(v);
                            fiber[k] = GoldilocksExt4::from_base(v);
                        }
                    } else {
                        for (p_idx, w_pair) in weights.iter().enumerate() {
                            let mut x = y0;
                            for k in 0..arity {
                                let v = word_to_gl_checked(raw_q[f_base + p_idx * arity + k])?;
                                round0_vals.push(v);
                                fiber[k] += (w_pair[0] + w_pair[1].mul_base(x)).mul_base(v);
                                x *= zeta_0;
                            }
                        }
                    }
                    let v_shift = fold_coset_group_ext4(
                        &fiber[..arity],
                        y0,
                        inv_y0,
                        inv_two,
                        &inv_zetas,
                        chals_slice,
                    );
                    let z_u = pow2_iter_base(y0, st.step_vars);
                    claims.push((z_u, v_shift));
                }
                round0_multiproof = CanopyMultiProof {
                    auth_siblings: decode_merkle_siblings(&raw_q[salt_words + fiber_words..]),
                };
                claims
            } else {
                let (domain_cur, prev_comm, prev_ood) = active_gpu_stage
                    .take()
                    .ok_or(qsag_accel::VulkanError::WorkspacePoisoned)?;
                let num_groups_cur = domain_cur / arity;
                let log_d = domain_cur.trailing_zeros() as usize;
                let log_leaves_cur = num_groups_cur.trailing_zeros() as usize;
                let omega = Goldilocks::two_adic_generator(log_d);
                let q_indices =
                    sample_stage_queries(transcript, stage_idx, num_groups_cur, st.num_queries);
                let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega, &q_indices);
                let q_u64: Vec<u64> = q_indices.iter().map(|&i| i as u64).collect();
                let sib_indices = collect_steiner_sibling_indices(log_leaves_cur, &q_indices);

                let fiber_words = 4 * arity * q_indices.len();
                let mut raw_q = vec![0u64; fiber_words + 4 * sib_indices.len()];
                session.exec_verified_unit(|raw, key, anchor| {
                    raw.prover_whir_gather_queries_with_receipt(
                        key,
                        anchor,
                        stage_idx,
                        arity,
                        1,
                        num_groups_cur,
                        &q_u64,
                        &sib_indices,
                        &mut raw_q,
                    )
                })?;

                let mut opened_vals = Vec::with_capacity(q_indices.len() * arity);
                let mut claims = Vec::with_capacity(q_indices.len());
                for q_pos in 0..q_indices.len() {
                    let f_base = q_pos * 4 * arity;
                    let mut fiber = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                    for (k, slot) in fiber.iter_mut().enumerate().take(arity) {
                        let o = f_base + 4 * k;
                        *slot = arr_to_ext4_checked([
                            raw_q[o],
                            raw_q[o + 1],
                            raw_q[o + 2],
                            raw_q[o + 3],
                        ])?;
                    }
                    opened_vals.extend_from_slice(&fiber[..arity]);
                    let v_shift = fold_coset_group_ext4(
                        &fiber[..arity],
                        y0s[q_pos],
                        inv_y0s[q_pos],
                        inv_two,
                        &inv_zetas,
                        chals_slice,
                    );
                    let z_u = pow2_iter_base(y0s[q_pos], st.step_vars);
                    claims.push((z_u, v_shift));
                }
                let multiproof = CanopyMultiProof {
                    auth_siblings: decode_merkle_siblings(&raw_q[fiber_words..]),
                };
                folded_layers.push(WhirStageProof {
                    commitment: prev_comm,
                    stage_ood_evals: prev_ood,
                    pow_nonce,
                    opened_vals,
                    multiproof,
                });
                claims
            };

            let mut shift_bytes = Vec::with_capacity(32 * shift_claims.len());
            for &(_, v_shift) in &shift_claims {
                shift_bytes.extend_from_slice(&v_shift.to_le_bytes());
            }
            transcript.absorb(b"WHIR_SHIFT_VALS", &shift_bytes);

            let xi_next_0 = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
            cur_sum_claim += xi_next_0 * ood_eval_next[0];
            let xi_next_1 = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
            cur_sum_claim += xi_next_1 * ood_eval_next[1];
            let xi_z_next_kron =
                pair_geometric_kronecker_2048(xi_next_0, z_ood_next[0], xi_next_1, z_ood_next[1]);
            session.exec_verified_unit(|raw, key, anchor| {
                raw.prover_whir_add_ood_claims_1024_with_receipt(
                    key,
                    anchor,
                    k_len,
                    0,
                    &xi_z_next_kron,
                )
            })?;

            let gamma_shift = transcript.squeeze_ext4(b"WHIR_SHIFT_GAMMA");
            let mut z_pow_256 = Vec::with_capacity(shift_claims.len() * 256);
            let mut claims_meta = Vec::with_capacity(shift_claims.len());
            let mut w = gamma_shift;
            for &(z_u, v_shift) in &shift_claims {
                cur_sum_claim += w * v_shift;
                let mut p = Goldilocks::ONE;
                for _ in 0..256 {
                    z_pow_256.push(p.to_canonical_u64());
                    p *= z_u;
                }
                let wa = ext4_to_arr(w);
                claims_meta.push([z_u.to_canonical_u64(), 0, 0, 0, wa[0], wa[1], wa[2], wa[3]]);
                w *= gamma_shift;
            }
            session.exec_verified_unit(|raw, key, anchor| {
                raw.prover_whir_accumulate_shift_claims_with_receipt(
                    key,
                    anchor,
                    k_len,
                    0,
                    &z_pow_256,
                    &claims_meta,
                )
            })?;

            active_gpu_stage = Some((next_domain, comm_next, ood_eval_next));
        } else {
            let final_len = (1usize << early_stop) + 2;
            let mut final_raw = vec![[0u64; 4]; final_len];
            session.exec_verified_unit(|raw, key, anchor| {
                raw.prover_whir_read_final_coeffs_with_receipt(key, anchor, 0, &mut final_raw)
            })?;
            let final_coeffs: Vec<GoldilocksExt4> = final_raw
                .into_iter()
                .map(arr_to_ext4_checked)
                .collect::<Result<Vec<_>, _>>()?;

            let mut final_bytes = Vec::with_capacity(32 * final_coeffs.len());
            for &v in &final_coeffs {
                final_bytes.extend_from_slice(&v.to_le_bytes());
            }
            transcript.absorb(b"WHIR_FINAL_POLY", &final_bytes);

            let pow_nonce = grind_pcs_pow(transcript);
            transcript.absorb(b"WHIR_FINAL_POW", &pow_nonce.to_le_bytes());

            let final_coeffs_v = to_verified_coeffs(&final_coeffs);

            if stage_idx == 0 {
                stage_pow_nonce_0 = pow_nonce;
                let num_groups_0 = state.num_groups_0();
                let domain_0 = core_len * sched.stages[0].blowup;
                let log_d0 = domain_0.trailing_zeros() as usize;
                let log_leaves_0 = num_groups_0.trailing_zeros() as usize;
                let omega_0 = Goldilocks::two_adic_generator(log_d0);
                let zeta_0 = omega_0.pow(num_groups_0 as u64);
                let q_indices = sample_stage_queries(transcript, 0, num_groups_0, st.num_queries);
                let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega_0, &q_indices);
                let q_u64: Vec<u64> = q_indices.iter().map(|&i| i as u64).collect();
                let sib_indices = collect_steiner_sibling_indices(log_leaves_0, &q_indices);

                let salt_words = 2 * q_indices.len();
                let fiber_words = num_polys * arity * q_indices.len();
                let mut raw_q = vec![0u64; salt_words + fiber_words + 4 * sib_indices.len()];
                session.exec_verified_unit(|raw, key, anchor| {
                    raw.prover_whir_gather_queries_with_receipt(
                        key,
                        anchor,
                        0,
                        arity,
                        num_polys,
                        num_groups_0,
                        &q_u64,
                        &sib_indices,
                        &mut raw_q,
                    )
                })?;

                round0_salts.reserve(q_indices.len());
                round0_vals.reserve(fiber_words);
                for qi in 0..q_indices.len() {
                    let mut salt = [0u8; 16];
                    salt[0..8].copy_from_slice(&raw_q[2 * qi].to_le_bytes());
                    salt[8..16].copy_from_slice(&raw_q[2 * qi + 1].to_le_bytes());
                    round0_salts.push(salt);
                }
                for q_pos in 0..q_indices.len() {
                    let f_base = salt_words + q_pos * (num_polys * arity);
                    let y0 = y0s[q_pos];
                    let inv_y0 = inv_y0s[q_pos];
                    let mut fiber = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                    if single {
                        for k in 0..arity {
                            let v = word_to_gl_checked(raw_q[f_base + k])?;
                            round0_vals.push(v);
                            fiber[k] = GoldilocksExt4::from_base(v);
                        }
                    } else {
                        for (p_idx, w_pair) in weights.iter().enumerate() {
                            let mut x = y0;
                            for k in 0..arity {
                                let v = word_to_gl_checked(raw_q[f_base + p_idx * arity + k])?;
                                round0_vals.push(v);
                                fiber[k] += (w_pair[0] + w_pair[1].mul_base(x)).mul_base(v);
                                x *= zeta_0;
                            }
                        }
                    }
                    if !final_fiber_matches_terminal_poly(
                        &fiber[..arity],
                        y0,
                        inv_y0,
                        inv_two,
                        &inv_zetas,
                        chals_slice,
                        &final_coeffs_v,
                    ) {
                        return Err(qsag_accel::VulkanError::WorkspacePoisoned);
                    }
                }
                round0_multiproof = CanopyMultiProof {
                    auth_siblings: decode_merkle_siblings(&raw_q[salt_words + fiber_words..]),
                };
            } else {
                let (domain_cur, prev_comm, prev_ood) = active_gpu_stage
                    .take()
                    .ok_or(qsag_accel::VulkanError::WorkspacePoisoned)?;
                let num_groups_cur = domain_cur / arity;
                let log_d = domain_cur.trailing_zeros() as usize;
                let log_leaves_cur = num_groups_cur.trailing_zeros() as usize;
                let omega = Goldilocks::two_adic_generator(log_d);
                let q_indices =
                    sample_stage_queries(transcript, stage_idx, num_groups_cur, st.num_queries);
                let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega, &q_indices);
                let q_u64: Vec<u64> = q_indices.iter().map(|&i| i as u64).collect();
                let sib_indices = collect_steiner_sibling_indices(log_leaves_cur, &q_indices);

                let fiber_words = 4 * arity * q_indices.len();
                let mut raw_q = vec![0u64; fiber_words + 4 * sib_indices.len()];
                session.exec_verified_unit(|raw, key, anchor| {
                    raw.prover_whir_gather_queries_with_receipt(
                        key,
                        anchor,
                        stage_idx,
                        arity,
                        1,
                        num_groups_cur,
                        &q_u64,
                        &sib_indices,
                        &mut raw_q,
                    )
                })?;

                let mut opened_vals = Vec::with_capacity(q_indices.len() * arity);
                for q_pos in 0..q_indices.len() {
                    let f_base = q_pos * 4 * arity;
                    let mut fiber = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                    for (k, slot) in fiber.iter_mut().enumerate().take(arity) {
                        let o = f_base + 4 * k;
                        *slot = arr_to_ext4_checked([
                            raw_q[o],
                            raw_q[o + 1],
                            raw_q[o + 2],
                            raw_q[o + 3],
                        ])?;
                    }
                    opened_vals.extend_from_slice(&fiber[..arity]);
                    if !final_fiber_matches_terminal_poly(
                        &fiber[..arity],
                        y0s[q_pos],
                        inv_y0s[q_pos],
                        inv_two,
                        &inv_zetas,
                        chals_slice,
                        &final_coeffs_v,
                    ) {
                        return Err(qsag_accel::VulkanError::WorkspacePoisoned);
                    }
                }
                let multiproof = CanopyMultiProof {
                    auth_siblings: decode_merkle_siblings(&raw_q[fiber_words..]),
                };
                folded_layers.push(WhirStageProof {
                    commitment: prev_comm,
                    stage_ood_evals: prev_ood,
                    pow_nonce,
                    opened_vals,
                    multiproof,
                });
            }

            if !session.record_stage(qsag_accel::ProverKernelSlot::WhirFoldSumcheck) {
                return Err(qsag_accel::VulkanError::WorkspacePoisoned);
            }
            return Ok(HemWhirOpeningProof {
                stage0_ood_evals,
                fold_sumcheck_polys,
                fold_pow_nonces,
                folded_layers,
                final_coeffs,
                pow_nonce: stage_pow_nonce_0,
                round0_salts,
                round0_vals,
                round0_multiproof,
            });
        }
    }

    Err(qsag_accel::VulkanError::WorkspacePoisoned)
}

/// Accumulate `q` shift evaluation claims `(z_u, v_shift)` with weights $\gamma_{\text{shift}}^{m+1}$
/// ($m = 0 \dots q-1$) into `(cur_k, cur_sum_claim)`.
fn accumulate_shift_claims_into_kernel(
    cur_k: &mut [GoldilocksExt4],
    cur_sum_claim: &mut GoldilocksExt4,
    rem_vars: usize,
    gamma_shift: GoldilocksExt4,
    shift_claims: &[(Goldilocks, GoldilocksExt4)],
) {
    debug_assert_eq!(cur_k.len(), (1usize << rem_vars) + 2);
    if shift_claims.is_empty() {
        return;
    }
    let mut weighted: Vec<(Goldilocks, GoldilocksExt4)> = Vec::with_capacity(shift_claims.len());
    let mut w = gamma_shift;
    for &(z, e) in shift_claims {
        *cur_sum_claim += w * e;
        weighted.push((z, w));
        w *= gamma_shift;
    }

    #[cfg(feature = "std")]
    if cur_k.len() >= 4_096 {
        let workers = crate::parallel_workers().min(cur_k.len());
        let chunk = cur_k.len().div_ceil(workers);
        let weighted_ref = weighted.as_slice();
        std::thread::scope(|scope| {
            for (t_idx, sub) in cur_k.chunks_mut(chunk).enumerate() {
                let start = (t_idx * chunk) as u64;
                crate::spawn_bounded(scope, move || {
                    for &(z, weight) in weighted_ref {
                        let mut power = z.pow(start);
                        for slot in sub.iter_mut() {
                            *slot += weight.mul_base(power);
                            power *= z;
                        }
                    }
                });
            }
        });
        return;
    }

    for &(z, weight) in &weighted {
        let mut power = Goldilocks::ONE;
        for slot in cur_k.iter_mut() {
            *slot += weight.mul_base(power);
            power *= z;
        }
    }
}

#[inline]
fn pcs_num_vars_supported(num_vars: usize) -> bool {
    (2..=MAX_PCS_NUM_VARS).contains(&num_vars)
}

/// Verify a single-point `Hem` WHIR opening proof over `GoldilocksExt4`.
pub fn whir_verify(
    comm_0: &CanopyCommitment,
    num_vars: usize,
    point: &[GoldilocksExt4],
    claimed_eval: GoldilocksExt4,
    proof: &HemWhirOpeningProof,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> bool {
    if !pcs_num_vars_supported(num_vars) {
        return false;
    }
    let schedule = whir_stage_schedule(num_vars);
    whir_verify_with_schedule(
        comm_0,
        num_vars,
        point,
        claimed_eval,
        proof,
        transcript,
        &schedule,
    )
}

pub fn whir_verify_with_schedule(
    comm_0: &CanopyCommitment,
    num_vars: usize,
    point: &[GoldilocksExt4],
    claimed_eval: GoldilocksExt4,
    proof: &HemWhirOpeningProof,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    schedule: &WhirSchedule,
) -> bool {
    absorb_whir_schedule(transcript, schedule);
    if !pcs_num_vars_supported(num_vars) || point.len() != num_vars {
        return false;
    }
    transcript.absorb(b"PCS_NUM_VARS", &(num_vars as u64).to_le_bytes());
    transcript.absorb(b"PCS_COMM0", &comm_0.to_bytes());
    for &c in point {
        transcript.absorb_ext4(b"PCS_POINT_COORD", c);
    }
    transcript.absorb_ext4(b"PCS_CLAIMED_EVAL", claimed_eval);

    whir_verify_core(
        comm_0,
        &[[GoldilocksExt4::ONE, GoldilocksExt4::ZERO]],
        point,
        claimed_eval,
        proof,
        transcript,
        schedule,
    )
}

/// Verify a batched `Hem` WHIR opening proof: $W_i(\text{points}[i]) = \text{evals}[i]$ for all $i$.
pub fn whir_verify_batch(
    comm_0: &CanopyCommitment,
    num_vars: usize,
    points: &[&[GoldilocksExt4]],
    evals: &[GoldilocksExt4],
    proof: &HemWhirBatchOpeningProof,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> bool {
    if !pcs_num_vars_supported(num_vars) {
        return false;
    }
    let schedule = whir_stage_schedule(num_vars);
    whir_verify_batch_with_schedule(
        comm_0, num_vars, points, evals, proof, transcript, &schedule,
    )
}

pub fn whir_verify_batch_with_schedule(
    comm_0: &CanopyCommitment,
    num_vars: usize,
    points: &[&[GoldilocksExt4]],
    evals: &[GoldilocksExt4],
    proof: &HemWhirBatchOpeningProof,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    schedule: &WhirSchedule,
) -> bool {
    let _phase = crate::profile::span("whir_verify_batch");
    absorb_whir_schedule(transcript, schedule);
    let num_polys = points.len();
    if !pcs_num_vars_supported(num_vars)
        || num_polys == 0
        || num_polys > MAX_BATCH_POLYS
        || evals.len() != num_polys
        || points.iter().any(|p| p.len() != num_vars)
    {
        return false;
    }
    absorb_batch_statement(transcript, num_vars, comm_0, points, evals);

    if num_polys == 1 {
        if !proof.point_sumcheck_polys.is_empty()
            || !proof.common_point_evals.is_empty()
            || !proof.shifted_evals.is_empty()
            || proof.batch_pow_nonce != 0
        {
            return false;
        }
        return whir_verify_core(
            comm_0,
            &[[GoldilocksExt4::ONE, GoldilocksExt4::ZERO]],
            points[0],
            evals[0],
            &proof.opening,
            transcript,
            schedule,
        );
    }
    if proof.point_sumcheck_polys.len() != num_vars
        || proof.common_point_evals.len() != num_polys
        || proof.shifted_evals.len() != num_polys
    {
        return false;
    }

    // Verify point-reduction sumcheck (`c_1 = claim - 2*c_0 - c_2` enforces `g(0) + g(1) == claim`):
    let lambda = transcript.squeeze_ext4(b"PCS_BATCH_LAMBDA");
    let lambda_pows = powers_of_ext4(lambda, num_polys);
    let mut claim = GoldilocksExt4::ZERO;
    for (&w, &e) in lambda_pows.iter().zip(evals) {
        claim += w * e;
    }
    let mut rho = Vec::with_capacity(num_vars);
    for wire in &proof.point_sumcheck_polys {
        transcript.absorb_ext4(b"PCS_BATCH_SC_C0", wire[0]);
        transcript.absorb_ext4(b"PCS_BATCH_SC_C2", wire[1]);
        let r = transcript.squeeze_ext4(b"PCS_BATCH_SC_CHAL");
        claim = eval_quadratic_wire(wire, claim, r);
        rho.push(r);
    }

    let mut expected = GoldilocksExt4::ZERO;
    for ((&w, point), &e) in lambda_pows
        .iter()
        .zip(points)
        .zip(&proof.common_point_evals)
    {
        expected += w * eq_poly_ext4(point, &rho) * e;
    }
    if !qsag_whir_verified::verify_ood_pin_eq(
        &expected.to_limbs().map(Goldilocks::to_canonical_u64),
        &claim.to_limbs().map(Goldilocks::to_canonical_u64),
    ) {
        return false;
    }
    for &e in &proof.common_point_evals {
        transcript.absorb_ext4(b"PCS_BATCH_COMMON_EVAL", e);
    }

    for &e in &proof.shifted_evals {
        transcript.absorb_ext4(b"PCS_BATCH_SHIFT", e);
    }
    if !verify_pcs_pow(transcript, proof.batch_pow_nonce) {
        return false;
    }
    transcript.absorb(b"PCS_BATCH_POW", &proof.batch_pow_nonce.to_le_bytes());
    let weights = cascade_weights(num_polys, transcript);
    let combined_claim = combine_claims(&weights, &proof.common_point_evals, &proof.shifted_evals);
    whir_verify_core(
        comm_0,
        &weights,
        &rho,
        combined_claim,
        &proof.opening,
        transcript,
        schedule,
    )
}

/// One dual linear-functional bridge round as the verifier saw it: the prover's wire, the
/// incoming claim, and the challenges squeezed for it.
struct BridgeRound {
    wire: [GoldilocksExt4; 5],
    claim: GoldilocksExt4,
    phi: GoldilocksExt4,
    chals: [GoldilocksExt4; 3],
}

/// One term `weight * W(point)` of a linear evaluation claim on a committed multilinear `W`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WeightedPoint {
    pub weight: GoldilocksExt4,
    pub point: Vec<GoldilocksExt4>,
}

/// `kernel[i] += weight * prod_j point[j]^{bit_j(i)}` for `i < 2^point.len()`: the
/// monomial-basis functional of `weight * W(point, 0, ..., 0)`.
pub fn add_point_kernel(
    kernel: &mut [GoldilocksExt4],
    weight: GoldilocksExt4,
    point: &[GoldilocksExt4],
) {
    let n = 1usize << point.len();
    assert!(kernel.len() >= n);
    let (lo, hi) = split_monomial_table(point);
    let add = |base: usize, part: &mut [GoldilocksExt4]| {
        for (offset, dst) in part.iter_mut().enumerate() {
            let index = base + offset;
            *dst += weight * lo[index % lo.len()] * hi[index / lo.len()];
        }
    };
    #[cfg(feature = "std")]
    if n >= 16_384 && crate::parallel_workers() > 1 {
        let chunk = n.div_ceil(crate::parallel_workers());
        std::thread::scope(|scope| {
            let add = &add;
            for (i, part) in kernel[..n].chunks_mut(chunk).enumerate() {
                crate::spawn_bounded(scope, move || add(i * chunk, part));
            }
        });
        return;
    }
    add(0, &mut kernel[..n]);
}

/// Square-root-sized Kronecker factors for a monomial evaluation functional.
pub(crate) fn split_monomial_table(
    point: &[GoldilocksExt4],
) -> (Vec<GoldilocksExt4>, Vec<GoldilocksExt4>) {
    let split = point.len() / 2;
    let mut lo = affine::monomial_table(&point[..split]);
    let mut hi = affine::monomial_table(&point[split..]);
    lo.truncate(1 << split);
    hi.truncate(1 << (point.len() - split));
    (lo, hi)
}

/// Open the scalar blend $U = \sum_i \text{scalars}[i] \cdot W_i$ of a batch commitment against
/// one linear functional: prove $\langle \text{coeffs}(U), \text{kernel} \rangle = \text{claim}$.
///
/// `kernel` holds the functional on the $2^\ell$ monomial coefficients followed by two zero
/// overflow slots; `monomial_polys[i]` is `hypercube_to_monomial_coeffs` of polynomial `i`.
/// Unlike [`whir_open_batch`], no per-polynomial evaluation is sent: the only values derived
/// from an individual polynomial are its queried Stage-0 symbols. The caller binds the
/// commitment, the scalars, the functional and the claim into `transcript` beforehand.
pub fn whir_open_blend(
    state: &HemWhirProverState,
    scalars: &[GoldilocksExt4],
    monomial_polys: &[Vec<Goldilocks>],
    kernel: Vec<GoldilocksExt4>,
    claim: GoldilocksExt4,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> HemWhirOpeningProof {
    assert!(state.num_polys() >= 2 && scalars.len() == state.num_polys());
    assert_eq!(monomial_polys.len(), state.num_polys());
    assert_eq!(kernel.len(), (1usize << state.num_vars) + 2);
    let weights: Vec<[GoldilocksExt4; 2]> =
        scalars.iter().map(|&s| [s, GoldilocksExt4::ZERO]).collect();
    whir_open_core(
        state,
        Some(monomial_polys),
        &weights,
        kernel,
        claim,
        transcript,
    )
}

/// [`whir_open_blend`] taking the monomial coefficients from `state`: its cache when it has
/// one, otherwise one polynomial at a time from the hypercube evaluations.
pub(crate) fn whir_open_blend_from_state(
    state: &HemWhirProverState,
    scalars: &[GoldilocksExt4],
    kernel: Vec<GoldilocksExt4>,
    claim: GoldilocksExt4,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> HemWhirOpeningProof {
    assert!(state.num_polys() >= 2 && scalars.len() == state.num_polys());
    assert_eq!(kernel.len(), (1usize << state.num_vars) + 2);
    let weights: Vec<[GoldilocksExt4; 2]> =
        scalars.iter().map(|&s| [s, GoldilocksExt4::ZERO]).collect();
    whir_open_core(state, None, &weights, kernel, claim, transcript)
}

/// Drop the Stage-0 Reed-Solomon cache of a public CPU commitment. An opening re-encodes
/// it from the retained evaluations, so the proof is unchanged and the opening is slower.
pub(crate) fn release_round0_cache(state: &mut HemWhirProverState) {
    debug_assert!(!state.secret);
    state.codewords_0 = Vec::new();
    state.monomial_coeffs_0 = Vec::new();
}

/// Verify a [`whir_open_blend`] proof for the functional
/// $\sum_t \text{terms}[t].\text{weight} \cdot U(\text{terms}[t].\text{point})$.
#[allow(clippy::too_many_arguments)]
pub fn whir_verify_blend(
    comm_0: &CanopyCommitment,
    num_vars: usize,
    scalars: &[GoldilocksExt4],
    terms: &[WeightedPoint],
    claim: GoldilocksExt4,
    proof: &HemWhirOpeningProof,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    schedule: &WhirSchedule,
) -> bool {
    if scalars.len() < 2 || terms.iter().any(|t| t.point.len() != num_vars) {
        return false;
    }
    let weights: Vec<[GoldilocksExt4; 2]> =
        scalars.iter().map(|&s| [s, GoldilocksExt4::ZERO]).collect();
    let claims = terms
        .iter()
        .map(|t| KernelClaim::Point {
            offset: 0,
            weight: t.weight,
            point: t.point.clone(),
            overflow: [GoldilocksExt4::ZERO; 2],
        })
        .collect();
    whir_verify_core_claims(
        comm_0, &weights, num_vars, claims, claim, proof, transcript, schedule,
    )
}

/// Verify the multi-stage `Hem` WHIR opening of $\sum_i \text{weights}[i] \cdot W_i$ at `init_point`
/// against `comm_0`.
fn whir_verify_core(
    comm_0: &CanopyCommitment,
    weights: &[[GoldilocksExt4; 2]],
    init_point: &[GoldilocksExt4],
    init_sum_claim: GoldilocksExt4,
    proof: &HemWhirOpeningProof,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    sched: &WhirSchedule,
) -> bool {
    whir_verify_core_claims(
        comm_0,
        weights,
        init_point.len(),
        vec![KernelClaim::initial(init_point.to_vec())],
        init_sum_claim,
        proof,
        transcript,
        sched,
    )
}

/// [`whir_verify_core`] for an initial claim that is a weighted sum of evaluation functionals.
#[allow(clippy::too_many_arguments)]
fn whir_verify_core_claims(
    comm_0: &CanopyCommitment,
    weights: &[[GoldilocksExt4; 2]],
    num_vars: usize,
    init_claims: Vec<KernelClaim>,
    init_sum_claim: GoldilocksExt4,
    proof: &HemWhirOpeningProof,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    sched: &WhirSchedule,
) -> bool {
    let num_polys = weights.len();
    if !pcs_num_vars_supported(num_vars)
        || num_polys == 0
        || num_polys > MAX_BATCH_POLYS
        || init_claims.is_empty()
        || comm_0.log_leaves > 28
    {
        return false;
    }

    if !sched.validate_structural(num_vars) {
        return false;
    }
    let num_stages = sched.stages.len();
    let early_stop = sched.early_stop_vars;
    let fold_vars = num_vars - early_stop;

    if proof.fold_sumcheck_polys.len() != fold_vars
        || proof.fold_pow_nonces.len() != fold_vars
        || proof.folded_layers.len() + 1 != num_stages
        || proof.final_coeffs.len() != (1usize << early_stop) + 2
    {
        return false;
    }

    let st0 = sched.stages[0];
    let arity_0 = 1usize << st0.step_vars;
    let domain_0 = (1usize << num_vars) * st0.blowup;
    let num_groups_0 = domain_0 / arity_0;
    if (1usize << (comm_0.log_leaves as usize)) != num_groups_0 {
        return false;
    }

    // Bind WHIR schedule into transcript.
    absorb_whir_schedule(transcript, sched);

    let total_claims = 3usize
        + sched
            .stages
            .iter()
            .take(num_stages.saturating_sub(1))
            .map(|s| 2 + s.num_queries)
            .sum::<usize>();
    let mut kernel_claims = Vec::with_capacity(total_claims + init_claims.len());
    kernel_claims.extend(init_claims);
    let mut cur_sum_claim = init_sum_claim;
    let z_ood_0 = core::array::from_fn::<_, 2, _>(|_| transcript.squeeze_ext4(b"WHIR_OOD_CHAL"));
    for e in proof.stage0_ood_evals {
        transcript.absorb_ext4(b"WHIR_OOD_EVAL", e);
    }
    for (z, e) in z_ood_0.into_iter().zip(proof.stage0_ood_evals) {
        let xi = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
        kernel_claims.push(KernelClaim::evaluation(0, xi, z, num_vars));
        cur_sum_claim += xi * e;
    }

    let inv_two = Goldilocks::TWO.inv();
    let inv_zetas = build_inv_zetas();

    let mut alphas = Vec::with_capacity(fold_vars);
    let mut phis = Vec::with_capacity(fold_vars);
    let mut sc_cursor = 0usize;
    let mut var_off = 0usize;
    let mut rem_vars = num_vars;
    // Inputs of the most recent bridge round; the terminal gate re-checks the last one.
    let mut last_bridge: Option<BridgeRound> = None;

    for (stage_idx, st) in sched.stages.iter().enumerate() {
        let arity = 1usize << st.step_vars;
        let stage_alpha_start = alphas.len();

        for _ in 0..st.step_vars {
            let wire = proof.fold_sumcheck_polys[sc_cursor];
            let fold_pow_nonce = proof.fold_pow_nonces[sc_cursor];
            sc_cursor += 1;
            let phi = bridge_prefix(&wire, transcript);
            let Some((next, chals)) =
                bridge_verify_finish(&wire, fold_pow_nonce, cur_sum_claim, phi, transcript)
            else {
                return false;
            };
            last_bridge = Some(BridgeRound {
                wire,
                claim: cur_sum_claim,
                phi,
                chals,
            });
            cur_sum_claim = next;
            phis.push(phi);
            alphas.push(chals);
        }
        var_off += st.step_vars;
        rem_vars -= st.step_vars;
        let stage_chals = &alphas[stage_alpha_start..stage_alpha_start + st.step_vars];

        if stage_idx + 1 < num_stages {
            // 2A. Intermediate transition `stage_idx -> stage_idx + 1`:
            let next_spec = sched.stages[stage_idx + 1];
            let next_arity = 1usize << next_spec.step_vars;
            let domain_next = (1usize << rem_vars) * next_spec.blowup;
            let num_groups_next = domain_next / next_arity;

            let next_layer = &proof.folded_layers[stage_idx];
            if next_layer.commitment.log_leaves > 28
                || (1usize << (next_layer.commitment.log_leaves as usize)) != num_groups_next
            {
                return false;
            }
            transcript.absorb(b"WHIR_NEXT_COMMIT", &next_layer.commitment.to_bytes());
            let z_ood_next =
                core::array::from_fn::<_, 2, _>(|_| transcript.squeeze_ext4(b"WHIR_OOD_CHAL"));
            for e in next_layer.stage_ood_evals {
                transcript.absorb_ext4(b"WHIR_OOD_EVAL", e);
            }

            let stage_pow_nonce = if stage_idx == 0 {
                proof.pow_nonce
            } else {
                proof.folded_layers[stage_idx - 1].pow_nonce
            };
            if !verify_pcs_pow(transcript, stage_pow_nonce) {
                return false;
            }
            transcript.absorb(b"WHIR_STAGE_POW", &stage_pow_nonce.to_le_bytes());

            let shift_claims = if stage_idx == 0 {
                verify_and_fold_stage0_fibers(
                    CanopyHash::for_stage(sched.regime, 0),
                    comm_0,
                    num_polys,
                    weights,
                    domain_0,
                    arity_0,
                    st.num_queries,
                    stage_chals,
                    inv_two,
                    &inv_zetas,
                    proof,
                    None,
                    transcript,
                )
            } else {
                let cur_layer = &proof.folded_layers[stage_idx - 1];
                let domain_cur = (1usize << (rem_vars + st.step_vars)) * st.blowup;
                verify_and_fold_ext4_stage_fibers(
                    CanopyHash::for_stage(sched.regime, stage_idx),
                    stage_idx,
                    cur_layer,
                    domain_cur,
                    arity,
                    st.num_queries,
                    stage_chals,
                    inv_two,
                    &inv_zetas,
                    None,
                    transcript,
                )
            };
            let Some(shift_claims) = shift_claims else {
                return false;
            };

            let mut shift_bytes = Vec::with_capacity(32 * shift_claims.len());
            for &(_, v_shift) in &shift_claims {
                shift_bytes.extend_from_slice(&v_shift.to_le_bytes());
            }
            transcript.absorb(b"WHIR_SHIFT_VALS", &shift_bytes);

            for (z, e) in z_ood_next.into_iter().zip(next_layer.stage_ood_evals) {
                let xi = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
                kernel_claims.push(KernelClaim::evaluation(var_off, xi, z, rem_vars));
                cur_sum_claim += xi * e;
            }
            let gamma_shift = transcript.squeeze_ext4(b"WHIR_SHIFT_GAMMA");
            let mut w_shift = gamma_shift;
            for &(z_u, v_shift) in &shift_claims {
                cur_sum_claim += w_shift * v_shift;
                kernel_claims.push(KernelClaim::evaluation(
                    var_off,
                    w_shift,
                    GoldilocksExt4::from_base(z_u),
                    rem_vars,
                ));
                w_shift *= gamma_shift;
            }
        } else {
            // 2B. Final WHIR Stage (`stage_idx + 1 == num_stages`):
            if rem_vars != early_stop || alphas.len() != fold_vars {
                return false;
            }

            let mut final_bytes = Vec::with_capacity(32 * proof.final_coeffs.len());
            for &v in &proof.final_coeffs {
                final_bytes.extend_from_slice(&v.to_le_bytes());
            }
            transcript.absorb(b"WHIR_FINAL_POLY", &final_bytes);

            // Mandatory terminal sumcheck check across all accumulated evaluation, OOD, and shift
            // claims: the last bridge round must land exactly on the terminal contraction. The
            // acceptance is the extracted `verify_cwyz_bridge_claim_step` gate.
            let expected_terminal = terminal_sum_owned(
                &phis,
                early_stop,
                core::mem::take(&mut kernel_claims),
                &proof.final_coeffs,
            );
            let Some(last) = last_bridge.as_ref() else {
                return false;
            };
            let [theta, alpha, beta] = last.chals;
            if !qsag_whir_verified::verify_cwyz_bridge_claim_step(
                to_verified_ext4(last.wire[0]),
                to_verified_ext4(last.wire[1]),
                to_verified_ext4(last.wire[2]),
                to_verified_ext4(last.wire[3]),
                to_verified_ext4(last.wire[4]),
                to_verified_ext4(last.claim),
                to_verified_ext4(last.phi),
                to_verified_ext4(theta),
                to_verified_ext4(alpha),
                to_verified_ext4(beta),
                to_verified_ext4(expected_terminal),
            ) {
                return false;
            }
            let terminal_coeffs = alloc::sync::Arc::new(to_verified_coeffs(&proof.final_coeffs));

            let final_pow_nonce = if stage_idx == 0 {
                proof.pow_nonce
            } else {
                proof.folded_layers[stage_idx - 1].pow_nonce
            };
            if !verify_pcs_pow(transcript, final_pow_nonce) {
                return false;
            }
            transcript.absorb(b"WHIR_FINAL_POW", &final_pow_nonce.to_le_bytes());

            let final_claims = if stage_idx == 0 {
                verify_and_fold_stage0_fibers(
                    CanopyHash::for_stage(sched.regime, 0),
                    comm_0,
                    num_polys,
                    weights,
                    domain_0,
                    arity_0,
                    st.num_queries,
                    stage_chals,
                    inv_two,
                    &inv_zetas,
                    proof,
                    Some(&terminal_coeffs),
                    transcript,
                )
            } else {
                let cur_layer = &proof.folded_layers[stage_idx - 1];
                let domain_cur = (1usize << (rem_vars + st.step_vars)) * st.blowup;
                verify_and_fold_ext4_stage_fibers(
                    CanopyHash::for_stage(sched.regime, stage_idx),
                    stage_idx,
                    cur_layer,
                    domain_cur,
                    arity,
                    st.num_queries,
                    stage_chals,
                    inv_two,
                    &inv_zetas,
                    Some(&terminal_coeffs),
                    transcript,
                )
            };
            // Every final-stage fiber was pinned to `final_coeffs` by the extracted
            // `verify_ext4_univariate_at_base_pin` inside the fold.
            if final_claims.is_none() {
                return false;
            }
        }
    }

    true
}

/// Map independent public query indices in stable order, `chunk` per work item, on the
/// persistent verification pool (inline without `std`).
fn map_query_indices<T, F>(count: usize, chunk: usize, f: F) -> Vec<T>
where
    T: Send + 'static,
    F: Fn(usize) -> T + Send + Sync + 'static,
{
    #[cfg(feature = "std")]
    {
        crate::pool::map_indices(count, chunk, f)
    }
    #[cfg(not(feature = "std"))]
    {
        let _ = chunk;
        (0..count).map(f).collect()
    }
}

/// One folded fiber: the shift point `z_u`, the folded value, and (final stage only) whether
/// the extracted terminal pin accepted `final_coeffs(z_u) == folded value`.
type FoldedFiber = (Goldilocks, GoldilocksExt4, bool);

/// Fold one opened fiber with the extracted duet fold and, in the final stage, pin it to the
/// terminal polynomial with the extracted Horner gate.
#[inline]
fn fold_and_pin_fiber(
    fiber: &[GoldilocksExt4],
    y0: Goldilocks,
    inv_y0: Goldilocks,
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    stage_chals: &[[GoldilocksExt4; 3]],
    terminal: Option<&[qsag_whir_verified::Ext4]>,
) -> FoldedFiber {
    let duet = fold_coset_group_to_last_duet(fiber, y0, inv_y0, inv_two, inv_zetas, stage_chals);
    let v_shift = duet.fold(inv_two);
    let z_u = pow2_iter_base(y0, stage_chals.len());
    let pinned = terminal.is_none_or(|coeffs| {
        qsag_whir_verified::verify_ext4_univariate_at_base_pin(
            coeffs,
            z_u.to_canonical_u64(),
            to_verified_ext4(v_shift),
        ) && duet.accepts(inv_two, to_verified_ext4(v_shift))
    });
    (z_u, v_shift, pinned)
}

fn accepted_fiber_claims(folded: Vec<FoldedFiber>) -> Option<Vec<(Goldilocks, GoldilocksExt4)>> {
    folded
        .into_iter()
        .map(|(z_u, v_shift, pinned)| pinned.then_some((z_u, v_shift)))
        .collect()
}

/// Authenticate and fold the Round-0 fibers. With `terminal` set (final stage) every folded
/// value must also equal the terminal polynomial at its shift point.
#[allow(clippy::too_many_arguments)]
fn verify_and_fold_stage0_fibers(
    hash: CanopyHash,
    comm_0: &CanopyCommitment,
    num_polys: usize,
    weights: &[[GoldilocksExt4; 2]],
    domain_0: usize,
    arity_0: usize,
    num_queries: usize,
    stage_chals: &[[GoldilocksExt4; 3]],
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    proof: &HemWhirOpeningProof,
    terminal: Option<&alloc::sync::Arc<Vec<qsag_whir_verified::Ext4>>>,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> Option<Vec<(Goldilocks, GoldilocksExt4)>> {
    let _phase = crate::profile::span("verify_and_fold_stage0_fibers");
    let num_groups_0 = domain_0 / arity_0;
    let q_indices = sample_stage_queries(transcript, 0, num_groups_0, num_queries);
    let per_query = num_polys * arity_0;
    if proof.round0_salts.len() != q_indices.len()
        || proof.round0_vals.len() != q_indices.len() * per_query
    {
        return None;
    }

    let log_d0 = domain_0.trailing_zeros() as usize;
    let omega_0 = Goldilocks::two_adic_generator(log_d0);
    // Fiber points are `x_k = y_0 * zeta^k` with `zeta = omega_0^{num_groups_0}`.
    let zeta_0 = omega_0.pow(num_groups_0 as u64);
    let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega_0, &q_indices);

    let q_len = q_indices.len();
    // Partition `round0_vals` into `<= 32 KiB` pages (aligned to 4-query batches) so every `Arc`
    // stays strictly inside glibc per-thread `tcache` (`< 128 KiB` `MMAP_THRESHOLD`, zero IPI TLB shootdowns).
    let batches_per_page = (32_768 / (4 * per_query * core::mem::size_of::<Goldilocks>())).max(1);
    let queries_per_page = batches_per_page * 4;
    let val_pages: alloc::sync::Arc<[alloc::sync::Arc<[Goldilocks]>]> = proof
        .round0_vals
        .chunks(queries_per_page * per_query)
        .map(alloc::sync::Arc::<[Goldilocks]>::from)
        .collect::<Vec<_>>()
        .into();
    let q_indices: alloc::sync::Arc<[usize]> = q_indices.into();
    let salts: alloc::sync::Arc<[[u8; 16]]> = proof.round0_salts.as_slice().into();
    let y0s: alloc::sync::Arc<[Goldilocks]> = y0s.into();
    let inv_y0s: alloc::sync::Arc<[Goldilocks]> = inv_y0s.into();
    let weights: alloc::sync::Arc<[[GoldilocksExt4; 2]]> = weights.into();
    let stage_chals: alloc::sync::Arc<[[GoldilocksExt4; 3]]> = stage_chals.into();
    let inv_zetas = *inv_zetas;
    let terminal = terminal.cloned();

    let batches = q_len.div_ceil(4);
    // Each pool item hashes four leaves with SIMD and folds their public values.
    let results = map_query_indices(batches, 2, move |batch| {
        let start = batch * 4;
        let end = (start + 4).min(q_len);
        let indices = &q_indices[start..end];
        let page = &val_pages[batch / batches_per_page];
        let page_off = (batch % batches_per_page) * 4 * per_query;
        let mut leaves = [(0usize, [0u8; 32]); 4];
        if indices.len() == 4
            && let Some(turbo) = hash.byte_turbo_mode()
        {
            let hashes = queried_round0_hash_x4_mode(
                turbo,
                indices,
                &salts[start..],
                num_polys,
                &page[page_off..],
                per_query,
            );
            for (slot, (&index, hash)) in leaves.iter_mut().zip(indices.iter().zip(hashes)) {
                *slot = (index, hash);
            }
        } else {
            for (lane, &g) in indices.iter().enumerate() {
                let i = start + lane;
                let off = page_off + lane * per_query;
                leaves[lane] = (
                    g,
                    round0_leaf_digest(
                        hash,
                        g as u32,
                        &salts[i],
                        num_polys,
                        &page[off..off + per_query],
                    ),
                );
            }
        }
        let mut folded = [(Goldilocks::ZERO, GoldilocksExt4::ZERO, false); 4];
        for (lane, (slot, i)) in folded.iter_mut().zip(start..end).enumerate() {
            let off = page_off + lane * per_query;
            let q_vals = &page[off..off + per_query];
            let y0 = y0s[i];
            if num_polys == 1 {
                let duet = fold_base_coset_group_to_last_duet(
                    q_vals,
                    y0,
                    inv_y0s[i],
                    inv_two,
                    &inv_zetas,
                    &stage_chals,
                );
                let v_shift = duet.fold(inv_two);
                let z_u = pow2_iter_base(y0, stage_chals.len());
                let pinned = terminal.as_ref().is_none_or(|coeffs| {
                    qsag_whir_verified::verify_ext4_univariate_at_base_pin(
                        coeffs,
                        z_u.to_canonical_u64(),
                        to_verified_ext4(v_shift),
                    ) && duet.accepts(inv_two, to_verified_ext4(v_shift))
                });
                *slot = (z_u, v_shift, pinned);
            } else {
                let mut ext_vals = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                for (w, poly_vals) in weights.iter().zip(q_vals.chunks_exact(arity_0)) {
                    let mut x = y0;
                    for (dst, &v) in ext_vals.iter_mut().zip(poly_vals) {
                        *dst += (w[0] + w[1].mul_base(x)).mul_base(v);
                        x *= zeta_0;
                    }
                }
                *slot = fold_and_pin_fiber(
                    &ext_vals[..arity_0],
                    y0,
                    inv_y0s[i],
                    inv_two,
                    &inv_zetas,
                    &stage_chals,
                    terminal.as_ref().map(|coeffs| coeffs.as_slice()),
                );
            }
        }
        (leaves, folded, end - start)
    });
    let mut sorted_leaves = Vec::with_capacity(q_len);
    let mut folded = Vec::with_capacity(q_len);
    for (leaves, values, len) in results {
        sorted_leaves.extend_from_slice(&leaves[..len]);
        folded.extend_from_slice(&values[..len]);
    }
    if !verify_canopy_multiproof_with(hash, comm_0, &sorted_leaves, &proof.round0_multiproof) {
        return None;
    }
    accepted_fiber_claims(folded)
}

/// Authenticate and fold the fibers of a committed `Ext4` stage oracle. With `terminal` set
/// (final stage) every folded value must also equal the terminal polynomial at its shift point.
#[allow(clippy::too_many_arguments)]
fn verify_and_fold_ext4_stage_fibers(
    hash: CanopyHash,
    stage_idx: usize,
    layer: &WhirStageProof,
    domain_cur: usize,
    arity: usize,
    num_queries: usize,
    stage_chals: &[[GoldilocksExt4; 3]],
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    terminal: Option<&alloc::sync::Arc<Vec<qsag_whir_verified::Ext4>>>,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> Option<Vec<(Goldilocks, GoldilocksExt4)>> {
    let _phase = crate::profile::span("verify_and_fold_ext4_stage_fibers");
    let num_groups_cur = domain_cur / arity;
    if layer.commitment.log_leaves > 28
        || (1usize << (layer.commitment.log_leaves as usize)) != num_groups_cur
    {
        return None;
    }
    let q_indices = sample_stage_queries(transcript, stage_idx, num_groups_cur, num_queries);
    if layer.opened_vals.len() != q_indices.len() * arity {
        return None;
    }

    let log_d = domain_cur.trailing_zeros() as usize;
    let omega = Goldilocks::two_adic_generator(log_d);
    let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega, &q_indices);
    let stage_u8 = stage_idx as u8;

    let q_len = q_indices.len();
    let batches_per_page = (32_768 / (4 * arity * core::mem::size_of::<GoldilocksExt4>())).max(1);
    let queries_per_page = batches_per_page * 4;
    let val_pages: alloc::sync::Arc<[alloc::sync::Arc<[GoldilocksExt4]>]> = layer
        .opened_vals
        .chunks(queries_per_page * arity)
        .map(alloc::sync::Arc::<[GoldilocksExt4]>::from)
        .collect::<Vec<_>>()
        .into();
    let q_indices: alloc::sync::Arc<[usize]> = q_indices.into();
    let y0s: alloc::sync::Arc<[Goldilocks]> = y0s.into();
    let inv_y0s: alloc::sync::Arc<[Goldilocks]> = inv_y0s.into();
    let stage_chals: alloc::sync::Arc<[[GoldilocksExt4; 3]]> = stage_chals.into();
    let inv_zetas = *inv_zetas;
    let terminal = terminal.cloned();

    let batches = q_len.div_ceil(4);
    // Each pool item hashes four leaves with SIMD and folds their public values.
    let results = map_query_indices(batches, 2, move |batch| {
        let start = batch * 4;
        let end = (start + 4).min(q_len);
        let indices = &q_indices[start..end];
        let page = &val_pages[batch / batches_per_page];
        let page_off = (batch % batches_per_page) * 4 * arity;
        let mut leaves = [(0usize, [0u8; 32]); 4];
        if indices.len() == 4
            && let Some(turbo) = hash.byte_turbo_mode()
        {
            let hashes =
                queried_ext4_hash_x4_mode(turbo, stage_u8, indices, &page[page_off..], arity);
            for (slot, (&index, hash)) in leaves.iter_mut().zip(indices.iter().zip(hashes)) {
                *slot = (index, hash);
            }
        } else {
            for (lane, &g) in indices.iter().enumerate() {
                let off = page_off + lane * arity;
                leaves[lane] = (
                    g,
                    ext4_leaf_digest(hash, stage_u8, g as u32, &page[off..off + arity]),
                );
            }
        }
        let mut folded = [(Goldilocks::ZERO, GoldilocksExt4::ZERO, false); 4];
        for (lane, (slot, i)) in folded.iter_mut().zip(start..end).enumerate() {
            let off = page_off + lane * arity;
            *slot = fold_and_pin_fiber(
                &page[off..off + arity],
                y0s[i],
                inv_y0s[i],
                inv_two,
                &inv_zetas,
                &stage_chals,
                terminal.as_ref().map(|coeffs| coeffs.as_slice()),
            );
        }
        (leaves, folded, end - start)
    });
    let mut sorted_leaves = Vec::with_capacity(q_len);
    let mut folded = Vec::with_capacity(q_len);
    for (leaves, values, len) in results {
        sorted_leaves.extend_from_slice(&leaves[..len]);
        folded.extend_from_slice(&values[..len]);
    }
    if !verify_canopy_multiproof_with(hash, &layer.commitment, &sorted_leaves, &layer.multiproof) {
        return None;
    }
    accepted_fiber_claims(folded)
}

// ============================================================================
// 6. Deterministic 4-Way SIMD Proof-of-Work (`POW_MIDSTATE`)
// ============================================================================

/// Deterministically find the minimum `nonce: u64` whose PoW word has at least
/// `transcript.pow_bits()` low zero bits. `cSHAKE256` transcripts scan `POW_MIDSTATE` in 8-way
/// SIMD (`cshake256_pow_u64_x8`); Poseidon2 transcripts scan [`poseidon2_pow_word`]. Returns `0`
/// without hashing when the regime has no PoW.
fn grind_pcs_pow(transcript: &FiatShamirTranscript<InstanceBound>) -> u64 {
    let _phase = crate::profile::span("grind_pcs_pow");
    let pow_bits = transcript.pow_bits();
    if pow_bits == 0 {
        return 0;
    }
    let mask = (1u64 << pow_bits) - 1;
    if let Some(chain) = transcript.poseidon2_chain() {
        return grind_min_nonce(|n| {
            (0..8u64).find_map(|lane| {
                let nonce = n.checked_add(lane)?;
                (poseidon2_pow_word(chain, nonce) & mask == 0).then_some(nonce)
            })
        });
    }
    let chal = transcript.transcript_digest();
    let turbo = transcript.uses_turboshake_pow();
    grind_min_nonce(|n| {
        let words = if turbo {
            turboshake256_pow_u64_x8(&TURBOSHAKE_POW_MIDSTATE, &chal, n)
        } else {
            cshake256_pow_u64_x8(&POW_MIDSTATE, &chal, n)
        };
        words
            .iter()
            .position(|&w| (w & mask) == 0)
            .map(|lane| n + lane as u64)
    })
}

/// Smallest nonce accepted by `scan8`, where `scan8(n)` reports the first hit in `n .. n + 8`.
/// Scans fixed windows across worker threads; the result does not depend on the thread count.
fn grind_min_nonce<F>(scan8: F) -> u64
where
    F: Fn(u64) -> Option<u64> + Sync,
{
    #[cfg(feature = "std")]
    {
        use core::sync::atomic::{AtomicU64, Ordering};
        let threads = crate::parallel_workers() as u64;
        const PER_THREAD: u64 = 4_096; // 512 `scan8` calls per thread
        let window: u64 = threads * PER_THREAD;

        let mut win_base = 0u64;
        loop {
            let best = AtomicU64::new(u64::MAX);
            let best_ref = &best;
            let scan_ref = &scan8;
            std::thread::scope(|scope| {
                for t in 0..threads {
                    let start = win_base + t * PER_THREAD;

                    crate::spawn_bounded(scope, move || {
                        for offset in (0..PER_THREAD).step_by(8) {
                            let n = start + offset;
                            if n >= best_ref.load(Ordering::Relaxed) {
                                break;
                            }
                            if let Some(hit) = scan_ref(n) {
                                best_ref.fetch_min(hit, Ordering::Relaxed);
                                return;
                            }
                        }
                    });
                }
            });
            let found = best.load(Ordering::Relaxed);
            if found != u64::MAX {
                return found;
            }
            win_base = match win_base.checked_add(window) {
                Some(next) => next,
                None => panic!("PoW nonce space exhausted"),
            };
        }
    }

    #[cfg(not(feature = "std"))]
    {
        let mut n = 0u64;
        loop {
            if let Some(hit) = scan8(n) {
                return hit;
            }
            n = match n.checked_add(8) {
                Some(next) => next,
                None => panic!("PoW nonce space exhausted"),
            };
        }
    }
}

/// Check a PoW nonce against the transcript state. A regime without PoW admits only nonce `0`.
#[inline]
fn verify_pcs_pow(transcript: &FiatShamirTranscript<InstanceBound>, nonce: u64) -> bool {
    let pow_bits = transcript.pow_bits();
    if pow_bits == 0 {
        return nonce == 0;
    }
    let word = match transcript.poseidon2_chain() {
        Some(chain) => poseidon2_pow_word(chain, nonce),
        None if transcript.uses_turboshake_pow() => turboshake256_pow_u64_single(
            &TURBOSHAKE_POW_MIDSTATE,
            &transcript.transcript_digest(),
            nonce,
        ),
        None => cshake256_pow_u64_single(&POW_MIDSTATE, &transcript.transcript_digest(), nonce),
    };
    qsag_whir_verified::verify_stage_pow_mask(word, pow_bits)
}

#[cfg(test)]
mod pcs_unit_tests {
    use super::*;

    /// The blocked transform against the one-variable-per-pass definition, on sizes below and
    /// above the cache block and both sides of the parallel threshold.
    #[test]
    fn blocked_mobius_matches_one_variable_per_pass() {
        for ell in [1usize, 2, 7, 13, 14, 15, 16, 18] {
            let mut x = 0x9E37_79B9u64 + ell as u64;
            let evals: Vec<Goldilocks> = (0..1usize << ell)
                .map(|_| {
                    x = x.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                    Goldilocks::from_u64_reduced(x ^ (x >> 31))
                })
                .collect();
            let mut expected = evals.clone();
            for bit in 0..ell {
                let stride = 1usize << bit;
                for base in (0..expected.len()).step_by(2 * stride) {
                    for i in 0..stride {
                        let lo = expected[base + i];
                        expected[base + stride + i] -= lo;
                    }
                }
            }
            assert_eq!(hypercube_to_monomial_coeffs(&evals), expected, "ell {ell}");
            let lift = |v: &[Goldilocks]| -> Vec<GoldilocksExt4> {
                v.iter()
                    .enumerate()
                    .map(|(i, &g)| {
                        GoldilocksExt4::from_limbs([
                            g,
                            g + Goldilocks::ONE,
                            Goldilocks::from_u64_reduced(i as u64),
                            g.square(),
                        ])
                    })
                    .collect()
            };
            let ext = lift(&evals);
            let mut expected_ext = ext.clone();
            for bit in 0..ell {
                let stride = 1usize << bit;
                for base in (0..expected_ext.len()).step_by(2 * stride) {
                    for i in 0..stride {
                        let lo = expected_ext[base + i];
                        expected_ext[base + stride + i] -= lo;
                    }
                }
            }
            assert_eq!(
                hypercube_to_monomial_coeffs_ext4(&ext),
                expected_ext,
                "ext ell {ell}"
            );
        }
    }

    #[test]
    fn extracted_affine_core_matches_tower_arithmetic() {
        let mut state = 1u64;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            Goldilocks::from_u64_reduced(state)
        };
        for _ in 0..1024 {
            let v0 = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let v1 = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let theta = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let alpha = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let beta = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let iy = next();
            let it = next();
            let yy = next();
            let even = (v0 + v1).mul_base(it);
            let odd = (v0 - v1).mul_base(iy);
            let expected = odd + (alpha + beta.mul_base(yy)) * (even + theta * odd);
            let last = FiberLastDuet {
                v0,
                v1,
                inv_two_x: iy,
                x_sq: yy,
                chal: [theta, alpha, beta],
            };
            assert_eq!(last.fold(it), expected);
            assert!(last.accepts(it, to_verified_ext4(expected)));
            assert!(!last.accepts(it, to_verified_ext4(expected + GoldilocksExt4::V)));
            assert!(qsag_whir_verified::verify_cwyz_duet_fold_step(
                to_verified_ext4(v0),
                to_verified_ext4(v1),
                iy.to_canonical_u64(),
                it.to_canonical_u64(),
                yy.to_canonical_u64(),
                to_verified_ext4(theta),
                to_verified_ext4(alpha),
                to_verified_ext4(beta),
                to_verified_ext4(expected),
            ));
            assert!(!qsag_whir_verified::verify_cwyz_duet_fold_step(
                to_verified_ext4(v0),
                to_verified_ext4(v1),
                iy.to_canonical_u64(),
                it.to_canonical_u64(),
                yy.to_canonical_u64(),
                to_verified_ext4(theta),
                to_verified_ext4(alpha),
                to_verified_ext4(beta),
                to_verified_ext4(expected + GoldilocksExt4::ONE),
            ));
            let w0 = v0;
            let w1 = v1;
            let w2 = theta;
            let w3 = alpha;
            let fourth_power = beta;
            let claim = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let phi = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let f = w0 + phi * w1;
            let g = w2 + phi * (claim - w0);
            let bridge_expected = g + alpha * (f + theta * g) + beta * (w3 + theta * fourth_power);
            assert!(qsag_whir_verified::verify_cwyz_bridge_claim_step(
                to_verified_ext4(w0),
                to_verified_ext4(w1),
                to_verified_ext4(w2),
                to_verified_ext4(w3),
                to_verified_ext4(fourth_power),
                to_verified_ext4(claim),
                to_verified_ext4(phi),
                to_verified_ext4(theta),
                to_verified_ext4(alpha),
                to_verified_ext4(beta),
                to_verified_ext4(bridge_expected),
            ));
            assert_eq!(
                eval_quadratic_wire(&[v0, v1], claim, phi),
                (v1 * phi + (claim - (v0 + v0) - v1)) * phi + v0
            );
            let poly = [v0, v1, theta, alpha, beta];
            let poly_v: Vec<_> = poly.iter().copied().map(to_verified_ext4).collect();
            let horner_expected = eval_univariate_ext4_at_base(&poly, iy);
            assert!(qsag_whir_verified::verify_ext4_univariate_at_base_pin(
                &poly_v,
                iy.to_canonical_u64(),
                to_verified_ext4(horner_expected),
            ));
            assert!(!qsag_whir_verified::verify_ext4_univariate_at_base_pin(
                &poly_v,
                iy.to_canonical_u64(),
                to_verified_ext4(horner_expected + GoldilocksExt4::V),
            ));
            let simple = odd + alpha * even;
            assert!(qsag_whir_verified::verify_affine_duet_fold_step(
                to_verified_ext4(v0),
                to_verified_ext4(v1),
                iy.to_canonical_u64(),
                it.to_canonical_u64(),
                to_verified_ext4(alpha),
                to_verified_ext4(simple)
            ));
            assert!(!qsag_whir_verified::verify_affine_duet_fold_step(
                to_verified_ext4(v0),
                to_verified_ext4(v1),
                iy.to_canonical_u64(),
                it.to_canonical_u64(),
                to_verified_ext4(alpha),
                to_verified_ext4(simple + GoldilocksExt4::ONE)
            ));
        }
    }

    #[test]
    fn exact_regime_ladder() {
        assert_eq!(
            WhirSecurityRegime::default(),
            WhirSecurityRegime::BciksJohnsonQrom128
        );
        // Retired capacity-proximity wire tags (`0`, `1`, `3`) MUST fail closed on decode.
        assert_eq!(WhirSecurityRegime::from_u8(0), None);
        assert_eq!(WhirSecurityRegime::from_u8(1), None);
        assert_eq!(WhirSecurityRegime::from_u8(3), None);

        for (tag, counts, bits, pow_bits, poseidon2, turboshake) in [
            (2, [129, 65, 44, 33], 144, 16, false, false),
            (4, [258, 130, 88, 66], 272, 16, false, false),
            (5, [202, 102, 70, 52], 216, 16, false, false),
            (6, [216, 109, 74, 56], 214, 0, false, false),
            (7, [202, 102, 70, 52], 216, 16, true, false),
            (8, [216, 109, 74, 56], 214, 0, true, false),
            (9, [258, 130, 88, 66], 272, 16, false, true),
            (10, [202, 102, 70, 52], 216, 16, false, true),
        ] {
            let regime = WhirSecurityRegime::from_u8(tag).unwrap();
            assert_eq!(regime as u8, tag);
            assert_eq!(regime.classical_fs_round_bits(), bits);
            assert_eq!(regime.qrom_grover_round_bits(), bits / 2);
            assert_eq!(regime.is_accepted_aggregate_profile(), tag != 2);
            assert_eq!(
                regime.meets_unconditional_grover_128_floor(),
                matches!(tag, 4 | 9)
            );
            assert_eq!(regime.is_bounded_query_profile(), matches!(tag, 5..=8 | 10));
            assert_eq!(regime.pow_bits(), pow_bits);
            assert_eq!(regime.uses_poseidon2_canopy(), poseidon2);
            assert_eq!(regime.uses_turboshake_canopy(), turboshake);
            assert_eq!(
                regime
                    .schedule(24)
                    .stages
                    .iter()
                    .map(|s| s.num_queries)
                    .collect::<Vec<_>>(),
                counts
            );
            let mut excessive = regime.schedule(24);
            excessive.stages[0].num_queries = NUM_PCS_QUERIES + 1;
            assert!(!excessive.validate(24));
            assert!(WhirSchedule::from_bytes_canonical(&excessive.to_bytes(), 24).is_none());
        }
        for tag in (0..=255u8).filter(|t| !matches!(t, 2 | 4..=10)) {
            assert_eq!(WhirSecurityRegime::from_u8(tag), None);
        }
        assert_eq!(
            WhirSecurityRegime::ALL.map(|r| r as u8),
            [2u8, 4, 5, 6, 7, 8, 9, 10]
        );
    }

    #[test]
    fn security_regimes_roundtrip_and_query_budgets() {
        for regime in WhirSecurityRegime::ALL {
            for nv in 2..=MAX_PCS_NUM_VARS {
                let schedule = regime.schedule(nv);
                assert!(schedule.validate_structural(nv));
                if !regime.is_accepted_aggregate_profile() {
                    assert!(!schedule.validate(nv));
                    assert!(WhirSchedule::from_bytes_canonical(&schedule.to_bytes(), nv).is_none());
                    continue;
                }
                assert!(schedule.validate(nv));
                let wire = schedule.to_bytes();
                assert_eq!(
                    WhirSchedule::from_bytes_canonical(&wire, nv),
                    Some((schedule.clone(), wire.len()))
                );
                for stage in &schedule.stages {
                    let log_b = stage.blowup.trailing_zeros() as usize;
                    // Johnson agreement `sqrt(rho)` gives `log_b / 2` bits per query.
                    assert!(
                        stage.num_queries * log_b > 2 * regime.pure_query_target_bits() as usize
                    );
                }
                for retired_or_unknown_tag in [0u8, 1, 2, 3, 11] {
                    let mut mutated = wire.clone();
                    mutated[0] = retired_or_unknown_tag;
                    assert!(WhirSchedule::from_bytes_canonical(&mutated, nv).is_none());
                }
                assert!(WhirSchedule::from_bytes_canonical(&wire[..wire.len() - 1], nv).is_none());
                let mut custom = schedule.clone();
                custom.stages[0].num_queries += 1;
                assert!(!custom.validate(nv));
                assert!(WhirSchedule::from_bytes_canonical(&custom.to_bytes(), nv).is_none());
                let mut bad = schedule;
                bad.stages[0].num_queries = 1;
                assert!(!bad.validate(nv));
            }
        }
    }

    #[test]
    fn explicit_classical_pcs_works_without_authorizing_aggregates() {
        let nv = 3;
        let schedule = WhirSecurityRegime::BciksJohnsonClassical128.schedule(nv);
        assert!(schedule.validate_structural(nv));
        assert!(!schedule.validate(nv));
        let values: Vec<_> = (0..1u64 << nv).map(Goldilocks::from_u64_reduced).collect();
        let point = vec![GoldilocksExt4::from_u64(3); nv];
        let value = crate::field::mle_eval_base_at_ext4(&values, &point);
        let transcript = || {
            FiatShamirTranscript::new()
                .bind_relation(b"EXPLICIT_CLASSICAL_PCS", b"", &schedule)
                .bind_instance(&[b"test"])
        };
        let (comm, state) =
            whir_commit_batch_owned_with_schedule(vec![values], &[8; 32], &schedule);
        let proof = whir_open(&state, &point, value, &mut transcript());
        assert!(whir_verify_with_schedule(
            &comm,
            nv,
            &point,
            value,
            &proof,
            &mut transcript(),
            &schedule
        ));
        assert!(!whir_verify(
            &comm,
            nv,
            &point,
            value,
            &proof,
            &mut transcript()
        ));
    }

    #[test]
    fn explicit_security_regimes_end_to_end() {
        let nv = 12;
        let values: Vec<_> = (0..1u64 << nv).map(Goldilocks::from_u64_reduced).collect();
        let point = vec![GoldilocksExt4::from_base(Goldilocks::TWO); nv];
        let value = crate::field::mle_eval_base_at_ext4(&values, &point);

        let classical_sched = WhirSecurityRegime::BciksJohnsonClassical128.schedule(nv);
        assert!(!classical_sched.validate(nv));

        let regime = WhirSecurityRegime::BciksJohnsonQrom128;
        let schedule = regime.schedule(nv);
        let transcript = || {
            FiatShamirTranscript::new()
                .bind_relation(b"REGIME_TEST", b"", &schedule)
                .bind_instance(&[b"instance"])
        };
        let start = std::time::Instant::now();
        let (comm, state) =
            whir_commit_batch_owned_with_schedule(vec![values], &[7; 32], &schedule);
        let proof = whir_open(&state, &point, value, &mut transcript());
        let elapsed = start.elapsed();
        let start = std::time::Instant::now();
        assert!(whir_verify_with_schedule(
            &comm,
            nv,
            &point,
            value,
            &proof,
            &mut transcript(),
            &schedule
        ));
        let mut proof_bytes = Vec::new();
        proof.push_bytes(&mut proof_bytes);
        std::eprintln!(
            "{regime:?}: nv={nv}, bytes={}, prove={elapsed:?}, verify={:?}",
            proof_bytes.len(),
            start.elapsed()
        );
        let mut wrong = schedule.clone();
        wrong.regime = WhirSecurityRegime::BciksJohnsonClassical128;
        assert!(!whir_verify_with_schedule(
            &comm,
            nv,
            &point,
            value,
            &proof,
            &mut transcript(),
            &wrong
        ));
        let mut forged = proof;
        forged.final_coeffs[0] += GoldilocksExt4::ONE;
        assert!(!whir_verify_with_schedule(
            &comm,
            nv,
            &point,
            value,
            &forged,
            &mut transcript(),
            &schedule
        ));
    }

    #[test]
    fn whir_schedules_cover_all_supported_num_vars() {
        for nv in 2..=MAX_PCS_NUM_VARS {
            let sched = whir_stage_schedule(nv);
            assert!((1..=EARLY_STOP_VARS).contains(&sched.early_stop_vars));
            assert!((1..=MAX_WHIR_STAGES).contains(&sched.stages.len()));
            let step_sum: usize = sched.stages.iter().map(|s| s.step_vars).sum();
            assert_eq!(sched.early_stop_vars + step_sum, nv, "nv={nv}");
            let mut rem = nv;
            for st in &sched.stages {
                assert!(st.blowup.is_power_of_two() && st.blowup >= 4);
                assert!((1..=MAX_FOLD_STEP_VARS).contains(&st.step_vars));
                assert!((1..=NUM_PCS_QUERIES).contains(&st.num_queries));
                let domain = (1usize << rem) * st.blowup;
                let arity = 1usize << st.step_vars;
                assert!(domain / arity >= 8, "nv={nv} domain={domain} arity={arity}");
                rem -= st.step_vars;
            }
            assert_eq!(rem, sched.early_stop_vars);
        }
    }

    #[test]
    fn canopy_x4_tree_and_parallel_eq_match_scalar_reference() {
        let r: Vec<GoldilocksExt4> = (0..15u64)
            .map(|k| {
                GoldilocksExt4::from_limbs([
                    Goldilocks::from_u64_reduced(k * 17 + 3),
                    Goldilocks::from_u64_reduced(k * 31 + 5),
                    Goldilocks::from_u64_reduced(k * 47 + 7),
                    Goldilocks::from_u64_reduced(k * 61 + 11),
                ])
            })
            .collect();
        assert_eq!(build_eq_table_ext4_fast(&r), build_eq_table_ext4(&r));

        let n = 512usize;
        let leaf_scalar = |i: usize| hash_merkle_internal(i as u32, &[0x11; 32], &[0x22; 32]);
        let t_x4 = MerkleCanopyTree::build_from_fn_x4(n, |bl| {
            hash_merkle_internal_x4(bl as u32, [&[0x11; 32]; 4], [&[0x22; 32]; 4])
        });
        let t_x8 = MerkleCanopyTree::build_from_fn_x8(n, |bl| {
            hash_merkle_internal_x8(bl as u32, [&[0x11; 32]; 8], [&[0x22; 32]; 8])
        });
        let mut ref_nodes = vec![[0u8; 32]; 2 * n];
        for i in 0..n {
            ref_nodes[n + i] = leaf_scalar(i);
        }
        for idx in (1..n).rev() {
            ref_nodes[idx] =
                hash_merkle_internal(idx as u32, &ref_nodes[2 * idx], &ref_nodes[2 * idx + 1]);
        }
        let ref_root = hash_tree_root(n.trailing_zeros() as u8, &ref_nodes[1]);
        assert_eq!(t_x4.root, ref_root);
        assert_eq!(t_x8.root, ref_root);
        assert_eq!(t_x8.nodes, t_x4.nodes);

        let q = [0usize, 1, 7, 64, 65, 255, 510, 511];
        let mp = t_x4.open_multi_with_leaf_fn(&q, leaf_scalar);
        let leaves: Vec<(usize, [u8; 32])> = q.iter().map(|&i| (i, leaf_scalar(i))).collect();
        assert!(verify_canopy_multiproof(&t_x4.commitment(), &leaves, &mp));
    }

    #[test]
    fn frontier_batches_reject_noncanonical_and_tampered_proofs() {
        let leaf = |i: usize| cshake256_32_for_test(i);
        let tree = MerkleCanopyTree::build_from_fn(32, leaf);
        // Dense, sparse, sibling-coalescing, and non-multiple-of-four frontiers.
        for stride in 1..=9 {
            for offset in 0..stride {
                let indices: Vec<_> = (offset..32).step_by(stride).collect();
                let leaves: Vec<_> = indices.iter().map(|&i| (i, leaf(i))).collect();
                let proof = tree.open_multi_with_leaf_fn(&indices, leaf);
                assert!(verify_canopy_multiproof(
                    &tree.commitment(),
                    &leaves,
                    &proof
                ));
                let mut extra = proof.clone();
                extra.auth_siblings.push([0; 32]);
                assert!(!verify_canopy_multiproof(
                    &tree.commitment(),
                    &leaves,
                    &extra
                ));
                if !proof.auth_siblings.is_empty() {
                    let mut short = proof.clone();
                    short.auth_siblings.pop();
                    assert!(!verify_canopy_multiproof(
                        &tree.commitment(),
                        &leaves,
                        &short
                    ));
                    let mut bad = proof.clone();
                    bad.auth_siblings[0][0] ^= 1;
                    assert!(!verify_canopy_multiproof(&tree.commitment(), &leaves, &bad));
                }
                let mut bad = leaves.clone();
                bad[0].1[0] ^= 1;
                assert!(!verify_canopy_multiproof(&tree.commitment(), &bad, &proof));
                let mut duplicate = leaves.clone();
                duplicate.insert(0, leaves[0]);
                assert!(!verify_canopy_multiproof(
                    &tree.commitment(),
                    &duplicate,
                    &proof
                ));
            }
        }
    }

    fn cshake256_32_for_test(i: usize) -> [u8; 32] {
        crate::sponge::cshake256_32(b"frontier-test", &(i as u64).to_le_bytes())
    }

    #[test]
    fn whir_schedule_validate_rejects_32bit_domain_overflow() {
        // Reproducer from Focus-03 #2: 2^24 * 256 = 2^32 overflows 32-bit/wasm32 `usize`.
        let bad_sched = WhirSchedule {
            regime: WhirSecurityRegime::BciksJohnsonQrom128,
            early_stop_vars: 8,
            stages: vec![
                WhirStageSpec {
                    blowup: 256,
                    step_vars: 6,
                    num_queries: 66,
                },
                WhirStageSpec {
                    blowup: 4,
                    step_vars: 6,
                    num_queries: 258,
                },
                WhirStageSpec {
                    blowup: 4,
                    step_vars: 3,
                    num_queries: 258,
                },
                WhirStageSpec {
                    blowup: 4,
                    step_vars: 1,
                    num_queries: 258,
                },
            ],
        };
        assert!(!bad_sched.validate(24));
    }

    #[test]
    fn batch_coset_points_and_inverses_match_scalar_pow() {
        let omega = Goldilocks::two_adic_generator(22);
        let inv_omega = omega.inv();
        let inv_shift = Goldilocks::NON_RESIDUE.inv();
        let queries = [
            0usize,
            1,
            7,
            15,
            16,
            255,
            256,
            4095,
            65_535,
            (1 << 20) - 1,
            (1 << 22) - 3,
        ];
        let (y0s, inv_y0s) = batch_coset_points_and_inverses(omega, &queries);
        for (i, &g) in queries.iter().enumerate() {
            assert_eq!(y0s[i], Goldilocks::NON_RESIDUE * omega.pow(g as u64));
            assert_eq!(inv_y0s[i], inv_shift * inv_omega.pow(g as u64));
        }
    }

    fn regime_test_poly(nv: usize, tag: u64) -> Vec<Goldilocks> {
        (0..1u64 << nv)
            .map(|i| {
                Goldilocks::from_u64_reduced(
                    (i + 1)
                        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                        .wrapping_add(tag.wrapping_mul(0xD1B5_4A32_D192_ED03)),
                )
            })
            .collect()
    }

    fn regime_test_point(nv: usize, tag: u64) -> Vec<GoldilocksExt4> {
        (0..nv as u64)
            .map(|k| {
                GoldilocksExt4::from_limbs([
                    Goldilocks::from_u64_reduced((k + 1) * 31_337 + tag),
                    Goldilocks::from_u64_reduced((k + 5) * 4_242 + tag),
                    Goldilocks::from_u64_reduced((k + 9) * 1_717 + tag),
                    Goldilocks::from_u64_reduced((k + 13) * 9_001 + tag),
                ])
            })
            .collect()
    }

    fn regime_transcript(
        schedule: &WhirSchedule,
        instance: &[u8],
    ) -> FiatShamirTranscript<InstanceBound> {
        FiatShamirTranscript::new()
            .bind_relation(b"REGIME_TEST", b"", schedule)
            .bind_instance(&[instance])
    }

    #[test]
    #[cfg(feature = "vulkan")]
    fn gpu_round0_can_be_opened_after_session_release() {
        if std::env::var("QSAG_ACCEL").ok().as_deref() != Some("vulkan") {
            return;
        }
        let nv = 12;
        let schedule = WhirSecurityRegime::BciksJohnsonQrom128.schedule(nv);
        let poly = regime_test_poly(nv, 41);
        let point = regime_test_point(nv, 51);
        let value = crate::field::mle_eval_base_at_ext4(&poly, &point);
        let (commitment, mut state) = whir_commit_with_schedule(&poly, &[7; 32], &schedule);
        assert!(state.gpu_session.is_some());
        assert!(state.codewords_0.is_empty());
        drop(state.gpu_session.take());
        let mut prover = regime_transcript(&schedule, b"cpu-after-gpu");
        let proof = whir_open(&state, &point, value, &mut prover);
        let mut verifier = regime_transcript(&schedule, b"cpu-after-gpu");
        assert!(whir_verify_with_schedule(
            &commitment,
            nv,
            &point,
            value,
            &proof,
            &mut verifier,
            &schedule
        ));
    }

    /// Commit, batch-open and verify three polynomials at `nv` under `regime`.
    #[allow(clippy::type_complexity)]
    fn regime_batch_proof(
        regime: WhirSecurityRegime,
        nv: usize,
    ) -> (
        WhirSchedule,
        CanopyCommitment,
        Vec<Vec<GoldilocksExt4>>,
        Vec<GoldilocksExt4>,
        HemWhirBatchOpeningProof,
    ) {
        let schedule = regime.schedule(nv);
        let polys: Vec<_> = (0..3).map(|t| regime_test_poly(nv, 40 + t)).collect();
        let points: Vec<_> = (0..3).map(|t| regime_test_point(nv, 50 + t)).collect();
        let evals: Vec<_> = polys
            .iter()
            .zip(&points)
            .map(|(w, p)| crate::field::mle_eval_base_at_ext4(w, p))
            .collect();
        let refs: Vec<&[GoldilocksExt4]> = points.iter().map(Vec::as_slice).collect();
        let (comm, state) = whir_commit_batch_owned_with_schedule(polys, &[3; 32], &schedule);
        let proof = whir_open_batch(
            &state,
            &refs,
            &evals,
            &mut regime_transcript(&schedule, b"inst"),
        );
        (schedule, comm, points, evals, proof)
    }

    fn regime_batch_accepts(
        schedule: &WhirSchedule,
        comm: &CanopyCommitment,
        points: &[Vec<GoldilocksExt4>],
        evals: &[GoldilocksExt4],
        proof: &HemWhirBatchOpeningProof,
        instance: &[u8],
    ) -> bool {
        let refs: Vec<&[GoldilocksExt4]> = points.iter().map(Vec::as_slice).collect();
        whir_verify_batch_with_schedule(
            comm,
            points[0].len(),
            &refs,
            evals,
            proof,
            &mut regime_transcript(schedule, instance),
            schedule,
        )
    }

    #[test]
    fn cdhz25_and_poseidon2_regimes_accept_honest_and_reject_tampered_openings() {
        // `nv = 16` has three stages: a salted Round-0 tree and two `Ext4` stage trees.
        let nv = 16;
        for regime in [
            WhirSecurityRegime::Cdhz25JohnsonQrom128,
            WhirSecurityRegime::Cdhz25ZeroPowQrom128,
            WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
            WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
            WhirSecurityRegime::TurboShakeBciksJohnsonQrom128,
            WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128,
        ] {
            let (schedule, comm, points, evals, proof) = regime_batch_proof(regime, nv);
            let accepts = |p: &HemWhirBatchOpeningProof| {
                regime_batch_accepts(&schedule, &comm, &points, &evals, p, b"inst")
            };
            assert!(accepts(&proof), "{regime:?}");
            assert_eq!(proof.opening.folded_layers.len(), 2);

            let mut wire = Vec::new();
            proof.push_bytes(&mut wire);
            let (decoded, used) = HemWhirBatchOpeningProof::from_bytes_canonical(&wire).unwrap();
            assert_eq!(used, wire.len());
            assert_eq!(decoded, proof);

            // Mutated Round-0 leaf value and leaf salt.
            let mut bad = proof.clone();
            bad.opening.round0_vals[5] += Goldilocks::ONE;
            assert!(!accepts(&bad), "{regime:?} leaf value");
            let mut bad = proof.clone();
            bad.opening.round0_salts[0][15] ^= 1;
            assert!(!accepts(&bad), "{regime:?} leaf salt");
            // Mutated Round-0 sibling (low byte keeps a Poseidon2 limb canonical).
            let mut bad = proof.clone();
            bad.opening.round0_multiproof.auth_siblings[0][0] ^= 1;
            assert!(!accepts(&bad), "{regime:?} round0 sibling");
            // Mutated `Ext4` stage leaf, stage sibling and stage root.
            for layer in 0..2 {
                let mut bad = proof.clone();
                bad.opening.folded_layers[layer].opened_vals[1] += GoldilocksExt4::ONE;
                assert!(!accepts(&bad), "{regime:?} stage {layer} leaf");
                let mut bad = proof.clone();
                bad.opening.folded_layers[layer].multiproof.auth_siblings[0][8] ^= 1;
                assert!(!accepts(&bad), "{regime:?} stage {layer} sibling");
                let mut bad = proof.clone();
                bad.opening.folded_layers[layer].commitment.root[0] ^= 1;
                assert!(!accepts(&bad), "{regime:?} stage {layer} root");
            }
            // Wrong commitment and wrong claimed evaluation.
            let mut bad_comm = comm;
            bad_comm.root[0] ^= 1;
            assert!(!regime_batch_accepts(
                &schedule, &bad_comm, &points, &evals, &proof, b"inst"
            ));
            let mut bad_evals = evals.clone();
            bad_evals[1] += GoldilocksExt4::ONE;
            assert!(!regime_batch_accepts(
                &schedule, &comm, &points, &bad_evals, &proof, b"inst"
            ));
            // A different bound instance changes every Fiat–Shamir challenge.
            assert!(!regime_batch_accepts(
                &schedule, &comm, &points, &evals, &proof, b"other"
            ));
            // Sumcheck, OOD, terminal polynomial.
            let mut bad = proof.clone();
            bad.opening.fold_sumcheck_polys[2][1] += GoldilocksExt4::ONE;
            assert!(!accepts(&bad), "{regime:?} fold sumcheck");
            let mut bad = proof.clone();
            bad.opening.stage0_ood_evals[1] += GoldilocksExt4::ONE;
            assert!(!accepts(&bad), "{regime:?} ood");
            let mut bad = proof.clone();
            bad.opening.final_coeffs[0] += GoldilocksExt4::ONE;
            assert!(!accepts(&bad), "{regime:?} final coeffs");
            // PoW nonces: a zero-PoW regime admits only nonce 0; a 16-bit regime rejects a
            // nonce whose PoW word misses the mask.
            let mut bad = proof.clone();
            bad.opening.fold_pow_nonces[0] ^= 1;
            let mut bad_stage = proof.clone();
            bad_stage.opening.pow_nonce ^= 1;
            let mut bad_batch = proof.clone();
            bad_batch.batch_pow_nonce ^= 1;
            if regime.pow_bits() == 0 {
                assert_eq!(proof.opening.pow_nonce, 0);
                assert_eq!(proof.batch_pow_nonce, 0);
                assert!(proof.opening.fold_pow_nonces.iter().all(|&n| n == 0));
                assert!(proof.opening.folded_layers.iter().all(|l| l.pow_nonce == 0));
            }
            assert!(!accepts(&bad), "{regime:?} fold pow");
            assert!(!accepts(&bad_stage), "{regime:?} stage pow");
            assert!(!accepts(&bad_batch), "{regime:?} batch pow");

            // Every other regime, including the one sharing this query table, rejects the proof.
            for other in WhirSecurityRegime::ALL {
                if other == regime || !other.is_accepted_aggregate_profile() {
                    continue;
                }
                let other_schedule = other.schedule(nv);
                assert!(
                    !regime_batch_accepts(&other_schedule, &comm, &points, &evals, &proof, b"inst"),
                    "{regime:?} proof accepted under {other:?}"
                );
            }
        }
    }

    #[test]
    fn poseidon2_openings_reject_noncanonical_digests() {
        let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let (schedule, comm, points, evals, proof) = regime_batch_proof(regime, 12);
        assert!(regime_batch_accepts(
            &schedule, &comm, &points, &evals, &proof, b"inst"
        ));
        // `5 + p` is a second eight-byte encoding of the limb `5`; digests are compared and
        // hashed only in canonical form.
        let mut canonical = [0u8; 32];
        canonical[..8].copy_from_slice(&5u64.to_le_bytes());
        let mut lifted = canonical;
        lifted[..8].copy_from_slice(&(5 + crate::field::GOLDILOCKS_PRIME).to_le_bytes());
        let key = poseidon2_canopy_key(0, comm.log_leaves);
        assert!(poseidon2_canopy_node(key, 1, &canonical, &canonical).is_some());
        assert!(poseidon2_canopy_node(key, 1, &lifted, &canonical).is_none());
        assert!(poseidon2_canopy_node(key, 1, &canonical, &lifted).is_none());
        assert!(poseidon2_canopy_commitment_root(0, comm.log_leaves, &canonical).is_some());
        assert!(poseidon2_canopy_commitment_root(0, comm.log_leaves, &lifted).is_none());
        let leaves = [(0usize, lifted)];
        let one_leaf = CanopyCommitment {
            root: comm.root,
            log_leaves: 1,
        };
        assert!(!verify_canopy_multiproof_with(
            CanopyHash::Poseidon2 { stage_idx: 0 },
            &one_leaf,
            &leaves,
            &CanopyMultiProof {
                auth_siblings: vec![canonical],
            }
        ));
        let mut bad = proof.clone();
        bad.opening.round0_multiproof.auth_siblings[0] = [0xFF; 32];
        assert!(!regime_batch_accepts(
            &schedule, &comm, &points, &evals, &bad, b"inst"
        ));
    }

    #[test]
    fn poseidon2_canopy_multiproofs_bind_position_depth_and_stage() {
        let stage = 2u8;
        let leaf = |i: usize| {
            poseidon2_ext4_leaf(
                stage,
                i as u32,
                &[
                    GoldilocksExt4::from_base(Goldilocks::from_u64_reduced(i as u64 + 1)),
                    GoldilocksExt4::from_base(Goldilocks::from_u64_reduced(7 * i as u64 + 3)),
                ],
            )
        };
        let tree = MerkleCanopyTree::build_poseidon2(32, stage, leaf);
        let comm = tree.commitment();
        let hash = CanopyHash::Poseidon2 { stage_idx: stage };
        assert!(crate::sponge::bytes32_to_limbs4_le_canonical(&comm.root).is_some());
        for stride in 1..=9 {
            for offset in 0..stride {
                let indices: Vec<_> = (offset..32).step_by(stride).collect();
                let leaves: Vec<_> = indices.iter().map(|&i| (i, leaf(i))).collect();
                let proof = tree.open_multi_with_leaf_fn(&indices, leaf);
                assert!(verify_canopy_multiproof_with(hash, &comm, &leaves, &proof));
                // Other backend, other stage, other depth.
                assert!(!verify_canopy_multiproof(&comm, &leaves, &proof));
                assert!(!verify_canopy_multiproof_with(
                    CanopyHash::Poseidon2 { stage_idx: 1 },
                    &comm,
                    &leaves,
                    &proof
                ));
                let mut deeper = comm;
                deeper.log_leaves += 1;
                assert!(!verify_canopy_multiproof_with(
                    hash, &deeper, &leaves, &proof
                ));
                let mut shallower = comm;
                shallower.log_leaves -= 1;
                assert!(!verify_canopy_multiproof_with(
                    hash, &shallower, &leaves, &proof
                ));

                let mut extra = proof.clone();
                extra.auth_siblings.push([0; 32]);
                assert!(!verify_canopy_multiproof_with(hash, &comm, &leaves, &extra));
                if !proof.auth_siblings.is_empty() {
                    let mut short = proof.clone();
                    short.auth_siblings.pop();
                    assert!(!verify_canopy_multiproof_with(hash, &comm, &leaves, &short));
                    let mut bad = proof.clone();
                    bad.auth_siblings[0][0] ^= 1;
                    assert!(!verify_canopy_multiproof_with(hash, &comm, &leaves, &bad));
                }
                let mut bad = leaves.clone();
                bad[0].1[0] ^= 1;
                assert!(!verify_canopy_multiproof_with(hash, &comm, &bad, &proof));
                // A leaf digest moved to a neighbouring position.
                if indices[0] > 0 {
                    let mut moved = leaves.clone();
                    moved[0].0 -= 1;
                    assert!(!verify_canopy_multiproof_with(hash, &comm, &moved, &proof));
                }
                let mut duplicate = leaves.clone();
                duplicate.insert(0, leaves[0]);
                assert!(!verify_canopy_multiproof_with(
                    hash, &comm, &duplicate, &proof
                ));
            }
        }
        // Leaf digests bind their own index, arity, stage and (Round 0) salt and batch width.
        let vals = [
            Goldilocks::ONE,
            Goldilocks::TWO,
            Goldilocks::ONE,
            Goldilocks::TWO,
        ];
        let base = poseidon2_round0_leaf(3, &[1; 16], 1, &vals);
        assert_ne!(base, poseidon2_round0_leaf(4, &[1; 16], 1, &vals));
        assert_ne!(base, poseidon2_round0_leaf(3, &[2; 16], 1, &vals));
        assert_ne!(base, poseidon2_round0_leaf(3, &[1; 16], 2, &vals));
        assert_ne!(base, poseidon2_round0_leaf(3, &[1; 16], 1, &vals[..2]));
        let mut last_salt_byte = [1u8; 16];
        last_salt_byte[15] = 2;
        assert_ne!(base, poseidon2_round0_leaf(3, &last_salt_byte, 1, &vals));
        let e = [GoldilocksExt4::ONE, GoldilocksExt4::ZERO];
        assert_ne!(poseidon2_ext4_leaf(1, 0, &e), poseidon2_ext4_leaf(2, 0, &e));
        assert_ne!(poseidon2_ext4_leaf(1, 0, &e), poseidon2_ext4_leaf(1, 1, &e));
    }

    #[test]
    fn poseidon2_pow_grind_returns_the_minimum_nonce() {
        let schedule = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128.schedule(12);
        let transcript = regime_transcript(&schedule, b"pow");
        let chain = transcript.poseidon2_chain().unwrap();
        let nonce = grind_pcs_pow(&transcript);
        assert!(verify_pcs_pow(&transcript, nonce));
        let mask = (1u64 << transcript.pow_bits()) - 1;
        assert_eq!(transcript.pow_bits(), 16);
        assert!((0..nonce).all(|n| poseidon2_pow_word(chain, n) & mask != 0));
        assert!((0..nonce).all(|n| !verify_pcs_pow(&transcript, n)));
    }

    #[cfg(feature = "vulkan")]
    #[test]
    fn gpu_turboshake_whir_single_and_batch_match_cpu_bit_for_bit() {
        if crate::acceleration::vulkan_execution_counts().is_none() {
            return;
        }
        let cpu_state = |polys: Vec<Vec<Goldilocks>>,
                         salt_seed: &[u8; 32],
                         schedule: &WhirSchedule|
         -> (CanopyCommitment, HemWhirProverState) {
            let st0 = schedule.stages[0];
            let group_arity_0 = 1usize << st0.step_vars;
            let (monomial_coeffs_0, codewords_0, tree_0) = build_cpu_round0(
                &polys,
                salt_seed,
                schedule.regime,
                st0.blowup,
                group_arity_0,
                true,
            );
            let comm = tree_0.commitment();
            (
                comm,
                HemWhirProverState {
                    num_vars: polys[0].len().trailing_zeros() as usize,
                    schedule: schedule.clone(),
                    group_arity_0,
                    hypercube_evals: polys,
                    codewords_0,
                    monomial_coeffs_0,
                    secret: true,
                    salt_seed: *salt_seed,
                    tree_0,
                    round0_tree_on_cpu: true,
                    gpu_session: None,
                },
            )
        };
        let nv = 14usize;
        for regime in [
            WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128,
            WhirSecurityRegime::TurboShakeBciksJohnsonQrom128,
        ] {
            let schedule = regime.schedule(nv);
            let p0 = regime_test_poly(nv, 101);
            let p1 = regime_test_poly(nv, 202);
            let pt0 = regime_test_point(nv, 303);
            let pt1 = regime_test_point(nv, 404);
            let val0 = crate::field::mle_eval_base_at_ext4(&p0, &pt0);
            let val1 = crate::field::mle_eval_base_at_ext4(&p1, &pt1);

            // Single polynomial GPU commitment + opening vs CPU reference (`0` GPU fallbacks!).
            let before = crate::acceleration::vulkan_execution_counts().unwrap();
            let (comm_gpu, state_gpu) =
                whir_commit_owned_with_schedule(p0.clone(), &[0x79; 32], &schedule);
            assert!(
                state_gpu.gpu_session.is_some(),
                "TurboSHAKE single commit fell back to CPU"
            );
            let mut tr_gpu = regime_transcript(&schedule, b"turbo-gpu-single");
            let proof_gpu = whir_open(&state_gpu, &pt0, val0, &mut tr_gpu);
            drop(state_gpu);
            let after = crate::acceleration::vulkan_execution_counts().unwrap();
            assert_eq!(after.2, before.2, "unexpected GPU fallback on {regime:?}");

            let (comm_cpu, state_cpu) = cpu_state(alloc::vec![p0.clone()], &[0x79; 32], &schedule);
            assert_eq!(comm_gpu, comm_cpu);
            let mut tr_cpu = regime_transcript(&schedule, b"turbo-gpu-single");
            let proof_cpu = whir_open(&state_cpu, &pt0, val0, &mut tr_cpu);
            drop(state_cpu);
            assert_eq!(proof_gpu, proof_cpu);
            assert_eq!(tr_gpu.transcript_digest(), tr_cpu.transcript_digest());
            let mut tr_ver = regime_transcript(&schedule, b"turbo-gpu-single");
            assert!(whir_verify_with_schedule(
                &comm_gpu,
                nv,
                &pt0,
                val0,
                &proof_gpu,
                &mut tr_ver,
                &schedule,
            ));

            // Multi-polynomial batch GPU commitment + opening vs CPU reference (`0` GPU fallbacks!).
            let before_b = crate::acceleration::vulkan_execution_counts().unwrap();
            let (bcomm_gpu, bstate_gpu) = whir_commit_batch_owned_with_schedule(
                alloc::vec![p0.clone(), p1.clone()],
                &[0x5A; 32],
                &schedule,
            );
            assert!(
                bstate_gpu.gpu_session.is_some(),
                "TurboSHAKE batch commit fell back to CPU"
            );
            let mut btr_gpu = regime_transcript(&schedule, b"turbo-gpu-batch");
            let bproof_gpu =
                whir_open_batch(&bstate_gpu, &[&pt0, &pt1], &[val0, val1], &mut btr_gpu);
            drop(bstate_gpu);
            let after_b = crate::acceleration::vulkan_execution_counts().unwrap();
            assert_eq!(
                after_b.2, before_b.2,
                "unexpected GPU batch fallback on {regime:?}"
            );

            let (bcomm_cpu, bstate_cpu) = cpu_state(alloc::vec![p0, p1], &[0x5A; 32], &schedule);
            assert_eq!(bcomm_gpu, bcomm_cpu);
            let mut btr_cpu = regime_transcript(&schedule, b"turbo-gpu-batch");
            let bproof_cpu =
                whir_open_batch(&bstate_cpu, &[&pt0, &pt1], &[val0, val1], &mut btr_cpu);
            drop(bstate_cpu);
            assert_eq!(bproof_gpu, bproof_cpu);
            let mut btr_ver = regime_transcript(&schedule, b"turbo-gpu-batch");
            assert!(whir_verify_batch_with_schedule(
                &bcomm_gpu,
                nv,
                &[&pt0, &pt1],
                &[val0, val1],
                &bproof_gpu,
                &mut btr_ver,
                &schedule,
            ));
        }
    }

    #[cfg(feature = "vulkan")]
    #[test]
    #[ignore = "large RX 6750 XT GPU gate; QSAG_ACCEL=vulkan"]
    fn gpu_nv25_nv26_native_openings() {
        use std::time::Instant;
        assert!(crate::acceleration::vulkan_execution_counts().is_some());
        for nv in [25, 26] {
            let schedule = whir_stage_schedule(nv);
            let evals = regime_test_poly(nv, 77);
            let point = regime_test_point(nv, 78);
            let value = crate::field::mle_eval_base_at_ext4(&evals, &point);
            let before = crate::acceleration::vulkan_execution_counts().unwrap();
            let start = Instant::now();
            let (comm, state) = whir_commit_owned_with_schedule(evals, &[5; 32], &schedule);
            let commit_ms = start.elapsed().as_secs_f64() * 1000.0;
            assert!(state.gpu_session.is_some(), "nv={nv} CPU fallback");
            let start = Instant::now();
            let proof = whir_open(
                &state,
                &point,
                value,
                &mut regime_transcript(&schedule, b"large-gpu"),
            );
            let open_ms = start.elapsed().as_secs_f64() * 1000.0;
            drop(state);
            let after = crate::acceleration::vulkan_execution_counts().unwrap();
            assert!(after.0 > before.0 && after.1 > before.1);
            assert_eq!(after.2, before.2, "GPU fallback at nv={nv}");
            let start = Instant::now();
            assert!(whir_verify_with_schedule(
                &comm,
                nv,
                &point,
                value,
                &proof,
                &mut regime_transcript(&schedule, b"large-gpu"),
                &schedule
            ));
            std::println!(
                "GPU_LARGE nv={nv} commit_ms={commit_ms:.2} open_ms={open_ms:.2} verify_ms={:.2} submissions={} stages={}",
                start.elapsed().as_secs_f64() * 1000.0,
                after.0 - before.0,
                after.1 - before.1
            );
        }
    }

    /// One flat opening above the former `nv = 24` ceiling under the default regime.
    #[test]
    fn nv25_single_opening_roundtrip() {
        let nv = 25;
        let schedule = whir_stage_schedule(nv);
        assert_eq!(schedule.stages.len(), 4);
        let evals = regime_test_poly(nv, 77);
        let point = regime_test_point(nv, 78);
        let value = crate::field::mle_eval_base_at_ext4(&evals, &point);
        let (comm, state) = whir_commit_owned_with_schedule(evals, &[5; 32], &schedule);
        assert_eq!(comm.log_leaves, 21);
        let proof = whir_open(
            &state,
            &point,
            value,
            &mut regime_transcript(&schedule, b"nv25"),
        );
        drop(state);
        assert!(whir_verify_with_schedule(
            &comm,
            nv,
            &point,
            value,
            &proof,
            &mut regime_transcript(&schedule, b"nv25"),
            &schedule
        ));
        let mut bad = proof.clone();
        bad.round0_vals[0] += Goldilocks::ONE;
        assert!(!whir_verify_with_schedule(
            &comm,
            nv,
            &point,
            value,
            &bad,
            &mut regime_transcript(&schedule, b"nv25"),
            &schedule
        ));
        let mut bad = proof;
        bad.folded_layers[2].opened_vals[0] += GoldilocksExt4::ONE;
        assert!(!whir_verify_with_schedule(
            &comm,
            nv,
            &point,
            value,
            &bad,
            &mut regime_transcript(&schedule, b"nv25"),
            &schedule
        ));
    }
}
