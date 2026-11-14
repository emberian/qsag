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
//!    with default conjectural QROM query counts $q = (128, 64, 43)$,
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

mod affine;
#[cfg(test)]
mod affine_schedule;
use affine::*;

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::{
    Goldilocks, GoldilocksExt4, build_eq_table_ext4, encode_rs_coset_ext4,
    encode_rs_coset_goldilocks, eq_poly_ext4, eval_univariate_ext4, eval_univariate_ext4_at_base,
    fold_first_var_in_place_ext4, pow2_point_ext4,
};
use crate::sponge::{
    CANOPY_MIDSTATE, FiatShamirTranscript, InstanceBound, POW_MIDSTATE,
    cshake256_from_midstate_16_x4, cshake256_from_midstate_32, cshake256_from_midstate_32_x4,
    cshake256_from_midstate_into, cshake256_pow_u64_single, cshake256_pow_u64_x4,
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

/// Largest number of multilinear variables supported by the PCS (`24` -> $2^{24}$ witness entries).
pub const MAX_PCS_NUM_VARS: usize = 24;

/// Largest number of polynomials committed jointly under one Round-0 Merkle-Canopy tree.
pub const MAX_BATCH_POLYS: usize = 16;

/// Largest number of base-field elements inside a single Round-0 batch leaf (`16 * 64 = 1024`).
const MAX_ROUND0_LEAF_VALS: usize = MAX_BATCH_POLYS * MAX_FIBER_ARITY;

/// Maximum number of WHIR stages across `2..=24` variables.
const MAX_WHIR_STAGES: usize = 4;

// Prefix-free 1-byte domain tags under `CANOPY_MIDSTATE` (`cSHAKE256("", ., "QSAG.PCS.CANOPY/v2")`):
const TAG_MERKLE_INTERNAL: u8 = qsag_whir_verified::TAG_CANOPY_MERKLE_INTERNAL;
const TAG_MERKLE_ROOT: u8 = 0x01;
const TAG_ROUND0_SALT: u8 = 0x02;
const TAG_ROUND0_SINGLE: u8 = 0x10;
const TAG_ROUND0_BATCH: u8 = 0x11;
const TAG_EXT4_STAGE_LEAF: u8 = 0x12;

// ============================================================================
// 1. WHIR Rate-Escalation Schedule (`num_vars` in `2..=24`)
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

/// Query-accounting regime. HABR24 uses conjectural agreement rho; BCIKS20
/// uses Johnson agreement sqrt(rho) + eta. These are per-stage query bounds,
/// not a proof of total Fiat–Shamir/QROM security (which also needs reduction,
/// list-size, field-error, and union-bound accounting).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(u8)]
pub enum WhirSecurityRegime {
    Habr24Classical128 = 0,
    Habr24Interactive128 = 1,
    BciksJohnsonClassical128 = 2,
    #[default]
    Habr24Qrom128 = 3,
    BciksJohnsonQrom128 = 4,
}

impl WhirSecurityRegime {
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::Habr24Classical128),
            1 => Some(Self::Habr24Interactive128),
            2 => Some(Self::BciksJohnsonClassical128),
            3 => Some(Self::Habr24Qrom128),
            4 => Some(Self::BciksJohnsonQrom128),
            _ => None,
        }
    }

    pub fn meets_qrom_128_floor(self) -> bool {
        matches!(self, Self::Habr24Qrom128 | Self::BciksJohnsonQrom128)
    }

    /// Conservative per-round query plus PoW budget, before other protocol errors.
    pub fn classical_fs_round_bits(self) -> u32 {
        match self {
            Self::Habr24Classical128 => 128,
            Self::Habr24Interactive128 | Self::BciksJohnsonClassical128 => 144,
            Self::Habr24Qrom128 | Self::BciksJohnsonQrom128 => 272,
        }
    }

    /// Grover round-search budget; total security requires separate reduction accounting.
    pub fn qrom_grover_round_bits(self) -> u32 {
        self.classical_fs_round_bits() / 2
    }

    fn minimum_queries(self, log_b: usize) -> usize {
        match self {
            Self::Habr24Classical128 => 112usize.div_ceil(log_b),
            Self::Habr24Interactive128 => 128usize.div_ceil(log_b),
            Self::BciksJohnsonClassical128 => 256usize.div_ceil(log_b) + 1,
            Self::Habr24Qrom128 => 256usize.div_ceil(log_b),
            Self::BciksJohnsonQrom128 => 512usize.div_ceil(log_b) + 2,
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

/// Default HABR24 QROM schedule: ceil(256/log2(B)) queries plus 16-bit PoW.
/// This budgets 272 classical or 136 Grover round-search bits, leaving eight
/// quantum bits for multi-round union slack. HABR24 agreement is conjectural.
/// Johnson QROM uses ceil(512/log2(B)) + 2 queries for unconditional Johnson
/// proximity below 2^-256, with positive proximity slack, without HABR24.
/// Neither per-round budget alone proves total PCS/QROM security.
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
        _ => unreachable!(),
    }
}

impl WhirSchedule {
    /// Reject malformed, under-budget, or oversized schedules before any allocation.
    pub fn validate(&self, num_vars: usize) -> bool {
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
        remaining == self.early_stop_vars
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
        for chunk in bytes.get(3..3 + 5 * count)?.chunks_exact(5) {
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
        let auth_siblings = sib_bytes
            .chunks_exact(32)
            .map(|c| {
                let mut h = [0u8; 32];
                h.copy_from_slice(c);
                h
            })
            .collect();
        Some((Self { auth_siblings }, end))
    }
}

/// Prover-side Merkle-Canopy tree (`nodes[1]` is top node; for `num_leaves >= 256`, stores only
/// internal nodes `0 .. num_leaves / 2` (`4x` lower RAM) and recomputes leaf/parent siblings on
/// opening).
pub struct MerkleCanopyTree {
    pub log_leaves: usize,
    pub is_compact: bool,
    pub nodes: Vec<[u8; 32]>,
    pub root: [u8; 32],
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
                    let p4 = hash_merkle_internal_x4(
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
                nodes[idx] = hash_merkle_internal(idx as u32, &nodes[2 * idx], &nodes[2 * idx + 1]);
            }
            let root = hash_tree_root(log_leaves as u8, &nodes[1]);
            return Self {
                log_leaves,
                is_compact: false,
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
            let p_lo = hash_merkle_internal_x4(
                2 * k_base,
                [&l0[0], &l0[2], &l1[0], &l1[2]],
                [&l0[1], &l0[3], &l1[1], &l1[3]],
            );
            let p_hi = hash_merkle_internal_x4(
                2 * k_base + 4,
                [&l2[0], &l2[2], &l3[0], &l3[2]],
                [&l2[1], &l2[3], &l3[1], &l3[3]],
            );
            hash_merkle_internal_x4(
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
                            scope.spawn(move || {
                                for (off, dst4) in sub.chunks_exact_mut(4).enumerate() {
                                    dst4.copy_from_slice(&fold_ref(base_m + off));
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
                                scope.spawn(move || {
                                    for (g, dst4) in p_sub.chunks_exact_mut(4).enumerate() {
                                        let c = 8 * g;
                                        let out4 = hash_merkle_internal_x4(
                                            (base_node + 4 * g) as u32,
                                            [&c_sub[c], &c_sub[c + 2], &c_sub[c + 4], &c_sub[c + 6]],
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
                            let out4 = hash_merkle_internal_x4(
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
                    nodes[idx] = hash_merkle_internal(idx as u32, &nodes[2 * idx], &nodes[2 * idx + 1]);
                }
                let root = hash_tree_root(log_leaves as u8, &nodes[1]);
                return Self {
                    log_leaves,
                    is_compact: true,
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
                let out4 = hash_merkle_internal_x4(
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
            nodes[idx] = hash_merkle_internal(idx as u32, &nodes[2 * idx], &nodes[2 * idx + 1]);
        }
        let root = hash_tree_root(log_leaves as u8, &nodes[1]);
        Self {
            log_leaves,
            is_compact: true,
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

        let get_node = |node_idx: usize| -> [u8; 32] {
            if !self.is_compact || node_idx < n / 2 {
                self.nodes[node_idx]
            } else if node_idx < n {
                let b = 2 * (node_idx - n / 2);
                let l0 = leaf_fn(b);
                let l1 = leaf_fn(b + 1);
                hash_merkle_internal(node_idx as u32, &l0, &l1)
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
            let (u, hu) = active[k];
            let sib = u ^ 1;
            let parent = u >> 1;
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
            let hp = hash_merkle_internal_tagged(pair.tag, parent as u32, &pair.left, &pair.right);
            active[write] = (parent, hp);
            write += 1;
        }
        active.truncate(write);
        cur_depth -= 1;
    }
    if sib_cursor != proof.auth_siblings.len() {
        return false;
    }
    matches!(active.as_slice(), [(1, top)] if hash_tree_root(commitment.log_leaves, top) == commitment.root)
}

/// Zero-alloc fixed-frame internal node hash (`[0x00] || node_idx(4B) || left(32B) || right(32B)` = `69` bytes,
/// `1` Keccak permutation from [`CANOPY_MIDSTATE`]).
#[inline]
fn hash_merkle_internal_tagged(
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
    cshake256_from_midstate_32(&CANOPY_MIDSTATE, &buf)
}

#[inline]
fn hash_merkle_internal(node_idx: u32, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    hash_merkle_internal_tagged(TAG_MERKLE_INTERNAL, node_idx, left, right)
}

/// 4-way SIMD internal node hash (`4` consecutive parent indices `base_node_idx .. base_node_idx + 4`
/// in ONE `keccak_f1600_x4` permutation from [`CANOPY_MIDSTATE`]).
#[inline]
fn hash_merkle_internal_x4(
    base_node_idx: u32,
    lefts: [&[u8; 32]; 4],
    rights: [&[u8; 32]; 4],
) -> [[u8; 32]; 4] {
    let mut bufs = [[0u8; 69]; 4];
    for k in 0..4 {
        bufs[k][0] = TAG_MERKLE_INTERNAL;
        bufs[k][1..5].copy_from_slice(&(base_node_idx + k as u32).to_le_bytes());
        bufs[k][5..37].copy_from_slice(lefts[k]);
        bufs[k][37..69].copy_from_slice(rights[k]);
    }
    cshake256_from_midstate_32_x4(&CANOPY_MIDSTATE, [&bufs[0], &bufs[1], &bufs[2], &bufs[3]])
}

/// Commitment digest of a tree: its top node bound to `log_leaves` (`34` bytes, `1` Keccak block).
#[inline]
fn hash_tree_root(log_leaves: u8, top_node: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 34];
    buf[0] = TAG_MERKLE_ROOT;
    buf[1] = log_leaves;
    buf[2..34].copy_from_slice(top_node);
    cshake256_from_midstate_32(&CANOPY_MIDSTATE, &buf)
}

/// Deterministic Round-0 per-fiber 16-byte blinding salt (`37` bytes, `1` Keccak block).
#[inline]
fn derive_round0_salt(salt_seed: &[u8; 32], group_idx: u32) -> [u8; 16] {
    let mut buf = [0u8; 37];
    buf[0] = TAG_ROUND0_SALT;
    buf[1..33].copy_from_slice(salt_seed);
    buf[33..37].copy_from_slice(&group_idx.to_le_bytes());
    let mut out = [0u8; 16];
    cshake256_from_midstate_into(&CANOPY_MIDSTATE, &buf, &mut out);
    out
}

/// 4-way SIMD Round-0 salt derivation for fibers `base_group .. base_group + 4`.
#[inline]
fn derive_round0_salt_x4(salt_seed: &[u8; 32], base_group: u32) -> [[u8; 16]; 4] {
    let mut bufs = [[0u8; 37]; 4];
    for (k, buf) in bufs.iter_mut().enumerate() {
        buf[0] = TAG_ROUND0_SALT;
        buf[1..33].copy_from_slice(salt_seed);
        buf[33..37].copy_from_slice(&(base_group + k as u32).to_le_bytes());
    }
    cshake256_from_midstate_16_x4(&CANOPY_MIDSTATE, [&bufs[0], &bufs[1], &bufs[2], &bufs[3]])
}

/// Zero-alloc single-polynomial Round-0 salted leaf hash (`arity` in `{2, 4, 8, 16, 32, 64}`).
#[inline]
fn hash_salted_base_group(leaf_idx: u32, salt: &[u8; 16], vals: &[Goldilocks]) -> [u8; 32] {
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
    cshake256_from_midstate_32(&CANOPY_MIDSTATE, &buf[..used])
}

/// Round-0 salted leaf hash across `num_polys` codewords.
fn hash_round0_leaf(
    leaf_idx: u32,
    salt: &[u8; 16],
    num_polys: usize,
    vals: &[Goldilocks],
) -> [u8; 32] {
    if num_polys == 1 {
        return hash_salted_base_group(leaf_idx, salt, vals);
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
        for (dst, v) in buf[23..used_bytes].chunks_exact_mut(8).zip(vals) {
            dst.copy_from_slice(&v.to_le_bytes());
        }
        return cshake256_from_midstate_32(&CANOPY_MIDSTATE, &buf[..used_bytes]);
    }
    let mut buf = [0u8; 23 + 8 * MAX_ROUND0_LEAF_VALS];
    buf[0] = TAG_ROUND0_BATCH;
    buf[1] = arity as u8;
    buf[2] = num_polys as u8;
    buf[3..7].copy_from_slice(&leaf_idx.to_le_bytes());
    buf[7..23].copy_from_slice(salt);
    for (dst, v) in buf[23..used_bytes].chunks_exact_mut(8).zip(vals) {
        dst.copy_from_slice(&v.to_le_bytes());
    }
    cshake256_from_midstate_32(&CANOPY_MIDSTATE, &buf[..used_bytes])
}

/// 4-way SIMD Round-0 salted leaf hash for 4 consecutive fibers `base_g .. base_g + 4`.
fn round0_leaf_hash_x4(
    codewords: &[Vec<Goldilocks>],
    salt_seed: &[u8; 32],
    base_g: usize,
    num_groups: usize,
    arity: usize,
) -> [[u8; 32]; 4] {
    let salts = derive_round0_salt_x4(salt_seed, base_g as u32);
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
        return cshake256_from_midstate_32_x4(
            &CANOPY_MIDSTATE,
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
        return cshake256_from_midstate_32_x4(
            &CANOPY_MIDSTATE,
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
    cshake256_from_midstate_32_x4(&CANOPY_MIDSTATE, [&bufs[0], &bufs[1], &bufs[2], &bufs[3]])
}

/// Scalar Round-0 leaf hash of fiber `g` (used during `open_multi_with_leaf_fn`).
fn round0_leaf_hash(
    codewords: &[Vec<Goldilocks>],
    salt_seed: &[u8; 32],
    g: usize,
    num_groups: usize,
    arity: usize,
) -> [u8; 32] {
    let salt = derive_round0_salt(salt_seed, g as u32);
    if let [codeword] = codewords {
        let vals = collect_coset_group_base(codeword, g, num_groups, arity);
        return hash_salted_base_group(g as u32, &salt, &vals[..arity]);
    }
    let used = codewords.len() * arity;
    let mut vals = [Goldilocks::ZERO; MAX_ROUND0_LEAF_VALS];
    for (chunk, codeword) in vals[..used].chunks_exact_mut(arity).zip(codewords) {
        for (k, slot) in chunk.iter_mut().enumerate() {
            *slot = codeword[g + k * num_groups];
        }
    }
    hash_round0_leaf(g as u32, &salt, codewords.len(), &vals[..used])
}

/// Zero-alloc Stage `>= 1` `GoldilocksExt4` coset fiber leaf hash (`arity` in `{2, 4, 8, 16, 32, 64}`).
#[inline]
fn hash_ext4_group(stage_idx: u8, leaf_idx: u32, vals: &[GoldilocksExt4]) -> [u8; 32] {
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
    cshake256_from_midstate_32(&CANOPY_MIDSTATE, &buf[..used])
}

/// 4-way SIMD Stage `>= 1` `GoldilocksExt4` coset fiber leaf hash for `base_g .. base_g + 4`.
fn hash_ext4_group_x4(
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
        return cshake256_from_midstate_32_x4(
            &CANOPY_MIDSTATE,
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
    cshake256_from_midstate_32_x4(
        &CANOPY_MIDSTATE,
        [
            &bufs[0][..used],
            &bufs[1][..used],
            &bufs[2][..used],
            &bufs[3][..used],
        ],
    )
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
    pub salt_seed: [u8; 32],
    pub tree_0: MerkleCanopyTree,
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
        self.codewords_0[0].len() / self.group_arity_0
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

/// Compatibility alias for [`WhirStageProof`].
pub type FoldedOracleProof = WhirStageProof;

/// Complete `Hem` WHIR rate-escalated opening proof over `GoldilocksExt4` against one commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemWhirOpeningProof {
    /// Two independent out-of-domain evaluations of the Stage-0 polynomial.
    pub stage0_ood_evals: [GoldilocksExt4; 2],
    /// Affine bridge scalars `[sigma_even, tau_01, tau_10, c_F, c_G]` per fold.
    /// Cross terms precede phi; shifted claims precede theta, alpha, and beta.
    pub fold_sumcheck_polys: Vec<[GoldilocksExt4; 5]>,
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
        for v in self.stage0_ood_evals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        push_sumcheck_wire_polys(&self.fold_sumcheck_polys, out);
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
        let round0_salts: Vec<[u8; 16]> = salt_bytes
            .chunks_exact(16)
            .map(|c| {
                let mut salt = [0u8; 16];
                salt.copy_from_slice(c);
                salt
            })
            .collect();
        pos += 16 * n_queries;

        let n_r0 = read_u32(bytes, &mut pos)? as usize;
        if n_r0 == 0 || n_r0 % n_queries != 0 || n_r0 / n_queries > MAX_ROUND0_LEAF_VALS {
            return None;
        }
        let val_bytes = bytes.get(pos..pos.checked_add(8 * n_r0)?)?;
        let mut round0_vals = Vec::with_capacity(n_r0);
        for c in val_bytes.chunks_exact(8) {
            let mut lb = [0u8; 8];
            lb.copy_from_slice(c);
            round0_vals.push(Goldilocks::from_le_bytes_canonical(lb)?);
        }
        pos += 8 * n_r0;

        let (round0_multiproof, used_r0_mp) =
            CanopyMultiProof::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += used_r0_mp;

        Some((
            Self {
                stage0_ood_evals,
                fold_sumcheck_polys,
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
    /// Single opening of the degree-preserving asymmetric affine cascade.
    pub opening: HemWhirOpeningProof,
}

impl HemWhirBatchOpeningProof {
    pub fn push_bytes(&self, out: &mut Vec<u8>) {
        push_sumcheck_wire_polys(&self.point_sumcheck_polys, out);
        out.extend_from_slice(&(self.common_point_evals.len() as u32).to_le_bytes());
        for v in &self.common_point_evals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        for v in &self.shifted_evals {
            out.extend_from_slice(&v.to_le_bytes());
        }
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
        let (opening, used) = HemWhirOpeningProof::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += used;
        Some((
            Self {
                point_sumcheck_polys,
                common_point_evals,
                shifted_evals,
                opening,
            },
            pos,
        ))
    }
}

// ============================================================================
// 4. Möbius Basis Transforms, Fast Parallel Kernels & Fiber Folding
// ============================================================================

/// Convert boolean-hypercube evaluations `evals[0..2^\ell]` into multilinear monomial coefficients.
pub fn hypercube_to_monomial_coeffs(evals: &[Goldilocks]) -> Vec<Goldilocks> {
    assert!(evals.len().is_power_of_two() && evals.len() >= 2);
    let ell = evals.len().trailing_zeros() as usize;
    let mut coeffs = evals.to_vec();

    #[cfg(feature = "std")]
    if coeffs.len() >= 32_768 {
        let threads = crate::parallel_pow2_workers(coeffs.len() / 2);
        let chunk_n = coeffs.len() / threads;
        let chunk_bits = chunk_n.trailing_zeros() as usize;
        std::thread::scope(|scope| {
            for sub in coeffs.chunks_mut(chunk_n) {
                scope.spawn(move || {
                    for bit in 0..chunk_bits {
                        let stride = 1usize << bit;
                        for base in (0..sub.len()).step_by(stride * 2) {
                            for i in 0..stride {
                                let v0 = sub[base + i];
                                sub[base + stride + i] -= v0;
                            }
                        }
                    }
                });
            }
        });
        for bit in chunk_bits..ell {
            let stride = 1usize << bit;
            for block in coeffs.chunks_mut(stride * 2) {
                let (lo, hi) = block.split_at_mut(stride);
                let sub_len = (stride / threads).max(1);
                std::thread::scope(|scope| {
                    for (lo_c, hi_c) in lo.chunks(sub_len).zip(hi.chunks_mut(sub_len)) {
                        scope.spawn(move || {
                            for (h, &l) in hi_c.iter_mut().zip(lo_c.iter()) {
                                *h -= l;
                            }
                        });
                    }
                });
            }
        }
        return coeffs;
    }

    for bit in 0..ell {
        let stride = 1usize << bit;
        for base in (0..coeffs.len()).step_by(stride * 2) {
            for i in 0..stride {
                let v0 = coeffs[base + i];
                coeffs[base + stride + i] -= v0;
            }
        }
    }
    coeffs
}

/// Convert `GoldilocksExt4` boolean-hypercube evaluations into multilinear monomial coefficients.
pub fn hypercube_to_monomial_coeffs_ext4(evals: &[GoldilocksExt4]) -> Vec<GoldilocksExt4> {
    assert!(evals.len().is_power_of_two() && evals.len() >= 2);
    let ell = evals.len().trailing_zeros() as usize;
    let mut coeffs = evals.to_vec();

    #[cfg(feature = "std")]
    if coeffs.len() >= 8_192 {
        let threads = crate::parallel_pow2_workers(coeffs.len() / 2);
        let chunk_n = coeffs.len() / threads;
        let chunk_bits = chunk_n.trailing_zeros() as usize;
        std::thread::scope(|scope| {
            for sub in coeffs.chunks_mut(chunk_n) {
                scope.spawn(move || {
                    for bit in 0..chunk_bits {
                        let stride = 1usize << bit;
                        for base in (0..sub.len()).step_by(stride * 2) {
                            for i in 0..stride {
                                let v0 = sub[base + i];
                                sub[base + stride + i] -= v0;
                            }
                        }
                    }
                });
            }
        });
        for bit in chunk_bits..ell {
            let stride = 1usize << bit;
            for block in coeffs.chunks_mut(stride * 2) {
                let (lo, hi) = block.split_at_mut(stride);
                let sub_len = (stride / threads).max(1);
                std::thread::scope(|scope| {
                    for (lo_c, hi_c) in lo.chunks(sub_len).zip(hi.chunks_mut(sub_len)) {
                        scope.spawn(move || {
                            for (h, &l) in hi_c.iter_mut().zip(lo_c.iter()) {
                                *h -= l;
                            }
                        });
                    }
                });
            }
        }
        return coeffs;
    }

    for bit in 0..ell {
        let stride = 1usize << bit;
        for base in (0..coeffs.len()).step_by(stride * 2) {
            for i in 0..stride {
                let v0 = coeffs[base + i];
                coeffs[base + stride + i] -= v0;
            }
        }
    }
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
                scope.spawn(move || {
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

#[inline]
#[allow(clippy::too_many_arguments)]
fn fold_duet_affine_ext4(
    v0: GoldilocksExt4,
    v1: GoldilocksExt4,
    inv_two_xk: Goldilocks,
    inv_two: Goldilocks,
    xk_sq: Goldilocks,
    theta: GoldilocksExt4,
    alpha: GoldilocksExt4,
    beta: GoldilocksExt4,
) -> GoldilocksExt4 {
    from_verified_ext4(qsag_whir_verified::cwyz_duet_fold(
        to_verified_ext4(v0),
        to_verified_ext4(v1),
        inv_two_xk.to_canonical_u64(),
        inv_two.to_canonical_u64(),
        xk_sq.to_canonical_u64(),
        to_verified_ext4(theta),
        to_verified_ext4(alpha),
        to_verified_ext4(beta),
    ))
}

/// Fold a coset fiber `vals` of size $A = 2^s \in \{2, 4, 8, 16, 32, 64\}$ at points
/// $x_k = y_0 \cdot \zeta_A^k$ across `chals[0..s]`, returning $W^{(s)}(\text{pow2}(y_0^{2^s}))$.
#[inline]
fn fold_coset_group_ext4(
    vals: &[GoldilocksExt4],
    mut inv_y0: Goldilocks,
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    chals: &[[GoldilocksExt4; 3]],
) -> GoldilocksExt4 {
    let step = chals.len();
    debug_assert!((1..=MAX_FOLD_STEP_VARS).contains(&step) && vals.len() == (1usize << step));
    let mut buf = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
    buf[..vals.len()].copy_from_slice(vals);
    let mut cur_len = vals.len();
    let mut inv_zeta = inv_zetas[step];
    let mut y0 = inv_y0.inv();
    let mut zeta = inv_zeta.inv();
    for &[theta, alpha, beta] in chals {
        let half = cur_len / 2;
        let mut inv_two_xk = inv_two * inv_y0;
        let mut xk = y0;
        for k in 0..half {
            buf[k] = fold_duet_affine_ext4(
                buf[k],
                buf[k + half],
                inv_two_xk,
                inv_two,
                xk.square(),
                theta,
                alpha,
                beta,
            );
            xk *= zeta;
            inv_two_xk *= inv_zeta;
        }
        cur_len = half;
        inv_y0 = inv_y0.square();
        inv_zeta = inv_zeta.square();
        y0 = y0.square();
        zeta = zeta.square();
    }
    buf[0]
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

fn fill_indexed<T, F>(out: &mut [T], f: F)
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
                scope.spawn(move || {
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
                        scope.spawn(move || {
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
                        scope.spawn(move || {
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
                scope.spawn(move || {
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
    assert!(!polys.is_empty() && polys.len() <= MAX_BATCH_POLYS);
    let table_len = polys[0].len();
    assert!(table_len.is_power_of_two() && table_len >= 4);
    assert!(polys.iter().all(|p| p.len() == table_len));
    let num_vars = table_len.trailing_zeros() as usize;
    assert!(num_vars <= MAX_PCS_NUM_VARS);

    assert!(schedule.validate(num_vars));
    let schedule = schedule.clone();
    let st0 = schedule.stages[0];
    let group_arity_0 = 1usize << st0.step_vars;

    #[cfg(feature = "std")]
    let codewords_0: Vec<Vec<Goldilocks>> = if polys.len() > 1 && crate::parallel_workers() > 1 {
        let blowup = st0.blowup;
        std::thread::scope(|scope| {
            let handles: Vec<_> = polys
                .iter()
                .map(|evals| {
                    scope.spawn(move || {
                        let coeffs = hypercube_to_monomial_coeffs(evals);
                        encode_rs_coset_goldilocks(&coeffs, blowup)
                    })
                })
                .collect();
            handles.into_iter().map(crate::join_worker).collect()
        })
    } else {
        polys
            .iter()
            .map(|evals| {
                let coeffs = hypercube_to_monomial_coeffs(evals);
                encode_rs_coset_goldilocks(&coeffs, st0.blowup)
            })
            .collect()
    };
    #[cfg(not(feature = "std"))]
    let codewords_0: Vec<Vec<Goldilocks>> = polys
        .iter()
        .map(|evals| {
            let coeffs = hypercube_to_monomial_coeffs(evals);
            encode_rs_coset_goldilocks(&coeffs, st0.blowup)
        })
        .collect();
    let domain_len = codewords_0[0].len();
    let num_groups = domain_len / group_arity_0;

    let tree_0 = MerkleCanopyTree::build_from_fn_x4(num_groups, |base_g| {
        round0_leaf_hash_x4(&codewords_0, salt_seed, base_g, num_groups, group_arity_0)
    });
    let comm = tree_0.commitment();
    (
        comm,
        HemWhirProverState {
            num_vars,
            schedule,
            group_arity_0,
            hypercube_evals: polys,
            codewords_0,
            salt_seed: *salt_seed,
            tree_0,
        },
    )
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
    absorb_whir_schedule(transcript, &state.schedule);
    let num_polys = state.num_polys();
    let num_vars = state.num_vars;
    assert_eq!(points.len(), num_polys);
    assert_eq!(evals.len(), num_polys);
    assert!(points.iter().all(|p| p.len() == num_vars));
    absorb_batch_statement(transcript, num_vars, &state.commitment(), points, evals);

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
    #[cfg(feature = "std")]
    let monomial_polys: Vec<Vec<Goldilocks>> =
        if state.hypercube_evals.len() > 1 && crate::parallel_workers() > 1 {
            std::thread::scope(|scope| {
                let handles: Vec<_> = state
                    .hypercube_evals
                    .iter()
                    .map(|w| scope.spawn(move || hypercube_to_monomial_coeffs(w)))
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
    let monomial_polys: Vec<Vec<Goldilocks>> = state
        .hypercube_evals
        .iter()
        .map(|w| hypercube_to_monomial_coeffs(w))
        .collect();
    let shifted_evals: Vec<_> = monomial_polys
        .iter()
        .map(|c| dot_base_ext4_fast(c, &kernel[1..1 + c.len()]))
        .collect();
    for &e in &shifted_evals {
        transcript.absorb_ext4(b"PCS_BATCH_SHIFT", e);
    }
    let weights = cascade_weights(num_polys, transcript);
    let combined_claim = combine_claims(&weights, &common_point_evals, &shifted_evals);
    let opening = whir_open_core(
        state,
        Some(&monomial_polys),
        &weights,
        kernel,
        combined_claim,
        transcript,
    );
    HemWhirBatchOpeningProof {
        point_sumcheck_polys,
        common_point_evals,
        shifted_evals,
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
                        scope.spawn(move || run_ref(j0, j1))
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

/// Core multi-stage `Hem` WHIR rate-escalated opening over `GoldilocksExt4`.
fn whir_open_core(
    state: &HemWhirProverState,
    precomputed_monomial_polys: Option<&[Vec<Goldilocks>]>,
    weights: &[[GoldilocksExt4; 2]],
    mut cur_k: Vec<GoldilocksExt4>,
    mut cur_sum_claim: GoldilocksExt4,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> HemWhirOpeningProof {
    let num_polys = state.num_polys();
    assert_eq!(weights.len(), num_polys);
    let single = num_polys == 1;
    let sched = &state.schedule;
    let num_stages = sched.stages.len();
    let early_stop = sched.early_stop_vars;
    let fold_vars = state.num_vars - early_stop;
    absorb_whir_schedule(transcript, sched);
    let core_len = 1usize << state.num_vars;
    let mut cur_coeffs = vec![GoldilocksExt4::ZERO; core_len + 2];
    for (poly_idx, (w, table)) in weights.iter().zip(&state.hypercube_evals).enumerate() {
        let owned_c;
        let c: &[Goldilocks] = match precomputed_monomial_polys {
            Some(pre) => &pre[poly_idx],
            None => {
                owned_c = hypercube_to_monomial_coeffs(table);
                &owned_c
            }
        };
        cur_coeffs[0] += w[0].mul_base(c[0]);
        #[cfg(feature = "std")]
        if core_len >= 16_384 {
            let workers = crate::parallel_workers();
            let chunk = (core_len - 1).div_ceil(workers);
            let c_ref = c;
            let w0 = w[0];
            let w1 = w[1];
            std::thread::scope(|scope| {
                for (t_idx, sub) in cur_coeffs[1..core_len].chunks_mut(chunk).enumerate() {
                    let base_i = 1 + t_idx * chunk;
                    scope.spawn(move || {
                        for (off, dst) in sub.iter_mut().enumerate() {
                            let i = base_i + off;
                            *dst = (*dst + w1.mul_base(c_ref[i - 1])) + w0.mul_base(c_ref[i]);
                        }
                    });
                }
            });
        } else {
            for i in 1..core_len {
                cur_coeffs[i] = (cur_coeffs[i] + w[1].mul_base(c[i - 1])) + w[0].mul_base(c[i]);
            }
        }
        #[cfg(not(feature = "std"))]
        for i in 1..core_len {
            cur_coeffs[i] = (cur_coeffs[i] + w[1].mul_base(c[i - 1])) + w[0].mul_base(c[i]);
        }
        cur_coeffs[core_len] += w[1].mul_base(c[core_len - 1]);
    }
    let z_ood_0 = core::array::from_fn::<_, 2, _>(|_| transcript.squeeze_ext4(b"WHIR_OOD_CHAL"));
    let stage0_ood_evals = z_ood_0.map(|z| eval_univariate_ext4(&cur_coeffs, z));
    for e in stage0_ood_evals {
        transcript.absorb_ext4(b"WHIR_OOD_EVAL", e);
    }
    for (z, e) in z_ood_0.into_iter().zip(stage0_ood_evals) {
        let xi = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
        add_geometric_scaled_in_place(&mut cur_k, xi, z);
        cur_sum_claim += xi * e;
    }

    let inv_two = Goldilocks::TWO.inv();
    let inv_shift = Goldilocks::NON_RESIDUE.inv();
    let inv_zetas = build_inv_zetas();

    let mut rem_vars = state.num_vars;
    let mut fold_sumcheck_polys = Vec::with_capacity(fold_vars);
    let mut stage_pow_nonce_0: u64 = 0;
    let mut round0_salts: Vec<[u8; 16]> = Vec::new();
    let mut round0_vals: Vec<Goldilocks> = Vec::new();
    let mut round0_multiproof = CanopyMultiProof {
        auth_siblings: Vec::new(),
    };
    let mut c_scratch = Vec::with_capacity(cur_coeffs.len() / 2 + 2);
    let mut k_scratch = Vec::with_capacity(cur_k.len() / 2 + 2);

    // Staged `Ext4` oracle currently active for `stage_idx >= 1`: `(cw, tree, ood_eval)`.
    let mut active_stage_oracle: Option<(
        Vec<GoldilocksExt4>,
        MerkleCanopyTree,
        [GoldilocksExt4; 2],
    )> = None;
    let mut folded_layers: Vec<WhirStageProof> = Vec::with_capacity(num_stages.saturating_sub(1));

    for (stage_idx, st) in sched.stages.iter().enumerate() {
        let arity = 1usize << st.step_vars;

        let mut stage_chals = [[GoldilocksExt4::ZERO; 3]; MAX_FOLD_STEP_VARS];
        for slot in stage_chals.iter_mut().take(st.step_vars) {
            let (wire, chals) = prove_fold_in_place(
                &mut cur_coeffs,
                &mut cur_k,
                &mut c_scratch,
                &mut k_scratch,
                &mut cur_sum_claim,
                transcript,
            );
            fold_sumcheck_polys.push(wire);
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
            let tree_next = MerkleCanopyTree::build_from_fn_x4(num_groups_next, |base_g| {
                hash_ext4_group_x4(next_stage_u8, &cw_next, base_g, num_groups_next, next_arity)
            });
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
                let num_groups_0 = state.num_groups_0();
                let domain_0 = state.codewords_0[0].len();
                let log_d0 = domain_0.trailing_zeros() as usize;
                let omega_0 = Goldilocks::two_adic_generator(log_d0);
                let inv_omega_0 = omega_0.inv();
                let q_indices = sample_stage_queries(transcript, 0, num_groups_0, st.num_queries);

                round0_salts.reserve(q_indices.len());
                round0_vals.reserve(q_indices.len() * num_polys * arity);
                let mut claims = Vec::with_capacity(q_indices.len());
                for &g in &q_indices {
                    round0_salts.push(derive_round0_salt(&state.salt_seed, g as u32));
                    let mut fiber = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                    if single {
                        let cw0 = &state.codewords_0[0];
                        for k in 0..arity {
                            let v = cw0[g + k * num_groups_0];
                            round0_vals.push(v);
                            fiber[k] = GoldilocksExt4::from_base(v);
                        }
                    } else {
                        for (w, cw) in weights.iter().zip(&state.codewords_0) {
                            for k in 0..arity {
                                let v = cw[g + k * num_groups_0];
                                round0_vals.push(v);
                                let x = Goldilocks::NON_RESIDUE
                                    * omega_0.pow((g + k * num_groups_0) as u64);
                                fiber[k] += (w[0] + w[1].mul_base(x)).mul_base(v);
                            }
                        }
                    }
                    let y0 = Goldilocks::NON_RESIDUE * omega_0.pow(g as u64);
                    let inv_y0 = inv_shift * inv_omega_0.pow(g as u64);
                    let v_shift = fold_coset_group_ext4(
                        &fiber[..arity],
                        inv_y0,
                        inv_two,
                        &inv_zetas,
                        chals_slice,
                    );
                    let z_u = pow2_iter_base(y0, st.step_vars);
                    claims.push((z_u, v_shift));
                }
                round0_multiproof = state.tree_0.open_multi_with_leaf_fn(&q_indices, |g| {
                    round0_leaf_hash(&state.codewords_0, &state.salt_seed, g, num_groups_0, arity)
                });
                claims
            } else {
                let (prev_cw, prev_tree, prev_ood) = match active_stage_oracle.take() {
                    Some(oracle) => oracle,
                    None => unreachable!("a noninitial stage follows a committed oracle"),
                };
                let domain_cur = prev_cw.len();
                let num_groups_cur = domain_cur / arity;
                let log_d = domain_cur.trailing_zeros() as usize;
                let omega = Goldilocks::two_adic_generator(log_d);
                let inv_omega = omega.inv();
                let q_indices =
                    sample_stage_queries(transcript, stage_idx, num_groups_cur, st.num_queries);

                let mut opened_vals = Vec::with_capacity(q_indices.len() * arity);
                let mut claims = Vec::with_capacity(q_indices.len());
                for &g in &q_indices {
                    let fiber = collect_coset_group_ext4(&prev_cw, g, num_groups_cur, arity);
                    opened_vals.extend_from_slice(&fiber[..arity]);
                    let y0 = Goldilocks::NON_RESIDUE * omega.pow(g as u64);
                    let inv_y0 = inv_shift * inv_omega.pow(g as u64);
                    let v_shift = fold_coset_group_ext4(
                        &fiber[..arity],
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
                    hash_ext4_group(stage_u8, g as u32, &fiber[..arity])
                });
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

            #[cfg(debug_assertions)]
            let final_coeffs_dbg = &cur_coeffs;

            if stage_idx == 0 {
                stage_pow_nonce_0 = pow_nonce;
                let num_groups_0 = state.num_groups_0();
                let domain_0 = state.codewords_0[0].len();
                let log_d0 = domain_0.trailing_zeros() as usize;
                let omega_0 = Goldilocks::two_adic_generator(log_d0);
                let inv_omega_0 = omega_0.inv();
                let q_indices = sample_stage_queries(transcript, 0, num_groups_0, st.num_queries);
                round0_salts.reserve(q_indices.len());
                round0_vals.reserve(q_indices.len() * num_polys * arity);
                for &g in &q_indices {
                    round0_salts.push(derive_round0_salt(&state.salt_seed, g as u32));
                    let mut fiber = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
                    if single {
                        let cw0 = &state.codewords_0[0];
                        for k in 0..arity {
                            let v = cw0[g + k * num_groups_0];
                            round0_vals.push(v);
                            fiber[k] = GoldilocksExt4::from_base(v);
                        }
                    } else {
                        for (w, cw) in weights.iter().zip(&state.codewords_0) {
                            for k in 0..arity {
                                let v = cw[g + k * num_groups_0];
                                round0_vals.push(v);
                                let x = Goldilocks::NON_RESIDUE
                                    * omega_0.pow((g + k * num_groups_0) as u64);
                                fiber[k] += (w[0] + w[1].mul_base(x)).mul_base(v);
                            }
                        }
                    }
                    #[cfg(debug_assertions)]
                    {
                        let y0 = Goldilocks::NON_RESIDUE * omega_0.pow(g as u64);
                        let inv_y0 = inv_shift * inv_omega_0.pow(g as u64);
                        let v_shift = fold_coset_group_ext4(
                            &fiber[..arity],
                            inv_y0,
                            inv_two,
                            &inv_zetas,
                            chals_slice,
                        );
                        let z_u = pow2_iter_base(y0, st.step_vars);
                        debug_assert_eq!(
                            v_shift,
                            eval_univariate_ext4_at_base(final_coeffs_dbg, z_u)
                        );
                    }
                    #[cfg(not(debug_assertions))]
                    let _ = (omega_0, inv_omega_0);
                }
                round0_multiproof = state.tree_0.open_multi_with_leaf_fn(&q_indices, |g| {
                    round0_leaf_hash(&state.codewords_0, &state.salt_seed, g, num_groups_0, arity)
                });
            } else {
                let (prev_cw, prev_tree, prev_ood) = match active_stage_oracle.take() {
                    Some(oracle) => oracle,
                    None => unreachable!("a noninitial stage follows a committed oracle"),
                };
                let domain_cur = prev_cw.len();
                let num_groups_cur = domain_cur / arity;
                let log_d = domain_cur.trailing_zeros() as usize;
                let omega = Goldilocks::two_adic_generator(log_d);
                let inv_omega = omega.inv();
                let q_indices =
                    sample_stage_queries(transcript, stage_idx, num_groups_cur, st.num_queries);
                let mut opened_vals = Vec::with_capacity(q_indices.len() * arity);
                for &g in &q_indices {
                    let fiber = collect_coset_group_ext4(&prev_cw, g, num_groups_cur, arity);
                    opened_vals.extend_from_slice(&fiber[..arity]);
                    #[cfg(debug_assertions)]
                    {
                        let y0 = Goldilocks::NON_RESIDUE * omega.pow(g as u64);
                        let inv_y0 = inv_shift * inv_omega.pow(g as u64);
                        let v_shift = fold_coset_group_ext4(
                            &fiber[..arity],
                            inv_y0,
                            inv_two,
                            &inv_zetas,
                            chals_slice,
                        );
                        let z_u = pow2_iter_base(y0, st.step_vars);
                        debug_assert_eq!(
                            v_shift,
                            eval_univariate_ext4_at_base(final_coeffs_dbg, z_u)
                        );
                    }
                    #[cfg(not(debug_assertions))]
                    let _ = (omega, inv_omega);
                }
                let stage_u8 = stage_idx as u8;
                let multiproof = prev_tree.open_multi_with_leaf_fn(&q_indices, |g| {
                    let fiber = collect_coset_group_ext4(&prev_cw, g, num_groups_cur, arity);
                    hash_ext4_group(stage_u8, g as u32, &fiber[..arity])
                });
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

    HemWhirOpeningProof {
        stage0_ood_evals,
        fold_sumcheck_polys,
        folded_layers,
        final_coeffs: cur_coeffs,
        pow_nonce: stage_pow_nonce_0,
        round0_salts,
        round0_vals,
        round0_multiproof,
    }
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
                scope.spawn(move || {
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
    let num_vars = init_point.len();
    let num_polys = weights.len();
    if !pcs_num_vars_supported(num_vars)
        || num_polys == 0
        || num_polys > MAX_BATCH_POLYS
        || init_point.len() != num_vars
        || comm_0.log_leaves > 28
    {
        return false;
    }

    if !sched.validate(num_vars) {
        return false;
    }
    let num_stages = sched.stages.len();
    let early_stop = sched.early_stop_vars;
    let fold_vars = num_vars - early_stop;

    if proof.fold_sumcheck_polys.len() != fold_vars
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

    let mut kernel_claims = vec![KernelClaim {
        offset: 0,
        weight: GoldilocksExt4::ONE,
        point: init_point.to_vec(),
        overflow: [GoldilocksExt4::ZERO; 2],
    }];
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
    let inv_shift = Goldilocks::NON_RESIDUE.inv();
    let inv_zetas = build_inv_zetas();

    let mut alphas = Vec::with_capacity(fold_vars);
    let mut phis = Vec::with_capacity(fold_vars);
    let mut sc_cursor = 0usize;
    let mut var_off = 0usize;
    let mut rem_vars = num_vars;

    for (stage_idx, st) in sched.stages.iter().enumerate() {
        let arity = 1usize << st.step_vars;
        let stage_alpha_start = alphas.len();

        for _ in 0..st.step_vars {
            let wire = proof.fold_sumcheck_polys[sc_cursor];
            sc_cursor += 1;
            let phi = bridge_prefix(&wire, transcript);
            let (next, chals) = bridge_finish(&wire, cur_sum_claim, phi, transcript);
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
                    comm_0,
                    num_polys,
                    weights,
                    domain_0,
                    arity_0,
                    st.num_queries,
                    stage_chals,
                    inv_shift,
                    inv_two,
                    &inv_zetas,
                    proof,
                    transcript,
                )
            } else {
                let cur_layer = &proof.folded_layers[stage_idx - 1];
                let domain_cur = (1usize << (rem_vars + st.step_vars)) * st.blowup;
                verify_and_fold_ext4_stage_fibers(
                    stage_idx,
                    cur_layer,
                    domain_cur,
                    arity,
                    st.num_queries,
                    stage_chals,
                    inv_shift,
                    inv_two,
                    &inv_zetas,
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

            // Mandatory terminal sumcheck check across all accumulated evaluation, OOD, and shift claims!
            let expected_terminal =
                terminal_sum(&phis, early_stop, &kernel_claims, &proof.final_coeffs);
            if !qsag_whir_verified::verify_ood_pin_eq(
                &expected_terminal
                    .to_limbs()
                    .map(Goldilocks::to_canonical_u64),
                &cur_sum_claim.to_limbs().map(Goldilocks::to_canonical_u64),
            ) {
                return false;
            }

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
                    comm_0,
                    num_polys,
                    weights,
                    domain_0,
                    arity_0,
                    st.num_queries,
                    stage_chals,
                    inv_shift,
                    inv_two,
                    &inv_zetas,
                    proof,
                    transcript,
                )
            } else {
                let cur_layer = &proof.folded_layers[stage_idx - 1];
                let domain_cur = (1usize << (rem_vars + st.step_vars)) * st.blowup;
                verify_and_fold_ext4_stage_fibers(
                    stage_idx,
                    cur_layer,
                    domain_cur,
                    arity,
                    st.num_queries,
                    stage_chals,
                    inv_shift,
                    inv_two,
                    &inv_zetas,
                    transcript,
                )
            };
            let Some(final_claims) = final_claims else {
                return false;
            };

            let verified_final_coeffs: Vec<qsag_whir_verified::Ext4> = proof
                .final_coeffs
                .iter()
                .copied()
                .map(to_verified_ext4)
                .collect();
            for &(z_u, v_shift) in &final_claims {
                if !qsag_whir_verified::verify_ext4_univariate_at_base_pin(
                    &verified_final_coeffs,
                    z_u.to_canonical_u64(),
                    to_verified_ext4(v_shift),
                ) {
                    return false;
                }
            }
        }
    }

    true
}

#[allow(clippy::too_many_arguments)]
fn verify_and_fold_stage0_fibers(
    comm_0: &CanopyCommitment,
    num_polys: usize,
    weights: &[[GoldilocksExt4; 2]],
    domain_0: usize,
    arity_0: usize,
    num_queries: usize,
    stage_chals: &[[GoldilocksExt4; 3]],
    inv_shift: Goldilocks,
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    proof: &HemWhirOpeningProof,
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> Option<Vec<(Goldilocks, GoldilocksExt4)>> {
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
    let inv_omega_0 = omega_0.inv();
    let step_vars = stage_chals.len();

    let mut sorted_leaves = Vec::with_capacity(q_indices.len());
    let mut claims = Vec::with_capacity(q_indices.len());

    for ((&g, salt), vals) in q_indices
        .iter()
        .zip(&proof.round0_salts)
        .zip(proof.round0_vals.chunks_exact(per_query))
    {
        sorted_leaves.push((g, hash_round0_leaf(g as u32, salt, num_polys, vals)));

        let mut ext_vals = [GoldilocksExt4::ZERO; MAX_FIBER_ARITY];
        if num_polys == 1 {
            for (slot, &v) in ext_vals.iter_mut().zip(vals) {
                *slot = GoldilocksExt4::from_base(v);
            }
        } else {
            for (w, poly_vals) in weights.iter().zip(vals.chunks_exact(arity_0)) {
                for (k, (slot, &v)) in ext_vals.iter_mut().zip(poly_vals).enumerate() {
                    let x = Goldilocks::NON_RESIDUE * omega_0.pow((g + k * num_groups_0) as u64);
                    *slot += (w[0] + w[1].mul_base(x)).mul_base(v);
                }
            }
        }

        let y0 = Goldilocks::NON_RESIDUE * omega_0.pow(g as u64);
        let inv_y0 = inv_shift * inv_omega_0.pow(g as u64);
        let v_shift = fold_coset_group_ext4(
            &ext_vals[..arity_0],
            inv_y0,
            inv_two,
            inv_zetas,
            stage_chals,
        );
        let z_u = pow2_iter_base(y0, step_vars);
        claims.push((z_u, v_shift));
    }

    if !verify_canopy_multiproof(comm_0, &sorted_leaves, &proof.round0_multiproof) {
        return None;
    }
    Some(claims)
}

#[allow(clippy::too_many_arguments)]
fn verify_and_fold_ext4_stage_fibers(
    stage_idx: usize,
    layer: &WhirStageProof,
    domain_cur: usize,
    arity: usize,
    num_queries: usize,
    stage_chals: &[[GoldilocksExt4; 3]],
    inv_shift: Goldilocks,
    inv_two: Goldilocks,
    inv_zetas: &[Goldilocks; MAX_FOLD_STEP_VARS + 1],
    transcript: &mut FiatShamirTranscript<InstanceBound>,
) -> Option<Vec<(Goldilocks, GoldilocksExt4)>> {
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
    let inv_omega = omega.inv();
    let step_vars = stage_chals.len();
    let stage_u8 = stage_idx as u8;

    let mut sorted_leaves = Vec::with_capacity(q_indices.len());
    let mut claims = Vec::with_capacity(q_indices.len());

    for (&g, vals) in q_indices.iter().zip(layer.opened_vals.chunks_exact(arity)) {
        sorted_leaves.push((g, hash_ext4_group(stage_u8, g as u32, vals)));
        let y0 = Goldilocks::NON_RESIDUE * omega.pow(g as u64);
        let inv_y0 = inv_shift * inv_omega.pow(g as u64);
        let v_shift = fold_coset_group_ext4(vals, inv_y0, inv_two, inv_zetas, stage_chals);
        let z_u = pow2_iter_base(y0, step_vars);
        claims.push((z_u, v_shift));
    }

    if !verify_canopy_multiproof(&layer.commitment, &sorted_leaves, &layer.multiproof) {
        return None;
    }
    Some(claims)
}

// ============================================================================
// 6. Deterministic 4-Way SIMD Proof-of-Work (`POW_MIDSTATE`)
// ============================================================================

/// Deterministically find the minimum `nonce: u64` whose `POW_MIDSTATE` digest has at least
/// `PCS_POW_BITS` low zero bits, scanning in 4-way SIMD (`cshake256_pow_u64_x4`) across 8 threads.
fn grind_pcs_pow(transcript: &FiatShamirTranscript<InstanceBound>) -> u64 {
    if PCS_POW_BITS == 0 {
        return 0;
    }
    let chal = transcript.transcript_digest();
    let mask = (1u64 << PCS_POW_BITS) - 1;

    #[cfg(feature = "std")]
    {
        use core::sync::atomic::{AtomicU64, Ordering};
        let threads = crate::parallel_workers() as u64;
        const PER_THREAD: u64 = 4_096; // 1,024 `x4` calls per thread
        let window: u64 = threads * PER_THREAD;

        let mut win_base = 0u64;
        loop {
            let best = AtomicU64::new(u64::MAX);
            let best_ref = &best;
            std::thread::scope(|scope| {
                for t in 0..threads {
                    let start = win_base + t * PER_THREAD;

                    scope.spawn(move || {
                        for offset in (0..PER_THREAD).step_by(4) {
                            let n = start + offset;
                            if n >= best_ref.load(Ordering::Relaxed) {
                                break;
                            }
                            let words = cshake256_pow_u64_x4(&POW_MIDSTATE, &chal, n);
                            for (lane, &w) in words.iter().enumerate() {
                                if (w & mask) == 0 {
                                    let hit = n + lane as u64;
                                    best_ref.fetch_min(hit, Ordering::Relaxed);
                                    return;
                                }
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
            let words = cshake256_pow_u64_x4(&POW_MIDSTATE, &chal, n);
            for (lane, &w) in words.iter().enumerate() {
                if (w & mask) == 0 {
                    return n + lane as u64;
                }
            }
            n = match n.checked_add(4) {
                Some(next) => next,
                None => panic!("PoW nonce space exhausted"),
            };
        }
    }
}

#[inline]
fn verify_pcs_pow(transcript: &FiatShamirTranscript<InstanceBound>, nonce: u64) -> bool {
    if PCS_POW_BITS == 0 {
        return true;
    }
    let chal = transcript.transcript_digest();
    let word = cshake256_pow_u64_single(&POW_MIDSTATE, &chal, nonce);
    qsag_whir_verified::verify_stage_pow_mask(word, PCS_POW_BITS)
}

#[cfg(test)]
mod pcs_unit_tests {
    use super::*;

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
            assert_eq!(
                fold_duet_affine_ext4(v0, v1, iy, it, yy, theta, alpha, beta),
                expected
            );
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
            let w4 = beta;
            let claim = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let phi = GoldilocksExt4::from_limbs(core::array::from_fn(|_| next()));
            let f = w0 + phi * w1;
            let g = w2 + phi * (claim - w0);
            let bridge_expected = g + alpha * (f + theta * g) + beta * (w3 + theta * w4);
            assert!(qsag_whir_verified::verify_cwyz_bridge_claim_step(
                to_verified_ext4(w0),
                to_verified_ext4(w1),
                to_verified_ext4(w2),
                to_verified_ext4(w3),
                to_verified_ext4(w4),
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
            WhirSecurityRegime::Habr24Qrom128
        );
        for (tag, counts, bits) in [
            (0, [56, 28, 19, 14], 128),
            (1, [64, 32, 22, 16], 144),
            (2, [129, 65, 44, 33], 144),
            (3, [128, 64, 43, 32], 272),
            (4, [258, 130, 88, 66], 272),
        ] {
            let regime = WhirSecurityRegime::from_u8(tag).unwrap();
            assert_eq!(regime as u8, tag);
            assert_eq!(regime.classical_fs_round_bits(), bits);
            assert_eq!(regime.qrom_grover_round_bits(), bits / 2);
            assert_eq!(regime.meets_qrom_128_floor(), tag >= 3);
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
        for tag in 5..=255 {
            assert_eq!(WhirSecurityRegime::from_u8(tag), None);
        }
    }

    #[test]
    fn security_regimes_roundtrip_and_query_budgets() {
        for regime in [
            WhirSecurityRegime::Habr24Classical128,
            WhirSecurityRegime::Habr24Interactive128,
            WhirSecurityRegime::BciksJohnsonClassical128,
            WhirSecurityRegime::Habr24Qrom128,
            WhirSecurityRegime::BciksJohnsonQrom128,
        ] {
            for nv in 2..=MAX_PCS_NUM_VARS {
                let schedule = regime.schedule(nv);
                assert!(schedule.validate(nv));
                let wire = schedule.to_bytes();
                assert_eq!(
                    WhirSchedule::from_bytes_canonical(&wire, nv),
                    Some((schedule.clone(), wire.len()))
                );
                for stage in &schedule.stages {
                    let log_b = stage.blowup.trailing_zeros() as usize;
                    match regime {
                        WhirSecurityRegime::Habr24Classical128 => {
                            assert!(stage.num_queries * log_b + 16 >= 128)
                        }
                        WhirSecurityRegime::Habr24Interactive128 => {
                            assert!(stage.num_queries * log_b >= 128)
                        }
                        WhirSecurityRegime::Habr24Qrom128 => {
                            assert!(stage.num_queries * log_b >= 256)
                        }
                        WhirSecurityRegime::BciksJohnsonQrom128 => {
                            assert!(stage.num_queries * log_b > 512)
                        }
                        WhirSecurityRegime::BciksJohnsonClassical128 => {
                            assert!(stage.num_queries * log_b > 256)
                        }
                    }
                }
                let mut unknown_regime = wire.clone();
                unknown_regime[0] = 5;
                assert!(WhirSchedule::from_bytes_canonical(&unknown_regime, nv).is_none());
                assert!(WhirSchedule::from_bytes_canonical(&wire[..wire.len() - 1], nv).is_none());
                let mut custom = schedule.clone();
                custom.stages[0].num_queries += 1;
                assert!(custom.validate(nv));
                assert_eq!(
                    WhirSchedule::from_bytes_canonical(&custom.to_bytes(), nv)
                        .unwrap()
                        .0,
                    custom
                );
                let mut bad = schedule;
                bad.stages[0].num_queries = 1;
                assert!(!bad.validate(nv));
            }
        }
    }

    #[test]
    fn explicit_security_regimes_end_to_end() {
        let nv = 12;
        let values: Vec<_> = (0..1u64 << nv).map(Goldilocks::from_u64_reduced).collect();
        let point = vec![GoldilocksExt4::from_base(Goldilocks::TWO); nv];
        let value = crate::field::mle_eval_base_at_ext4(&values, &point);
        for regime in [
            WhirSecurityRegime::Habr24Interactive128,
            WhirSecurityRegime::BciksJohnsonClassical128,
            WhirSecurityRegime::Habr24Qrom128,
            WhirSecurityRegime::BciksJohnsonQrom128,
        ] {
            let schedule = regime.schedule(nv);
            let transcript = || {
                FiatShamirTranscript::new()
                    .bind_relation(b"REGIME_TEST", b"", &schedule)
                    .bind_instance(&[b"instance"])
            };
            let start = std::time::Instant::now();
            let (comm, state) =
                whir_commit_batch_owned_with_schedule(vec![values.clone()], &[7; 32], &schedule);
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
            wrong.regime = WhirSecurityRegime::Habr24Classical128;
            assert!(!whir_verify_with_schedule(
                &comm,
                nv,
                &point,
                value,
                &proof,
                &mut transcript(),
                &wrong
            ));
            let mut forged = proof.clone();
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

        let q = [0usize, 1, 7, 64, 65, 255, 510, 511];
        let mp = t_x4.open_multi_with_leaf_fn(&q, leaf_scalar);
        let leaves: Vec<(usize, [u8; 32])> = q.iter().map(|&i| (i, leaf_scalar(i))).collect();
        assert!(verify_canopy_multiproof(&t_x4.commitment(), &leaves, &mp));
    }

    #[test]
    fn whir_schedule_validate_rejects_32bit_domain_overflow() {
        // Reproducer from Focus-03 #2: 2^24 * 256 = 2^32 overflows 32-bit/wasm32 `usize`.
        let bad_sched = WhirSchedule {
            regime: WhirSecurityRegime::Habr24Qrom128,
            early_stop_vars: 8,
            stages: vec![
                WhirStageSpec {
                    blowup: 256,
                    step_vars: 6,
                    num_queries: 32,
                },
                WhirStageSpec {
                    blowup: 4,
                    step_vars: 6,
                    num_queries: 128,
                },
                WhirStageSpec {
                    blowup: 4,
                    step_vars: 3,
                    num_queries: 128,
                },
                WhirStageSpec {
                    blowup: 4,
                    step_vars: 1,
                    num_queries: 128,
                },
            ],
        };
        assert!(!bad_sched.validate(24));
    }
}
