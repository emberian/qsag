//! `Hem` Succinct Multilinear Polynomial Commitment Scheme (`WHIR` EUROCRYPT 2025 Rate-Escalation
//! over `GoldilocksExt4` + Steiner-Deduplicated `CANOPY_MIDSTATE` Merkle-Canopy Oracles).
//!
//! Commits to multilinear polynomials $W_i \in \mathbb{F}_p[X_0, \dots, X_{\ell-1}]$ and proves
//! evaluation claims over the quartic extension $\mathbb{F}_{p^4}$ (`GoldilocksExt4`,
//! $|\mathbb{F}_{p^4}| > 2^{255.99}$) via:
//! 1. Exact hypercube-to-monomial Möbius basis transform ($O(\ell 2^\ell)$),
//! 2. Multi-stage WHIR **rate escalation** (`whir_stage_schedule`): instead of folding an initial
//!    high-rate codeword passively at fixed rate across every round, each intermediate stage
//!    re-encodes the folded multilinear witness at an **escalating Reed–Solomon blowup**
//!    (e.g. $B = (4, 16, 64)$, i.e. $\rho_0 = 1/4 \to \rho_1 = 1/16 \to \rho_2 = 1/64$ at
//!    $\ell = 20$), keeping intermediate evaluation domains bounded ($D_1 = 2^{19}, D_2 = 2^{18} \le 2^{20}$)
//!    with default conjectural QROM query counts $q = (128, 64, 43)$,
//! 3. **Out-of-Domain (OOD) List-Pinning & Shift-Query Accumulation:** every committed oracle
//!    $f^{(k)}$ is pinned at a fresh $\mathbb{F}_{p^4}$ Kronecker point $\text{pow2}(z_{\text{ood},k})$
//!    before sumcheck challenges are squeezed, and stage-$k$ fiber openings fold into shift claims
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
//! sumcheck over $\mathbb{F}_{p^4}$ followed by a single `Hem` WHIR opening of $\sum_i \mu^i W_i$.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use crate::field::{
    Goldilocks, GoldilocksExt4, build_eq_table_base, build_eq_table_ext4, encode_rs_coset_ext4,
    encode_rs_coset_goldilocks, eq_poly_base_ext4, eq_poly_ext4, eval_univariate_ext4,
    eval_univariate_ext4_at_base, fold_first_var_in_place_ext4, pow2_point_base, pow2_point_ext4,
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
const TAG_MERKLE_INTERNAL: u8 = 0x00;
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
            Self::BciksJohnsonQrom128 => 512usize.div_ceil(log_b) + 1,
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
/// Johnson QROM uses ceil(512/log2(B)) + 1 queries for unconditional Johnson
/// proximity below 2^-256, with positive proximity slack, without HABR24.
/// Neither per-round budget alone proves total PCS/QROM security.
pub fn whir_stage_schedule(num_vars: usize) -> WhirSchedule {
    WhirSecurityRegime::default().schedule(num_vars)
}

/// Complete multi-stage WHIR rate-escalation schedule for a given `num_vars`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirSchedule {
    pub regime: WhirSecurityRegime,
    /// Remaining multilinear variables sent explicitly as `final_hypercube_evals` (`1..=8`).
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
        if s16 >= 64 {
            const THREADS: usize = 16;
            let m_chunk = s16 / THREADS;
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
                if half >= 1024 {
                    let (upper, children) = nodes[..4 * half].split_at_mut(2 * half);
                    let parents = &mut upper[half..2 * half];
                    let p_chunk = half / THREADS;
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
            let hp = if k + 1 < active.len() && active[k + 1].0 == sib {
                k += 2;
                hash_merkle_internal(parent as u32, &hu, &active[k - 1].1)
            } else {
                let Some(hsib) = proof.auth_siblings.get(sib_cursor) else {
                    return false;
                };
                sib_cursor += 1;
                k += 1;
                if (u & 1) == 0 {
                    hash_merkle_internal(parent as u32, &hu, hsib)
                } else {
                    hash_merkle_internal(parent as u32, hsib, &hu)
                }
            };
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
fn hash_merkle_internal(node_idx: u32, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 69];
    buf[0] = TAG_MERKLE_INTERNAL;
    buf[1..5].copy_from_slice(&node_idx.to_le_bytes());
    buf[5..37].copy_from_slice(left);
    buf[37..69].copy_from_slice(right);
    cshake256_from_midstate_32(&CANOPY_MIDSTATE, &buf)
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
/// escalated-rate Merkle commitment, out-of-domain `Ext4` evaluation, 16-bit stage PoW nonce,
/// opened coset fibers, and Steiner-deduplicated Merkle multi-proof.
#[derive(Clone, Debug, PartialEq, Eq)]
