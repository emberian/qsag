//! The polynomial commitment of zk-Hem v2 (SECURITY.md V2.1, rounds 7 on): one Stage-0 tree
//! over a base-field table codeword `Z^` and a challenge-field mask codeword `R^` (each leaf
//! bound to a fresh 256-bit per-tree `tree_nonce` and per-leaf 256-bit `salt`), opened against
//! one linear claim `<c, K> = V` on the monomial coefficients `c` of the table.
//!
//! Also provides [`SplitOpening`], [`open_from_reduced_split`] and [`verify_split`] for
//! collaborative proving across `1..=MAX_STAGE0_SHARES` additive Stage-0 commitments.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::Range;
use qsag_core::wipe::SecretBuffer;

use super::field5::Fp5;
use super::hash::{Channel, Digest, Hasher, MAX_LOG_LEAVES, MerkleTree, verify_multiproof};
use super::params::{
    DIGEST_BYTES, LATER_OOD_POINTS, MASK_POINTS, Profile, SALT_BYTES, Schedule, TREE_NONCE_BYTES,
};
use crate::field::{Goldilocks, GoldilocksOps as _, ntt_goldilocks};

/// Coset shift of every evaluation domain.
const SHIFT: Goldilocks = Goldilocks::NON_RESIDUE;
const INV_TWO: Goldilocks = Goldilocks::from_u64_reduced(0x7FFF_FFFF_8000_0001);
const _: () = assert!(INV_TWO.const_mul(Goldilocks::TWO).to_canonical_u64() == 1);

/// Largest number of additive Stage-0 committers accepted by [`verify_split`].
pub const MAX_STAGE0_SHARES: usize = 255;

/// The prover's coins fell outside the event Good of SECURITY.md V2.1 (conditions G2, G3);
/// the proof would not be zero knowledge. Retry with a new seed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaskRankDeficient;

/// One tensor term of a linear claim: `weight * W(point, 0, .., 0)` for the multilinear `W`
/// whose monomial coefficients are the committed vector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TensorTerm {
    pub weight: Fp5,
    pub point: Vec<Fp5>,
}

// ============================================================================
// Geometry
// ============================================================================

/// Geometry of one stage: the oracle committed at its start and the folds applied to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StageDims {
    pub vars: usize,
    pub step_vars: usize,
    pub log_domain: usize,
    pub fibers: usize,
    pub queries: usize,
}

impl StageDims {
    #[inline]
    pub fn arity(&self) -> usize {
        1 << self.step_vars
    }

    #[inline]
    pub fn log_leaves(&self) -> usize {
        self.log_domain - self.step_vars
    }

    pub(crate) fn fiber_base(&self, j: usize) -> Goldilocks {
        SHIFT.const_mul(Goldilocks::two_adic_generator(self.log_domain).pow(j as u64))
    }

    pub(crate) fn fiber_image(&self, j: usize) -> Goldilocks {
        self.fiber_base(j).pow(1 << self.step_vars)
    }
}

/// The stages of `schedule` on a table of `2^log_cells` cells, or `None` if unsupported.
pub fn stage_dims(log_cells: usize, schedule: &Schedule) -> Option<Vec<StageDims>> {
    let folds: usize = schedule.stages.iter().map(|st| st.step_vars).sum();
    if schedule.stages.len() < 2
        || folds < 2
        || folds.checked_add(schedule.early_stop_vars) != Some(log_cells)
        || log_cells > 28
    {
        return None;
    }
    let mut vars = log_cells;
    let mut out = Vec::with_capacity(schedule.stages.len());
    for st in &schedule.stages {
        if !(1..=6).contains(&st.step_vars)
            || !st.blowup.is_power_of_two()
            || st.blowup < 2
            || st.num_queries == 0
        {
            return None;
        }
        let log_domain = vars + st.blowup.trailing_zeros() as usize;
        if log_domain > 32 || log_domain - st.step_vars > MAX_LOG_LEAVES {
            return None;
        }
        let fibers = 1usize << (log_domain - st.step_vars);
        out.push(StageDims {
            vars,
            step_vars: st.step_vars,
            log_domain,
            fibers,
            queries: st.num_queries.min(fibers),
        });
        vars -= st.step_vars;
    }
    Some(out)
}

/// Coefficients of the mask polynomial `R` and of the masked polynomial `g`.
pub fn mask_len(log_cells: usize, step_vars: usize) -> usize {
    (1usize << (log_cells - step_vars)) + 2
}

// ============================================================================
// Parallel helpers
// ============================================================================

const PAR_MIN: usize = 1 << 12;

pub(super) fn par_chunk(len: usize) -> usize {
    #[cfg(feature = "std")]
    let workers = crate::parallel_workers();
    #[cfg(not(feature = "std"))]
    let workers = 1;
    len.div_ceil(workers).max(PAR_MIN)
}

pub(in crate::zk_hem) fn par_chunks_mut<T: Send>(
    data: &mut [T],
    f: impl Fn(usize, &mut [T]) + Sync,
) {
    let chunk = par_chunk(data.len());
    #[cfg(feature = "std")]
    if data.len() > chunk {
        std::thread::scope(|scope| {
            for (k, part) in data.chunks_mut(chunk).enumerate() {
                let f = &f;
                crate::spawn_bounded(scope, move || f(k * chunk, part));
            }
        });
        return;
    }
    for (k, part) in data.chunks_mut(chunk).enumerate() {
        f(k * chunk, part);
    }
}

pub(super) fn par_sum<const K: usize>(
    n: usize,
    f: impl Fn(Range<usize>) -> [Fp5; K] + Sync,
) -> [Fp5; K] {
    #[cfg(feature = "std")]
    if n > PAR_MIN && crate::parallel_workers() > 1 {
        let chunk = par_chunk(n);
        let mut parts: Vec<[Fp5; K]> = std::thread::scope(|scope| {
            let workers: Vec<_> = (0..n)
                .step_by(chunk)
                .map(|start| {
                    let (f, end) = (&f, (start + chunk).min(n));
                    crate::spawn_bounded(scope, move || f(start..end))
                })
                .collect();
            workers.into_iter().map(crate::join_worker).collect()
        });
        let mut total = [Fp5::ZERO; K];
        for part in &mut parts {
            for (t, p) in total.iter_mut().zip(part.iter()) {
                *t += *p;
            }
            qsag_asm::volatile_fill(part, Fp5::ZERO);
        }
        return total;
    }
    f(0..n)
}

// ============================================================================
// Polynomials and codewords
// ============================================================================

pub trait Coef: Copy + Send + Sync {
    const ZERO: Self;
    fn scale(self, e: Fp5) -> Fp5;
    fn lift(self) -> Fp5;
}

impl Coef for Goldilocks {
    const ZERO: Self = Goldilocks::ZERO;
    #[inline(always)]
    fn scale(self, e: Fp5) -> Fp5 {
        e.mul_base(self)
    }
    #[inline(always)]
    fn lift(self) -> Fp5 {
        Fp5::from_base(self)
    }
}

impl Coef for Fp5 {
    const ZERO: Self = Fp5::ZERO;
    #[inline(always)]
    fn scale(self, e: Fp5) -> Fp5 {
        self * e
    }
    #[inline(always)]
    fn lift(self) -> Fp5 {
        self
    }
}

pub fn eval_poly<T: Coef, const K: usize>(coeffs: &[T], xs: [Fp5; K]) -> [Fp5; K] {
    let powers: [[Fp5; EVAL_BLOCK + 1]; K] = xs.map(|x| {
        let mut row = [Fp5::ONE; EVAL_BLOCK + 1];
        for j in 1..=EVAL_BLOCK {
            row[j] = row[j - 1] * x;
        }
        row
    });
    par_sum(coeffs.len(), |range| {
        let start = range.start as u64;
        let mut acc = [Fp5::ZERO; K];
        for block in coeffs[range].chunks(EVAL_BLOCK).rev() {
            for (a, row) in acc.iter_mut().zip(&powers) {
                let low = block
                    .iter()
                    .zip(row)
                    .fold(Fp5::ZERO, |sum, (c, &p)| sum + c.scale(p));
                *a = *a * row[EVAL_BLOCK] + low;
            }
        }
        for (a, x) in acc.iter_mut().zip(&xs) {
            *a *= x.pow(start);
        }
        acc
    })
}

const EVAL_BLOCK: usize = 32;

pub(crate) fn eval_at_base(coeffs: &[Fp5], y: Goldilocks) -> Fp5 {
    let verified: Vec<qsag_whir_verified::Fp5> = coeffs.iter().copied().map(Into::into).collect();
    Fp5::from(qsag_whir_verified::eval_fp5_univariate_at_base(
        &verified,
        y.to_canonical_u64(),
    ))
}

pub(crate) fn verify_at_base_pin(coeffs: &[Fp5], y: Goldilocks, expected: Fp5) -> bool {
    let verified: Vec<qsag_whir_verified::Fp5> = coeffs.iter().copied().map(Into::into).collect();
    qsag_whir_verified::verify_fp5_univariate_at_base_pin(
        &verified,
        y.to_canonical_u64(),
        expected.into(),
    )
}

fn shifted_limb_ntt(
    len: usize,
    log_domain: usize,
    limb: impl Fn(usize) -> Goldilocks,
) -> Vec<Goldilocks> {
    let mut buf = vec![Goldilocks::ZERO; 1 << log_domain];
    let mut power = Goldilocks::ONE;
    for (i, slot) in buf[..len].iter_mut().enumerate() {
        *slot = limb(i).const_mul(power);
        power = power.const_mul(SHIFT);
    }
    ntt_goldilocks(&mut buf);
    buf
}

pub fn encode_base(coeffs: &[Goldilocks], log_domain: usize) -> Vec<Goldilocks> {
    assert!(coeffs.len() <= 1 << log_domain);
    shifted_limb_ntt(coeffs.len(), log_domain, |i| coeffs[i])
}

pub fn encode_ext(coeffs: &[Fp5], log_domain: usize) -> Vec<Fp5> {
    assert!(coeffs.len() <= 1 << log_domain);
    let mut out = vec![Fp5::ZERO; 1 << log_domain];
    for limb in 0..5 {
        let mut buf = shifted_limb_ntt(coeffs.len(), log_domain, |i| coeffs[i].0[limb]);
        par_chunks_mut(&mut out, |off, part| {
            for (slot, v) in part.iter_mut().zip(&buf[off..]) {
                slot.0[limb] = *v;
            }
        });
        qsag_asm::volatile_fill(&mut buf, Goldilocks::ZERO);
    }
    out
}

pub(in crate::zk_hem) fn encode_ext_folded(
    coeffs: &[Fp5],
    log_domain: usize,
    step_vars: usize,
) -> Vec<Fp5> {
    let log_folded = log_domain - step_vars;
    assert!(coeffs.len() <= 1 << log_folded);
    let shift = SHIFT.pow(1 << step_vars);
    let mut out = vec![Fp5::ZERO; 1 << log_folded];
    for limb in 0..5 {
        let mut buf = vec![Goldilocks::ZERO; 1 << log_folded];
        let mut power = Goldilocks::ONE;
        for (slot, c) in buf.iter_mut().zip(coeffs) {
            *slot = c.0[limb].const_mul(power);
            power = power.const_mul(shift);
        }
        ntt_goldilocks(&mut buf);
        for (slot, v) in out.iter_mut().zip(&buf) {
            slot.0[limb] = *v;
        }
        qsag_asm::volatile_fill(&mut buf, Goldilocks::ZERO);
    }
    out
}

pub(crate) fn fiber<T: Copy>(code: &[T], dims: &StageDims, j: usize) -> Vec<T> {
    (0..dims.arity())
        .map(|t| code[j + t * dims.fibers])
        .collect()
}

pub(crate) fn fold_fiber(mut vals: Vec<Fp5>, x0: Goldilocks, chals: &[[Fp5; 3]]) -> Fp5 {
    let steps = vals.len().trailing_zeros() as usize;
    debug_assert!(vals.len().is_power_of_two() && steps == chals.len());
    let mut x = x0;
    let mut x_inv = x0.inv();
    let mut zeta = Goldilocks::two_adic_generator(steps);
    let mut zeta_inv = zeta.inv();
    let mut len = vals.len();
    for &[theta, alpha, beta] in chals {
        let half = len / 2;
        let (mut xt, mut xt_inv) = (x, x_inv);
        for t in 0..half {
            let (a, b) = (vals[t], vals[t + half]);
            vals[t] = Fp5::from(qsag_whir_verified::cwyz_duet_fold_fp5(
                a.into(),
                b.into(),
                INV_TWO.const_mul(xt_inv).to_canonical_u64(),
                INV_TWO.to_canonical_u64(),
                xt.square().to_canonical_u64(),
                theta.into(),
                alpha.into(),
                beta.into(),
            ));
            xt = xt.const_mul(zeta);
            xt_inv = xt_inv.const_mul(zeta_inv);
        }
        len = half;
        x = x.square();
        x_inv = x_inv.square();
        zeta = zeta.square();
        zeta_inv = zeta_inv.square();
    }
    vals[0]
}

// ============================================================================
// Commitment
// ============================================================================

/// Prover state of a Stage-0 commitment.
pub struct Committed {
    profile: Profile,
    log_cells: usize,
    schedule: Schedule,
    dims: Vec<StageDims>,
    coeffs: Vec<Goldilocks>,
    mask: Vec<Fp5>,
    z_code: Vec<Goldilocks>,
    r_code: Vec<Fp5>,
    salt_seed: [u8; 32],
    tree_nonce: [u8; TREE_NONCE_BYTES],
    tree: MerkleTree,
}

impl Drop for Committed {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.coeffs, Goldilocks::ZERO);
        qsag_asm::volatile_fill(&mut self.mask, Fp5::ZERO);
        qsag_asm::volatile_fill(&mut self.z_code, Goldilocks::ZERO);
        qsag_asm::volatile_fill(&mut self.r_code, Fp5::ZERO);
        qsag_asm::volatile_fill(&mut self.salt_seed, 0u8);
    }
}

impl Committed {
    pub fn root(&self) -> Digest {
        self.tree.root()
    }

    pub fn tree_nonce(&self) -> [u8; TREE_NONCE_BYTES] {
        self.tree_nonce
    }

    pub fn log_cells(&self) -> usize {
        self.log_cells
    }

    pub fn schedule(&self) -> &Schedule {
        &self.schedule
    }

    pub fn coeffs(&self) -> &[Goldilocks] {
        &self.coeffs
    }

    pub fn mask(&self) -> &[Fp5] {
        &self.mask
    }
}

/// Commit to the table with monomial coefficients `coeffs` (`2^log_cells`) and mask polynomial
/// `mask` ([`mask_len`] coefficients), domain-separated by `tree_nonce` and salted by `salt_seed`.
pub fn commit(
    profile: Profile,
    log_cells: usize,
    schedule: &Schedule,
    coeffs: Vec<Goldilocks>,
    mask: Vec<Fp5>,
    salt_seed: &[u8; 32],
    tree_nonce: &[u8; TREE_NONCE_BYTES],
) -> Committed {
    commit_inner(
        profile,
        log_cells,
        schedule,
        coeffs,
        mask,
        salt_seed,
        tree_nonce,
        #[cfg(feature = "vulkan")]
        None,
    )
    .expect("CPU commitment is infallible")
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn commit_inner(
    profile: Profile,
    log_cells: usize,
    schedule: &Schedule,
    coeffs: Vec<Goldilocks>,
    mask: Vec<Fp5>,
    salt_seed: &[u8; 32],
    tree_nonce: &[u8; TREE_NONCE_BYTES],
    #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
) -> Result<Committed, super::protocol::ZkHemV2Error> {
    let coeffs = SecretBuffer::new(coeffs);
    let mask = SecretBuffer::new(mask);
    let _phase = crate::profile::span("zkhem2_commit");
    let dims = stage_dims(log_cells, schedule).expect("unsupported v2 schedule");
    let d0 = dims[0];
    assert_eq!(coeffs.len(), 1 << log_cells);
    assert_eq!(mask.len(), mask_len(log_cells, d0.step_vars));
    let phase = crate::profile::span("zkhem2_commit_encode");
    let encode_cpu = || {
        (
            SecretBuffer::new(encode_base(&coeffs, d0.log_domain)),
            SecretBuffer::new(encode_ext_folded(&mask, d0.log_domain, d0.step_vars)),
        )
    };
    #[cfg(feature = "vulkan")]
    let (z_code, r_code) = if let Some(gpu) = gpu {
        crate::vulkan::encode_stage0(gpu, &coeffs, &mask, d0.log_domain, d0.step_vars)
            .map_err(super::protocol::ZkHemV2Error::Vulkan)?
    } else {
        encode_cpu()
    };
    #[cfg(not(feature = "vulkan"))]
    let (z_code, r_code) = encode_cpu();
    drop(phase);
    let _merkle = crate::profile::span("zkhem2_commit_merkle");
    let hasher = Hasher::new(profile);
    let cpu_tree = || {
        let mut leaves = vec![[0u8; DIGEST_BYTES]; d0.fibers];
        crate::pcs::fill_indexed(&mut leaves, |j| {
            let mut salt = hasher.salt(salt_seed, j as u32);
            let mut z = fiber(&z_code, &d0, j);
            let digest = hasher.leaf_stage0(tree_nonce, j as u32, &salt, &z, r_code[j]);
            qsag_asm::volatile_fill(&mut salt, 0u8);
            qsag_asm::volatile_fill(&mut z, Goldilocks::ZERO);
            digest
        });
        MerkleTree::build(hasher, 0, leaves)
    };
    #[cfg(feature = "vulkan")]
    let tree = if let Some(gpu) = gpu {
        let word4 = |bytes: &[u8; 32]| {
            core::array::from_fn(|i| u64::from_le_bytes(bytes.as_chunks::<8>().0[i]))
        };
        let mask = crate::vulkan::ext_words(&r_code);
        let framing = qsag_accel::vulkan::CanopyProfile::ZkStage0 {
            midstate: hasher.tree_midstate(),
            turbo: profile.uses_turboshake(),
            salt_seed: word4(salt_seed),
            nonce: word4(tree_nonce),
            mask_code: &mask,
        };
        crate::vulkan::tree(
            gpu,
            hasher,
            framing,
            0,
            d0.arity(),
            &crate::vulkan::base_words(&z_code),
        )
        .map_err(super::protocol::ZkHemV2Error::Vulkan)?
    } else {
        cpu_tree()
    };
    #[cfg(not(feature = "vulkan"))]
    let tree = cpu_tree();
    Ok(Committed {
        profile,
        log_cells,
        schedule: schedule.clone(),
        dims,
        coeffs: coeffs.into_inner(),
        mask: mask.into_inner(),
        z_code: z_code.into_inner(),
        r_code: r_code.into_inner(),
        salt_seed: *salt_seed,
        tree_nonce: *tree_nonce,
        tree,
    })
}

// ============================================================================
// Proof types & Wire Codecs
// ============================================================================

/// An opened Stage-0 leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage0Leaf {
    pub salt: [u8; SALT_BYTES],
    pub z: Vec<Goldilocks>,
    pub r: Fp5,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage0Query {
    pub leaves: Vec<Stage0Leaf>,
    pub siblings: Vec<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtQuery {
    pub leaves: Vec<Vec<Fp5>>,
    pub siblings: Vec<Digest>,
}

/// Messages of a stage after the first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaterStage {
    pub root: Digest,
    pub ood: [Fp5; LATER_OOD_POINTS],
    pub folds: Vec<[Fp5; 5]>,
    pub query: ExtQuery,
}

/// Single-committer Stage-0 opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening {
    pub mask_evals: [Fp5; MASK_POINTS],
    pub stage0_folds: Vec<[Fp5; 5]>,
    pub mask_claim: Fp5,
    pub stage0_query: Stage0Query,
    pub stages: Vec<LaterStage>,
    pub final_coeffs: Vec<Fp5>,
}

/// Multi-committer additive Stage-0 opening (`1..=MAX_STAGE0_SHARES` shares).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitOpening {
    pub mask_evals: [Fp5; MASK_POINTS],
    pub stage0_folds: Vec<[Fp5; 5]>,
    pub mask_claim: Fp5,
    pub stage0_shares: Vec<Stage0Query>,
    pub stages: Vec<LaterStage>,
    pub final_coeffs: Vec<Fp5>,
}

fn push_fp5(out: &mut Vec<u8>, v: &Fp5) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn push_siblings(out: &mut Vec<u8>, siblings: &[Digest]) {
    out.extend_from_slice(&(siblings.len() as u32).to_le_bytes());
    for d in siblings {
        out.extend_from_slice(d);
    }
}

pub fn push_stage0_query(out: &mut Vec<u8>, q: &Stage0Query) {
    for leaf in &q.leaves {
        out.extend_from_slice(&leaf.salt);
        for z in &leaf.z {
            out.extend_from_slice(&z.to_le_bytes());
        }
        push_fp5(out, &leaf.r);
    }
    push_siblings(out, &q.siblings);
}

fn push_ext_query(out: &mut Vec<u8>, q: &ExtQuery) {
    q.leaves.iter().flatten().for_each(|v| push_fp5(out, v));
    push_siblings(out, &q.siblings);
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> Option<[u8; N]> {
        let chunk: [u8; N] = self
            .bytes
            .get(self.pos..self.pos.checked_add(N)?)?
            .try_into()
            .ok()?;
        self.pos += N;
        Some(chunk)
    }

    fn fp5(&mut self) -> Option<Fp5> {
        Fp5::from_le_bytes_canonical(self.take()?)
    }

    fn base(&mut self) -> Option<Goldilocks> {
        Goldilocks::from_canonical_u64(u64::from_le_bytes(self.take()?))
    }

    fn fold(&mut self) -> Option<[Fp5; 5]> {
        Some([
            self.fp5()?,
            self.fp5()?,
            self.fp5()?,
            self.fp5()?,
            self.fp5()?,
        ])
    }

    fn siblings(&mut self, dims: &StageDims) -> Option<Vec<Digest>> {
        let n = u32::from_le_bytes(self.take()?) as usize;
        if n > dims.queries * dims.log_leaves() {
            return None;
        }
        (0..n).map(|_| self.take()).collect()
    }

    fn stage0_query(&mut self, d0: &StageDims) -> Option<Stage0Query> {
        let leaves = (0..d0.queries)
            .map(|_| {
                Some(Stage0Leaf {
                    salt: self.take()?,
                    z: (0..d0.arity())
                        .map(|_| self.base())
                        .collect::<Option<_>>()?,
                    r: self.fp5()?,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Stage0Query {
            leaves,
            siblings: self.siblings(d0)?,
        })
    }

    fn ext_query(&mut self, dims: &StageDims) -> Option<ExtQuery> {
        let leaves = (0..dims.queries)
            .map(|_| (0..dims.arity()).map(|_| self.fp5()).collect())
            .collect::<Option<Vec<Vec<Fp5>>>>()?;
        Some(ExtQuery {
            leaves,
            siblings: self.siblings(dims)?,
        })
    }
}

/// Read one [`Stage0Query`] of geometry `d0` from the entirety of `bytes`.
pub fn read_stage0_query_exact(bytes: &[u8], d0: &StageDims) -> Option<Stage0Query> {
    let mut r = Reader { bytes, pos: 0 };
    let q = r.stage0_query(d0)?;
    (r.pos == bytes.len()).then_some(q)
}

impl Opening {
    pub fn push_bytes(&self, out: &mut Vec<u8>) {
        self.mask_evals.iter().for_each(|v| push_fp5(out, v));
        self.stage0_folds
            .iter()
            .flatten()
            .for_each(|v| push_fp5(out, v));
        push_fp5(out, &self.mask_claim);
        for (i, stage) in self.stages.iter().enumerate() {
            out.extend_from_slice(&stage.root);
            stage.ood.iter().for_each(|v| push_fp5(out, v));
            if i == 0 {
                push_stage0_query(out, &self.stage0_query);
            } else {
                push_ext_query(out, &self.stages[i - 1].query);
            }
            stage.folds.iter().flatten().for_each(|v| push_fp5(out, v));
        }
        self.final_coeffs.iter().for_each(|v| push_fp5(out, v));
        if let Some(last) = self.stages.last() {
            push_ext_query(out, &last.query);
        }
    }

    pub fn read(
        bytes: &[u8],
        pos: &mut usize,
        log_cells: usize,
        schedule: &Schedule,
    ) -> Option<Self> {
        let mut split = SplitOpening::read(bytes, pos, log_cells, schedule, 1)?;
        Some(Self {
            mask_evals: split.mask_evals,
            stage0_folds: split.stage0_folds,
            mask_claim: split.mask_claim,
            stage0_query: split.stage0_shares.pop()?,
            stages: split.stages,
            final_coeffs: split.final_coeffs,
        })
    }
}

impl SplitOpening {
    pub fn push_bytes(&self, out: &mut Vec<u8>) {
        self.mask_evals.iter().for_each(|v| push_fp5(out, v));
        self.stage0_folds
            .iter()
            .flatten()
            .for_each(|v| push_fp5(out, v));
        push_fp5(out, &self.mask_claim);
        for (i, stage) in self.stages.iter().enumerate() {
            out.extend_from_slice(&stage.root);
            stage.ood.iter().for_each(|v| push_fp5(out, v));
            if i == 0 {
                for share in &self.stage0_shares {
                    push_stage0_query(out, share);
                }
            } else {
                push_ext_query(out, &self.stages[i - 1].query);
            }
            stage.folds.iter().flatten().for_each(|v| push_fp5(out, v));
        }
        self.final_coeffs.iter().for_each(|v| push_fp5(out, v));
        if let Some(last) = self.stages.last() {
            push_ext_query(out, &last.query);
        }
    }

    pub fn read(
        bytes: &[u8],
        pos: &mut usize,
        log_cells: usize,
        schedule: &Schedule,
        committers: usize,
    ) -> Option<Self> {
        if !(1..=MAX_STAGE0_SHARES).contains(&committers) {
            return None;
        }
        let dims = stage_dims(log_cells, schedule)?;
        let mut r = Reader { bytes, pos: *pos };
        let mask_evals = r.fold()?;
        let stage0_folds = (0..dims[0].step_vars)
            .map(|_| r.fold())
            .collect::<Option<Vec<_>>>()?;
        let mask_claim = r.fp5()?;
        let mut stage0_shares = None;
        let mut stages: Vec<LaterStage> = Vec::with_capacity(dims.len() - 1);
        for i in 1..dims.len() {
            let root = r.take()?;
            let ood = [r.fp5()?, r.fp5()?];
            if i == 1 {
                let d0 = &dims[0];
                stage0_shares = Some(
                    (0..committers)
                        .map(|_| r.stage0_query(d0))
                        .collect::<Option<Vec<_>>>()?,
                );
            } else {
                stages[i - 2].query = r.ext_query(&dims[i - 1])?;
            }
            let folds = (0..dims[i].step_vars)
                .map(|_| r.fold())
                .collect::<Option<Vec<_>>>()?;
            stages.push(LaterStage {
                root,
                ood,
                folds,
                query: ExtQuery {
                    leaves: Vec::new(),
                    siblings: Vec::new(),
                },
            });
        }
        let final_coeffs = (0..(1usize << schedule.early_stop_vars) + 2)
            .map(|_| r.fp5())
            .collect::<Option<Vec<_>>>()?;
        let last = dims.len() - 1;
        stages[last - 1].query = r.ext_query(&dims[last])?;
        *pos = r.pos;
        Some(Self {
            mask_evals,
            stage0_folds,
            mask_claim,
            stage0_shares: stage0_shares?,
            stages,
            final_coeffs,
        })
    }
}

// ============================================================================
// The event Good (conditions on Stage-0 challenges)
// ============================================================================

/// Condition (G2): each `omega_j^(2^step_vars)` lies outside `F_p` and no two are Frobenius conjugates.
pub fn mask_points_good(omegas: &[Fp5], step_vars: usize) -> bool {
    let z: Vec<Fp5> = omegas
        .iter()
        .map(|w| (0..step_vars).fold(*w, |acc, _| acc.square()))
        .collect();
    z.iter().all(|x| !x.is_base())
        && (0..z.len()).all(|i| (0..i).all(|j| (0..5).all(|k| z[i].frobenius_pow(k) != z[j])))
}

/// Condition (G3): `phi != 0` and `1 + phi x != 0` for each current mask point `x`.
pub fn fold_challenge_good(phi: Fp5, xs: &[Fp5]) -> bool {
    !phi.is_zero() && xs.iter().all(|&x| !(Fp5::ONE + phi * x).is_zero())
}

// ============================================================================
// Kernels
// ============================================================================

/// Continuation of point terms `sum_j w_j x_j^i` for `i = from..from + count`.
pub fn point_tail(points: &[(Fp5, Fp5)], from: usize, count: usize) -> Vec<Fp5> {
    let mut out = vec![Fp5::ZERO; count];
    for &(w, x) in points {
        let mut t = w * x.pow(from as u64);
        for slot in &mut out {
            *slot += t;
            t *= x;
        }
    }
    out
}

/// `kernel[i] += sum_j w_j x_j^i`.
pub fn add_points(kernel: &mut [Fp5], points: &[(Fp5, Fp5)]) {
    par_chunks_mut(kernel, |off, part| {
        for &(w, x) in points {
            let mut t = w * x.pow(off as u64);
            if x.is_base() {
                let y = x.0[0];
                for slot in part.iter_mut() {
                    *slot += t;
                    t = t.mul_base(y);
                }
            } else {
                for slot in part.iter_mut() {
                    *slot += t;
                    t *= x;
                }
            }
        }
    });
}

pub fn extend_kernel(kernel: &mut Vec<Fp5>, points: &[(Fp5, Fp5)], len: usize) {
    if kernel.len() < len {
        let tail = point_tail(points, kernel.len(), len - kernel.len());
        kernel.extend(tail);
    }
}

pub fn fold_points(points: &mut [(Fp5, Fp5)], phi: Fp5) {
    for (w, x) in points {
        *w *= Fp5::ONE + phi * *x;
        *x = x.square();
    }
}

pub(crate) struct KernelTerms<'a> {
    tensor: Vec<(Fp5, &'a [Fp5])>,
    consumed: usize,
    pub(crate) points: Vec<(Fp5, Fp5)>,
}

impl<'a> KernelTerms<'a> {
    pub(crate) fn new(terms: &'a [TensorTerm]) -> Self {
        Self {
            tensor: terms
                .iter()
                .map(|t| (t.weight, t.point.as_slice()))
                .collect(),
            consumed: 0,
            points: Vec::new(),
        }
    }

    fn fold(&mut self, phi: Fp5) {
        for (w, point) in &mut self.tensor {
            if let Some(&r) = point.get(self.consumed) {
                *w *= Fp5::ONE + phi * r;
            }
        }
        self.consumed += 1;
        fold_points(&mut self.points, phi);
    }

    pub(crate) fn apply(&self, coeffs: &[Fp5]) -> Fp5 {
        let mut acc = Fp5::ZERO;
        for &(w, point) in &self.tensor {
            let rest = point.get(self.consumed..).unwrap_or(&[]);
            let mut vals = coeffs[..1 << rest.len()].to_vec();
            for &r in rest {
                vals = vals
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|p| p[0] + r * p[1])
                    .collect();
            }
            acc += w * vals[0];
        }
        for &(w, x) in &self.points {
            acc += w * coeffs.iter().rev().fold(Fp5::ZERO, |a, &c| a * x + c);
        }
        acc
    }
}

// ============================================================================
// The affine fold
// ============================================================================

pub fn next_claim(wire: &[Fp5; 5], claim: Fp5, phi: Fp5, [theta, alpha, beta]: [Fp5; 3]) -> Fp5 {
    let [sigma_even, tau_01, tau_10, c_f, c_g] = *wire;
    Fp5::from(qsag_whir_verified::cwyz_bridge_claim_step_fp5(
        sigma_even.into(),
        tau_01.into(),
        tau_10.into(),
        c_f.into(),
        c_g.into(),
        claim.into(),
        phi.into(),
        theta.into(),
        alpha.into(),
        beta.into(),
    ))
}

pub(crate) fn verify_fold<C: Channel>(
    wire: &[Fp5; 5],
    claim: &mut Fp5,
    kernel: &mut KernelTerms<'_>,
    ch: &mut C,
) -> [Fp5; 3] {
    ch.absorb_fp5_slice(b"FOLD_A", &wire[..3]);
    let phi = ch.squeeze_fp5(b"FOLD_PHI");
    ch.absorb_fp5_slice(b"FOLD_B", &wire[3..]);
    let chals = [
        ch.squeeze_fp5(b"FOLD_THETA"),
        ch.squeeze_fp5(b"FOLD_ALPHA"),
        ch.squeeze_fp5(b"FOLD_BETA"),
    ];
    *claim = next_claim(wire, *claim, phi, chals);
    kernel.fold(phi);
    chals
}

/// Prover folding state for WHIR stages (`kernel`, `points`, `claim`).
pub struct Folding {
    pub kernel: Vec<Fp5>,
    pub points: Vec<(Fp5, Fp5)>,
    pub claim: Fp5,
}

type Folded = (Vec<Fp5>, [Fp5; 5], [Fp5; 3]);

pub(crate) fn prove_fold<T: Coef, C: Channel>(
    poly: &[T],
    st: &mut Folding,
    guarded: usize,
    ch: &mut C,
) -> Result<Folded, MaskRankDeficient> {
    let m = poly.len();
    assert_eq!(st.kernel.len(), m);
    let half = m.div_ceil(2);
    let tail = point_tail(&st.points, m, 3);
    let kernel = &st.kernel;
    let k_at = |i: usize| if i < m { kernel[i] } else { tail[i - m] };
    let p_at = |i: usize| if i < m { poly[i] } else { T::ZERO };

    let [sigma_even, tau_01, tau_10] = par_sum(half, |range| {
        let mut acc = [Fp5::ZERO; 3];
        for n in range {
            let (f, g) = (p_at(2 * n), p_at(2 * n + 1));
            let (ke, ko) = (k_at(2 * n), k_at(2 * n + 1));
            acc[0] += f.scale(ke);
            acc[1] += f.scale(ko);
            acc[2] += g.scale(ke);
        }
        acc
    });
    ch.absorb_fp5_slice(b"FOLD_A", &[sigma_even, tau_01, tau_10]);
    let phi = ch.squeeze_fp5(b"FOLD_PHI");
    if guarded > 0 {
        let xs: Vec<Fp5> = st.points[..guarded].iter().map(|p| p.1).collect();
        if !fold_challenge_good(phi, &xs) {
            return Err(MaskRankDeficient);
        }
    }

    let mut v = vec![Fp5::ZERO; half + 1];
    par_chunks_mut(&mut v, |off, part| {
        for (i, slot) in part.iter_mut().enumerate() {
            let n = off + i;
            *slot = k_at(2 * n) + phi * k_at(2 * n + 1);
        }
    });
    let [c_f, c_g] = par_sum(half, |range| {
        let mut acc = [Fp5::ZERO; 2];
        for n in range {
            acc[0] += p_at(2 * n).scale(v[n + 1]);
            acc[1] += p_at(2 * n + 1).scale(v[n + 1]);
        }
        acc
    });
    ch.absorb_fp5_slice(b"FOLD_B", &[c_f, c_g]);
    let chals = [
        ch.squeeze_fp5(b"FOLD_THETA"),
        ch.squeeze_fp5(b"FOLD_ALPHA"),
        ch.squeeze_fp5(b"FOLD_BETA"),
    ];
    let [theta, alpha, beta] = chals;
    let wire = [sigma_even, tau_01, tau_10, c_f, c_g];

    let h_at = |n: usize| p_at(2 * n).lift() + p_at(2 * n + 1).scale(theta);
    let mut next = vec![Fp5::ZERO; half + 1];
    par_chunks_mut(&mut next, |off, part| {
        for (i, slot) in part.iter_mut().enumerate() {
            let n = off + i;
            let mut acc = Fp5::ZERO;
            if n < half {
                acc = p_at(2 * n + 1).lift() + alpha * h_at(n);
            }
            if n > 0 {
                acc += beta * h_at(n - 1);
            }
            *slot = acc;
        }
    });

    st.claim = next_claim(&wire, st.claim, phi, chals);
    st.kernel = v;
    fold_points(&mut st.points, phi);
    Ok((next, wire, chals))
}

// ============================================================================
// Stage 0, rounds 7 to 10
// ============================================================================

pub(in crate::zk_hem) struct Stage0Reduced {
    pub(in crate::zk_hem) mask_evals: Vec<Fp5>,
    pub(in crate::zk_hem) folds: Vec<[Fp5; 5]>,
    pub(in crate::zk_hem) mask_claim: Fp5,
    pub(in crate::zk_hem) g: Vec<Fp5>,
    pub(in crate::zk_hem) st: Folding,
    pub(in crate::zk_hem) chals: Vec<[Fp5; 3]>,
    pub(in crate::zk_hem) beta_r: Fp5,
}

pub(in crate::zk_hem) fn stage0_reduce<C: Channel>(
    coeffs: &[Goldilocks],
    mask: &[Fp5],
    step_vars: usize,
    points: usize,
    mut kernel: Vec<Fp5>,
    claim: Fp5,
    ch: &mut C,
) -> Result<Stage0Reduced, MaskRankDeficient> {
    assert_eq!(kernel.len(), coeffs.len());
    let omegas: Vec<Fp5> = (0..points).map(|_| ch.squeeze_fp5(b"MASK_POINT")).collect();
    if !mask_points_good(&omegas, step_vars) {
        return Err(MaskRankDeficient);
    }
    let mut mask_evals = Vec::with_capacity(points);
    for chunk in omegas.chunks(5) {
        let mut xs = [Fp5::ZERO; 5];
        xs[..chunk.len()].copy_from_slice(chunk);
        mask_evals.extend_from_slice(&eval_poly(coeffs, xs)[..chunk.len()]);
    }
    ch.absorb_fp5_slice(b"MASK_EVAL", &mask_evals);
    let weights: Vec<Fp5> = (0..points)
        .map(|_| ch.squeeze_fp5(b"MASK_WEIGHT"))
        .collect();
    if weights.iter().any(|w| w.is_zero()) {
        return Err(MaskRankDeficient);
    }
    let point_terms: Vec<(Fp5, Fp5)> = weights.iter().copied().zip(omegas).collect();
    add_points(&mut kernel, &point_terms);
    let mut st = Folding {
        kernel,
        claim: mask_evals
            .iter()
            .zip(&weights)
            .fold(claim, |acc, (&a, &w)| acc + w * a),
        points: point_terms,
    };

    let mut folds = Vec::with_capacity(step_vars);
    let mut chals = Vec::with_capacity(step_vars);
    let (mut poly, wire, c) = prove_fold(coeffs, &mut st, points, ch)?;
    folds.push(wire);
    chals.push(c);
    for _ in 1..step_vars {
        let folded = prove_fold(&poly, &mut st, points, ch);
        qsag_asm::volatile_fill(&mut poly, Fp5::ZERO);
        let (next, wire, c) = folded?;
        poly = next;
        folds.push(wire);
        chals.push(c);
    }

    extend_kernel(&mut st.kernel, &st.points, mask.len());
    let kernel = &st.kernel;
    let [mask_claim] = par_sum(mask.len(), |range| {
        [range.fold(Fp5::ZERO, |acc, i| acc + mask[i] * kernel[i])]
    });
    ch.absorb_fp5_slice(b"MASK_CLAIM", &[mask_claim]);
    let beta_r = ch.squeeze_fp5_nonzero(b"MASK_BETA");
    let mut g = vec![Fp5::ZERO; mask.len()];
    par_chunks_mut(&mut g, |off, part| {
        for (i, slot) in part.iter_mut().enumerate() {
            let n = off + i;
            *slot = poly.get(n).copied().unwrap_or(Fp5::ZERO) + beta_r * mask[n];
        }
    });
    qsag_asm::volatile_fill(&mut poly, Fp5::ZERO);
    st.claim += beta_r * mask_claim;
    Ok(Stage0Reduced {
        mask_evals,
        folds,
        mask_claim,
        g,
        st,
        chals,
        beta_r,
    })
}

fn stage0_reduce_verify_fields<C: Channel>(
    mask_evals: &[Fp5; MASK_POINTS],
    stage0_folds: &[[Fp5; 5]],
    mask_claim: Fp5,
    claim: &mut Fp5,
    kernel: &mut KernelTerms<'_>,
    ch: &mut C,
) -> (Vec<[Fp5; 3]>, Fp5) {
    let omegas: [Fp5; MASK_POINTS] = core::array::from_fn(|_| ch.squeeze_fp5(b"MASK_POINT"));
    ch.absorb_fp5_slice(b"MASK_EVAL", mask_evals);
    for (omega, &a) in omegas.into_iter().zip(mask_evals) {
        let w = ch.squeeze_fp5(b"MASK_WEIGHT");
        *claim += w * a;
        kernel.points.push((w, omega));
    }
    let chals = stage0_folds
        .iter()
        .map(|wire| verify_fold(wire, claim, kernel, ch))
        .collect();
    ch.absorb_fp5_slice(b"MASK_CLAIM", &[mask_claim]);
    let beta_r = ch.squeeze_fp5_nonzero(b"MASK_BETA");
    *claim += beta_r * mask_claim;
    (chals, beta_r)
}

// ============================================================================
// Stage 0, round 12: opened fibers (single and split)
// ============================================================================

/// The prover's answer to the Stage-0 queries `idx` (sorted, distinct) for one commitment.
pub fn stage0_answer(st: &Committed, idx: &[usize]) -> Stage0Query {
    let hasher = Hasher::new(st.profile);
    let d0 = &st.dims[0];
    Stage0Query {
        leaves: idx
            .iter()
            .map(|&j| Stage0Leaf {
                salt: hasher.salt(&st.salt_seed, j as u32),
                z: fiber(&st.z_code, d0, j),
                r: st.r_code[j],
            })
            .collect(),
        siblings: st.tree.open(idx),
    }
}

/// The Stage-0 share trees of one opening: tree `p` has nonce `tree_nonces[p]` and root
/// `roots[p]`.
#[derive(Clone, Copy)]
struct Stage0Trees<'a> {
    hasher: Hasher,
    tree_nonces: &'a [[u8; TREE_NONCE_BYTES]],
    roots: &'a [Digest],
}

/// Check `shares` against `trees` and fold the summed Stage-0 fibers to values of
/// `g = P_s + beta_R R`.
fn stage0_check_split_fibers(
    trees: Stage0Trees<'_>,
    d0: &StageDims,
    idx: &[usize],
    shares: &[Stage0Query],
    chals: &[[Fp5; 3]],
    beta_r: Fp5,
) -> Option<Vec<(Goldilocks, Fp5)>> {
    let Stage0Trees {
        hasher,
        tree_nonces,
        roots,
    } = trees;
    if shares.len() != roots.len()
        || tree_nonces.len() != roots.len()
        || !(1..=MAX_STAGE0_SHARES).contains(&roots.len())
    {
        return None;
    }
    for ((nonce, root), query) in tree_nonces.iter().zip(roots).zip(shares) {
        if query.leaves.len() != idx.len() || query.leaves.iter().any(|l| l.z.len() != d0.arity()) {
            return None;
        }
        let digests: Vec<(usize, Digest)> = idx
            .iter()
            .zip(&query.leaves)
            .map(|(&j, leaf)| {
                (
                    j,
                    hasher.leaf_stage0(nonce, j as u32, &leaf.salt, &leaf.z, leaf.r),
                )
            })
            .collect();
        if !verify_multiproof(hasher, 0, d0.log_leaves(), root, &digests, &query.siblings) {
            return None;
        }
    }
    Some(
        idx.iter()
            .enumerate()
            .map(|(q_pos, &j)| {
                let mut z_sum = vec![Goldilocks::ZERO; d0.arity()];
                let mut r_sum = Fp5::ZERO;
                for share in shares {
                    let leaf = &share.leaves[q_pos];
                    for (acc, &v) in z_sum.iter_mut().zip(&leaf.z) {
                        *acc += v;
                    }
                    r_sum += leaf.r;
                }
                let x0 = d0.fiber_base(j);
                let vals = z_sum.into_iter().map(Fp5::from_base).collect();
                let folded = fold_fiber(vals, x0, chals);
                (d0.fiber_image(j), folded + beta_r * r_sum)
            })
            .collect(),
    )
}

fn ext_check_fibers(
    hasher: Hasher,
    stage: usize,
    root: &Digest,
    dims: &StageDims,
    idx: &[usize],
    query: &ExtQuery,
    chals: &[[Fp5; 3]],
) -> Option<Vec<(Goldilocks, Fp5)>> {
    if query.leaves.len() != idx.len() || query.leaves.iter().any(|l| l.len() != dims.arity()) {
        return None;
    }
    let digests: Vec<(usize, Digest)> = idx
        .iter()
        .zip(&query.leaves)
        .map(|(&j, leaf)| (j, hasher.leaf_ext(stage as u8, j as u32, leaf)))
        .collect();
    if !verify_multiproof(
        hasher,
        stage as u8,
        dims.log_leaves(),
        root,
        &digests,
        &query.siblings,
    ) {
        return None;
    }
    Some(
        idx.iter()
            .zip(&query.leaves)
            .map(|(&j, leaf)| {
                (
                    dims.fiber_image(j),
                    fold_fiber(leaf.clone(), dims.fiber_base(j), chals),
                )
            })
            .collect(),
    )
}

// ============================================================================
// Opening and verification
// ============================================================================

pub(crate) fn stage_claims<C: Channel>(
    ood_points: [Fp5; LATER_OOD_POINTS],
    ood: &[Fp5; LATER_OOD_POINTS],
    shifts: &[(Goldilocks, Fp5)],
    ch: &mut C,
) -> (Vec<(Fp5, Fp5)>, Fp5) {
    let vals: Vec<Fp5> = shifts.iter().map(|s| s.1).collect();
    ch.absorb_fp5_slice(b"QUERY_VALUES", &vals);
    let mut terms = Vec::with_capacity(LATER_OOD_POINTS + shifts.len());
    let mut delta = Fp5::ZERO;
    for (z, &e) in ood_points.into_iter().zip(ood) {
        let xi = ch.squeeze_fp5(b"OOD_WEIGHT");
        terms.push((xi, z));
        delta += xi * e;
    }
    let gamma = ch.squeeze_fp5(b"QUERY_GAMMA");
    let mut w = gamma;
    for &(y, v) in shifts {
        terms.push((w, Fp5::from_base(y)));
        delta += w * v;
        w *= gamma;
    }
    (terms, delta)
}

/// Complete WHIR Stages `1..` from a public masked Stage-0 polynomial `g` and a callback
/// `answer_stage0` supplying the `committers` Stage-0 share openings. Every Stage-0 multiproof
/// and consistency against `g` is checked before returning.
#[allow(clippy::too_many_arguments)]
pub fn open_from_reduced_split<C: Channel>(
    profile: Profile,
    log_cells: usize,
    schedule: &Schedule,
    tree_nonces: &[[u8; TREE_NONCE_BYTES]],
    roots: &[Digest],
    mask_evals: [Fp5; MASK_POINTS],
    stage0_folds: Vec<[Fp5; 5]>,
    mask_claim: Fp5,
    mut poly: Vec<Fp5>,
    mut fold: Folding,
    mut prev_chals: Vec<[Fp5; 3]>,
    beta_r: Fp5,
    ch: &mut C,
    answer_stage0: &mut dyn FnMut(&[usize]) -> Option<Vec<Stage0Query>>,
) -> Option<SplitOpening> {
    let dims = stage_dims(log_cells, schedule)?;
    let hasher = Hasher::new(profile);
    let mut stage0_shares = None;
    let mut stages: Vec<LaterStage> = Vec::with_capacity(dims.len() - 1);
    let mut prev_oracle: Option<(Vec<Fp5>, MerkleTree)> = None;
    for (i, d) in dims.iter().enumerate().skip(1) {
        let code = encode_ext(&poly, d.log_domain);
        let mut leaves = vec![[0u8; DIGEST_BYTES]; d.fibers];
        crate::pcs::fill_indexed(&mut leaves, |j| {
            hasher.leaf_ext(i as u8, j as u32, &fiber(&code, d, j))
        });
        let tree = MerkleTree::build(hasher, i as u8, leaves);
        let root = tree.root();
        ch.absorb(b"STAGE_ROOT", &root);
        let ood_points: [Fp5; LATER_OOD_POINTS] =
            core::array::from_fn(|_| ch.squeeze_fp5(b"OOD_POINT"));
        let ood = eval_poly(&poly, ood_points);
        ch.absorb_fp5_slice(b"OOD_EVAL", &ood);

        let before = &dims[i - 1];
        let idx = ch.squeeze_distinct_indices(b"QUERY", before.fibers, before.queries);
        let shifts: Vec<(Goldilocks, Fp5)> = match &prev_oracle {
            None => {
                let shares = answer_stage0(&idx)?;
                let shifts = stage0_check_split_fibers(
                    Stage0Trees {
                        hasher,
                        tree_nonces,
                        roots,
                    },
                    before,
                    &idx,
                    &shares,
                    &prev_chals,
                    beta_r,
                )?;
                if !shifts.iter().all(|&(y, v)| eval_at_base(&poly, y) == v) {
                    return None;
                }
                stage0_shares = Some(shares);
                shifts
            }
            Some((prev_code, prev_tree)) => {
                let query = ExtQuery {
                    leaves: idx.iter().map(|&j| fiber(prev_code, before, j)).collect(),
                    siblings: prev_tree.open(&idx),
                };
                let shifts = idx
                    .iter()
                    .zip(&query.leaves)
                    .map(|(&j, leaf)| {
                        (
                            before.fiber_image(j),
                            fold_fiber(leaf.clone(), before.fiber_base(j), &prev_chals),
                        )
                    })
                    .collect();
                stages[i - 2].query = query;
                shifts
            }
        };
        let (terms, delta) = stage_claims(ood_points, &ood, &shifts, ch);
        add_points(&mut fold.kernel, &terms);
        fold.points.extend(terms);
        fold.claim += delta;

        let mut folds = Vec::with_capacity(d.step_vars);
        prev_chals = Vec::with_capacity(d.step_vars);
        for _ in 0..d.step_vars {
            let folded = prove_fold(&poly, &mut fold, 0, ch).ok()?;
            qsag_asm::volatile_fill(&mut poly, Fp5::ZERO);
            let (next, wire, c) = folded;
            poly = next;
            folds.push(wire);
            prev_chals.push(c);
        }
        stages.push(LaterStage {
            root,
            ood,
            folds,
            query: ExtQuery {
                leaves: Vec::new(),
                siblings: Vec::new(),
            },
        });
        if let Some((mut old_code, _)) = prev_oracle.replace((code, tree)) {
            qsag_asm::volatile_fill(&mut old_code, Fp5::ZERO);
        }
    }

    ch.absorb_fp5_slice(b"FINAL_POLY", &poly);
    let last = dims.len() - 1;
    let d = &dims[last];
    let idx = ch.squeeze_distinct_indices(b"QUERY", d.fibers, d.queries);
    let (mut code, tree) = prev_oracle.take().expect("at least two stages");
    stages[last - 1].query = ExtQuery {
        leaves: idx.iter().map(|&j| fiber(&code, d, j)).collect(),
        siblings: tree.open(&idx),
    };
    qsag_asm::volatile_fill(&mut code, Fp5::ZERO);
    Some(SplitOpening {
        mask_evals,
        stage0_folds,
        mask_claim,
        stage0_shares: stage0_shares?,
        stages,
        final_coeffs: poly,
    })
}

/// Open a single Stage-0 commitment against `<coeffs, kernel> = claim`.
pub fn open<C: Channel>(
    st: &Committed,
    kernel: Vec<Fp5>,
    claim: Fp5,
    ch: &mut C,
) -> Result<Opening, MaskRankDeficient> {
    open_with(st, kernel, claim, ch, cpu_oracle)
}

fn cpu_oracle(
    i: usize,
    d: &StageDims,
    poly: &[Fp5],
    hasher: Hasher,
) -> Result<(Vec<Fp5>, MerkleTree), MaskRankDeficient> {
    let phase = crate::profile::span("zkhem2_open_encode");
    let code = encode_ext(poly, d.log_domain);
    drop(phase);
    let _phase = crate::profile::span("zkhem2_open_merkle");
    let mut leaves = vec![[0u8; DIGEST_BYTES]; d.fibers];
    crate::pcs::fill_indexed(&mut leaves, |j| {
        hasher.leaf_ext(i as u8, j as u32, &fiber(&code, d, j))
    });
    Ok((code, MerkleTree::build(hasher, i as u8, leaves)))
}

impl From<MaskRankDeficient> for super::protocol::ZkHemV2Error {
    fn from(_: MaskRankDeficient) -> Self {
        Self::MaskRankDeficient
    }
}
pub(crate) fn open_prover<C: Channel>(
    st: &Committed,
    kernel: Vec<Fp5>,
    claim: Fp5,
    ch: &mut C,
    #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
) -> Result<Opening, super::protocol::ZkHemV2Error> {
    #[cfg(feature = "vulkan")]
    if let Some(gpu) = gpu {
        return open_with(st, kernel, claim, ch, |i, d, poly, hasher| {
            let code = SecretBuffer::new(
                crate::vulkan::encode_ext(gpu, poly, d.log_domain, SHIFT)
                    .map_err(super::protocol::ZkHemV2Error::Vulkan)?,
            );
            let framing = qsag_accel::vulkan::CanopyProfile::ZkExtension {
                midstate: hasher.tree_midstate(),
                turbo: st.profile.uses_turboshake(),
            };
            let tree = crate::vulkan::tree(
                gpu,
                hasher,
                framing,
                i as u8,
                d.arity(),
                &crate::vulkan::ext_words(&code),
            )
            .map_err(super::protocol::ZkHemV2Error::Vulkan)?;
            Ok((code.into_inner(), tree))
        });
    }
    Ok(open(st, kernel, claim, ch)?)
}

fn open_with<C: Channel, Err: From<MaskRankDeficient>>(
    st: &Committed,
    kernel: Vec<Fp5>,
    claim: Fp5,
    ch: &mut C,
    oracle: impl Fn(usize, &StageDims, &[Fp5], Hasher) -> Result<(Vec<Fp5>, MerkleTree), Err>,
) -> Result<Opening, Err> {
    let _phase = crate::profile::span("zkhem2_open");
    let hasher = Hasher::new(st.profile);
    let dims = &st.dims;
    let phase = crate::profile::span("zkhem2_open_stage0_folds");
    let red = stage0_reduce(
        &st.coeffs,
        &st.mask,
        dims[0].step_vars,
        MASK_POINTS,
        kernel,
        claim,
        ch,
    )?;
    drop(phase);
    let Stage0Reduced {
        mask_evals,
        folds: stage0_folds,
        mask_claim,
        g: poly,
        st: mut fold,
        chals: mut prev_chals,
        beta_r,
    } = red;
    let mut poly = SecretBuffer::new(poly);
    let mut stage0_query = None;
    let mut stages: Vec<LaterStage> = Vec::with_capacity(dims.len() - 1);
    let mut prev_oracle: Option<(SecretBuffer<Vec<Fp5>>, MerkleTree)> = None;
    for (i, d) in dims.iter().enumerate().skip(1) {
        let (code, tree) = oracle(i, d, &poly, hasher)?;
        let code = SecretBuffer::new(code);
        let root = tree.root();
        ch.absorb(b"STAGE_ROOT", &root);
        let ood_points: [Fp5; LATER_OOD_POINTS] =
            core::array::from_fn(|_| ch.squeeze_fp5(b"OOD_POINT"));
        let ood = eval_poly(&poly, ood_points);
        ch.absorb_fp5_slice(b"OOD_EVAL", &ood);

        let before = &dims[i - 1];
        let idx = ch.squeeze_distinct_indices(b"QUERY", before.fibers, before.queries);
        let shifts: Vec<(Goldilocks, Fp5)> = match &prev_oracle {
            None => {
                let query = stage0_answer(st, &idx);
                let shifts = idx
                    .iter()
                    .zip(&query.leaves)
                    .map(|(&j, leaf)| {
                        let vals = leaf.z.iter().map(|&z| Fp5::from_base(z)).collect();
                        let folded = fold_fiber(vals, before.fiber_base(j), &prev_chals);
                        (before.fiber_image(j), folded + beta_r * leaf.r)
                    })
                    .collect();
                stage0_query = Some(query);
                shifts
            }
            Some((prev_code, prev_tree)) => {
                let query = ExtQuery {
                    leaves: idx.iter().map(|&j| fiber(prev_code, before, j)).collect(),
                    siblings: prev_tree.open(&idx),
                };
                let shifts = idx
                    .iter()
                    .zip(&query.leaves)
                    .map(|(&j, leaf)| {
                        (
                            before.fiber_image(j),
                            fold_fiber(leaf.clone(), before.fiber_base(j), &prev_chals),
                        )
                    })
                    .collect();
                stages[i - 2].query = query;
                shifts
            }
        };
        let (terms, delta) = stage_claims(ood_points, &ood, &shifts, ch);
        let _folds = crate::profile::span("zkhem2_open_points_and_folds");
        add_points(&mut fold.kernel, &terms);
        fold.points.extend(terms);
        fold.claim += delta;

        let mut folds = Vec::with_capacity(d.step_vars);
        prev_chals = Vec::with_capacity(d.step_vars);
        for _ in 0..d.step_vars {
            let folded = prove_fold(&poly, &mut fold, 0, ch);
            let (next, wire, c) = folded?;
            poly = SecretBuffer::new(next);
            folds.push(wire);
            prev_chals.push(c);
        }
        stages.push(LaterStage {
            root,
            ood,
            folds,
            query: ExtQuery {
                leaves: Vec::new(),
                siblings: Vec::new(),
            },
        });
        prev_oracle = Some((code, tree));
    }

    ch.absorb_fp5_slice(b"FINAL_POLY", &poly);
    let last = dims.len() - 1;
    let d = &dims[last];
    let idx = ch.squeeze_distinct_indices(b"QUERY", d.fibers, d.queries);
    let (code, tree) = prev_oracle.take().expect("at least two stages");
    stages[last - 1].query = ExtQuery {
        leaves: idx.iter().map(|&j| fiber(&code, d, j)).collect(),
        siblings: tree.open(&idx),
    };
    drop(code);
    let mut mask_eval_array = [Fp5::ZERO; MASK_POINTS];
    mask_eval_array.copy_from_slice(&mask_evals);
    Ok(Opening {
        mask_evals: mask_eval_array,
        stage0_folds,
        mask_claim,
        stage0_query: stage0_query.expect("at least two stages"),
        stages,
        final_coeffs: poly.into_inner(),
    })
}

/// Verify a single-committer [`Opening`] against `(tree_nonce, root)`.
#[allow(clippy::too_many_arguments)]
pub fn verify<C: Channel>(
    profile: Profile,
    tree_nonce: &[u8; TREE_NONCE_BYTES],
    root: &Digest,
    log_cells: usize,
    schedule: &Schedule,
    terms: &[TensorTerm],
    claim: Fp5,
    opening: &Opening,
    ch: &mut C,
) -> bool {
    verify_inner(
        profile,
        core::slice::from_ref(tree_nonce),
        core::slice::from_ref(root),
        log_cells,
        schedule,
        terms,
        claim,
        &opening.mask_evals,
        &opening.stage0_folds,
        opening.mask_claim,
        core::slice::from_ref(&opening.stage0_query),
        &opening.stages,
        &opening.final_coeffs,
        ch,
    )
}

/// Verify a multi-committer [`SplitOpening`] against `(tree_nonces, roots)`.
#[allow(clippy::too_many_arguments)]
pub fn verify_split<C: Channel>(
    profile: Profile,
    tree_nonces: &[[u8; TREE_NONCE_BYTES]],
    roots: &[Digest],
    log_cells: usize,
    schedule: &Schedule,
    terms: &[TensorTerm],
    claim: Fp5,
    opening: &SplitOpening,
    ch: &mut C,
) -> bool {
    verify_inner(
        profile,
        tree_nonces,
        roots,
        log_cells,
        schedule,
        terms,
        claim,
        &opening.mask_evals,
        &opening.stage0_folds,
        opening.mask_claim,
        &opening.stage0_shares,
        &opening.stages,
        &opening.final_coeffs,
        ch,
    )
}

#[allow(clippy::too_many_arguments)]
fn verify_inner<C: Channel>(
    profile: Profile,
    tree_nonces: &[[u8; TREE_NONCE_BYTES]],
    roots: &[Digest],
    log_cells: usize,
    schedule: &Schedule,
    terms: &[TensorTerm],
    claim: Fp5,
    mask_evals: &[Fp5; MASK_POINTS],
    stage0_folds: &[[Fp5; 5]],
    mask_claim: Fp5,
    stage0_shares: &[Stage0Query],
    stages: &[LaterStage],
    final_coeffs: &[Fp5],
    ch: &mut C,
) -> bool {
    let Some(dims) = stage_dims(log_cells, schedule) else {
        return false;
    };
    let hasher = Hasher::new(profile);
    if !(1..=MAX_STAGE0_SHARES).contains(&roots.len())
        || tree_nonces.len() != roots.len()
        || stage0_shares.len() != roots.len()
        || terms.iter().any(|t| t.point.len() > log_cells)
        || stage0_folds.len() != dims[0].step_vars
        || stages.len() + 1 != dims.len()
        || stages
            .iter()
            .zip(&dims[1..])
            .any(|(stage, d)| stage.folds.len() != d.step_vars)
        || final_coeffs.len() != (1usize << schedule.early_stop_vars) + 2
    {
        return false;
    }
    let mut claim = claim;
    let mut kernel = KernelTerms::new(terms);
    let (mut prev_chals, beta_r) = stage0_reduce_verify_fields(
        mask_evals,
        stage0_folds,
        mask_claim,
        &mut claim,
        &mut kernel,
        ch,
    );

    for i in 1..dims.len() {
        let stage = &stages[i - 1];
        ch.absorb(b"STAGE_ROOT", &stage.root);
        let ood_points: [Fp5; LATER_OOD_POINTS] =
            core::array::from_fn(|_| ch.squeeze_fp5(b"OOD_POINT"));
        ch.absorb_fp5_slice(b"OOD_EVAL", &stage.ood);

        let before = &dims[i - 1];
        let idx = ch.squeeze_distinct_indices(b"QUERY", before.fibers, before.queries);
        let shifts = if i == 1 {
            stage0_check_split_fibers(
                Stage0Trees {
                    hasher,
                    tree_nonces,
                    roots,
                },
                before,
                &idx,
                stage0_shares,
                &prev_chals,
                beta_r,
            )
        } else {
            let prev = &stages[i - 2];
            ext_check_fibers(
                hasher,
                i - 1,
                &prev.root,
                before,
                &idx,
                &prev.query,
                &prev_chals,
            )
        };
        let Some(shifts) = shifts else {
            return false;
        };
        let (new_terms, delta) = stage_claims(ood_points, &stage.ood, &shifts, ch);
        kernel.points.extend(new_terms);
        claim += delta;

        prev_chals = stage
            .folds
            .iter()
            .map(|wire| verify_fold(wire, &mut claim, &mut kernel, ch))
            .collect();
    }

    ch.absorb_fp5_slice(b"FINAL_POLY", final_coeffs);
    if !qsag_whir_verified::verify_ood_pin_eq_fp5(kernel.apply(final_coeffs).into(), claim.into()) {
        return false;
    }
    let last = dims.len() - 1;
    let d = &dims[last];
    let idx = ch.squeeze_distinct_indices(b"QUERY", d.fibers, d.queries);
    let stage = &stages[last - 1];
    let Some(values) = ext_check_fibers(
        hasher,
        last,
        &stage.root,
        d,
        &idx,
        &stage.query,
        &prev_chals,
    ) else {
        return false;
    };
    values
        .iter()
        .all(|&(y, v)| verify_at_base_pin(final_coeffs, y, v))
}

#[cfg(test)]
pub(super) mod tests {
    use super::super::hash::Transcript;
    use super::super::params::StageSpec;
    use super::*;

    const P: u64 = crate::field::GOLDILOCKS_PRIME;

    struct Rng(u64);

    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }
        fn base(&mut self) -> Goldilocks {
            Goldilocks::from_u64_reduced(self.next_u64())
        }
        fn fp5(&mut self) -> Fp5 {
            Fp5(core::array::from_fn(|_| self.base()))
        }
    }

    struct FixedCoins {
        rng: Rng,
        indices: Vec<usize>,
    }

    impl Channel for FixedCoins {
        fn absorb(&mut self, _: &[u8], _: &[u8]) {}
        fn squeeze_fp5(&mut self, _: &[u8]) -> Fp5 {
            self.rng.fp5()
        }
        fn squeeze_distinct_indices(&mut self, _: &[u8], n: usize, count: usize) -> Vec<usize> {
            self.indices
                .iter()
                .copied()
                .filter(|&i| i < n)
                .take(count)
                .collect()
        }
    }

    fn toy_schedule() -> Schedule {
        Schedule {
            early_stop_vars: 3,
            stages: vec![
                StageSpec {
                    blowup: 4,
                    step_vars: 2,
                    num_queries: 6,
                },
                StageSpec {
                    blowup: 16,
                    step_vars: 2,
                    num_queries: 5,
                },
                StageSpec {
                    blowup: 64,
                    step_vars: 1,
                    num_queries: 4,
                },
            ],
        }
    }

    const LOG_CELLS: usize = 8;

    fn kernel_of(terms: &[TensorTerm], log_cells: usize) -> Vec<Fp5> {
        let mut k = vec![Fp5::ZERO; 1 << log_cells];
        for t in terms {
            for (i, slot) in k.iter_mut().enumerate().take(1 << t.point.len()) {
                *slot += t
                    .point
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| (i >> j) & 1 == 1)
                    .fold(t.weight, |acc, (_, &r)| acc * r);
            }
        }
        k
    }

    fn dot(c: &[Goldilocks], k: &[Fp5]) -> Fp5 {
        c.iter()
            .zip(k)
            .fold(Fp5::ZERO, |acc, (&c, &k)| acc + k.mul_base(c))
    }

    struct Fixture {
        profile: Profile,
        schedule: Schedule,
        st: Committed,
        terms: Vec<TensorTerm>,
        claim: Fp5,
    }

    fn fixture(profile: Profile, seed: u64) -> Fixture {
        let mut rng = Rng(seed);
        let schedule = toy_schedule();
        let coeffs: Vec<Goldilocks> = (0..1 << LOG_CELLS).map(|_| rng.base()).collect();
        let mask: Vec<Fp5> = (0..mask_len(LOG_CELLS, 2)).map(|_| rng.fp5()).collect();
        let mut terms = vec![
            TensorTerm {
                weight: rng.fp5(),
                point: (0..LOG_CELLS).map(|_| rng.fp5()).collect(),
            },
            TensorTerm {
                weight: rng.fp5(),
                point: (0..3).map(|_| rng.fp5()).collect(),
            },
            TensorTerm {
                weight: rng.fp5(),
                point: Vec::new(),
            },
        ];
        let mut bits: Vec<Fp5> = (0..LOG_CELLS)
            .map(|j| if j % 3 == 0 { Fp5::ONE } else { Fp5::ZERO })
            .collect();
        bits[1] = rng.fp5();
        terms.push(TensorTerm {
            weight: rng.fp5(),
            point: bits,
        });
        let claim = dot(&coeffs, &kernel_of(&terms, LOG_CELLS));
        let salt_seed = [seed as u8; 32];
        let tree_nonce = [(seed as u8).wrapping_add(0x55); TREE_NONCE_BYTES];
        let st = commit(
            profile,
            LOG_CELLS,
            &schedule,
            coeffs,
            mask,
            &salt_seed,
            &tree_nonce,
        );
        Fixture {
            profile,
            schedule,
            st,
            terms,
            claim,
        }
    }

    fn transcript(f: &Fixture) -> Transcript {
        Transcript::new(f.profile, &[b"pcs-test", &f.st.tree_nonce(), &f.st.root()])
    }

    fn prove(f: &Fixture) -> Opening {
        let kernel = kernel_of(&f.terms, LOG_CELLS);
        open(&f.st, kernel, f.claim, &mut transcript(f)).expect("coins in Good")
    }

    fn check(f: &Fixture, opening: &Opening) -> bool {
        verify(
            f.profile,
            &f.st.tree_nonce(),
            &f.st.root(),
            LOG_CELLS,
            &f.schedule,
            &f.terms,
            f.claim,
            opening,
            &mut transcript(f),
        )
    }

    #[test]
    fn roundtrip_both_profiles_tree_nonce_and_serialization() {
        for profile in Profile::ALL {
            let f = fixture(profile, 21);
            let opening = prove(&f);
            assert!(check(&f, &opening));
            let mut bad_nonce = f.st.tree_nonce();
            bad_nonce[0] ^= 1;
            assert!(!verify(
                f.profile,
                &bad_nonce,
                &f.st.root(),
                LOG_CELLS,
                &f.schedule,
                &f.terms,
                f.claim,
                &opening,
                &mut transcript(&f),
            ));
            let mut bytes = vec![0xAA];
            opening.push_bytes(&mut bytes);
            let mut pos = 1;
            let back = Opening::read(&bytes, &mut pos, LOG_CELLS, &f.schedule).unwrap();
            assert_eq!(pos, bytes.len());
            assert_eq!(back, opening);
            let mut bad = bytes.clone();
            bad[1..9].copy_from_slice(&P.to_le_bytes());
            let mut pos = 1;
            assert!(Opening::read(&bad, &mut pos, LOG_CELLS, &f.schedule).is_none());
        }
    }

    #[test]
    fn split_opening_across_three_additive_shares_verifies_and_rejects_tamper() {
        let mut rng = Rng(88);
        let profile = Profile::TurboShakeJohnson400;
        let schedule = toy_schedule();
        let shares_c: [Vec<Goldilocks>; 3] =
            core::array::from_fn(|_| (0..1 << LOG_CELLS).map(|_| rng.base()).collect());
        let shares_r: [Vec<Fp5>; 3] =
            core::array::from_fn(|_| (0..mask_len(LOG_CELLS, 2)).map(|_| rng.fp5()).collect());
        let mut sum_c = vec![Goldilocks::ZERO; 1 << LOG_CELLS];
        let mut sum_r = vec![Fp5::ZERO; mask_len(LOG_CELLS, 2)];
        for s in &shares_c {
            for (a, &v) in sum_c.iter_mut().zip(s) {
                *a += v;
            }
        }
        for s in &shares_r {
            for (a, &v) in sum_r.iter_mut().zip(s) {
                *a += v;
            }
        }
        let commits: Vec<Committed> = (0..3)
            .map(|k| {
                commit(
                    profile,
                    LOG_CELLS,
                    &schedule,
                    shares_c[k].clone(),
                    shares_r[k].clone(),
                    &[10 + k as u8; 32],
                    &[90 + k as u8; TREE_NONCE_BYTES],
                )
            })
            .collect();
        let nonces: Vec<_> = commits.iter().map(Committed::tree_nonce).collect();
        let roots: Vec<_> = commits.iter().map(Committed::root).collect();
        let terms = vec![TensorTerm {
            weight: rng.fp5(),
            point: (0..LOG_CELLS).map(|_| rng.fp5()).collect(),
        }];
        let kernel = kernel_of(&terms, LOG_CELLS);
        let claim = dot(&sum_c, &kernel);
        let mk_tr = || Transcript::new(profile, &[b"split-pcs"]);
        let mut tr = mk_tr();
        let red = stage0_reduce(&sum_c, &sum_r, 2, MASK_POINTS, kernel, claim, &mut tr).unwrap();
        let mut mask_evals = [Fp5::ZERO; MASK_POINTS];
        mask_evals.copy_from_slice(&red.mask_evals);
        let split = open_from_reduced_split(
            profile,
            LOG_CELLS,
            &schedule,
            &nonces,
            &roots,
            mask_evals,
            red.folds,
            red.mask_claim,
            red.g,
            red.st,
            red.chals,
            red.beta_r,
            &mut tr,
            &mut |idx| Some(commits.iter().map(|c| stage0_answer(c, idx)).collect()),
        )
        .unwrap();
        assert!(verify_split(
            profile,
            &nonces,
            &roots,
            LOG_CELLS,
            &schedule,
            &terms,
            claim,
            &split,
            &mut mk_tr(),
        ));
        let mut wire = Vec::new();
        split.push_bytes(&mut wire);
        let mut pos = 0;
        let decoded = SplitOpening::read(&wire, &mut pos, LOG_CELLS, &schedule, 3).unwrap();
        assert_eq!(pos, wire.len());
        assert_eq!(decoded, split);
        let mut bad = split.clone();
        bad.stage0_shares[1].leaves[0].z[0] += Goldilocks::ONE;
        assert!(!verify_split(
            profile,
            &nonces,
            &roots,
            LOG_CELLS,
            &schedule,
            &terms,
            claim,
            &bad,
            &mut mk_tr(),
        ));
    }

    /// Exercise the V2.Z coupling using the real folding, encoding, Merkle and opening
    /// routines on a small domain. Independent coins are translated by a solution of
    /// the linear system for (opened Z, mask evaluations, fold scalars), then by the
    /// inverse mask line. The caller supplies distinct lower tables with an equal claim.
    pub(in crate::zk_hem::v2) fn couple_lookup_openings(
        tables: [Vec<Goldilocks>; 2],
        terms: Vec<TensorTerm>,
        seed: u64,
    ) {
        let nv = 9;
        let n = 1usize << nv;
        let profile = Profile::TurboShakeJohnson400;
        let mut schedule = toy_schedule();
        schedule.early_stop_vars += 1;
        let d0 = stage_dims(nv, &schedule).unwrap()[0];
        let indices: Vec<usize> = (1..=d0.queries).map(|j| 3 * j).collect();
        let blind = (d0.queries + 5 * MASK_POINTS) * d0.arity();
        let mut rng = Rng(seed);
        let mut coeffs = tables.map(|mut t| {
            assert!(t.len() <= n - blind);
            t.resize(n, Goldilocks::ZERO);
            crate::pcs::hypercube_to_monomial_coeffs(&t)
        });
        let kernel = kernel_of(&terms, nv);
        assert!(kernel[n - blind..].iter().all(|v| v.is_zero()));
        let claim = dot(&coeffs[0], &kernel);
        assert_eq!(claim, dot(&coeffs[1], &kernel));
        let [ref mut c0, ref mut c1] = coeffs;
        for (a, b) in c0[n - blind..n].iter_mut().zip(&mut c1[n - blind..n]) {
            let common = rng.base();
            *a += common;
            *b += common;
        }
        let coins = || FixedCoins {
            rng: Rng(seed + 1),
            indices: indices.clone(),
        };
        let zeros = vec![Fp5::ZERO; mask_len(nv, d0.step_vars)];
        let reduce = |c: &[Goldilocks]| {
            stage0_reduce(
                c,
                &zeros,
                d0.step_vars,
                MASK_POINTS,
                kernel.clone(),
                claim,
                &mut coins(),
            )
            .unwrap()
        };
        let view = |c: &[Goldilocks]| {
            let red = reduce(c);
            let code = encode_base(c, d0.log_domain);
            let mut v: Vec<_> = indices.iter().flat_map(|&j| fiber(&code, &d0, j)).collect();
            v.extend(
                red.mask_evals
                    .iter()
                    .chain(red.folds.iter().flatten())
                    .flat_map(|e| e.to_limbs()),
            );
            v
        };
        let target = view(&coeffs[0]);
        let current = view(&coeffs[1]);
        // Rows [observations | desired difference], columns blinding directions.
        let mut matrix: Vec<_> = target
            .iter()
            .zip(&current)
            .map(|(&a, &b)| {
                let mut row = vec![Goldilocks::ZERO; blind + 1];
                row[blind] = a - b;
                row
            })
            .collect();
        for col in 0..blind {
            let idx = n - blind + col;
            coeffs[1][idx] += Goldilocks::ONE;
            for ((row, v), &old) in matrix.iter_mut().zip(view(&coeffs[1])).zip(&current) {
                row[col] = v - old;
            }
            coeffs[1][idx] -= Goldilocks::ONE;
        }
        let mut pivots = Vec::new();
        for col in 0..blind {
            let i = pivots.len();
            let Some(j) = (i..matrix.len()).find(|&j| !matrix[j][col].is_zero()) else {
                continue;
            };
            matrix.swap(i, j);
            let inv = matrix[i][col].inv();
            for v in &mut matrix[i] {
                *v *= inv;
            }
            let pivot = matrix[i].clone();
            for (j, row) in matrix.iter_mut().enumerate() {
                if i == j {
                    continue;
                }
                let scale = row[col];
                for (x, &p) in row.iter_mut().zip(&pivot) {
                    *x -= scale * p;
                }
            }
            pivots.push(col);
        }
        assert_eq!(pivots.len(), target.len());
        for (col, row) in pivots.into_iter().zip(matrix) {
            coeffs[1][n - blind + col] += row[blind];
        }
        assert_eq!(view(&coeffs[1]), target);
        let [a, b] = coeffs.each_ref().map(|c| reduce(c));
        let mask: Vec<_> = (0..zeros.len()).map(|_| rng.fp5()).collect();
        let inv = a.beta_r.inverse();
        let other_mask = mask
            .iter()
            .zip(a.g)
            .zip(b.g)
            .map(|((&m, x), y)| m + (x - y) * inv)
            .collect();
        let salt = [seed as u8; 32];
        let nonce = [(seed + 3) as u8; 32];
        let [left, right] = coeffs
            .into_iter()
            .zip([mask, other_mask])
            .map(|(c, m)| {
                let st = commit(profile, nv, &schedule, c, m, &salt, &nonce);
                let opening = open(&st, kernel.clone(), claim, &mut coins()).unwrap();
                assert!(verify(
                    profile,
                    &nonce,
                    &st.root(),
                    nv,
                    &schedule,
                    &terms,
                    claim,
                    &opening,
                    &mut coins()
                ));
                (st.root(), opening)
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let (root_a, proof_a) = left;
        let (root_b, mut proof_b) = right;
        assert_ne!(root_a, root_b);
        assert_eq!(proof_a.stage0_query.leaves, proof_b.stage0_query.leaves);
        // Lazy-RO hybrid: give unopened leaves the same labels in the two
        // worlds. Its only effect on the opening is the path to the shared root.
        proof_b
            .stage0_query
            .siblings
            .clone_from(&proof_a.stage0_query.siblings);
        assert_eq!(proof_a, proof_b);
        assert!(verify(
            profile,
            &nonce,
            &root_a,
            nv,
            &schedule,
            &terms,
            claim,
            &proof_b,
            &mut coins()
        ));
    }

    #[test]
    fn blinders_cover_the_stage0_view_with_five_points_and_not_with_four() {
        fn rank(mut rows: Vec<Vec<Goldilocks>>) -> usize {
            let cols = rows[0].len();
            let mut rank = 0;
            for col in 0..cols {
                let Some(piv) = (rank..rows.len()).find(|&r| !rows[r][col].is_zero()) else {
                    continue;
                };
                rows.swap(rank, piv);
                let inv = rows[rank][col].inv();
                for v in &mut rows[rank] {
                    *v *= inv;
                }
                let pivot = rows[rank].clone();
                for (r, row) in rows.iter_mut().enumerate() {
                    if r != rank && !row[col].is_zero() {
                        let f = row[col];
                        for (v, &p) in row.iter_mut().zip(&pivot) {
                            *v -= f * p;
                        }
                    }
                }
                rank += 1;
            }
            rank
        }
        let stage0_view =
            |coeffs: &[Goldilocks], kernel: &[Fp5], points: usize, fibers: &[usize]| {
                let schedule = toy_schedule();
                let dims = stage_dims(LOG_CELLS, &schedule).unwrap();
                let d0 = dims[0];
                let code = encode_base(coeffs, d0.log_domain);
                let mut view: Vec<Goldilocks> =
                    fibers.iter().flat_map(|&j| fiber(&code, &d0, j)).collect();
                let mask = vec![Fp5::ZERO; mask_len(LOG_CELLS, d0.step_vars)];
                let mut coins = FixedCoins {
                    rng: Rng(77),
                    indices: Vec::new(),
                };
                let red = stage0_reduce(
                    coeffs,
                    &mask,
                    d0.step_vars,
                    points,
                    kernel.to_vec(),
                    dot(coeffs, kernel),
                    &mut coins,
                )
                .unwrap();
                view.extend(red.mask_evals.iter().flat_map(|a| a.to_limbs()));
                view.extend(red.folds.iter().flatten().flat_map(|a| a.to_limbs()));
                view
            };
        let blinder_rank = |points: usize| {
            let mut rng = Rng(41);
            let n = 1usize << LOG_CELLS;
            let (s, q0) = (2usize, 2usize);
            let blind = (q0 + 5 * points) << s;
            let fibers = [3usize, 100];
            let mut coeffs: Vec<Goldilocks> = (0..n).map(|_| rng.base()).collect();
            coeffs[n - blind..].fill(Goldilocks::ZERO);
            let kernel: Vec<Fp5> = (0..n)
                .map(|i| if i < n - blind { rng.fp5() } else { Fp5::ZERO })
                .collect();
            let base = stage0_view(&coeffs, &kernel, points, &fibers);
            let rows: Vec<Vec<Goldilocks>> = (0..blind)
                .map(|i| {
                    let mut c = coeffs.clone();
                    c[n - blind + i] = Goldilocks::ONE;
                    stage0_view(&c, &kernel, points, &fibers)
                        .iter()
                        .zip(&base)
                        .map(|(&a, &b)| a - b)
                        .collect()
                })
                .collect();
            (blind, base.len(), rank(rows))
        };
        let (blind, dims, r) = blinder_rank(5);
        assert_eq!((blind, dims), (108, 8 + 25 * 3));
        assert_eq!(r, dims);
        let (blind, dims, r) = blinder_rank(4);
        assert_eq!((blind, dims), (88, 8 + 20 + 50));
        assert!(r < dims);
    }
}
