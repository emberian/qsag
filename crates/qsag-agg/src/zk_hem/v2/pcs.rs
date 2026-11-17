//! The polynomial commitment of zk-Hem v2 (SECURITY.md V2.1, rounds 7 on): one Stage-0 tree
//! over a base-field table codeword `Z^` and a challenge-field mask codeword `R^`, opened
//! against one linear claim `<c, K> = V` on the monomial coefficients `c` of the table.
//!
//! Rounds 7 to 10 ([`stage0_reduce`] and [`stage0_reduce_verify`]) turn the claim on `c` into
//! a claim on the masked polynomial `g = P_s + beta_R R`; round 12 ([`stage0_answer`] and
//! [`stage0_check_fibers`]) opens Stage-0 fibers and folds them to values of `g`. Everything
//! after that is the affine-fold WHIR of v1 on `g` over `F_{p^5}`, without grinding or salts.
//!
//! Kernels. A claim is `<c, kappa> = v` with `kappa` a sum of *tensor terms*
//! (`kappa_i = w prod_j r_j^{bit_j(i)}` below `2^len(r)`, zero elsewhere, in particular on
//! overflow coefficients) and *point terms* (`kappa_i = w x^i` for every index). One fold maps
//! `kappa` to `kappa_even + phi kappa_odd`: a tensor term loses its first coordinate and its
//! weight is multiplied by `1 + phi r_0`; a point term at `x` becomes the point term at `x^2`
//! with weight `w (1 + phi x)`. The prover keeps `kappa` as a vector as long as the
//! polynomial and continues it past the end from the point terms; the verifier keeps the terms.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::Range;

use super::field5::Fp5;
use super::hash::{Channel, Digest, Hasher, MAX_LOG_LEAVES, MerkleTree, verify_multiproof};
use super::params::{DIGEST_BYTES, LATER_OOD_POINTS, MASK_POINTS, Profile, SALT_BYTES, Schedule};
use crate::field::{Goldilocks, GoldilocksOps as _, ntt_goldilocks};

/// Coset shift of every evaluation domain, as in v1.
const SHIFT: Goldilocks = Goldilocks::NON_RESIDUE;
const INV_TWO: Goldilocks = Goldilocks::from_u64_reduced(0x7FFF_FFFF_8000_0001);
const _: () = assert!(INV_TWO.const_mul(Goldilocks::TWO).to_canonical_u64() == 1);

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
    /// Variables before the stage's folds.
    pub vars: usize,
    pub step_vars: usize,
    pub log_domain: usize,
    /// Leaves of the stage's tree.
    pub fibers: usize,
    /// Distinct fibers opened.
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

    /// The point of index `j` of the stage's domain: the first point of fiber `j`.
    fn fiber_base(&self, j: usize) -> Goldilocks {
        SHIFT.const_mul(Goldilocks::two_adic_generator(self.log_domain).pow(j as u64))
    }

    /// The point below fiber `j` after the stage's folds.
    fn fiber_image(&self, j: usize) -> Goldilocks {
        self.fiber_base(j).pow(1 << self.step_vars)
    }
}

/// The stages of `schedule` on a table of `2^log_cells` cells, or `None` if this code does
/// not support the schedule: at least two stages, one to six folds each, at least two folds in
/// all, and domains within the two-adicity of the field.
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

/// `f(offset, chunk)` over consecutive chunks of `data`.
pub(super) fn par_chunks_mut<T: Send>(data: &mut [T], f: impl Fn(usize, &mut [T]) + Sync) {
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

/// Sum of `f` over consecutive subranges of `0..n`. Partial sums are erased.
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

/// A coefficient of a polynomial being folded: base field before the first fold, challenge
/// field after it.
pub trait Coef: Copy + Send + Sync {
    const ZERO: Self;
    /// `self * e`.
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

/// `sum_i coeffs[i] x^i` at each of `K` points.
pub fn eval_poly<T: Coef, const K: usize>(coeffs: &[T], xs: [Fp5; K]) -> [Fp5; K] {
    par_sum(coeffs.len(), |range| {
        let start = range.start as u64;
        let mut acc = [Fp5::ZERO; K];
        for c in coeffs[range].iter().rev() {
            for (a, &x) in acc.iter_mut().zip(&xs) {
                *a = *a * x + c.lift();
            }
        }
        for (a, x) in acc.iter_mut().zip(&xs) {
            *a *= x.pow(start);
        }
        acc
    })
}

/// A challenge-field polynomial at a base-field point.
fn eval_at_base(coeffs: &[Fp5], y: Goldilocks) -> Fp5 {
    coeffs
        .iter()
        .rev()
        .fold(Fp5::ZERO, |acc, &c| acc.mul_base(y) + c)
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

/// Values of `sum_i coeffs[i] x^i` at `x = SHIFT * w^j`, `j < 2^log_domain`, `w` the generator
/// of that order, in natural order.
pub fn encode_base(coeffs: &[Goldilocks], log_domain: usize) -> Vec<Goldilocks> {
    assert!(coeffs.len() <= 1 << log_domain);
    shifted_limb_ntt(coeffs.len(), log_domain, |i| coeffs[i])
}

/// [`encode_base`] for a challenge-field polynomial: one base-field transform per limb.
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

/// Values on the points of `SHIFT^(2^step) * <w^(2^step)>`, the images of the fibers of a
/// domain of `2^log_domain` points: the codeword of the mask on the folded domain.
fn encode_ext_folded(coeffs: &[Fp5], log_domain: usize, step_vars: usize) -> Vec<Fp5> {
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

/// The symbols of fiber `j`: the points `SHIFT w^(j + t * fibers)`, `t < arity`.
fn fiber<T: Copy>(code: &[T], dims: &StageDims, j: usize) -> Vec<T> {
    (0..dims.arity())
        .map(|t| code[j + t * dims.fibers])
        .collect()
}

/// Fold the symbols of a codeword on one fiber (first point `x0`) with the stage's
/// challenges `(theta, alpha, beta)` to the value of the folded polynomial at `x0^arity`:
/// `P'(x^2) = G + (alpha + beta x^2)(F + theta G)` with `F = (P(x) + P(-x)) / 2`,
/// `G = (P(x) - P(-x)) / (2x)`.
fn fold_fiber(mut vals: Vec<Fp5>, x0: Goldilocks, chals: &[[Fp5; 3]]) -> Fp5 {
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
            let f = (a + b).mul_base(INV_TWO);
            let g = (a - b).mul_base(INV_TWO.const_mul(xt_inv));
            vals[t] = g + (alpha + beta.mul_base(xt.square())) * (f + theta * g);
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

/// Prover state of a Stage-0 commitment. Everything in it is secret.
pub struct Committed {
    profile: Profile,
    log_cells: usize,
    schedule: Schedule,
    dims: Vec<StageDims>,
    /// Monomial coefficients of the table.
    coeffs: Vec<Goldilocks>,
    /// Coefficients of the mask `R`.
    mask: Vec<Fp5>,
    z_code: Vec<Goldilocks>,
    r_code: Vec<Fp5>,
    salt_seed: [u8; 32],
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

    pub fn log_cells(&self) -> usize {
        self.log_cells
    }

    pub fn schedule(&self) -> &Schedule {
        &self.schedule
    }

    /// Monomial coefficients of the committed table.
    pub fn coeffs(&self) -> &[Goldilocks] {
        &self.coeffs
    }
}

/// Commit to the table with monomial coefficients `coeffs` (`2^log_cells` of them) and to the
/// mask polynomial `mask` ([`mask_len`] uniform coefficients). `salt_seed` must be uniform and
/// secret. Panics if the schedule is not supported or a length is wrong.
pub fn commit(
    profile: Profile,
    log_cells: usize,
    schedule: &Schedule,
    coeffs: Vec<Goldilocks>,
    mask: Vec<Fp5>,
    salt_seed: &[u8; 32],
) -> Committed {
    let _phase = crate::profile::span("zkhem2_commit");
    let dims = stage_dims(log_cells, schedule).expect("unsupported v2 schedule");
    let d0 = dims[0];
    assert_eq!(coeffs.len(), 1 << log_cells);
    assert_eq!(mask.len(), mask_len(log_cells, d0.step_vars));
    let phase = crate::profile::span("zkhem2_commit_encode");
    let z_code = encode_base(&coeffs, d0.log_domain);
    let r_code = encode_ext_folded(&mask, d0.log_domain, d0.step_vars);
    drop(phase);
    let _merkle = crate::profile::span("zkhem2_commit_merkle");
    let hasher = Hasher::new(profile);
    let mut leaves = vec![[0u8; DIGEST_BYTES]; d0.fibers];
    crate::pcs::fill_indexed(&mut leaves, |j| {
        let mut salt = hasher.salt(salt_seed, j as u32);
        let mut z = fiber(&z_code, &d0, j);
        let digest = hasher.leaf_stage0(j as u32, &salt, &z, r_code[j]);
        qsag_asm::volatile_fill(&mut salt, 0u8);
        qsag_asm::volatile_fill(&mut z, Goldilocks::ZERO);
        digest
    });
    let tree = MerkleTree::build(hasher, 0, leaves);
    Committed {
        profile,
        log_cells,
        schedule: schedule.clone(),
        dims,
        coeffs,
        mask,
        z_code,
        r_code,
        salt_seed: *salt_seed,
        tree,
    }
}

// ============================================================================
// Proof
// ============================================================================

/// An opened Stage-0 leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage0Leaf {
    pub salt: [u8; SALT_BYTES],
    /// Symbols of the table codeword on the fiber.
    pub z: Vec<Goldilocks>,
    /// Symbol of the mask codeword below the fiber.
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
    /// Root of the stage's oracle, the codeword of the polynomial entering the stage.
    pub root: Digest,
    /// Its values at the two out-of-domain points.
    pub ood: [Fp5; LATER_OOD_POINTS],
    /// Five scalars per fold of the stage.
    pub folds: Vec<[Fp5; 5]>,
    /// Opened fibers of the stage's oracle.
    pub query: ExtQuery,
}

/// The opening of a Stage-0 commitment against one linear claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening {
    /// `a_j = Z^(omega_j)`.
    pub mask_evals: [Fp5; MASK_POINTS],
    /// Five scalars per Stage-0 fold.
    pub stage0_folds: Vec<[Fp5; 5]>,
    /// `mu = <R, v_s>`.
    pub mask_claim: Fp5,
    pub stage0_query: Stage0Query,
    pub stages: Vec<LaterStage>,
    /// The terminal polynomial, `2^early_stop_vars + 2` coefficients.
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

impl Opening {
    /// Serialize in the order of the rounds: the five out-of-domain values, the Stage-0 fold
    /// scalars, the mask claim; then for each later stage its root, its two out-of-domain
    /// values, the opened fibers of the stage before it and its own fold scalars; then the
    /// terminal polynomial and the opened fibers of the last stage.
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
                for leaf in &self.stage0_query.leaves {
                    out.extend_from_slice(&leaf.salt);
                    for z in &leaf.z {
                        out.extend_from_slice(&z.to_le_bytes());
                    }
                    push_fp5(out, &leaf.r);
                }
                push_siblings(out, &self.stage0_query.siblings);
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

    /// Canonical decoding for the given geometry, starting at `*pos` and advancing it. Field
    /// elements must be reduced; every count is fixed by the geometry except the number of
    /// authentication siblings, which is bounded here and checked exactly by the verifier.
    pub fn read(
        bytes: &[u8],
        pos: &mut usize,
        log_cells: usize,
        schedule: &Schedule,
    ) -> Option<Self> {
        let dims = stage_dims(log_cells, schedule)?;
        let mut r = Reader { bytes, pos: *pos };
        let mask_evals = r.fold()?;
        let stage0_folds = (0..dims[0].step_vars)
            .map(|_| r.fold())
            .collect::<Option<Vec<_>>>()?;
        let mask_claim = r.fp5()?;
        let mut stage0_query = None;
        let mut stages: Vec<LaterStage> = Vec::with_capacity(dims.len() - 1);
        for i in 1..dims.len() {
            let root = r.take()?;
            let ood = [r.fp5()?, r.fp5()?];
            if i == 1 {
                let d0 = &dims[0];
                let leaves = (0..d0.queries)
                    .map(|_| {
                        Some(Stage0Leaf {
                            salt: r.take()?,
                            z: (0..d0.arity()).map(|_| r.base()).collect::<Option<_>>()?,
                            r: r.fp5()?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?;
                stage0_query = Some(Stage0Query {
                    leaves,
                    siblings: r.siblings(d0)?,
                });
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
            stage0_query: stage0_query?,
            stages,
            final_coeffs,
        })
    }
}

// ============================================================================
// The event Good (conditions on the Stage-0 challenges)
// ============================================================================

/// Condition (G2): each `omega_j^(2^step_vars)` lies outside `F_p` and no two of them are
/// Frobenius conjugates.
pub fn mask_points_good(omegas: &[Fp5], step_vars: usize) -> bool {
    let z: Vec<Fp5> = omegas
        .iter()
        .map(|w| (0..step_vars).fold(*w, |acc, _| acc.square()))
        .collect();
    z.iter().all(|x| !x.is_base())
        && (0..z.len()).all(|i| (0..i).all(|j| (0..5).all(|k| z[i].frobenius_pow(k) != z[j])))
}

/// The part of condition (G3) on the challenge `phi` of one Stage-0 fold: `phi != 0` and
/// `1 + phi x != 0` for the current point `x = omega_j^(2^i)` of each mask point.
pub fn fold_challenge_good(phi: Fp5, xs: &[Fp5]) -> bool {
    !phi.is_zero() && xs.iter().all(|&x| !(Fp5::ONE + phi * x).is_zero())
}

// ============================================================================
// Kernels
// ============================================================================

/// `sum_j w_j x_j^i` for `i = from, .., from + count - 1`: the continuation of the point terms
/// past the stored kernel.
fn point_tail(points: &[(Fp5, Fp5)], from: usize, count: usize) -> Vec<Fp5> {
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
fn add_points(kernel: &mut [Fp5], points: &[(Fp5, Fp5)]) {
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

fn extend_kernel(kernel: &mut Vec<Fp5>, points: &[(Fp5, Fp5)], len: usize) {
    if kernel.len() < len {
        let tail = point_tail(points, kernel.len(), len - kernel.len());
        kernel.extend(tail);
    }
}

fn fold_points(points: &mut [(Fp5, Fp5)], phi: Fp5) {
    for (w, x) in points {
        *w *= Fp5::ONE + phi * *x;
        *x = x.square();
    }
}

/// The verifier's kernel: tensor terms with the number of coordinates already folded away,
/// and point terms.
struct KernelTerms<'a> {
    tensor: Vec<(Fp5, &'a [Fp5])>,
    consumed: usize,
    points: Vec<(Fp5, Fp5)>,
}

impl<'a> KernelTerms<'a> {
    fn new(terms: &'a [TensorTerm]) -> Self {
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

    /// `<coeffs, kernel>` for the terminal polynomial.
    fn apply(&self, coeffs: &[Fp5]) -> Fp5 {
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

/// `sigma' = gamma_G + alpha (gamma_F + theta gamma_G) + beta (c_F + theta c_G)`.
fn next_claim(wire: &[Fp5; 5], claim: Fp5, phi: Fp5, [theta, alpha, beta]: [Fp5; 3]) -> Fp5 {
    let [sigma_even, tau_01, tau_10, c_f, c_g] = *wire;
    let gamma_f = sigma_even + phi * tau_01;
    let gamma_g = tau_10 + phi * (claim - sigma_even);
    gamma_g + alpha * (gamma_f + theta * gamma_g) + beta * (c_f + theta * c_g)
}

/// The verifier's side of one fold: absorb the scalars in two groups, draw the challenges,
/// update the claim and the kernel terms.
fn verify_fold<C: Channel>(
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

/// The prover's working state: a polynomial, its kernel as a vector of the same length, the
/// point terms the kernel contains, and the claimed value `<poly, kernel>`.
struct Folding {
    kernel: Vec<Fp5>,
    points: Vec<(Fp5, Fp5)>,
    claim: Fp5,
}

/// The folded polynomial, the five scalars and `(theta, alpha, beta)`.
type Folded = (Vec<Fp5>, [Fp5; 5], [Fp5; 3]);

/// One fold of `poly` (even and odd parts `F`, `G`) to `G + (alpha + beta Y)(F + theta G)`.
/// Returns the new polynomial, the five scalars and `(theta, alpha, beta)`. With
/// `guarded > 0` the first `guarded` point terms are the mask points and the fold stops, after
/// the first three scalars are absorbed and before the last two exist, unless `phi` satisfies
/// condition (G3).
fn prove_fold<T: Coef, C: Channel>(
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
// Stage 0, rounds 7 to 10: from the claim on the table to the claim on `g`
// ============================================================================

/// What the prover holds after rounds 7 to 10.
struct Stage0Reduced {
    mask_evals: Vec<Fp5>,
    folds: Vec<[Fp5; 5]>,
    mask_claim: Fp5,
    /// `g = P_s + beta_R R`.
    g: Vec<Fp5>,
    st: Folding,
    chals: Vec<[Fp5; 3]>,
    beta_r: Fp5,
}

/// Rounds 7 to 10 for the prover with `points` mask points ([`MASK_POINTS`] in the protocol;
/// the tests also run four to exhibit the leak). `kernel` is the tensor part of the claim's
/// kernel on the `coeffs.len()` coefficients and `claim` its value.
fn stage0_reduce<C: Channel>(
    coeffs: &[Goldilocks],
    mask: &[Fp5],
    step_vars: usize,
    points: usize,
    mut kernel: Vec<Fp5>,
    claim: Fp5,
    ch: &mut C,
) -> Result<Stage0Reduced, MaskRankDeficient> {
    assert_eq!(kernel.len(), coeffs.len());
    // Round 7: the mask points. (G2) is tested before any value at them exists.
    let omegas: Vec<Fp5> = (0..points).map(|_| ch.squeeze_fp5(b"MASK_POINT")).collect();
    if !mask_points_good(&omegas, step_vars) {
        return Err(MaskRankDeficient);
    }
    // Round 8.
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

    // Round 9.
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

    // Round 10: the mask line.
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

/// Rounds 7 to 10 for the verifier: returns the Stage-0 fold challenges and `beta_R`, and
/// leaves in `claim` and `kernel` the claim on `g`.
fn stage0_reduce_verify<C: Channel>(
    opening: &Opening,
    claim: &mut Fp5,
    kernel: &mut KernelTerms<'_>,
    ch: &mut C,
) -> (Vec<[Fp5; 3]>, Fp5) {
    let omegas: [Fp5; MASK_POINTS] = core::array::from_fn(|_| ch.squeeze_fp5(b"MASK_POINT"));
    ch.absorb_fp5_slice(b"MASK_EVAL", &opening.mask_evals);
    for (omega, a) in omegas.into_iter().zip(opening.mask_evals) {
        let w = ch.squeeze_fp5(b"MASK_WEIGHT");
        *claim += w * a;
        kernel.points.push((w, omega));
    }
    let chals = opening
        .stage0_folds
        .iter()
        .map(|wire| verify_fold(wire, claim, kernel, ch))
        .collect();
    ch.absorb_fp5_slice(b"MASK_CLAIM", &[opening.mask_claim]);
    let beta_r = ch.squeeze_fp5_nonzero(b"MASK_BETA");
    *claim += beta_r * opening.mask_claim;
    (chals, beta_r)
}

