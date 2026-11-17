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

/// `sum_i coeffs[i] x^i` at each of `K` points. Blocks of [`EVAL_BLOCK`] coefficients are
/// taken against a table of powers, so that a base-field coefficient costs one
/// multiplication by a base-field element, and the blocks are combined by Horner's rule.
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

// ============================================================================
// Stage 0, round 12: opened fibers
// ============================================================================

/// The prover's answer to the Stage-0 queries `idx` (sorted, distinct).
fn stage0_answer(st: &Committed, idx: &[usize]) -> Stage0Query {
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

/// Check the opened Stage-0 leaves against `root` and fold each to the value of `g` at the
/// point below its fiber: `P_s(y) + beta_R R^(y)`.
fn stage0_check_fibers(
    hasher: Hasher,
    root: &Digest,
    d0: &StageDims,
    idx: &[usize],
    query: &Stage0Query,
    chals: &[[Fp5; 3]],
    beta_r: Fp5,
) -> Option<Vec<(Goldilocks, Fp5)>> {
    if query.leaves.len() != idx.len() || query.leaves.iter().any(|l| l.z.len() != d0.arity()) {
        return None;
    }
    let digests: Vec<(usize, Digest)> = idx
        .iter()
        .zip(&query.leaves)
        .map(|(&j, leaf)| (j, hasher.leaf_stage0(j as u32, &leaf.salt, &leaf.z, leaf.r)))
        .collect();
    if !verify_multiproof(hasher, 0, d0.log_leaves(), root, &digests, &query.siblings) {
        return None;
    }
    Some(
        idx.iter()
            .zip(&query.leaves)
            .map(|(&j, leaf)| {
                let x0 = d0.fiber_base(j);
                let vals = leaf.z.iter().map(|&z| Fp5::from_base(z)).collect();
                let folded = fold_fiber(vals, x0, chals);
                (d0.fiber_image(j), folded + beta_r * leaf.r)
            })
            .collect(),
    )
}

/// The same for a later stage: values of the polynomial after the stage's folds.
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

/// Absorb the folded query values, draw the weights of the out-of-domain values and of the
/// query values, and return the new point terms `(weight, point)` with the claim increment.
fn stage_claims<C: Channel>(
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

/// Open the commitment against `<coeffs, kernel> = claim`, where `kernel` is a sum of tensor
/// terms given as a vector over the `2^log_cells` coefficients. The caller has bound the
/// commitment, the kernel and the claim into `ch`. For zero knowledge the kernel must vanish
/// on the blinder coefficients (SECURITY.md Theorem V2.Z); this function does not check it.
pub fn open<C: Channel>(
    st: &Committed,
    kernel: Vec<Fp5>,
    claim: Fp5,
    ch: &mut C,
) -> Result<Opening, MaskRankDeficient> {
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
        g: mut poly,
        st: mut fold,
        chals: mut prev_chals,
        beta_r,
    } = red;
    let mut stage0_query = None;
    let mut stages: Vec<LaterStage> = Vec::with_capacity(dims.len() - 1);
    // The oracle of the stage before the current one, for stages after the first.
    let mut prev_oracle: Option<(Vec<Fp5>, MerkleTree)> = None;
    for (i, d) in dims.iter().enumerate().skip(1) {
        let phase = crate::profile::span("zkhem2_open_encode");
        let code = encode_ext(&poly, d.log_domain);
        drop(phase);
        let phase = crate::profile::span("zkhem2_open_merkle");
        let mut leaves = vec![[0u8; DIGEST_BYTES]; d.fibers];
        crate::pcs::fill_indexed(&mut leaves, |j| {
            hasher.leaf_ext(i as u8, j as u32, &fiber(&code, d, j))
        });
        let tree = MerkleTree::build(hasher, i as u8, leaves);
        drop(phase);
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
            let (next, wire, c) = prove_fold(&poly, &mut fold, 0, ch)?;
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
        prev_oracle = Some((code, tree));
    }

    ch.absorb_fp5_slice(b"FINAL_POLY", &poly);
    let last = dims.len() - 1;
    let d = &dims[last];
    let idx = ch.squeeze_distinct_indices(b"QUERY", d.fibers, d.queries);
    let (code, tree) = prev_oracle.as_ref().expect("at least two stages");
    stages[last - 1].query = ExtQuery {
        leaves: idx.iter().map(|&j| fiber(code, d, j)).collect(),
        siblings: tree.open(&idx),
    };
    let mut mask_eval_array = [Fp5::ZERO; MASK_POINTS];
    mask_eval_array.copy_from_slice(&mask_evals);
    Ok(Opening {
        mask_evals: mask_eval_array,
        stage0_folds,
        mask_claim,
        stage0_query: stage0_query.expect("at least two stages"),
        stages,
        final_coeffs: poly,
    })
}

/// Verify an [`Opening`] of the commitment `root` against the claim
/// `sum_t terms[t].weight * W(terms[t].point, 0, ..) = claim` on the committed table `W`.
/// The caller has bound `root`, the terms and the claim into `ch`.
#[allow(clippy::too_many_arguments)]
pub fn verify<C: Channel>(
    profile: Profile,
    root: &Digest,
    log_cells: usize,
    schedule: &Schedule,
    terms: &[TensorTerm],
    claim: Fp5,
    opening: &Opening,
    ch: &mut C,
) -> bool {
    let Some(dims) = stage_dims(log_cells, schedule) else {
        return false;
    };
    let hasher = Hasher::new(profile);
    if terms.iter().any(|t| t.point.len() > log_cells)
        || opening.stage0_folds.len() != dims[0].step_vars
        || opening.stages.len() + 1 != dims.len()
        || opening
            .stages
            .iter()
            .zip(&dims[1..])
            .any(|(stage, d)| stage.folds.len() != d.step_vars)
        || opening.final_coeffs.len() != (1usize << schedule.early_stop_vars) + 2
    {
        return false;
    }
    let mut claim = claim;
    let mut kernel = KernelTerms::new(terms);
    let (mut prev_chals, beta_r) = stage0_reduce_verify(opening, &mut claim, &mut kernel, ch);

    for i in 1..dims.len() {
        let stage = &opening.stages[i - 1];
        ch.absorb(b"STAGE_ROOT", &stage.root);
        let ood_points: [Fp5; LATER_OOD_POINTS] =
            core::array::from_fn(|_| ch.squeeze_fp5(b"OOD_POINT"));
        ch.absorb_fp5_slice(b"OOD_EVAL", &stage.ood);

        let before = &dims[i - 1];
        let idx = ch.squeeze_distinct_indices(b"QUERY", before.fibers, before.queries);
        let shifts = if i == 1 {
            stage0_check_fibers(
                hasher,
                root,
                before,
                &idx,
                &opening.stage0_query,
                &prev_chals,
                beta_r,
            )
        } else {
            let prev = &opening.stages[i - 2];
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

    ch.absorb_fp5_slice(b"FINAL_POLY", &opening.final_coeffs);
    if kernel.apply(&opening.final_coeffs) != claim {
        return false;
    }
    let last = dims.len() - 1;
    let d = &dims[last];
    let idx = ch.squeeze_distinct_indices(b"QUERY", d.fibers, d.queries);
    let stage = &opening.stages[last - 1];
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
        .all(|&(y, v)| eval_at_base(&opening.final_coeffs, y) == v)
}

#[cfg(test)]
mod tests {
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

    /// Coins that do not depend on the prover's messages.
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

    /// The tensor terms as a kernel vector: `kappa_i = sum_t w_t prod_j r_{t,j}^{bit_j(i)}`.
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
        // Full-length, short and zero/one-coordinate points.
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
        let st = commit(profile, LOG_CELLS, &schedule, coeffs, mask, &salt_seed);
        Fixture {
            profile,
            schedule,
            st,
            terms,
            claim,
        }
    }

    fn transcript(f: &Fixture) -> Transcript {
        Transcript::new(f.profile, &[b"pcs-test", &f.st.root()])
    }

    fn prove(f: &Fixture) -> Opening {
        let kernel = kernel_of(&f.terms, LOG_CELLS);
        open(&f.st, kernel, f.claim, &mut transcript(f)).expect("coins in Good")
    }

    fn check(f: &Fixture, opening: &Opening) -> bool {
        verify(
            f.profile,
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
    fn codewords_are_evaluations_in_natural_order() {
        let mut rng = Rng(11);
        let coeffs: Vec<Goldilocks> = (0..16).map(|_| rng.base()).collect();
        let code = encode_base(&coeffs, 6);
        let w = Goldilocks::two_adic_generator(6);
        for (j, &v) in code.iter().enumerate() {
            let x = SHIFT * w.pow(j as u64);
            let direct = coeffs
                .iter()
                .rev()
                .fold(Goldilocks::ZERO, |a, &c| a * x + c);
            assert_eq!(v, direct, "point {j}");
        }
        // 18 coefficients: two more than a power of two.
        let ext: Vec<Fp5> = (0..18).map(|_| rng.fp5()).collect();
        let code = encode_ext(&ext, 6);
        for (j, &v) in code.iter().enumerate() {
            let x = SHIFT * w.pow(j as u64);
            assert_eq!(v, eval_at_base(&ext, x), "point {j}");
            assert_eq!(v, eval_poly(&ext, [Fp5::from_base(x)])[0]);
        }
        // The folded domain holds the images of the fibers.
        let dims = StageDims {
            vars: 4,
            step_vars: 2,
            log_domain: 6,
            fibers: 16,
            queries: 1,
        };
        let folded = encode_ext_folded(&ext[..6], 6, 2);
        assert_eq!(folded.len(), 16);
        for (j, &v) in folded.iter().enumerate() {
            let y = dims.fiber_image(j);
            assert_eq!(v, eval_at_base(&ext[..6], y), "fiber {j}");
            for t in 0..4 {
                let x = SHIFT * w.pow((j + t * 16) as u64);
                assert_eq!(x.pow(4), y);
            }
        }
    }

    #[test]
    fn fiber_fold_matches_coefficient_fold() {
        let mut rng = Rng(12);
        let poly: Vec<Fp5> = (0..18).map(|_| rng.fp5()).collect();
        let dims = StageDims {
            vars: 4,
            step_vars: 2,
            log_domain: 6,
            fibers: 16,
            queries: 1,
        };
        let code = encode_ext(&poly, 6);
        let chals: Vec<[Fp5; 3]> = (0..2).map(|_| [rng.fp5(), rng.fp5(), rng.fp5()]).collect();
        // Fold the coefficients with the prover's routine under fixed coins equal to `chals`.
        struct Replay(Vec<Fp5>);
        impl Channel for Replay {
            fn absorb(&mut self, _: &[u8], _: &[u8]) {}
            fn squeeze_fp5(&mut self, _: &[u8]) -> Fp5 {
                self.0.remove(0)
            }
            fn squeeze_distinct_indices(&mut self, _: &[u8], _: usize, _: usize) -> Vec<usize> {
                Vec::new()
            }
        }
        let phis = [rng.fp5(), rng.fp5()];
        let mut coins = Replay(vec![
            phis[0],
            chals[0][0],
            chals[0][1],
            chals[0][2],
            phis[1],
            chals[1][0],
            chals[1][1],
            chals[1][2],
        ]);
        let kernel: Vec<Fp5> = (0..18).map(|_| rng.fp5()).collect();
        let claim = poly
            .iter()
            .zip(&kernel)
            .fold(Fp5::ZERO, |a, (&p, &k)| a + p * k);
        let mut st = Folding {
            kernel,
            points: Vec::new(),
            claim,
        };
        let (p1, _, c0) = prove_fold(&poly, &mut st, 0, &mut coins).unwrap();
        assert_eq!(c0, chals[0]);
        let (p2, _, _) = prove_fold(&p1, &mut st, 0, &mut coins).unwrap();
        assert_eq!(p2.len(), 6);
        // The claim follows the polynomial.
        let direct = p2
            .iter()
            .zip(&st.kernel)
            .fold(Fp5::ZERO, |a, (&p, &k)| a + p * k);
        assert_eq!(direct, st.claim);
        for j in 0..16 {
            let folded = fold_fiber(fiber(&code, &dims, j), dims.fiber_base(j), &chals);
            assert_eq!(folded, eval_at_base(&p2, dims.fiber_image(j)), "fiber {j}");
        }
        // A changed symbol changes the folded value.
        let mut symbols = fiber(&code, &dims, 3);
        symbols[2] += Fp5::ONE;
        assert_ne!(
            fold_fiber(symbols, dims.fiber_base(3), &chals),
            eval_at_base(&p2, dims.fiber_image(3))
        );
    }

    #[test]
    fn claim_chain_holds_with_point_terms_through_overflow() {
        // The identity of the prototype: after every fold, <P, kernel> equals the claim, with
        // point terms continued exactly past the end of the polynomial.
        let mut rng = Rng(13);
        let coeffs: Vec<Goldilocks> = (0..64).map(|_| rng.base()).collect();
        let mut kernel: Vec<Fp5> = (0..64).map(|_| rng.fp5()).collect();
        let points: Vec<(Fp5, Fp5)> = (0..3).map(|_| (rng.fp5(), rng.fp5())).collect();
        let tensor_claim = dot(&coeffs, &kernel);
        let evals: Fp5 = points
            .iter()
            .map(|&(w, x)| w * eval_poly(&coeffs, [x])[0])
            .fold(Fp5::ZERO, |a, b| a + b);
        add_points(&mut kernel, &points);
        assert_eq!(dot(&coeffs, &kernel), tensor_claim + evals);
        let mut st = Folding {
            kernel,
            points,
            claim: tensor_claim + evals,
        };
        let mut coins = FixedCoins {
            rng: Rng(99),
            indices: Vec::new(),
        };
        let (mut poly, _, _) = prove_fold(&coeffs, &mut st, 0, &mut coins).unwrap();
        for _ in 0..4 {
            assert_eq!(poly.len(), st.kernel.len());
            let direct = poly
                .iter()
                .zip(&st.kernel)
                .fold(Fp5::ZERO, |a, (&p, &k)| a + p * k);
            assert_eq!(direct, st.claim);
            poly = prove_fold(&poly, &mut st, 0, &mut coins).unwrap().0;
        }
        assert_eq!(poly.len(), 4);
        // A point term stays a point term: after a fold it is the evaluation kernel at `x^2`
        // with weight `w (1 + phi x)` on every coefficient, the last one included. Without the
        // continuation (v1's convention) the last coefficient is cut off.
        let (w, x) = (rng.fp5(), rng.fp5());
        let p: Vec<Fp5> = (0..6).map(|_| rng.fp5()).collect();
        let point_kernel = |w: Fp5, x: Fp5, len: usize| -> Vec<Fp5> {
            (0..len).map(|n| w * x.pow(n as u64)).collect()
        };
        for keep in [true, false] {
            let mut st = Folding {
                kernel: point_kernel(w, x, 6),
                points: if keep { vec![(w, x)] } else { Vec::new() },
                claim: w * eval_poly(&p, [x])[0],
            };
            let mut coins = FixedCoins {
                rng: Rng(98),
                indices: Vec::new(),
            };
            let phi = FixedCoins {
                rng: Rng(98),
                indices: Vec::new(),
            }
            .squeeze_fp5(b"");
            let (q, _, _) = prove_fold(&p, &mut st, 0, &mut coins).unwrap();
            let expected = point_kernel(w * (Fp5::ONE + phi * x), x.square(), 4);
            assert_eq!(st.kernel[..3], expected[..3]);
            assert_eq!(st.kernel[3] == expected[3], keep);
            if keep {
                assert_eq!(st.points, vec![(expected[0], x.square())]);
                assert_eq!(st.claim, expected[0] * eval_poly(&q, [x.square()])[0]);
            }
        }
    }

    #[test]
    fn roundtrip_both_profiles_and_serialization() {
        for profile in Profile::ALL {
            let f = fixture(profile, 21);
            let opening = prove(&f);
            assert!(check(&f, &opening));
            let mut bytes = vec![0xAA];
            opening.push_bytes(&mut bytes);
            let mut pos = 1;
            let back = Opening::read(&bytes, &mut pos, LOG_CELLS, &f.schedule).unwrap();
            assert_eq!(pos, bytes.len());
            assert_eq!(back, opening);
            // Truncation and a non-canonical limb are refused.
            let mut pos = 1;
            assert!(
                Opening::read(&bytes[..bytes.len() - 1], &mut pos, LOG_CELLS, &f.schedule)
                    .is_none()
            );
            let mut bad = bytes.clone();
            bad[1..9].copy_from_slice(&P.to_le_bytes());
            let mut pos = 1;
            assert!(Opening::read(&bad, &mut pos, LOG_CELLS, &f.schedule).is_none());
        }
        // The two profiles give different commitments and proofs.
        let a = fixture(Profile::CshakeJohnson400, 21);
        let b = fixture(Profile::TurboShakeJohnson400, 21);
        assert_ne!(a.st.root(), b.st.root());
        assert!(!verify(
            b.profile,
            &a.st.root(),
            LOG_CELLS,
            &a.schedule,
            &a.terms,
            a.claim,
            &prove(&a),
            &mut transcript(&a),
        ));
    }

    #[test]
    fn wrong_claim_terms_root_or_schedule_fail() {
        let f = fixture(Profile::CshakeJohnson400, 22);
        let opening = prove(&f);
        let run = |terms: &[TensorTerm], claim: Fp5, root: Digest, schedule: &Schedule| {
            verify(
                f.profile,
                &root,
                LOG_CELLS,
                schedule,
                terms,
                claim,
                &opening,
                &mut transcript(&f),
            )
        };
        assert!(run(&f.terms, f.claim, f.st.root(), &f.schedule));
        assert!(!run(&f.terms, f.claim + Fp5::ONE, f.st.root(), &f.schedule));
        let mut terms = f.terms.clone();
        terms[0].weight += Fp5::ONE;
        assert!(!run(&terms, f.claim, f.st.root(), &f.schedule));
        let mut terms = f.terms.clone();
        terms[0].point[LOG_CELLS - 1] += Fp5::ONE;
        assert!(!run(&terms, f.claim, f.st.root(), &f.schedule));
        let mut terms = f.terms.clone();
        terms[1].point.push(Fp5::ONE);
        assert!(!run(&terms, f.claim, f.st.root(), &f.schedule));
        let mut root = f.st.root();
        root[0] ^= 1;
        assert!(!run(&f.terms, f.claim, root, &f.schedule));
        let mut schedule = f.schedule.clone();
        schedule.stages[0].num_queries -= 1;
        assert!(!run(&f.terms, f.claim, f.st.root(), &schedule));
        let mut schedule = f.schedule.clone();
        schedule.stages.pop();
        assert!(!run(&f.terms, f.claim, f.st.root(), &schedule));
    }

    #[test]
    fn every_opening_field_is_bound() {
        let f = fixture(Profile::TurboShakeJohnson400, 23);
        let opening = prove(&f);
        assert!(check(&f, &opening));
        let bump = Fp5::X.pow(3);
        let mut cases: Vec<(&str, Opening)> = Vec::new();
        let mut add = |name: &'static str, edit: &dyn Fn(&mut Opening)| {
            let mut o = opening.clone();
            edit(&mut o);
            assert_ne!(o, opening, "{name}: the edit changed nothing");
            cases.push((name, o));
        };
        for j in 0..MASK_POINTS {
            add("mask eval", &|o| o.mask_evals[j] += bump);
        }
        for k in 0..5 {
            add("stage-0 fold scalar", &|o| o.stage0_folds[1][k] += bump);
            add("later fold scalar", &|o| o.stages[0].folds[0][k] += bump);
            add("last fold scalar", &|o| o.stages[1].folds[0][k] += bump);
        }
        add("mask claim", &|o| o.mask_claim += bump);
        add("stage-1 root", &|o| o.stages[0].root[7] ^= 1);
        add("stage-2 root", &|o| o.stages[1].root[49] ^= 0x80);
        add("ood eval", &|o| o.stages[0].ood[1] += bump);
        add("ood eval 2", &|o| o.stages[1].ood[0] += bump);
        add("opened Z symbol", &|o| {
            o.stage0_query.leaves[2].z[3] += Goldilocks::ONE
        });
        add("opened R symbol", &|o| o.stage0_query.leaves[0].r += bump);
        add("salt", &|o| o.stage0_query.leaves[1].salt[31] ^= 1);
        add("stage-0 sibling", &|o| o.stage0_query.siblings[0][0] ^= 1);
        add("stage-0 sibling dropped", &|o| {
            o.stage0_query.siblings.pop();
        });
        add("stage-0 leaf dropped", &|o| {
            o.stage0_query.leaves.pop();
        });
        add("stage-1 symbol", &|o| {
            o.stages[0].query.leaves[1][2] += bump
        });
        add("stage-1 sibling", &|o| {
            o.stages[0].query.siblings[1][3] ^= 1
        });
        add("stage-2 symbol", &|o| {
            o.stages[1].query.leaves[0][1] += bump
        });
        add("stage-2 sibling", &|o| {
            o.stages[1].query.siblings[0][9] ^= 1
        });
        add("stage-2 sibling added", &|o| {
            o.stages[1].query.siblings.push([0u8; DIGEST_BYTES])
        });
        for k in [0usize, 7, 8, 9] {
            add("terminal coefficient", &|o| o.final_coeffs[k] += bump);
        }
        add("terminal coefficient dropped", &|o| {
            o.final_coeffs.pop();
        });
        add("two leaves swapped", &|o| o.stage0_query.leaves.swap(0, 1));
        assert!(cases.len() > 40);
        for (name, o) in &cases {
            assert!(!check(&f, o), "accepted a proof with a changed {name}");
        }
    }

    #[test]
    fn good_event_predicates() {
        let mut rng = Rng(31);
        let omegas: Vec<Fp5> = (0..5).map(|_| rng.fp5()).collect();
        assert!(mask_points_good(&omegas, 2));
        // A point whose 2^s-th power is in the base field.
        let zeta4 = Goldilocks::two_adic_generator(2);
        let mut bad = omegas.clone();
        bad[3] = Fp5::from_base(zeta4 * rng.base());
        assert!(!mask_points_good(&bad, 2));
        // Conjugate points, and points whose 2^s-th powers are conjugate.
        let mut bad = omegas.clone();
        bad[4] = bad[1].frobenius_pow(3);
        assert!(!mask_points_good(&bad, 2));
        let mut bad = omegas.clone();
        bad[0] = bad[2].frobenius() * Fp5::from_base(zeta4);
        assert!(!mask_points_good(&bad, 2));
        assert!(mask_points_good(&bad, 1));
        let mut bad = omegas.clone();
        bad[2] = bad[1];
        assert!(!mask_points_good(&bad, 2));
        let mut bad = omegas.clone();
        bad[0] = Fp5::ZERO;
        assert!(!mask_points_good(&bad, 2));

        let xs = [rng.fp5(), rng.fp5()];
        assert!(fold_challenge_good(rng.fp5(), &xs));
        assert!(!fold_challenge_good(Fp5::ZERO, &xs));
        assert!(!fold_challenge_good(-xs[1].inverse(), &xs));
    }

    #[test]
    fn prover_aborts_outside_good() {
        let f = fixture(Profile::CshakeJohnson400, 24);
        let kernel = kernel_of(&f.terms, LOG_CELLS);
        struct Scripted {
            inner: FixedCoins,
            at: usize,
            value: Fp5,
            count: usize,
        }
        impl Channel for Scripted {
            fn absorb(&mut self, _: &[u8], _: &[u8]) {}
            fn squeeze_fp5(&mut self, l: &[u8]) -> Fp5 {
                self.count += 1;
                if self.count - 1 == self.at {
                    self.value
                } else {
                    self.inner.squeeze_fp5(l)
                }
            }
            fn squeeze_distinct_indices(&mut self, l: &[u8], n: usize, c: usize) -> Vec<usize> {
                self.inner.squeeze_distinct_indices(l, n, c)
            }
        }
        let run = |at: usize, value: Fp5| {
            let mut ch = Scripted {
                inner: FixedCoins {
                    rng: Rng(5),
                    indices: (0..256).collect(),
                },
                at,
                value,
                count: 0,
            };
            open(&f.st, kernel.clone(), f.claim, &mut ch).is_err()
        };
        // Draw order: five points, five weights, then per fold phi, theta, alpha, beta.
        assert!(!run(usize::MAX, Fp5::ZERO));
        assert!(run(2, Fp5::from_u64(9)), "mask point in the base field");
        assert!(run(7, Fp5::ZERO), "zero weight");
        assert!(run(10, Fp5::ZERO), "phi_0 = 0");
        assert!(run(14, Fp5::ZERO), "phi_1 = 0");
        assert!(!run(11, Fp5::ZERO), "theta may be zero");
        // Draws 18..=23 are beta_R, two out-of-domain points, their weights and gamma; 24 is
        // phi of the first later fold, which is not constrained.
        assert!(!run(24, Fp5::ZERO));
    }

    /// Rank over `F_p` by Gaussian elimination.
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

    /// The view of Lemmas V2.2 and V2.3 as base-field coordinates: the opened symbols of the
    /// table codeword, the out-of-domain values and the Stage-0 fold scalars, under fixed
    /// coins, computed by the prover's own routines.
    fn stage0_view(
        coeffs: &[Goldilocks],
        kernel: &[Fp5],
        points: usize,
        fibers: &[usize],
    ) -> Vec<Goldilocks> {
        let schedule = toy_schedule();
        let dims = stage_dims(LOG_CELLS, &schedule).unwrap();
        let d0 = dims[0];
        let code = encode_base(coeffs, d0.log_domain);
        let mut view: Vec<Goldilocks> = fibers.iter().flat_map(|&j| fiber(&code, &d0, j)).collect();
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
        .expect("fixed coins in Good");
        assert_eq!(red.folds.len(), d0.step_vars);
        view.extend(red.mask_evals.iter().flat_map(|a| a.to_limbs()));
        view.extend(red.folds.iter().flatten().flat_map(|a| a.to_limbs()));
        view
    }

    fn blinder_rank(points: usize) -> (usize, usize, usize) {
        let mut rng = Rng(41);
        let n = 1usize << LOG_CELLS;
        let (s, q0) = (2usize, 2usize);
        let blind = (q0 + 5 * points) << s;
        let fibers = [3usize, 100];
        let mut coeffs: Vec<Goldilocks> = (0..n).map(|_| rng.base()).collect();
        coeffs[n - blind..].fill(Goldilocks::ZERO);
        // An arbitrary kernel that reads no blinder coefficient.
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
    }

    #[test]
    fn blinders_cover_the_stage0_view_with_five_points_and_not_with_four() {
        // |Q| + 25 (s + 1) with |Q| = 8 opened symbols and s = 2.
        let (blind, dims, r) = blinder_rank(5);
        assert_eq!((blind, dims), (108, 8 + 25 * 3));
        assert_eq!(r, dims, "the view is not uniform");
        // Four points expose 20 coordinates of out-of-domain values and still 25 per fold.
        let (blind, dims, r) = blinder_rank(4);
        assert_eq!((blind, dims), (88, 8 + 20 + 50));
        assert!(
            r < dims,
            "four points should not cover five scalars per fold"
        );
        assert_eq!(r, 8 + 20 * 3);
    }
}
