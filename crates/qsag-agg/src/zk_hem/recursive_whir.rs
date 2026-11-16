//! Fixed-topology Poseidon2 WHIR verifier and its committed zk-Hem relation.
//!
//! This is a separately domain-separated opening mode, not a decoder for the legacy
//! byte-transcript/Steiner proofs. It uses the same CWYZ affine primal/dual folds,
//! two OOD pins per oracle, rate escalation, and terminal contraction, but distinct
//! fixed-path queries from a bounded partial Fisher-Yates shuffle.
//! Thus circuit shape depends only on the public schedule and polynomial dimension.
//! A merge certifies `k` PCS opening statements, each bound to a caller-supplied shard
//! header, not signature verification or quorum authorization. The caller must connect
//! these openings to the relevant child relation ([`crate::recursive`] does so for shard
//! summaries).
//! The bounded-query security labels retain their assumptions; this new transcript's
//! composed QROM reduction has not been mechanized.

use super::protocol::{self, PublicHemProof, ZkHemError};
use super::relation::{ConstraintSystem, Lc, Shape, poseidon2_perm};
use crate::field::{Goldilocks as F, GoldilocksExt4 as E, GoldilocksOps as _};
use crate::pcs::{WhirSchedule, WhirSecurityRegime, hypercube_to_monomial_coeffs};
use crate::sponge::poseidon2_perm12;
use alloc::{vec, vec::Vec};

pub type Digest = [F; 4];

// Separate field-native framing from every byte-oriented transcript and Merkle domain.
const VERSION: u64 = 0x4657_4849_5200_0001;
const LEAF: u64 = 0x4657_4C45_4146;
const NODE: u64 = 0x4657_4E4F_4445;
const MERGE: u64 = 0x4657_4D45_5247;

pub(crate) fn f(v: u64) -> F {
    F::from_u64_reduced(v)
}

pub(crate) trait Base: Clone {
    fn constant(v: F) -> Self;
    fn plus(&self, rhs: &Self) -> Self;
    fn minus(&self, rhs: &Self) -> Self;
    fn scale(&self, k: F) -> Self;
}
impl Base for F {
    fn constant(v: F) -> Self {
        v
    }
    fn plus(&self, rhs: &Self) -> Self {
        *self + *rhs
    }
    fn minus(&self, rhs: &Self) -> Self {
        *self - *rhs
    }
    fn scale(&self, k: F) -> Self {
        self.const_mul(k)
    }
}
impl Base for Lc {
    fn constant(v: F) -> Self {
        Lc::constant(v)
    }
    fn plus(&self, rhs: &Self) -> Self {
        self.plus(rhs)
    }
    fn minus(&self, rhs: &Self) -> Self {
        self.minus(rhs)
    }
    fn scale(&self, k: F) -> Self {
        self.scaled(k)
    }
}
pub(crate) trait Backend {
    type W: Base;
    fn alloc(&mut self, v: F) -> Self::W;
    fn value(&self, v: &Self::W) -> F;
    fn mul(&mut self, a: &Self::W, b: &Self::W) -> Self::W;
    fn equal(&mut self, a: &Self::W, b: &Self::W);
    /// One row `a * b = c` without a fresh product variable.
    fn product(&mut self, a: &Self::W, b: &Self::W, c: &Self::W);
    fn perm(&mut self, s: &mut [Self::W; 12]);
    fn pin(&mut self, v: Self::W) -> Self::W {
        let out = self.alloc(self.value(&v));
        self.equal(&out, &v);
        out
    }
}
#[derive(Default)]
pub(crate) struct Native {
    pub(crate) failed: bool,
}
impl Backend for Native {
    type W = F;
    fn alloc(&mut self, v: F) -> F {
        v
    }
    fn value(&self, v: &F) -> F {
        *v
    }
    fn mul(&mut self, a: &F, b: &F) -> F {
        a.const_mul(*b)
    }
    fn equal(&mut self, a: &F, b: &F) {
        self.failed |= a != b;
    }
    fn product(&mut self, a: &F, b: &F, c: &F) {
        self.failed |= a.const_mul(*b) != *c;
    }
    fn perm(&mut self, s: &mut [F; 12]) {
        poseidon2_perm12(s);
    }
    fn pin(&mut self, v: F) -> F {
        v
    }
}
/// Row census of a gadget: counts what [`ConstraintSystem`] would emit, without storing it.
/// `rows` are multiplication rows; each permutation adds one 128-row aligned block.
#[cfg(test)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Counter {
    pub(crate) perms: usize,
    pub(crate) rows: usize,
    pub(crate) vars: usize,
    /// `(permutations, multiplication rows)` by the section named by [`census`].
    pub(crate) sections: alloc::collections::BTreeMap<&'static str, (usize, usize)>,
}
#[cfg(test)]
std::thread_local! {
    static CENSUS_SECTION: core::cell::Cell<&'static str> = const { core::cell::Cell::new("") };
}
/// Name the verifier section the following rows belong to (a census label, test builds only).
#[inline(always)]
pub(crate) fn census(_section: &'static str) {
    #[cfg(test)]
    CENSUS_SECTION.with(|s| s.set(_section));
}
#[cfg(test)]
impl Counter {
    pub(crate) fn total_rows(&self) -> usize {
        128 * self.perms + self.rows
    }
    fn tally(&mut self, perms: usize, rows: usize) {
        self.perms += perms;
        self.rows += rows;
        let entry = self
            .sections
            .entry(CENSUS_SECTION.with(core::cell::Cell::get))
            .or_default();
        entry.0 += perms;
        entry.1 += rows;
    }
}
#[cfg(test)]
impl Backend for Counter {
    type W = F;
    fn alloc(&mut self, v: F) -> F {
        self.vars += 1;
        v
    }
    fn value(&self, v: &F) -> F {
        *v
    }
    fn mul(&mut self, a: &F, b: &F) -> F {
        self.tally(0, 1);
        self.vars += 1;
        a.const_mul(*b)
    }
    fn equal(&mut self, _a: &F, _b: &F) {
        self.tally(0, 1);
    }
    fn product(&mut self, _a: &F, _b: &F, _c: &F) {
        self.tally(0, 1);
    }
    fn perm(&mut self, s: &mut [F; 12]) {
        self.tally(1, 0);
        poseidon2_perm12(s);
    }
}
/// Execute the same gadget in field arithmetic, recording every allocated wire
/// in synthesis order. In particular `pin` allocates and each permutation records
/// all 118 S-box outputs. The compiled Shape still checks the whole assignment.
#[derive(Default)]
pub(crate) struct Assignment {
    pub(crate) values: Vec<F>,
    pub(crate) p2_values: Vec<F>,
    pub(crate) aligned: bool,
}
impl Assignment {
    pub(crate) fn hologram_aligned() -> Self {
        Self {
            values: Vec::new(),
            p2_values: Vec::new(),
            aligned: true,
        }
    }
}
impl Backend for Assignment {
    type W = F;
    fn alloc(&mut self, v: F) -> F {
        self.values.push(v);
        v
    }
    fn value(&self, v: &F) -> F {
        *v
    }
    fn mul(&mut self, a: &F, b: &F) -> F {
        self.alloc(a.const_mul(*b))
    }
    fn equal(&mut self, _a: &F, _b: &F) {}
    fn product(&mut self, _a: &F, _b: &F, _c: &F) {}
    fn perm(&mut self, s: &mut [F; 12]) {
        let mut outputs = [F::ZERO; 118];
        *s = crate::trace::record_poseidon2_perm12(*s, &mut outputs);
        if self.aligned {
            self.p2_values.extend(outputs);
            self.p2_values.extend([F::ZERO; 10]);
        } else {
            self.values.extend(outputs);
        }
    }
}

impl Backend for ConstraintSystem {
    type W = Lc;
    fn alloc(&mut self, v: F) -> Lc {
        ConstraintSystem::alloc(self, v).into()
    }
    fn value(&self, v: &Lc) -> F {
        self.eval(v)
    }
    fn mul(&mut self, a: &Lc, b: &Lc) -> Lc {
        ConstraintSystem::mul(self, a, b).into()
    }
    fn equal(&mut self, a: &Lc, b: &Lc) {
        self.enforce_equal(a, b);
    }
    fn product(&mut self, a: &Lc, b: &Lc, c: &Lc) {
        self.enforce_mul(a.clone(), b.clone(), c.clone());
    }
    fn perm(&mut self, s: &mut [Lc; 12]) {
        poseidon2_perm(self, s);
    }
}

/// Tower limbs [1, u, v, uv], u²=7, v²=u (polynomial order [1,v²,v,v³]).
#[derive(Clone)]
pub(crate) struct Ext<W: Base>(pub(crate) [W; 4]);
impl<W: Base> Ext<W> {
    pub(crate) fn constant(v: E) -> Self {
        Self(v.to_limbs().map(W::constant))
    }
    pub(crate) fn zero() -> Self {
        Self::constant(E::ZERO)
    }
    pub(crate) fn one() -> Self {
        Self::constant(E::ONE)
    }
    pub(crate) fn base(v: W) -> Self {
        Self([
            v,
            W::constant(F::ZERO),
            W::constant(F::ZERO),
            W::constant(F::ZERO),
        ])
    }
    pub(crate) fn alloc<B: Backend<W = W>>(b: &mut B, v: E) -> Self {
        Self(v.to_limbs().map(|v| b.alloc(v)))
    }
    /// A base-field value: only limb zero is a wire, the other limbs are the constant zero.
    pub(crate) fn alloc_base<B: Backend<W = W>>(b: &mut B, v: E) -> Self {
        Self::base(b.alloc(v.to_limbs()[0]))
    }
    pub(crate) fn value<B: Backend<W = W>>(&self, b: &B) -> E {
        E::from_limbs(core::array::from_fn(|i| b.value(&self.0[i])))
    }
    pub(crate) fn add(&self, v: &Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i].plus(&v.0[i])))
    }
    pub(crate) fn sub(&self, v: &Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i].minus(&v.0[i])))
    }
    pub(crate) fn scale(&self, k: F) -> Self {
        Self(core::array::from_fn(|i| self.0[i].scale(k)))
    }
    pub(crate) fn mul_base<B: Backend<W = W>>(&self, b: &mut B, v: &W) -> Self {
        Self(core::array::from_fn(|i| b.mul(&self.0[i], v)))
    }
    pub(crate) fn mul<B: Backend<W = W>>(&self, b: &mut B, v: &Self) -> Self {
        // Regard the tower as F[v]/(v^4 - 7), with polynomial-order
        // limbs [0,2,1,3]. Seven products at 0..6 determine the degree-six
        // product exactly; interpolate and reduce v^4=7. No witness-dependent
        // branch or random evaluation replaces the multiplication identity.
        const REDUCE: [[u64; 7]; 4] = [
            [
                17806232122559911257,
                768614336225607671,
                384307168112803860,
                3586866902386169150,
                7301836194143272976,
                9991986370932899835,
                15500389113883088215,
            ],
            [
                1255403415835159213,
                13988780919306059768,
                4227378849240842255,
                11785419822125984413,
                11144907875271311369,
                13988780919306059774,
                17396304476572920492,
            ],
            [
                12067245078742040574,
                15372286724512153608,
                4995993185466449910,
                15372286724512153611,
                4227378849240842234,
                15987178193492639747,
                5764607521692057600,
            ],
            [
                384307168112803839,
                3074457344902430725,
                11144907875271311351,
                12297829379609722891,
                7301836194143272954,
                15372286724512153603,
                5764607521692057600,
            ],
        ];
        let evaluate = |x: &Self, t: u64| {
            x.0[0]
                .plus(&x.0[2].scale(f(t)))
                .plus(&x.0[1].scale(f(t * t)))
                .plus(&x.0[3].scale(f(t * t * t)))
        };
        let products: [W; 7] =
            core::array::from_fn(|i| b.mul(&evaluate(self, i as u64), &evaluate(v, i as u64)));
        // Materialize the interpolated limbs once. Reusing seven-term output forms
        // in later products inflates the sparse hologram even when row counts look small.
        Self(core::array::from_fn(|i| {
            let limb = products
                .iter()
                .zip(REDUCE[i])
                .fold(W::constant(F::ZERO), |a, (p, c)| a.plus(&p.scale(f(c))));
            b.pin(limb)
        }))
    }

    pub(crate) fn equal<B: Backend<W = W>>(&self, b: &mut B, v: &Self) {
        for i in 0..4 {
            b.equal(&self.0[i], &v.0[i]);
        }
    }
}

#[derive(Clone)]
pub(crate) struct Transcript<W: Base> {
    pub(crate) state: [W; 12],
}
impl<W: Base> Transcript<W> {
    pub(crate) fn new() -> Self {
        Self {
            state: core::array::from_fn(|_| W::constant(F::ZERO)),
        }
    }
    // Fixed-length, domain-separated duplex frames. Capacity receives tag and length;
    // padding is mandatory even at an exact rate boundary.
    pub(crate) fn absorb<B: Backend<W = W>>(&mut self, b: &mut B, tag: u64, msg: &[W]) {
        self.state[10] = self.state[10].plus(&W::constant(f(tag)));
        self.state[11] = self.state[11].plus(&W::constant(f(msg.len() as u64)));
        for chunk in msg.chunks(6) {
            for (a, c) in self.state.iter_mut().zip(chunk) {
                *a = a.plus(c);
            }
            if chunk.len() < 6 {
                self.state[chunk.len()] = self.state[chunk.len()].plus(&W::constant(F::ONE));
            }
            b.perm(&mut self.state);
        }
        if msg.len().is_multiple_of(6) {
            self.state[0] = self.state[0].plus(&W::constant(F::ONE));
            b.perm(&mut self.state);
        }
    }
    pub(crate) fn ext<B: Backend<W = W>>(&mut self, b: &mut B, tag: u64) -> Ext<W> {
        self.absorb(b, tag, &[]);
        // A challenge enters many products: give it single-variable limbs. The state
        // itself stays a linear form over the permutation's last S-box outputs.
        Ext(core::array::from_fn(|i| b.pin(self.state[i].clone())))
    }
    pub(crate) fn absorb_exts<B: Backend<W = W>>(&mut self, b: &mut B, tag: u64, es: &[Ext<W>]) {
        let words: Vec<_> = es.iter().flat_map(|e| e.0.clone()).collect();
        self.absorb(b, tag, &words);
    }
}

/// Little-endian Boolean decomposition. Below 64 bits the integer sum cannot reach `p`;
/// at 64 bits the alias `x + p` is excluded explicitly.
pub(crate) fn bits<B: Backend>(b: &mut B, value: &B::W, n: usize) -> Vec<B::W> {
    assert!(n <= 64);
    let raw = b.value(value).to_canonical_u64();
    let zero = B::W::constant(F::ZERO);
    let one = B::W::constant(F::ONE);
    let out: Vec<_> = (0..n)
        .map(|i| {
            let v = b.alloc(f((raw >> i) & 1));
            b.product(&v, &one.minus(&v), &zero);
            v
        })
        .collect();
    let weighted = |bits: &[B::W]| {
        bits.iter()
            .enumerate()
            .fold(zero.clone(), |a, (i, bit)| a.plus(&bit.scale(f(1u64 << i))))
    };
    b.equal(value, &weighted(&out));
    if n == 64 {
        // p = 2^64 - 2^32 + 1: when the high 32 bits are all one, the low 32 must be zero.
        let mut high = out[32].clone();
        for v in &out[33..] {
            high = b.mul(&high, v);
        }
        b.product(&high, &weighted(&out[..32]), &zero);
    }
    out
}

/// The canonical representative of `word` has `difficulty` trailing zero bits.
fn low_bits_zero<B: Backend>(b: &mut B, word: &B::W, difficulty: u32) {
    if difficulty == 0 {
        return;
    }
    assert!(difficulty <= 64);
    if difficulty == 64 {
        b.equal(word, &B::W::constant(F::ZERO));
        return;
    }
    let n = 64 - difficulty as usize;
    let high = b.alloc(f(b.value(word).to_canonical_u64() >> difficulty));
    let binary = bits(b, &high, n);
    b.equal(word, &high.scale(f(1u64 << difficulty)));
    // Exclude high * 2^difficulty >= p; when the high 32 bits are all
    // ones the remaining low bits must be zero. For difficulty >= 32
    // the bit width alone already proves the canonical bound.
    if difficulty < 32 {
        let split = 32 - difficulty as usize;
        let mut all = binary[split].clone();
        for bit in &binary[split + 1..] {
            all = b.mul(&all, bit);
        }
        let low = binary[..split]
            .iter()
            .enumerate()
            .fold(B::W::constant(F::ZERO), |sum, (i, bit)| {
                sum.plus(&bit.scale(f(1 << i)))
            });
        b.product(&all, &low, &B::W::constant(F::ZERO));
    }
}

fn pow<B: Backend>(b: &mut B, tr: &mut Transcript<B::W>, nonce: [u32; 2], difficulty: u32) {
    let limbs = nonce.map(|v| b.alloc(f(u64::from(v))));
    if difficulty == 0 {
        // No grinding: the nonce is pinned to zero and stays out of the transcript.
        for limb in &limbs {
            b.equal(limb, &B::W::constant(F::ZERO));
        }
        return;
    }
    for limb in &limbs {
        bits(b, limb, 32);
    }
    let mut challenge = tr.clone();
    challenge.absorb(b, 30, &limbs);
    low_bits_zero(b, &challenge.state[0], difficulty);
    tr.absorb(b, 31, &limbs);
}
fn grind(tr: &Transcript<F>, difficulty: u32) -> [u32; 2] {
    if difficulty == 0 {
        return [0; 2];
    }
    let mut b = Native::default();
    for nonce in 0..u64::MAX {
        let limbs = [nonce as u32, (nonce >> 32) as u32];
        let mut trial = tr.clone();
        trial.absorb(&mut b, 30, &limbs.map(|x| f(u64::from(x))));
        if trial.state[0].to_canonical_u64() & ((1u64 << difficulty) - 1) == 0 {
            return limbs;
        }
    }
    unreachable!("PoW nonce space exhausted")
}

fn compress<B: Backend>(
    b: &mut B,
    left: &[B::W; 4],
    right: &[B::W; 4],
    stage: usize,
    level: usize,
) -> [B::W; 4] {
    let tweak = [f(NODE), f(stage as u64), f(level as u64), f(VERSION)].map(B::W::constant);
    let mut state = core::array::from_fn(|i| {
        if i < 4 {
            left[i].clone()
        } else if i < 8 {
            right[i - 4].clone()
        } else {
            tweak[i - 8].clone()
        }
    });
    b.perm(&mut state);
    core::array::from_fn(|i| {
        b.pin(
            state[i]
                .plus(&left[i])
                .plus(&right[i].scale(F::TWO))
                .plus(&tweak[i].scale(f(4))),
        )
    })
}
/// Leaf digest of one fiber. Stage 0 commits a base-field codeword, so its leaves hash one
/// limb per value; later stages hash all four.
fn leaf<B: Backend>(b: &mut B, stage: usize, index: &B::W, values: &[Ext<B::W>]) -> [B::W; 4] {
    let mut msg = vec![
        B::W::constant(f(VERSION)),
        B::W::constant(f(stage as u64)),
        index.clone(),
    ];
    if stage == 0 {
        msg.extend(values.iter().map(|v| v.0[0].clone()));
    } else {
        msg.extend(values.iter().flat_map(|v| v.0.clone()));
    }
    let mut tr = Transcript::new();
    tr.absorb(b, LEAF, &msg);
    core::array::from_fn(|i| b.pin(tr.state[i].clone()))
}

/// Canopy height capped at 5 levels (at most 32 leaves = 1 KiB per stage), trimming the top 5
/// Merkle siblings from every query path while eliminating per-query upper-sibling muxes.
pub(super) const CANOPY_MAX_DEPTH: usize = 5;

#[inline]
pub(super) fn canopy_split(path_depth: usize) -> (usize, usize) {
    let depth = path_depth.min(CANOPY_MAX_DEPTH);
    (depth, path_depth - depth)
}

/// One explicitly authenticated coset fiber. `siblings` carries only the bottom `base_level`
/// digests below the stage canopy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPathQuery {
    pub values: Vec<E>,
    pub siblings: Vec<Digest>,
}
/// Private witness for a fixed-path affine WHIR opening. The parent never serializes this.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPathWhirProof {
    pub stage_roots: Vec<Digest>,
    pub canopy_leaves: Vec<Vec<Digest>>,
    pub ood_evals: Vec<[E; 2]>,
    pub fold_polys: Vec<[E; 5]>,
    pub fold_nonces: Vec<[u32; 2]>,
    pub query_nonces: Vec<[u32; 2]>,
    pub queries: Vec<Vec<FixedPathQuery>>,
    pub final_coeffs: Vec<E>,
}
/// Public PCS statement, bound to a caller-supplied shard header digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChildWhirStatement {
    pub shard_header: [u8; 32],
    pub commitment: Digest,
    pub point: Vec<E>,
    pub value: E,
}
impl ChildWhirStatement {
    fn words(&self) -> Vec<F> {
        let mut out: Vec<_> = self
            .shard_header
            .as_chunks::<4>()
            .0
            .iter()
            .map(|x| f(u64::from(u32::from_le_bytes(*x))))
            .collect();
        out.extend(self.commitment);
        out.extend(self.point.iter().flat_map(|v| v.to_limbs()));
        out.extend(self.value.to_limbs());
        out
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursiveWhirError {
    InvalidParameters,
    MalformedProof,
    InvalidOpening,
    ZkHem(ZkHemError),
}

/// Pin the verifier geometry. Only the two Poseidon2 profiles are accepted.
/// domain_log2 is the log of the first RS oracle's domain, including blowup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPathWhirParams {
    pub schedule: WhirSchedule,
    pub domain_log2: usize,
}
impl FixedPathWhirParams {
    pub fn new(regime: WhirSecurityRegime, num_vars: usize) -> Result<Self, RecursiveWhirError> {
        if !(2..=crate::pcs::MAX_PCS_NUM_VARS).contains(&num_vars)
            || !regime.uses_poseidon2_canopy()
        {
            return Err(RecursiveWhirError::InvalidParameters);
        }
        let schedule = regime.schedule(num_vars);
        let domain_log2 = num_vars + schedule.stages[0].blowup.trailing_zeros() as usize;
        Ok(Self {
            schedule,
            domain_log2,
        })
    }
    pub fn num_vars(&self) -> Option<usize> {
        let stage = self.schedule.stages.first()?;
        let nv = self
            .domain_log2
            .checked_sub(stage.blowup.trailing_zeros() as usize)?;
        (self.schedule.validate(nv) && self.schedule.regime.uses_poseidon2_canopy()).then_some(nv)
    }
    fn geometries(&self) -> Vec<(usize, usize, usize)> {
        let mut rem = self.num_vars().expect("validated parameters");
        self.schedule
            .stages
            .iter()
            .map(|s| {
                let arity = 1 << s.step_vars;
                let groups = (1usize << rem) * s.blowup / arity;
                rem -= s.step_vars;
                (arity, groups, s.num_queries.min(groups))
            })
            .collect()
    }
    pub(super) fn placeholder(&self) -> FixedPathWhirProof {
        let nv = self.num_vars().expect("validated parameters");
        let geos = self.geometries();
        FixedPathWhirProof {
            stage_roots: vec![[F::ZERO; 4]; self.schedule.stages.len()],
            canopy_leaves: geos
                .iter()
                .map(|&(_, groups, _)| {
                    let (depth, _) = canopy_split(groups.trailing_zeros() as usize);
                    vec![[F::ZERO; 4]; 1usize << depth]
                })
                .collect(),
            ood_evals: vec![[E::ZERO; 2]; self.schedule.stages.len()],
            fold_polys: vec![[E::ZERO; 5]; nv - self.schedule.early_stop_vars],
            fold_nonces: vec![[0; 2]; nv - self.schedule.early_stop_vars],
            query_nonces: vec![[0; 2]; self.schedule.stages.len()],
            queries: geos
                .iter()
                .map(|&(arity, groups, count)| {
                    let (_, base_level) = canopy_split(groups.trailing_zeros() as usize);
                    vec![
                        FixedPathQuery {
                            values: vec![E::ZERO; arity],
                            siblings: vec![[F::ZERO; 4]; base_level],
                        };
                        count
                    ]
                })
                .collect(),
            final_coeffs: vec![E::ZERO; (1 << self.schedule.early_stop_vars) + 2],
        }
    }
    pub(super) fn well_formed(
        &self,
        statement: &ChildWhirStatement,
        proof: &FixedPathWhirProof,
    ) -> bool {
        let Some(nv) = self.num_vars() else {
            return false;
        };
        let stages = self.schedule.stages.len();
        let geos = self.geometries();
        statement.point.len() == nv
            && proof.stage_roots.len() == stages
            && proof.canopy_leaves.len() == stages
            && proof.ood_evals.len() == stages
            && proof.fold_polys.len() == nv - self.schedule.early_stop_vars
            && proof.fold_nonces.len() == proof.fold_polys.len()
            && proof.query_nonces.len() == stages
            && proof.final_coeffs.len() == (1 << self.schedule.early_stop_vars) + 2
            && proof.queries.len() == stages
            && geos
                .iter()
                .zip(&proof.canopy_leaves)
                .zip(&proof.queries)
                .all(|((&(arity, groups, count), leaves), queries)| {
                    let (depth, base_level) = canopy_split(groups.trailing_zeros() as usize);
                    leaves.len() == (1usize << depth)
                        && queries.len() == count
                        && queries
                            .iter()
                            .all(|q| q.values.len() == arity && q.siblings.len() == base_level)
                })
            // The committed polynomial and its first codeword are over the base field.
            && proof.queries[0]
                .iter()
                .flat_map(|q| &q.values)
                .all(|v| v.to_limbs()[1..] == [F::ZERO; 3])
    }
}

fn start<B: Backend>(b: &mut B, params: &FixedPathWhirParams, public: &[B::W]) -> Transcript<B::W> {
    // Header bytes are represented by eight independent u32 limbs, without modular aliases.
    for word in &public[..8] {
        bits(b, word, 32);
    }
    let mut tr = Transcript::new();
    let mut geometry = vec![f(VERSION), f(params.domain_log2 as u64)];
    geometry.extend(params.schedule.to_bytes().iter().map(|&x| f(u64::from(x))));
    tr.absorb(
        b,
        1,
        &geometry.into_iter().map(B::W::constant).collect::<Vec<_>>(),
    );
    tr.absorb(b, 2, public);
    tr
}
// All comparisons synthesize the same constraints. Values choose only the assignments
// of inverse/slack witnesses, never control flow or coefficients of the relation.
pub(crate) fn equal_bit<B: Backend>(b: &mut B, a: &B::W, c: &B::W) -> B::W {
    let d = a.minus(c);
    let v = b.value(&d);
    let eq = b.alloc(if v == F::ZERO { F::ONE } else { F::ZERO });
    let inv = b.alloc(v.inv_or_zero());
    b.product(&d, &eq, &B::W::constant(F::ZERO));
    b.product(&d, &inv, &B::W::constant(F::ONE).minus(&eq));
    eq
}
/// `0 <= v <= max` as integers, with a bitwise comparison to the public
/// bound. At each zero bit of max, equality of its higher prefix forces this
/// bit to zero. No slack integer or modular comparison is trusted.
fn bounded<B: Backend>(b: &mut B, v: &B::W, max: u64) {
    let n = (64 - max.leading_zeros()) as usize;
    assert!(n < 64);
    let binary = bits(b, v, n);
    let mut prefix = B::W::constant(F::ONE);
    let mut first = true;
    for i in (0..n).rev() {
        // Trailing ones impose no further upper-bound condition.
        if max & ((1u64 << (i + 1)) - 1) == (1u64 << (i + 1)) - 1 {
            break;
        }
        if (max >> i) & 1 == 1 {
            prefix = if first {
                binary[i].clone()
            } else {
                b.mul(&prefix, &binary[i])
            };
            first = false;
        } else {
            b.product(&prefix, &binary[i], &B::W::constant(F::ZERO));
        }
    }
}
pub(crate) fn select<B: Backend>(b: &mut B, bit: &B::W, yes: &B::W, no: &B::W) -> B::W {
    let delta = yes.minus(no);
    let out = b.alloc(b.value(no) + b.value(bit).const_mul(b.value(&delta)));
    b.product(bit, &delta, &out.minus(no));
    out
}
// Canonical integer remainder of a uniform field challenge; the quotient and remainder
// bounds exclude modular wrap. At most ceil(p/divisor) preimages per remainder.
fn remainder<B: Backend>(b: &mut B, word: &B::W, divisor: u64) -> B::W {
    if divisor.is_power_of_two() {
        let binary = bits(b, word, 64);
        return binary[..divisor.trailing_zeros() as usize]
            .iter()
            .enumerate()
            .fold(B::W::constant(F::ZERO), |a, (i, bit)| {
                a.plus(&bit.scale(f(1u64 << i)))
            });
    }
    let raw = b.value(word).to_canonical_u64();
    let q = b.alloc(f(raw / divisor));
    let r = b.alloc(f(raw % divisor));
    let max = (crate::field::GOLDILOCKS_PRIME - 1) / divisor;
    bounded(b, &q, max);
    let n = (64 - (divisor - 1).leading_zeros()) as usize;
    bits(b, &r, n);
    let at_max = equal_bit(b, &q, &B::W::constant(f(max)));
    // One conditional upper bound replaces two separate range checks. If q
    // reaches floor((p-1)/d), the remainder is bounded by the final short tail;
    // otherwise it is bounded by d-1. Both r and slack are short integers.
    let tail = (crate::field::GOLDILOCKS_PRIME - 1) % divisor;
    let bound = B::W::constant(f(divisor - 1)).minus(&at_max.scale(f(divisor - 1 - tail)));
    let slack = b.alloc(f(b
        .value(&bound)
        .to_canonical_u64()
        .saturating_sub(raw % divisor)));
    bits(b, &slack, n);
    b.equal(&r.plus(&slack), &bound);
    b.equal(word, &q.scale(f(divisor)).plus(&r));
    r
}
/// Threshold above which partial Fisher-Yates switches from direct scan (`<= 20` swaps)
/// to BEGKN91 Poseidon2-bound offline memory checking (`O(Q)` rows instead of `O(Q^2)`).
const DIRECT_SAMPLER_MAX_QUERIES: usize = 20;

#[derive(Default)]
struct QuerySampler<W> {
    swaps: Vec<(W, W)>,
}
impl<W: Base> QuerySampler<W> {
    fn lookup<B: Backend<W = W>>(&self, b: &mut B, key: &W) -> W {
        let mut out = key.clone();
        for (k, v) in &self.swaps {
            let equal = equal_bit(b, key, k);
            out = select(b, &equal, v, &out);
        }
        out
    }
    fn next<B: Backend<W = W>>(
        &mut self,
        b: &mut B,
        tr: &mut Transcript<W>,
        groups: usize,
        count: usize,
        q: usize,
    ) -> (W, Vec<W>) {
        let depth = groups.trailing_zeros() as usize;
        let index = if count == groups {
            W::constant(f(q as u64))
        } else {
            let word = tr.ext(b, 40).0[0].clone();
            let rank = remainder(b, &word, (groups - q) as u64);
            let index = self.lookup(b, &rank);
            let replacement = self.lookup(b, &W::constant(f((groups - q - 1) as u64)));
            self.swaps.push((rank, replacement));
            index
        };
        let binary = bits(b, &index, depth);
        (index, binary)
    }
}

/// Sample `count` distinct coset indices in `0..groups` via partial Fisher-Yates.
///
/// For `count > DIRECT_SAMPLER_MAX_QUERIES` (`count < groups`), replaces the `O(Q^2)` linear
/// swap scan with an `O(Q)` BEGKN91 offline-memory multiset check over `K = groups.min(2 * count)`
/// strictly increasing addresses in `0..groups`, bound via Poseidon2 Fiat-Shamir on a fork of `tr`
/// after all `count` raw challenges have been squeezed (preserving `tr` identically).
fn sample_queries<B: Backend>(
    b: &mut B,
    tr: &mut Transcript<B::W>,
    groups: usize,
    count: usize,
) -> Vec<(B::W, Vec<B::W>)> {
    let depth = groups.trailing_zeros() as usize;
    if count == groups || count <= DIRECT_SAMPLER_MAX_QUERIES {
        let mut sampler = QuerySampler { swaps: Vec::new() };
        return (0..count)
            .map(|q| sampler.next(b, tr, groups, count, q))
            .collect();
    }

    // 1. Squeeze and range-reduce all `count` Fisher-Yates ranks from `tr`.
    let ranks: Vec<B::W> = (0..count)
        .map(|q| {
            let word = tr.ext(b, 40).0[0].clone();
            remainder(b, &word, (groups - q) as u64)
        })
        .collect();

    // 2. Deterministic untrusted witness hints from the concrete rank values.
    let cap = groups.min(2 * count);
    let mut mem = alloc::collections::BTreeMap::<usize, (usize, usize)>::new();
    let mut step_hints = Vec::with_capacity(count);
    for (q, rank_w) in ranks.iter().enumerate() {
        let r_raw = (b.value(rank_w).to_canonical_u64() as usize).min(groups - 1 - q);
        let a_rep = groups - 1 - q;
        let (rep_val, rep_ts) = mem.get(&a_rep).copied().unwrap_or((a_rep, 0));
        mem.insert(a_rep, (rep_val, 2 * q + 1));
        let (idx_val, idx_ts) = mem.get(&r_raw).copied().unwrap_or((r_raw, 0));
        mem.insert(r_raw, (rep_val, 2 * q + 2));
        step_hints.push((rep_val, rep_ts, idx_val, idx_ts));
    }
    let mut pad_addr = 0usize;
    while mem.len() < cap {
        mem.entry(pad_addr).or_insert((pad_addr, 0));
        pad_addr += 1;
    }
    let table_hints: Vec<(usize, usize, usize)> = mem
        .into_iter()
        .map(|(addr, (val, ts))| (addr, val, ts))
        .collect();
    debug_assert_eq!(table_hints.len(), cap);

    // 3. Allocate strictly ordered address table `0 <= a_0 < a_1 < ... < a_{K-1} < groups`
    //    and final `(val, ts)` entries, plus causal step `(rep_val, rep_ts, idx_val, idx_ts)`.
    let ts_bits = (2 * count + 1).next_power_of_two().trailing_zeros().max(1) as usize;
    assert!(depth <= 30 && ts_bits <= 10);
    let one = B::W::constant(F::ONE);

    let mut addr_w = Vec::with_capacity(cap);
    let mut fval_w = Vec::with_capacity(cap);
    let mut fts_w = Vec::with_capacity(cap);
    for (i, &(addr, fval, fts)) in table_hints.iter().enumerate() {
        let aw = b.alloc(f(addr as u64));
        let vw = b.alloc(f(fval as u64));
        let tw = b.alloc(f(fts as u64));
        if i == 0 {
            bits(b, &aw, depth);
        } else {
            let diff = aw.minus(&addr_w[i - 1]).minus(&one);
            bits(b, &diff, depth);
        }
        if i + 1 == cap {
            bits(b, &aw, depth);
        }
        bits(b, &vw, depth);
        bits(b, &tw, ts_bits);
        addr_w.push(aw);
        fval_w.push(vw);
        fts_w.push(tw);
    }

    let mut out = Vec::with_capacity(count);
    let mut rep_val_w = Vec::with_capacity(count);
    let mut rep_ts_w = Vec::with_capacity(count);
    let mut idx_ts_w = Vec::with_capacity(count);
    for (q, &(rv, rt, iv, it)) in step_hints.iter().enumerate() {
        let rvw = b.alloc(f(rv as u64));
        let rtw = b.alloc(f(rt as u64));
        let ivw = b.alloc(f(iv as u64));
        let itw = b.alloc(f(it as u64));
        bits(b, &rvw, depth);
        let bin = bits(b, &ivw, depth);
        bits(b, &rtw, ts_bits);
        bits(b, &B::W::constant(f((2 * q) as u64)).minus(&rtw), ts_bits);
        bits(b, &itw, ts_bits);
        bits(
            b,
            &B::W::constant(f((2 * q + 1) as u64)).minus(&itw),
            ts_bits,
        );
        rep_val_w.push(rvw);
        rep_ts_w.push(rtw);
        idx_ts_w.push(itw);
        out.push((ivw, bin));
    }

    // 4. Injectively pack all bit-bounded memory wires (`<= 30`-bit pairs, `<= 10`-bit 6-tuples)
    //    into a forked Poseidon2 transcript before squeezing `(alpha_mem, gamma_mem)`.
    let mut packed = Vec::with_capacity(cap + count + (cap + 2 * count).div_ceil(6) + 4);
    let pack_pairs = |dst: &mut Vec<B::W>, items: &[B::W]| {
        let shift = f(1u64 << 30);
        for chunk in items.chunks(2) {
            if chunk.len() == 2 {
                dst.push(chunk[0].plus(&chunk[1].scale(shift)));
            } else {
                dst.push(chunk[0].clone());
            }
        }
    };
    let pack_ts = |dst: &mut Vec<B::W>, items: &[B::W]| {
        for chunk in items.chunks(6) {
            let mut acc = B::W::constant(F::ZERO);
            for (j, w) in chunk.iter().enumerate() {
                acc = acc.plus(&w.scale(f(1u64 << (10 * j))));
            }
            dst.push(acc);
        }
    };
    pack_pairs(&mut packed, &addr_w);
    pack_pairs(&mut packed, &fval_w);
    pack_pairs(&mut packed, &rep_val_w);
    let idx_vals: Vec<B::W> = out.iter().map(|(iv, _)| iv.clone()).collect();
    pack_pairs(&mut packed, &idx_vals);
    let mut all_ts = Vec::with_capacity(cap + 2 * count);
    all_ts.extend_from_slice(&fts_w);
    all_ts.extend_from_slice(&rep_ts_w);
    all_ts.extend_from_slice(&idx_ts_w);
    pack_ts(&mut packed, &all_ts);

    let mut mem_tr = tr.clone();
    mem_tr.absorb(b, 41, &packed);
    let alpha = mem_tr.ext(b, 42);
    let gamma = mem_tr.ext(b, 43);
    let alpha2 = alpha.mul(b, &alpha);

    // 5. Grand-product memory check: Init * StepWrites == StepReads * Final.
    let tuple_dyn = |b: &mut B, addr: &B::W, val: &B::W, ts: &B::W| -> Ext<B::W> {
        let av = alpha.mul_base(b, val);
        let a2t = alpha2.mul_base(b, ts);
        gamma.sub(&Ext::base(addr.clone()).add(&av).add(&a2t))
    };
    let tuple_const_ts = |b: &mut B, addr: &B::W, val: &B::W, ts: u64| -> Ext<B::W> {
        let av = alpha.mul_base(b, val);
        let a2t = alpha2.scale(f(ts));
        gamma.sub(&Ext::base(addr.clone()).add(&av).add(&a2t))
    };

    let mut lhs = Ext::one();
    let mut rhs = Ext::one();
    for i in 0..cap {
        let init_f = tuple_const_ts(b, &addr_w[i], &addr_w[i], 0);
        let fin_f = tuple_dyn(b, &addr_w[i], &fval_w[i], &fts_w[i]);
        lhs = lhs.mul(b, &init_f);
        rhs = rhs.mul(b, &fin_f);
    }
    for q in 0..count {
        let a_rep = B::W::constant(f((groups - 1 - q) as u64));
        let r1 = tuple_dyn(b, &a_rep, &rep_val_w[q], &rep_ts_w[q]);
        let w1 = tuple_const_ts(b, &a_rep, &rep_val_w[q], (2 * q + 1) as u64);
        let r2 = tuple_dyn(b, &ranks[q], &out[q].0, &idx_ts_w[q]);
        let w2 = tuple_const_ts(b, &ranks[q], &rep_val_w[q], (2 * q + 2) as u64);
        rhs = rhs.mul(b, &r1);
        rhs = rhs.mul(b, &r2);
        lhs = lhs.mul(b, &w1);
        lhs = lhs.mul(b, &w2);
    }
    lhs.equal(b, &rhs);
    out
}

// Explicit stage canopy: bottom `base_level` levels are hashed along each query path, while the
// top `depth <= CANOPY_MAX_DEPTH` levels (`<= 32` canopy leaves) are hashed once unconditionally
// to `root` and selected by each query's top index bits.
struct Canopy<W> {
    depth: usize,
    base_level: usize,
    queries: Vec<(Vec<W>, [W; 4])>,
}
impl<W: Base> Canopy<W> {
    fn new(path_depth: usize) -> Self {
        let (depth, base_level) = canopy_split(path_depth);
        Self {
            depth,
            base_level,
            queries: Vec::new(),
        }
    }
    fn path<B: Backend<W = W>>(
        &mut self,
        b: &mut B,
        stage: usize,
        index: &W,
        binary: &[W],
        values: &[Ext<W>],
        path: &[Digest],
    ) {
        let mut cur = leaf(b, stage, index, values);
        for (level, (bit, sibling)) in binary.iter().zip(path).take(self.base_level).enumerate() {
            let sibling = sibling.map(|x| b.alloc(x));
            let left = core::array::from_fn(|i| select(b, bit, &sibling[i], &cur[i]));
            let right = core::array::from_fn(|i| cur[i].plus(&sibling[i]).minus(&left[i]));
            cur = compress(b, &left, &right, stage, level);
        }
        self.queries.push((binary[self.base_level..].to_vec(), cur));
    }
    fn finish<B: Backend<W = W>>(
        self,
        b: &mut B,
        stage: usize,
        canopy_leaves: &[Digest],
        root: &[W; 4],
    ) {
        assert_eq!(canopy_leaves.len(), 1usize << self.depth);
        let bottom: Vec<[W; 4]> = canopy_leaves
            .iter()
            .map(|d| d.map(|v| b.alloc(v)))
            .collect();
        let choose = |b: &mut B, mut layer: Vec<[W; 4]>, bits: &[W]| -> [W; 4] {
            for bit in bits {
                layer = layer
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|pair| core::array::from_fn(|i| select(b, bit, &pair[1][i], &pair[0][i])))
                    .collect();
            }
            layer[0].clone()
        };
        for (top_bits, cur) in self.queries {
            let selected = choose(b, bottom.clone(), &top_bits);
            for (a, c) in cur.iter().zip(&selected) {
                b.equal(a, c);
            }
        }
        let mut layer = bottom;
        for h in 0..self.depth {
            layer = layer
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| compress(b, &pair[0], &pair[1], stage, self.base_level + h))
                .collect();
        }
        for (a, c) in layer[0].iter().zip(root) {
            b.equal(a, c);
        }
    }
}
fn coset_point<B: Backend>(b: &mut B, binary: &[B::W], domain_log2: usize) -> B::W {
    let omega = F::two_adic_generator(domain_log2);
    let mut out = B::W::constant(F::NON_RESIDUE);
    let mut power = omega;
    for bit in binary {
        let factor = B::W::constant(F::ONE).plus(&bit.scale(power - F::ONE));
        out = b.mul(&out, &factor);
        power *= power;
    }
    out
}
/// Fold one fiber `values[k] = f(x * zeta^k)` down to the next oracle's value at `x^arity`.
/// `x^-1` is witnessed once; every other point, inverse and square is a public multiple.
fn fold_fiber<B: Backend>(
    b: &mut B,
    values: &[Ext<B::W>],
    mut x: B::W,
    chals: &[[Ext<B::W>; 3]],
    base_values: bool,
) -> (B::W, Ext<B::W>) {
    let mut values = values.to_vec();
    let mut zeta = F::two_adic_generator(chals.len());
    let mut inv = b.alloc(b.value(&x).inv_or_zero());
    b.product(&x, &inv, &B::W::constant(F::ONE));
    let half_inv = F::TWO.inv();
    for (level, [theta, alpha, beta]) in chals.iter().enumerate() {
        let half = values.len() / 2;
        let x2 = b.mul(&x, &x);
        let beta_x2 = beta.mul_base(b, &x2);
        let zeta_inv = zeta.inv();
        let zeta2 = zeta.const_mul(zeta);
        // zeta^-i / 2 and zeta^2i.
        let (mut inv_scale, mut square_scale) = (half_inv, F::ONE);
        for i in 0..half {
            let inv_k = inv.scale(inv_scale);
            let even = values[i].add(&values[i + half]).scale(half_inv);
            let diff = values[i].sub(&values[i + half]);
            let (odd, theta_odd) = if base_values && level == 0 {
                let odd = b.mul(&diff.0[0], &inv_k);
                (Ext::base(odd.clone()), theta.mul_base(b, &odd))
            } else {
                let odd = diff.mul_base(b, &inv_k);
                let theta_odd = theta.mul(b, &odd);
                (odd, theta_odd)
            };
            let mixed = even.add(&theta_odd);
            let gamma = alpha.add(&beta_x2.scale(square_scale));
            values[i] = odd.add(&gamma.mul(b, &mixed));
            inv_scale = inv_scale.const_mul(zeta_inv);
            square_scale = square_scale.const_mul(zeta2);
        }
        values.truncate(half);
        if level + 1 < chals.len() {
            inv = b.mul(&inv, &inv);
        }
        x = x2;
        zeta = zeta2;
    }
    (x, values[0].clone())
}

fn bridge<B: Backend>(
    b: &mut B,
    w: &[Ext<B::W>; 5],
    claim: &Ext<B::W>,
    phi: &Ext<B::W>,
    chals: &[Ext<B::W>; 3],
) -> Ext<B::W> {
    let [theta, alpha, beta] = chals;
    let ff = w[0].add(&phi.mul(b, &w[1]));
    let gg = w[2].add(&phi.mul(b, &claim.sub(&w[0])));
    let mixed = ff.add(&theta.mul(b, &gg));
    let core = gg.add(&alpha.mul(b, &mixed));
    let shift = w[3].add(&theta.mul(b, &w[4]));
    core.add(&beta.mul(b, &shift))
}
enum KernelPoint<W: Base> {
    Ext {
        point: Vec<Ext<W>>,
        overflow: [Ext<W>; 2],
    },
    /// `(z, z^2, z^4, ...)` for a base-field shift point, then `z^n` and `z^(n+1)`.
    Base { powers: Vec<W>, overflow: [W; 2] },
}
struct Kernel<W: Base> {
    offset: usize,
    weight: Ext<W>,
    point: KernelPoint<W>,
}
impl<W: Base> Kernel<W> {
    fn initial(point: Vec<Ext<W>>) -> Self {
        Self {
            offset: 0,
            weight: Ext::one(),
            point: KernelPoint::Ext {
                point,
                overflow: [Ext::zero(), Ext::zero()],
            },
        }
    }
}
fn geometric<B: Backend>(
    b: &mut B,
    offset: usize,
    weight: Ext<B::W>,
    z: Ext<B::W>,
    vars: usize,
) -> Kernel<B::W> {
    let mut point = Vec::with_capacity(vars);
    let mut cur = z.clone();
    for _ in 0..vars {
        point.push(cur.clone());
        cur = cur.mul(b, &cur);
    }
    let tail = cur.mul(b, &z);
    Kernel {
        offset,
        weight,
        point: KernelPoint::Ext {
            point,
            overflow: [cur, tail],
        },
    }
}
fn geometric_base<B: Backend>(
    b: &mut B,
    offset: usize,
    weight: Ext<B::W>,
    z: B::W,
    vars: usize,
) -> Kernel<B::W> {
    let mut powers = Vec::with_capacity(vars);
    let mut cur = z.clone();
    for _ in 0..vars {
        powers.push(cur.clone());
        cur = b.mul(&cur, &cur);
    }
    let tail = b.mul(&cur, &z);
    Kernel {
        offset,
        weight,
        point: KernelPoint::Base {
            powers,
            overflow: [cur, tail],
        },
    }
}
/// `<final coefficients, deferred kernel>`, mirroring `pcs::affine::terminal_sum_serial`.
fn terminal<B: Backend>(
    b: &mut B,
    coeffs: &[Ext<B::W>],
    phis: &[Ext<B::W>],
    kernels: &[Kernel<B::W>],
) -> Ext<B::W> {
    let n = coeffs.len() - 2;
    let mut total = Ext::zero();
    // Base kernels folded at least once meet `coeffs[n]` through one product per offset.
    let mut shared: Vec<Option<[Ext<B::W>; 2]>> = vec![None; phis.len() + 1];
    for k in kernels {
        let prefix = phis.len() - k.offset;
        let mut scale = k.weight.clone();
        match &k.point {
            KernelPoint::Ext { point, overflow } => {
                for (r, phi) in point.iter().zip(&phis[k.offset..]) {
                    let factor = Ext::one().add(&phi.mul(b, r));
                    scale = scale.mul(b, &factor);
                }
                let mut values = coeffs[..n].to_vec();
                for r in &point[prefix..] {
                    let next: Vec<_> = values
                        .as_chunks::<2>()
                        .0
                        .iter()
                        .map(|pair| pair[0].add(&r.mul(b, &pair[1])))
                        .collect();
                    values = next;
                }
                total = total.add(&scale.mul(b, &values[0]));
                let tail = if prefix == 0 {
                    overflow[0]
                        .mul(b, &coeffs[n])
                        .add(&overflow[1].mul(b, &coeffs[n + 1]))
                } else {
                    let factor = overflow[0].add(&phis[k.offset].mul(b, &overflow[1]));
                    factor.mul(b, &coeffs[n])
                };
                total = total.add(&k.weight.mul(b, &tail));
            }
            KernelPoint::Base { powers, overflow } => {
                for (r, phi) in powers.iter().zip(&phis[k.offset..]) {
                    let factor = Ext::one().add(&phi.mul_base(b, r));
                    scale = scale.mul(b, &factor);
                }
                // The unfolded suffix of a geometric point is a univariate evaluation.
                let value = horner(b, &coeffs[..n], &powers[prefix]);
                total = total.add(&scale.mul(b, &value));
                if prefix == 0 {
                    let tail = coeffs[n]
                        .mul_base(b, &overflow[0])
                        .add(&coeffs[n + 1].mul_base(b, &overflow[1]));
                    total = total.add(&k.weight.mul(b, &tail));
                } else {
                    let terms = [
                        k.weight.mul_base(b, &overflow[0]),
                        k.weight.mul_base(b, &overflow[1]),
                    ];
                    shared[k.offset] = Some(match shared[k.offset].take() {
                        Some([p, q]) => [p.add(&terms[0]), q.add(&terms[1])],
                        None => terms,
                    });
                }
            }
        }
    }
    for (offset, sums) in shared.into_iter().enumerate() {
        if let Some([p, q]) = sums {
            let factor = p.add(&phis[offset].mul(b, &q));
            total = total.add(&factor.mul(b, &coeffs[n]));
        }
    }
    total
}
pub(super) fn horner<B: Backend>(b: &mut B, coeffs: &[Ext<B::W>], x: &B::W) -> Ext<B::W> {
    let (last, rest) = coeffs.split_last().expect("nonempty polynomial");
    rest.iter()
        .rev()
        .fold(last.clone(), |a, c| a.mul_base(b, x).add(c))
}

// This one verifier executes both natively and as a relation; equality checks never
// influence the control flow, and no witness value selects a circuit branch.
pub(super) fn verify_gadget<B: Backend>(
    b: &mut B,
    params: &FixedPathWhirParams,
    public: &[B::W],
    proof: &FixedPathWhirProof,
) {
    let nv = params.num_vars().expect("validated parameters");
    let point: Vec<_> = public[12..12 + nv * 4]
        .as_chunks::<4>()
        .0
        .iter()
        .map(|x| Ext(x.clone()))
        .collect();
    let mut claim = Ext(public[12 + nv * 4..].to_vec().try_into().ok().unwrap());
    let mut tr = start(b, params, public);
    let roots: Vec<[B::W; 4]> = proof
        .stage_roots
        .iter()
        .map(|r| r.map(|v| b.alloc(v)))
        .collect();
    for i in 0..4 {
        b.equal(&roots[0][i], &public[8 + i]);
    }
    let mut kernels = vec![Kernel::initial(point)];
    let mut phis = Vec::new();
    let mut cursor = 0;
    let mut remaining = nv;
    let geos = params.geometries();
    // Each commitment is absorbed BEFORE its OOD points and before any dependent folds.
    tr.absorb(b, 3, &roots[0]);
    let zs = [tr.ext(b, 4), tr.ext(b, 4)];
    let ood: Vec<_> = proof.ood_evals[0]
        .iter()
        .map(|&v| Ext::alloc(b, v))
        .collect();
    tr.absorb_exts(b, 5, &ood);
    for (z, e) in zs.into_iter().zip(ood) {
        let weight = tr.ext(b, 6);
        claim = claim.add(&weight.mul(b, &e));
        kernels.push(geometric(b, cursor, weight, z, remaining));
    }
    for (stage, spec) in params.schedule.stages.iter().enumerate() {
        let mut chals = Vec::with_capacity(spec.step_vars);
        for _ in 0..spec.step_vars {
            let wire = proof.fold_polys[cursor].map(|v| Ext::alloc(b, v));
            tr.absorb_exts(b, 10, &wire[..3]);
            let phi = tr.ext(b, 11);
            tr.absorb_exts(b, 12, &wire[3..]);
            pow(
                b,
                &mut tr,
                proof.fold_nonces[cursor],
                params.schedule.regime.pow_bits(),
            );
            let chal = [tr.ext(b, 13), tr.ext(b, 14), tr.ext(b, 15)];
            claim = bridge(b, &wire, &claim, &phi, &chal);
            phis.push(phi);
            chals.push(chal);
            cursor += 1;
        }
        remaining -= spec.step_vars;
        let last = stage + 1 == params.schedule.stages.len();
        // Next commitment (or final polynomial) is fixed BEFORE querying the current oracle.
        let mut next_ood = None;
        let final_coeffs: Vec<_> = if last {
            let values: Vec<_> = proof
                .final_coeffs
                .iter()
                .map(|&v| Ext::alloc(b, v))
                .collect();
            tr.absorb_exts(b, 21, &values);
            let expected = terminal(b, &values, &phis, &kernels);
            claim.equal(b, &expected);
            values
        } else {
            tr.absorb(b, 3, &roots[stage + 1]);
            let zs = [tr.ext(b, 4), tr.ext(b, 4)];
            let ood = proof.ood_evals[stage + 1].map(|v| Ext::alloc(b, v));
            tr.absorb_exts(b, 5, &ood);
            next_ood = Some((zs, ood));
            Vec::new()
        };
        pow(
            b,
            &mut tr,
            proof.query_nonces[stage],
            params.schedule.regime.pow_bits(),
        );
        let (arity, groups, count) = geos[stage];
        let mut shifted = Vec::with_capacity(count);
        let mut canopy = Canopy::new(groups.trailing_zeros() as usize);
        let sampled = sample_queries(b, &mut tr, groups, count);
        for (q, (index, binary)) in sampled.into_iter().enumerate() {
            let query = &proof.queries[stage][q];
            // Initial codeword is over the base field, as is the committed polynomial.
            let values: Vec<_> = query
                .values
                .iter()
                .map(|&v| {
                    if stage == 0 {
                        Ext::alloc_base(b, v)
                    } else {
                        Ext::alloc(b, v)
                    }
                })
                .collect();
            canopy.path(b, stage, &index, &binary, &values, &query.siblings);
            let x = coset_point(b, &binary, (groups * arity).trailing_zeros() as usize);
            let (z, e) = fold_fiber(b, &values, x, &chals, stage == 0);
            if last {
                let expected = horner(b, &final_coeffs, &z);
                e.equal(b, &expected);
            }
            shifted.push((z, e));
        }
        canopy.finish(b, stage, &proof.canopy_leaves[stage], &roots[stage]);
        if !last {
            let values: Vec<_> = shifted.iter().map(|(_, e)| e.clone()).collect();
            tr.absorb_exts(b, 22, &values);
            let (zs, ood) = next_ood.expect("nonterminal stage OOD pins");
            for (z, e) in zs.into_iter().zip(ood) {
                let weight = tr.ext(b, 6);
                claim = claim.add(&weight.mul(b, &e));
                kernels.push(geometric(b, cursor, weight, z, remaining));
            }
            let gamma = tr.ext(b, 23);
            let mut weight = gamma.clone();
            for (z, e) in shifted {
                claim = claim.add(&weight.mul(b, &e));
                kernels.push(geometric_base(b, cursor, weight.clone(), z, remaining));
                weight = weight.mul(b, &gamma);
            }
        }
    }
}

/// Verify a fixed-path child opening independently of a parent proof.
pub fn verify_fixed_path(
    params: &FixedPathWhirParams,
    statement: &ChildWhirStatement,
    proof: &FixedPathWhirProof,
) -> bool {
    if !params.well_formed(statement, proof) {
        return false;
    }
    let mut b = Native::default();
    verify_gadget(&mut b, params, &statement.words(), proof);
    !b.failed
}

/// A Reed-Solomon codeword. The first oracle encodes a base-field polynomial and stays in
/// the base field; later oracles are over the extension.
enum Codeword {
    Base(Vec<F>),
    Ext(Vec<E>),
}
impl Codeword {
    fn len(&self) -> usize {
        match self {
            Self::Base(v) => v.len(),
            Self::Ext(v) => v.len(),
        }
    }
    fn at(&self, i: usize) -> E {
        match self {
            Self::Base(v) => E::from_base(v[i]),
            Self::Ext(v) => v[i],
        }
    }
}
struct Oracle {
    codeword: Codeword,
    levels: Vec<Vec<Digest>>,
    arity: usize,
}
impl Oracle {
    /// First oracle: `coeffs` are the monomial coefficients of the committed polynomial.
    fn base(coeffs: &[F], blowup: usize, arity: usize) -> Self {
        let codeword = crate::field::encode_rs_coset_goldilocks(coeffs, blowup);
        Self::commit(Codeword::Base(codeword), arity, 0)
    }
    fn new(coeffs: &[E], blowup: usize, arity: usize, stage: usize) -> Self {
        let codeword = crate::pcs::affine::encode_overflow(coeffs, blowup);
        Self::commit(Codeword::Ext(codeword), arity, stage)
    }
    fn commit(codeword: Codeword, arity: usize, stage: usize) -> Self {
        let _phase = crate::profile::span("recursion_merkle");
        let groups = codeword.len() / arity;
        let mut leaves = vec![[F::ZERO; 4]; groups];
        crate::pcs::fill_indexed(&mut leaves, |g| {
            let fiber: Vec<_> = (0..arity)
                .map(|j| Ext::constant(codeword.at(g + j * groups)))
                .collect();
            leaf(&mut Native::default(), stage, &f(g as u64), &fiber)
        });
        let mut levels: Vec<Vec<Digest>> = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let depth = levels.len() - 1;
            let below = &levels[depth];
            let mut next = vec![[F::ZERO; 4]; below.len() / 2];
            crate::pcs::fill_indexed(&mut next, |i| {
                compress(
                    &mut Native::default(),
                    &below[2 * i],
                    &below[2 * i + 1],
                    stage,
                    depth,
                )
            });
            levels.push(next);
        }
        Self {
            codeword,
            levels,
            arity,
        }
    }
    fn root(&self) -> Digest {
        self.levels.last().unwrap()[0]
    }
    fn canopy_leaves(&self) -> Vec<Digest> {
        let path_depth = self.levels.len() - 1;
        let (_, base_level) = canopy_split(path_depth);
        self.levels[base_level].clone()
    }
    fn query(&self, index: usize) -> FixedPathQuery {
        let groups = self.codeword.len() / self.arity;
        let path_depth = self.levels.len() - 1;
        let (_, base_level) = canopy_split(path_depth);
        FixedPathQuery {
            values: (0..self.arity)
                .map(|j| self.codeword.at(index + j * groups))
                .collect(),
            siblings: (0..base_level)
                .map(|d| self.levels[d][(index >> d) ^ 1])
                .collect(),
        }
    }
}
impl Drop for Oracle {
    fn drop(&mut self) {
        match &mut self.codeword {
            Codeword::Base(v) => qsag_asm::volatile_fill(v, F::ZERO),
            Codeword::Ext(v) => qsag_asm::volatile_fill(v, E::ZERO),
        }
    }
}
struct SecretBases(Vec<F>);
impl Drop for SecretBases {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.0, F::ZERO);
    }
}
struct SecretExts(Vec<E>);
impl Drop for SecretExts {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.0, E::ZERO);
    }
}
/// `sum_i f(i)` over `0..count`, split across the worker budget.
fn sum_indexed<const N: usize>(count: usize, f: impl Fn(usize) -> [E; N] + Sync) -> [E; N] {
    let range = |start: usize, end: usize| {
        let mut acc = [E::ZERO; N];
        for i in start..end {
            for (a, v) in acc.iter_mut().zip(f(i)) {
                *a += v;
            }
        }
        acc
    };
    #[cfg(feature = "std")]
    if count >= 8_192 {
        let workers = crate::parallel_workers().min(count.div_ceil(2_048));
        let chunk = count.div_ceil(workers);
        let range = &range;
        return std::thread::scope(|scope| {
            let parts: Vec<_> = (0..workers)
                .map(|w| {
                    let (start, end) = ((w * chunk).min(count), ((w + 1) * chunk).min(count));
                    crate::spawn_bounded(scope, move || range(start, end))
                })
                .collect();
            let mut acc = [E::ZERO; N];
            for part in parts {
                for (a, v) in acc.iter_mut().zip(crate::join_worker(part)) {
                    *a += v;
                }
            }
            acc
        });
    }
    range(0, count)
}
fn dot(a: &[E], b: &[E]) -> E {
    let [out] = sum_indexed(a.len().min(b.len()), |i| [a[i] * b[i]]);
    out
}

/// A fixed-path commitment to a base-field evaluation table, kept by the prover until it
/// opens. Holds the committed polynomial; erased on drop.
pub struct RecursionCommitment {
    coeffs: SecretBases,
    oracle: Oracle,
}
impl RecursionCommitment {
    /// The commitment: Merkle root of the first Reed-Solomon oracle.
    pub fn root(&self) -> Digest {
        self.oracle.root()
    }
}

/// Commit to a base-field evaluation table in the recursion format.
/// This PCS mode is binding but not independently hiding; keep child witnesses private
/// when using the zero-knowledge merge.
pub fn commit_for_recursion(
    params: &FixedPathWhirParams,
    evaluations: &[F],
) -> Result<RecursionCommitment, RecursiveWhirError> {
    let nv = params
        .num_vars()
        .ok_or(RecursiveWhirError::InvalidParameters)?;
    if evaluations.len() != 1usize << nv {
        return Err(RecursiveWhirError::InvalidParameters);
    }
    let _phase = crate::profile::span("recursion_commit");
    let mut base = hypercube_to_monomial_coeffs(evaluations);
    let spec = params.schedule.stages[0];
    // The two overflow coefficients of the first oracle are zero, so its codeword is the
    // base-field encoding of the committed coefficients.
    let oracle = Oracle::base(&base, spec.blowup, 1 << spec.step_vars);
    base.extend([F::ZERO; 2]);
    Ok(RecursionCommitment {
        coeffs: SecretBases(base),
        oracle,
    })
}

/// Commit to a base-field evaluation table and prove its multilinear evaluation using
/// the recursion transcript. The returned commitment is part of the opening statement.
pub fn prove_for_recursion(
    params: &FixedPathWhirParams,
    shard_header: [u8; 32],
    evaluations: &[F],
    point: &[E],
) -> Result<(ChildWhirStatement, FixedPathWhirProof), RecursiveWhirError> {
    open_for_recursion(
        params,
        shard_header,
        commit_for_recursion(params, evaluations)?,
        point,
    )
}

/// Open a [`RecursionCommitment`] at `point` under the recursion transcript. The opening
/// statement binds the header, the commitment, the point and the value.
pub fn open_for_recursion(
    params: &FixedPathWhirParams,
    shard_header: [u8; 32],
    committed: RecursionCommitment,
    point: &[E],
) -> Result<(ChildWhirStatement, FixedPathWhirProof), RecursiveWhirError> {
    let nv = params
        .num_vars()
        .ok_or(RecursiveWhirError::InvalidParameters)?;
    let _phase = crate::profile::span("recursion_open");
    let RecursionCommitment {
        coeffs: base_coeffs,
        mut oracle,
    } = committed;
    let mut coeffs = SecretExts(vec![E::ZERO; base_coeffs.0.len()]);
    crate::pcs::fill_indexed(&mut coeffs.0, |i| E::from_base(base_coeffs.0[i]));
    drop(base_coeffs);
    if point.len() != nv || coeffs.0.len() != (1usize << nv) + 2 {
        return Err(RecursiveWhirError::InvalidParameters);
    }
    let mut kernel = crate::pcs::affine::monomial_table(point);
    let mut claim = dot(&coeffs.0, &kernel);
    let statement = ChildWhirStatement {
        shard_header,
        commitment: oracle.root(),
        point: point.to_vec(),
        value: claim,
    };
    let mut proof = params.placeholder();
    proof.stage_roots[0] = oracle.root();
    proof.canopy_leaves[0] = oracle.canopy_leaves();
    let mut b = Native::default();
    let mut tr = start(&mut b, params, &statement.words());
    tr.absorb(&mut b, 3, &oracle.root());
    let mut cursor = 0;
    let mut scratch_c = SecretExts(Vec::new());
    let mut scratch_k = Vec::new();
    let zs = [tr.ext(&mut b, 4).value(&b), tr.ext(&mut b, 4).value(&b)];
    let evals = zs.map(|z| crate::field::eval_univariate_ext4(&coeffs.0, z));
    proof.ood_evals[0] = evals;
    tr.absorb_exts(&mut b, 5, &evals.map(Ext::constant));
    for (z, e) in zs.into_iter().zip(evals) {
        let weight = tr.ext(&mut b, 6).value(&b);
        claim += weight * e;
        crate::pcs::affine::add_geometric_scaled_in_place(&mut kernel, weight, z);
    }
    for (stage, spec) in params.schedule.stages.iter().enumerate() {
        let mut chals = Vec::with_capacity(spec.step_vars);
        for _ in 0..spec.step_vars {
            let _phase = crate::profile::span("recursion_fold_round");
            let mut wire = [E::ZERO; 5];
            {
                let (c, k) = (&coeffs.0, &kernel);
                let head = sum_indexed(c.len() / 2, |i| {
                    [
                        c[2 * i] * k[2 * i],
                        c[2 * i] * k[2 * i + 1],
                        c[2 * i + 1] * k[2 * i],
                    ]
                });
                wire[..3].copy_from_slice(&head);
            }
            tr.absorb_exts(
                &mut b,
                10,
                &wire[..3]
                    .iter()
                    .copied()
                    .map(Ext::constant)
                    .collect::<Vec<_>>(),
            );
            let phi = tr.ext(&mut b, 11);
            crate::pcs::affine::fold_kernel_into(&kernel, phi.value(&b), &mut scratch_k);
            core::mem::swap(&mut kernel, &mut scratch_k);
            {
                let (c, k) = (&coeffs.0, &kernel);
                let tail = sum_indexed(c.len() / 2, |i| {
                    [c[2 * i] * k[i + 1], c[2 * i + 1] * k[i + 1]]
                });
                wire[3..].copy_from_slice(&tail);
            }
            tr.absorb_exts(
                &mut b,
                12,
                &wire[3..]
                    .iter()
                    .copied()
                    .map(Ext::constant)
                    .collect::<Vec<_>>(),
            );
            let nonce = grind(&tr, params.schedule.regime.pow_bits());
            pow(&mut b, &mut tr, nonce, params.schedule.regime.pow_bits());
            let chal = [tr.ext(&mut b, 13), tr.ext(&mut b, 14), tr.ext(&mut b, 15)];
            claim = bridge(
                &mut b,
                &wire.map(Ext::constant),
                &Ext::constant(claim),
                &phi,
                &chal,
            )
            .value(&b);
            let chal_values = core::array::from_fn(|i| chal[i].value(&b));
            crate::pcs::affine::fold_coeffs_into(&coeffs.0, chal_values, &mut scratch_c.0);
            // Erase the old table before the scratch buffer can shrink on another round.
            qsag_asm::volatile_fill(&mut coeffs.0, E::ZERO);
            core::mem::swap(&mut coeffs.0, &mut scratch_c.0);
            debug_assert_eq!(dot(&coeffs.0, &kernel), claim);
            proof.fold_polys[cursor] = wire;
            proof.fold_nonces[cursor] = nonce;
            chals.push(chal);
            cursor += 1;
        }
        let last = stage + 1 == params.schedule.stages.len();
        let mut next_ood = None;
        let next = if last {
            proof.final_coeffs.clone_from(&coeffs.0);
            tr.absorb_exts(
                &mut b,
                21,
                &coeffs
                    .0
                    .iter()
                    .copied()
                    .map(Ext::constant)
                    .collect::<Vec<_>>(),
            );
            None
        } else {
            let spec = params.schedule.stages[stage + 1];
            let next = Oracle::new(&coeffs.0, spec.blowup, 1 << spec.step_vars, stage + 1);
            proof.stage_roots[stage + 1] = next.root();
            proof.canopy_leaves[stage + 1] = next.canopy_leaves();
            tr.absorb(&mut b, 3, &next.root());
            let zs = [tr.ext(&mut b, 4).value(&b), tr.ext(&mut b, 4).value(&b)];
            let ood = zs.map(|z| crate::field::eval_univariate_ext4(&coeffs.0, z));
            proof.ood_evals[stage + 1] = ood;
            tr.absorb_exts(&mut b, 5, &ood.map(Ext::constant));
            next_ood = Some((zs, ood));
            Some(next)
        };
        let nonce = grind(&tr, params.schedule.regime.pow_bits());
        proof.query_nonces[stage] = nonce;
        pow(&mut b, &mut tr, nonce, params.schedule.regime.pow_bits());
        let _phase = crate::profile::span("recursion_queries");
        let groups = oracle.codeword.len() / oracle.arity;
        let count = groups.min(spec.num_queries);
        let mut shifted = Vec::with_capacity(count);
        let sampled = sample_queries(&mut b, &mut tr, groups, count);
        for (q, (index, binary)) in sampled.into_iter().enumerate() {
            let query = oracle.query(index.to_canonical_u64() as usize);
            let values: Vec<_> = query.values.iter().copied().map(Ext::constant).collect();
            let x = coset_point(
                &mut b,
                &binary,
                oracle.codeword.len().trailing_zeros() as usize,
            );
            shifted.push(fold_fiber(&mut b, &values, x, &chals, stage == 0));
            proof.queries[stage][q] = query;
        }
        if let Some(next) = next {
            let values: Vec<_> = shifted.iter().map(|(_, e)| e.clone()).collect();
            tr.absorb_exts(&mut b, 22, &values);
            let (zs, ood) = next_ood.expect("nonterminal stage OOD pins");
            for (z, e) in zs.into_iter().zip(ood) {
                let weight = tr.ext(&mut b, 6).value(&b);
                claim += weight * e;
                crate::pcs::affine::add_geometric_scaled_in_place(&mut kernel, weight, z);
            }
            let gamma = tr.ext(&mut b, 23).value(&b);
            let mut weight = gamma;
            for (z, e) in shifted {
                claim += weight * e.value(&b);
                crate::pcs::affine::add_geometric_scaled_in_place(
                    &mut kernel,
                    weight,
                    E::from_base(z),
                );
                weight *= gamma;
            }
            oracle = next;
        }
    }
    debug_assert!(!b.failed);
    Ok((statement, proof))
}

// ============================================================================
// Correlated 3-Oracle Fixed-Path WHIR (`(Z_pad, H_super, E_super)` in 1 Cascade)
// ============================================================================

/// Reusable non-hiding recursion commitment (used for deterministic public [`ShapeHologram`]
/// commitments so one compiled hologram can open across any number of recursive proofs).
pub struct PublicRecursionCommitment {
    coeffs: Vec<F>,
    oracle: Oracle,
}

impl Clone for PublicRecursionCommitment {
    fn clone(&self) -> Self {
        let codeword = match &self.oracle.codeword {
            Codeword::Base(v) => Codeword::Base(v.clone()),
            Codeword::Ext(v) => Codeword::Ext(v.clone()),
        };
        Self {
            coeffs: self.coeffs.clone(),
            oracle: Oracle {
                codeword,
                levels: self.oracle.levels.clone(),
                arity: self.oracle.arity,
            },
        }
    }
}

impl core::fmt::Debug for PublicRecursionCommitment {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_struct("PublicRecursionCommitment")
            .field("root", &self.root())
            .field("arity", &self.oracle.arity)
            .finish()
    }
}

impl PublicRecursionCommitment {
    pub fn commit(
        params: &FixedPathWhirParams,
        evaluations: &[F],
    ) -> Result<Self, RecursiveWhirError> {
        let nv = params
            .num_vars()
            .ok_or(RecursiveWhirError::InvalidParameters)?;
        if evaluations.len() != 1usize << nv {
            return Err(RecursiveWhirError::InvalidParameters);
        }
        let mut coeffs = hypercube_to_monomial_coeffs(evaluations);
        let spec = params.schedule.stages[0];
        let oracle = Oracle::base(&coeffs, spec.blowup, 1 << spec.step_vars);
        coeffs.extend([F::ZERO; 2]);
        Ok(Self { coeffs, oracle })
    }

    #[inline]
    pub fn root(&self) -> Digest {
        self.oracle.root()
    }
}

/// Correlated fixed-path WHIR opening of 3 Stage-0 base-field commitments `(W_0, W_1, W_2)`
/// across 3 evaluation points `(p_0, p_1, p_2)` sharing ONE CWYZ fold & query cascade.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Correlated3WhirProof {
    /// `cross_evals[m][j] = W_m(p_j)` for `m in 0..3, j in 0..3`.
    pub cross_evals: [[E; 3]; 3],
    /// Stage-0 canopy leaves for each of the 3 base-field commitments.
    pub stage0_canopy_leaves: [Vec<Digest>; 3],
    /// Stage-0 queries (`count` queries, each carrying the fiber in all 3 Stage-0 trees).
    pub stage0_queries: Vec<[FixedPathQuery; 3]>,
    /// Stage roots for folded extension stages `1..stages`.
    pub later_stage_roots: Vec<Digest>,
    /// Canopy leaves for folded extension stages `1..stages`.
    pub later_canopy_leaves: Vec<Vec<Digest>>,
    /// OOD evaluations `[z_0, z_1]` for all `0..stages` (on the combined polynomial `U`).
    pub ood_evals: Vec<[E; 2]>,
    pub fold_polys: Vec<[E; 5]>,
    pub fold_nonces: Vec<[u32; 2]>,
    pub query_nonces: Vec<[u32; 2]>,
    /// Queries for folded extension stages `1..stages`.
    pub later_queries: Vec<Vec<FixedPathQuery>>,
    pub final_coeffs: Vec<E>,
}

impl FixedPathWhirParams {
    pub(super) fn placeholder_correlated3(&self) -> Correlated3WhirProof {
        let nv = self.num_vars().expect("validated parameters");
        let geos = self.geometries();
        let (arity0, groups0, count0) = geos[0];
        let (depth0, base0) = canopy_split(groups0.trailing_zeros() as usize);
        let q0 = FixedPathQuery {
            values: vec![E::ZERO; arity0],
            siblings: vec![[F::ZERO; 4]; base0],
        };
        let stages = self.schedule.stages.len();
        Correlated3WhirProof {
            cross_evals: [[E::ZERO; 3]; 3],
            stage0_canopy_leaves: core::array::from_fn(|_| vec![[F::ZERO; 4]; 1usize << depth0]),
            stage0_queries: vec![[q0.clone(), q0.clone(), q0]; count0],
            later_stage_roots: vec![[F::ZERO; 4]; stages.saturating_sub(1)],
            later_canopy_leaves: geos[1..]
                .iter()
                .map(|&(_, groups, _)| {
                    let (depth, _) = canopy_split(groups.trailing_zeros() as usize);
                    vec![[F::ZERO; 4]; 1usize << depth]
                })
                .collect(),
            ood_evals: vec![[E::ZERO; 2]; stages],
            fold_polys: vec![[E::ZERO; 5]; nv - self.schedule.early_stop_vars],
            fold_nonces: vec![[0; 2]; nv - self.schedule.early_stop_vars],
            query_nonces: vec![[0; 2]; stages],
            later_queries: geos[1..]
                .iter()
                .map(|&(arity, groups, count)| {
                    let (_, base_level) = canopy_split(groups.trailing_zeros() as usize);
                    vec![
                        FixedPathQuery {
                            values: vec![E::ZERO; arity],
                            siblings: vec![[F::ZERO; 4]; base_level],
                        };
                        count
                    ]
                })
                .collect(),
            final_coeffs: vec![E::ZERO; (1 << self.schedule.early_stop_vars) + 2],
        }
    }

    pub(super) fn well_formed_correlated3(&self, proof: &Correlated3WhirProof) -> bool {
        let Some(nv) = self.num_vars() else {
            return false;
        };
        let stages = self.schedule.stages.len();
        let geos = self.geometries();
        let (arity0, groups0, count0) = geos[0];
        let (depth0, base0) = canopy_split(groups0.trailing_zeros() as usize);
        proof
            .stage0_canopy_leaves
            .iter()
            .all(|l| l.len() == (1usize << depth0))
            && proof.stage0_queries.len() == count0
            && proof.stage0_queries.iter().all(|triple| {
                triple.iter().all(|q| {
                    q.values.len() == arity0
                        && q.siblings.len() == base0
                        && q.values.iter().all(|v| v.to_limbs()[1..] == [F::ZERO; 3])
                })
            })
            && proof.later_stage_roots.len() == stages.saturating_sub(1)
            && proof.later_canopy_leaves.len() == stages.saturating_sub(1)
            && proof.ood_evals.len() == stages
            && proof.fold_polys.len() == nv - self.schedule.early_stop_vars
            && proof.fold_nonces.len() == proof.fold_polys.len()
            && proof.query_nonces.len() == stages
            && proof.final_coeffs.len() == (1 << self.schedule.early_stop_vars) + 2
            && proof.later_queries.len() == stages.saturating_sub(1)
            && geos[1..]
                .iter()
                .zip(&proof.later_canopy_leaves)
                .zip(&proof.later_queries)
                .all(|((&(arity, groups, count), leaves), queries)| {
                    let (depth, base_level) = canopy_split(groups.trailing_zeros() as usize);
                    leaves.len() == (1usize << depth)
                        && queries.len() == count
                        && queries
                            .iter()
                            .all(|q| q.values.len() == arity && q.siblings.len() == base_level)
                })
    }
}

/// Open `(w0, w1_public, w2)` at 3 points `points` on an existing Poseidon2 [`Transcript`].
pub(super) fn open_correlated3_for_recursion(
    params: &FixedPathWhirParams,
    tr: &mut Transcript<F>,
    w0: RecursionCommitment,
    w1: &PublicRecursionCommitment,
    w2: RecursionCommitment,
    points: &[Vec<E>; 3],
) -> Result<Correlated3WhirProof, RecursiveWhirError> {
    let nv = params
        .num_vars()
        .ok_or(RecursiveWhirError::InvalidParameters)?;
    let want_len = (1usize << nv) + 2;
    if points.iter().any(|p| p.len() != nv)
        || w0.coeffs.0.len() != want_len
        || w1.coeffs.len() != want_len
        || w2.coeffs.0.len() != want_len
    {
        return Err(RecursiveWhirError::InvalidParameters);
    }
    let mut b = Native::default();
    let coeffs_ref: [&[F]; 3] = [&w0.coeffs.0, &w1.coeffs, &w2.coeffs.0];
    let mut cross_evals = [[E::ZERO; 3]; 3];
    // Evaluate through square-root-sized Kronecker factors, without materializing
    // a full extension table for each of the three points.
    for (j, point) in points.iter().enumerate() {
        let (lo, hi) = crate::pcs::split_monomial_table(point);
        let values = sum_indexed(want_len - 2, |i| {
            let kernel = lo[i % lo.len()] * hi[i / lo.len()];
            core::array::from_fn::<_, 3, _>(|m| kernel.mul_base(coeffs_ref[m][i]))
        });
        for m in 0..3 {
            cross_evals[m][j] = values[m];
        }
    }

    let mut proof = params.placeholder_correlated3();
    proof.cross_evals = cross_evals;
    let oracles0 = [&w0.oracle, &w1.oracle, &w2.oracle];
    for (slot, orc) in proof.stage0_canopy_leaves.iter_mut().zip(&oracles0) {
        *slot = orc.canopy_leaves();
    }

    let flat_cross: Vec<Ext<F>> = cross_evals
        .iter()
        .flatten()
        .copied()
        .map(Ext::constant)
        .collect();
    tr.absorb_exts(&mut b, 50, &flat_cross);
    let mu = tr.ext(&mut b, 51).value(&b);
    let zeta = tr.ext(&mut b, 52).value(&b);
    let mu2 = mu * mu;
    let zeta2 = zeta * zeta;
    let mu_pows = [E::ONE, mu, mu2];
    let zeta_pows = [E::ONE, zeta, zeta2];

    let mut coeffs = SecretExts(vec![E::ZERO; want_len]);
    crate::pcs::fill_indexed(&mut coeffs.0, |i| {
        E::from_base(w0.coeffs.0[i]) + mu.mul_base(w1.coeffs[i]) + mu2.mul_base(w2.coeffs.0[i])
    });
    drop(w0.coeffs);
    drop(w2.coeffs);
    let mut kernel = vec![E::ZERO; want_len];
    for (point, weight) in points.iter().zip(zeta_pows) {
        crate::pcs::add_point_kernel(&mut kernel, weight, point);
    }
    let mut claim = E::ZERO;
    for j in 0..3 {
        let mut col_sum = E::ZERO;
        for m in 0..3 {
            col_sum += mu_pows[m] * cross_evals[m][j];
        }
        claim += zeta_pows[j] * col_sum;
    }

    let mut roots0_words = Vec::with_capacity(12);
    for orc in &oracles0 {
        roots0_words.extend_from_slice(&orc.root());
    }
    tr.absorb(&mut b, 53, &roots0_words);
    let zs = [tr.ext(&mut b, 4).value(&b), tr.ext(&mut b, 4).value(&b)];
    let evals = zs.map(|z| crate::field::eval_univariate_ext4(&coeffs.0, z));
    proof.ood_evals[0] = evals;
    tr.absorb_exts(&mut b, 5, &evals.map(Ext::constant));
    for (z, e) in zs.into_iter().zip(evals) {
        let weight = tr.ext(&mut b, 6).value(&b);
        claim += weight * e;
        crate::pcs::affine::add_geometric_scaled_in_place(&mut kernel, weight, z);
    }

    let mut cursor = 0usize;
    let mut scratch_c = SecretExts(Vec::new());
    let mut scratch_k = Vec::new();
    let mut later_oracle: Option<Oracle> = None;

    for (stage, spec) in params.schedule.stages.iter().enumerate() {
        let mut chals = Vec::with_capacity(spec.step_vars);
        for _ in 0..spec.step_vars {
            let mut wire = [E::ZERO; 5];
            {
                let (c, k) = (&coeffs.0, &kernel);
                let head = sum_indexed(c.len() / 2, |i| {
                    [
                        c[2 * i] * k[2 * i],
                        c[2 * i] * k[2 * i + 1],
                        c[2 * i + 1] * k[2 * i],
                    ]
                });
                wire[..3].copy_from_slice(&head);
            }
            tr.absorb_exts(
                &mut b,
                10,
                &wire[..3]
                    .iter()
                    .copied()
                    .map(Ext::constant)
                    .collect::<Vec<_>>(),
            );
            let phi = tr.ext(&mut b, 11);
            if kernel.len() >= 1 << 20 {
                crate::pcs::affine::fold_kernel_in_place(&mut kernel, phi.value(&b));
            } else {
                crate::pcs::affine::fold_kernel_into(&kernel, phi.value(&b), &mut scratch_k);
                core::mem::swap(&mut kernel, &mut scratch_k);
            }
            {
                let (c, k) = (&coeffs.0, &kernel);
                let tail = sum_indexed(c.len() / 2, |i| {
                    [c[2 * i] * k[i + 1], c[2 * i + 1] * k[i + 1]]
                });
                wire[3..].copy_from_slice(&tail);
            }
            tr.absorb_exts(
                &mut b,
                12,
                &wire[3..]
                    .iter()
                    .copied()
                    .map(Ext::constant)
                    .collect::<Vec<_>>(),
            );
            let nonce = grind(tr, params.schedule.regime.pow_bits());
            pow(&mut b, tr, nonce, params.schedule.regime.pow_bits());
            let chal = [tr.ext(&mut b, 13), tr.ext(&mut b, 14), tr.ext(&mut b, 15)];
            claim = bridge(
                &mut b,
                &wire.map(Ext::constant),
                &Ext::constant(claim),
                &phi,
                &chal,
            )
            .value(&b);
            let chal_values = core::array::from_fn(|i| chal[i].value(&b));
            if coeffs.0.len() >= 1 << 20 {
                crate::pcs::affine::fold_coeffs_in_place(&mut coeffs.0, chal_values);
            } else {
                crate::pcs::affine::fold_coeffs_into(&coeffs.0, chal_values, &mut scratch_c.0);
                qsag_asm::volatile_fill(&mut coeffs.0, E::ZERO);
                core::mem::swap(&mut coeffs.0, &mut scratch_c.0);
            }
            debug_assert_eq!(dot(&coeffs.0, &kernel), claim);
            proof.fold_polys[cursor] = wire;
            proof.fold_nonces[cursor] = nonce;
            chals.push(chal);
            cursor += 1;
        }
        let last = stage + 1 == params.schedule.stages.len();
        let mut next_ood = None;
        let next = if last {
            proof.final_coeffs.clone_from(&coeffs.0);
            tr.absorb_exts(
                &mut b,
                21,
                &coeffs
                    .0
                    .iter()
                    .copied()
                    .map(Ext::constant)
                    .collect::<Vec<_>>(),
            );
            None
        } else {
            let next_spec = params.schedule.stages[stage + 1];
            let next = Oracle::new(
                &coeffs.0,
                next_spec.blowup,
                1 << next_spec.step_vars,
                stage + 1,
            );
            proof.later_stage_roots[stage] = next.root();
            proof.later_canopy_leaves[stage] = next.canopy_leaves();
            tr.absorb(&mut b, 3, &next.root());
            let zs = [tr.ext(&mut b, 4).value(&b), tr.ext(&mut b, 4).value(&b)];
            let ood = zs.map(|z| crate::field::eval_univariate_ext4(&coeffs.0, z));
            proof.ood_evals[stage + 1] = ood;
            tr.absorb_exts(&mut b, 5, &ood.map(Ext::constant));
            next_ood = Some((zs, ood));
            Some(next)
        };
        let nonce = grind(tr, params.schedule.regime.pow_bits());
        proof.query_nonces[stage] = nonce;
        pow(&mut b, tr, nonce, params.schedule.regime.pow_bits());
        let (arity, groups, count) = params.geometries()[stage];
        let domain_log2 = (groups * arity).trailing_zeros() as usize;
        let mut shifted = Vec::with_capacity(count);
        let sampled = sample_queries(&mut b, tr, groups, count);
        if stage == 0 {
            for (q, (index, binary)) in sampled.into_iter().enumerate() {
                let idx = index.to_canonical_u64() as usize;
                let q_triple: [FixedPathQuery; 3] =
                    core::array::from_fn(|m| oracles0[m].query(idx));
                let combined: Vec<Ext<F>> = (0..arity)
                    .map(|k| {
                        Ext::constant(
                            q_triple[0].values[k]
                                + mu * q_triple[1].values[k]
                                + mu2 * q_triple[2].values[k],
                        )
                    })
                    .collect();
                let x = coset_point(&mut b, &binary, domain_log2);
                shifted.push(fold_fiber(&mut b, &combined, x, &chals, false));
                proof.stage0_queries[q] = q_triple;
            }
        } else {
            let cur_oracle = later_oracle.as_ref().expect("folded extension oracle");
            for (q, (index, binary)) in sampled.into_iter().enumerate() {
                let query = cur_oracle.query(index.to_canonical_u64() as usize);
                let values: Vec<_> = query.values.iter().copied().map(Ext::constant).collect();
                let x = coset_point(&mut b, &binary, domain_log2);
                shifted.push(fold_fiber(&mut b, &values, x, &chals, false));
                proof.later_queries[stage - 1][q] = query;
            }
        }
        if let Some(next) = next {
            let values: Vec<_> = shifted.iter().map(|(_, e)| e.clone()).collect();
            tr.absorb_exts(&mut b, 22, &values);
            let (zs, ood) = next_ood.expect("nonterminal stage OOD pins");
            for (z, e) in zs.into_iter().zip(ood) {
                let weight = tr.ext(&mut b, 6).value(&b);
                claim += weight * e;
                crate::pcs::affine::add_geometric_scaled_in_place(&mut kernel, weight, z);
            }
            let gamma = tr.ext(&mut b, 23).value(&b);
            let mut weight = gamma;
            for (z, e) in shifted {
                claim += weight * e.value(&b);
                crate::pcs::affine::add_geometric_scaled_in_place(
                    &mut kernel,
                    weight,
                    E::from_base(z),
                );
                weight *= gamma;
            }
            later_oracle = Some(next);
        }
    }
    debug_assert!(!b.failed);
    Ok(proof)
}

/// Verify a [`Correlated3WhirProof`] natively or inside a parent [`ConstraintSystem`].
pub(super) fn verify_correlated3_gadget<B: Backend>(
    b: &mut B,
    params: &FixedPathWhirParams,
    tr: &mut Transcript<B::W>,
    roots0: &[[B::W; 4]; 3],
    points: &[Vec<Ext<B::W>>; 3],
    expected_claims: &[[Option<Ext<B::W>>; 3]; 3],
    proof: &Correlated3WhirProof,
) {
    census("open.head");
    let nv = params.num_vars().expect("validated parameters");
    let geos = params.geometries();
    let cross_w: [[Ext<B::W>; 3]; 3] =
        core::array::from_fn(|m| core::array::from_fn(|j| Ext::alloc(b, proof.cross_evals[m][j])));
    for m in 0..3 {
        for j in 0..3 {
            if let Some(exp) = &expected_claims[m][j] {
                cross_w[m][j].equal(b, exp);
            }
        }
    }
    let flat_cross: Vec<Ext<B::W>> = cross_w.iter().flatten().cloned().collect();
    tr.absorb_exts(b, 50, &flat_cross);
    let mu = tr.ext(b, 51);
    let zeta = tr.ext(b, 52);
    let mu2 = mu.mul(b, &mu);
    let zeta2 = zeta.mul(b, &zeta);

    let mut kernels = vec![
        Kernel::initial(points[0].clone()),
        Kernel {
            offset: 0,
            weight: zeta.clone(),
            point: KernelPoint::Ext {
                point: points[1].clone(),
                overflow: [Ext::zero(), Ext::zero()],
            },
        },
        Kernel {
            offset: 0,
            weight: zeta2.clone(),
            point: KernelPoint::Ext {
                point: points[2].clone(),
                overflow: [Ext::zero(), Ext::zero()],
            },
        },
    ];
    let col_claim = |b: &mut B, j: usize| -> Ext<B::W> {
        let t1 = mu.mul(b, &cross_w[1][j]);
        let t2 = mu2.mul(b, &cross_w[2][j]);
        cross_w[0][j].add(&t1).add(&t2)
    };
    let c0 = col_claim(b, 0);
    let c1 = col_claim(b, 1);
    let c2 = col_claim(b, 2);
    let zc1 = zeta.mul(b, &c1);
    let zc2 = zeta2.mul(b, &c2);
    let mut claim = c0.add(&zc1).add(&zc2);

    let later_roots: Vec<[B::W; 4]> = proof
        .later_stage_roots
        .iter()
        .map(|r| r.map(|v| b.alloc(v)))
        .collect();
    let mut roots0_words = Vec::with_capacity(12);
    for r in roots0 {
        roots0_words.extend_from_slice(r);
    }
    tr.absorb(b, 53, &roots0_words);
    let zs = [tr.ext(b, 4), tr.ext(b, 4)];
    let ood0: Vec<_> = proof.ood_evals[0]
        .iter()
        .map(|&v| Ext::alloc(b, v))
        .collect();
    tr.absorb_exts(b, 5, &ood0);
    let mut cursor = 0usize;
    let mut remaining = nv;
    for (z, e) in zs.into_iter().zip(ood0) {
        let weight = tr.ext(b, 6);
        claim = claim.add(&weight.mul(b, &e));
        kernels.push(geometric(b, cursor, weight, z, remaining));
    }

    let mut phis = Vec::new();
    for (stage, spec) in params.schedule.stages.iter().enumerate() {
        let mut chals = Vec::with_capacity(spec.step_vars);
        census("open.fold_rounds");
        for _ in 0..spec.step_vars {
            let wire = proof.fold_polys[cursor].map(|v| Ext::alloc(b, v));
            tr.absorb_exts(b, 10, &wire[..3]);
            let phi = tr.ext(b, 11);
            tr.absorb_exts(b, 12, &wire[3..]);
            pow(
                b,
                tr,
                proof.fold_nonces[cursor],
                params.schedule.regime.pow_bits(),
            );
            let chal = [tr.ext(b, 13), tr.ext(b, 14), tr.ext(b, 15)];
            claim = bridge(b, &wire, &claim, &phi, &chal);
            phis.push(phi);
            chals.push(chal);
            cursor += 1;
        }
        remaining -= spec.step_vars;
        let last = stage + 1 == params.schedule.stages.len();
        let mut next_ood = None;
        let final_coeffs: Vec<_> = if last {
            let values: Vec<_> = proof
                .final_coeffs
                .iter()
                .map(|&v| Ext::alloc(b, v))
                .collect();
            tr.absorb_exts(b, 21, &values);
            census("open.terminal");
            let expected = terminal(b, &values, &phis, &kernels);
            census("open.fold_rounds");
            claim.equal(b, &expected);
            values
        } else {
            tr.absorb(b, 3, &later_roots[stage]);
            let zs = [tr.ext(b, 4), tr.ext(b, 4)];
            let ood = proof.ood_evals[stage + 1].map(|v| Ext::alloc(b, v));
            tr.absorb_exts(b, 5, &ood);
            next_ood = Some((zs, ood));
            Vec::new()
        };
        pow(
            b,
            tr,
            proof.query_nonces[stage],
            params.schedule.regime.pow_bits(),
        );
        let (arity, groups, count) = geos[stage];
        let path_depth = groups.trailing_zeros() as usize;
        let domain_log2 = (groups * arity).trailing_zeros() as usize;
        let mut shifted = Vec::with_capacity(count);
        census("open.sampler");
        let sampled = sample_queries(b, tr, groups, count);
        if stage == 0 {
            let mut canopies: [Canopy<B::W>; 3] = core::array::from_fn(|_| Canopy::new(path_depth));
            for (q, (index, binary)) in sampled.into_iter().enumerate() {
                let triple = &proof.stage0_queries[q];
                let tree_vals: [Vec<Ext<B::W>>; 3] = core::array::from_fn(|m| {
                    triple[m]
                        .values
                        .iter()
                        .map(|&v| Ext::alloc_base(b, v))
                        .collect()
                });
                census("open.stage0.paths");
                for m in 0..3 {
                    canopies[m].path(b, 0, &index, &binary, &tree_vals[m], &triple[m].siblings);
                }
                census("open.stage0.combine");
                let combined: Vec<Ext<B::W>> = (0..arity)
                    .map(|k| {
                        let t1 = mu.mul_base(b, &tree_vals[1][k].0[0]);
                        let t2 = mu2.mul_base(b, &tree_vals[2][k].0[0]);
                        tree_vals[0][k].add(&t1).add(&t2)
                    })
                    .collect();
                census("open.stage0.fold");
                let x = coset_point(b, &binary, domain_log2);
                let (z, e) = fold_fiber(b, &combined, x, &chals, false);
                if last {
                    let expected = horner(b, &final_coeffs, &z);
                    e.equal(b, &expected);
                }
                shifted.push((z, e));
            }
            census("open.canopy");
            let [c0, c1, c2] = canopies;
            c0.finish(b, 0, &proof.stage0_canopy_leaves[0], &roots0[0]);
            c1.finish(b, 0, &proof.stage0_canopy_leaves[1], &roots0[1]);
            c2.finish(b, 0, &proof.stage0_canopy_leaves[2], &roots0[2]);
        } else {
            let mut canopy = Canopy::new(path_depth);
            for (q, (index, binary)) in sampled.into_iter().enumerate() {
                census("open.later.paths");
                let query = &proof.later_queries[stage - 1][q];
                let values: Vec<_> = query.values.iter().map(|&v| Ext::alloc(b, v)).collect();
                canopy.path(b, stage, &index, &binary, &values, &query.siblings);
                census("open.later.fold");
                let x = coset_point(b, &binary, domain_log2);
                let (z, e) = fold_fiber(b, &values, x, &chals, false);
                if last {
                    let expected = horner(b, &final_coeffs, &z);
                    e.equal(b, &expected);
                }
                shifted.push((z, e));
            }
            census("open.canopy");
            canopy.finish(
                b,
                stage,
                &proof.later_canopy_leaves[stage - 1],
                &later_roots[stage - 1],
            );
        }
        census("open.kernels");
        if !last {
            let values: Vec<_> = shifted.iter().map(|(_, e)| e.clone()).collect();
            tr.absorb_exts(b, 22, &values);
            let (zs, ood) = next_ood.expect("nonterminal stage OOD pins");
            for (z, e) in zs.into_iter().zip(ood) {
                let weight = tr.ext(b, 6);
                claim = claim.add(&weight.mul(b, &e));
                kernels.push(geometric(b, cursor, weight, z, remaining));
            }
            let gamma = tr.ext(b, 23);
            let mut weight = gamma.clone();
            for (z, e) in shifted {
                claim = claim.add(&weight.mul(b, &e));
                kernels.push(geometric_base(b, cursor, weight.clone(), z, remaining));
                weight = weight.mul(b, &gamma);
            }
        }
    }
}

/// Largest fan-in of one merge relation.
pub const MAX_MERGE_CHILDREN: usize = 16;
const MERGE_LABEL: &[u8] = b"QSAG.FIXED.WHIR.MERGE/v1";

/// One outer proof and one merged digest for any number of children and any child path
/// counts. The child statements are verifier inputs, not hidden assertions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctChildWhirMerge {
    pub merged_root: Digest,
    pub proof: PublicHemProof,
}
impl SuccinctChildWhirMerge {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = b"QSAGFWP1".to_vec();
        for x in self.merged_root {
            out.extend_from_slice(&x.to_le_bytes());
        }
        out.extend(self.proof.to_bytes());
        out
    }
    pub fn from_bytes(
        bytes: &[u8],
        relation: &ChildWhirMergeRelation,
        regime: WhirSecurityRegime,
    ) -> Option<Self> {
        if bytes.get(..8)? != b"QSAGFWP1" {
            return None;
        }
        let mut root = [F::ZERO; 4];
        for (i, v) in root.iter_mut().enumerate() {
            let word = u64::from_le_bytes(bytes.get(8 + 8 * i..16 + 8 * i)?.try_into().ok()?);
            if word >= crate::field::GOLDILOCKS_PRIME {
                return None;
            }
            *v = f(word);
        }
        let proof = PublicHemProof::from_bytes(bytes.get(40..)?, &relation.shape, regime)?;
        Some(Self {
            merged_root: root,
            proof,
        })
    }
}
fn statement_words(children: &[ChildWhirStatement]) -> Vec<F> {
    children
        .iter()
        .flat_map(ChildWhirStatement::words)
        .collect()
}
// The frame length in the sponge capacity separates fan-ins and statement sizes.
fn merged_gadget<B: Backend>(b: &mut B, public: &[B::W]) -> [B::W; 4] {
    let mut tr = Transcript::new();
    tr.absorb(b, MERGE, public);
    core::array::from_fn(|i| tr.state[i].clone())
}
/// Digest of the ordered child statements (shard header, commitment, point and value each).
pub fn merged_child_whir_root(children: &[ChildWhirStatement]) -> Digest {
    merged_gadget(&mut Native::default(), &statement_words(children))
}

/// Counts exclude padding and the twelve masking rows added by the outer protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChildWhirRelationStats {
    pub sbox_rows: usize,
    pub multiplication_rows: usize,
    pub padded_rows: usize,
    pub variables: usize,
}
#[derive(Clone, Debug)]
pub struct ChildWhirMergeRelation {
    params: FixedPathWhirParams,
    children: usize,
    shape: Shape,
    stats: ChildWhirRelationStats,
}
impl ChildWhirMergeRelation {
    /// Two-child relation.
    pub fn new(params: FixedPathWhirParams) -> Result<Self, RecursiveWhirError> {
        Self::with_children(params, 2)
    }
    /// Relation verifying `children` openings that share one verifier geometry.
    pub fn with_children(
        params: FixedPathWhirParams,
        children: usize,
    ) -> Result<Self, RecursiveWhirError> {
        let nv = params
            .num_vars()
            .ok_or(RecursiveWhirError::InvalidParameters)?;
        if !(1..=MAX_MERGE_CHILDREN).contains(&children) {
            return Err(RecursiveWhirError::InvalidParameters);
        }
        let statements = vec![
            ChildWhirStatement {
                shard_header: [0; 32],
                commitment: [F::ZERO; 4],
                point: vec![E::ZERO; nv],
                value: E::ZERO,
            };
            children
        ];
        let proofs = vec![params.placeholder(); children];
        let (shape, mut z, used) = synthesize_merge(&params, &statements, &proofs, [F::ZERO; 4]);
        qsag_asm::volatile_fill(&mut z, F::ZERO);
        let stats = ChildWhirRelationStats {
            sbox_rows: shape.num_sbox,
            multiplication_rows: used - shape.num_sbox,
            padded_rows: shape.num_rows(),
            variables: shape.num_vars,
        };
        Ok(Self {
            params,
            children,
            shape,
            stats,
        })
    }
    pub fn shape(&self) -> &Shape {
        &self.shape
    }
    pub fn stats(&self) -> ChildWhirRelationStats {
        self.stats
    }
    pub fn params(&self) -> &FixedPathWhirParams {
        &self.params
    }
    pub fn num_children(&self) -> usize {
        self.children
    }
}
fn synthesize_merge(
    params: &FixedPathWhirParams,
    children: &[ChildWhirStatement],
    proofs: &[FixedPathWhirProof],
    root: Digest,
) -> (Shape, Vec<F>, usize) {
    let mut cs = ConstraintSystem::new();
    populate_merge(&mut cs, params, children, proofs, root);
    let used = cs.num_rows();
    let (shape, z) = cs.finish();
    (shape, z, used)
}

fn populate_merge(
    cs: &mut ConstraintSystem,
    params: &FixedPathWhirParams,
    children: &[ChildWhirStatement],
    proofs: &[FixedPathWhirProof],
    root: Digest,
) {
    let words = statement_words(children);
    let public: Vec<Lc> = words.iter().map(|&x| cs.public_input(x).into()).collect();
    let merged: [Lc; 4] = root.map(|x| cs.public_input(x).into());
    let inputs: Vec<_> = public
        .chunks(words.len() / children.len())
        .zip(proofs)
        .collect();
    let build = |chunk: &[(&[Lc], &FixedPathWhirProof)]| -> Vec<ConstraintSystem> {
        chunk
            .iter()
            .map(|(statement, proof)| {
                let mut child = cs.fork_public_inputs();
                verify_gadget(&mut child, params, statement, proof);
                child
            })
            .collect()
    };
    #[cfg(feature = "std")]
    let circuits = crate::map_chunks_bounded_with_limit(&inputs, children.len(), build)
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    #[cfg(not(feature = "std"))]
    let circuits = build(&inputs);
    for circuit in circuits {
        cs.append(circuit);
    }
    let digest = merged_gadget(cs, &public);
    for i in 0..4 {
        cs.enforce_equal(&merged[i], &digest[i]);
    }
}

fn merge_assignment(
    relation: &ChildWhirMergeRelation,
    children: &[ChildWhirStatement],
    proofs: &[FixedPathWhirProof],
    root: Digest,
) -> Result<Vec<F>, RecursiveWhirError> {
    let public = statement_words(children);
    let inputs: Vec<_> = public
        .chunks(public.len() / children.len())
        .zip(proofs)
        .collect();
    let build = |chunk: &[(&[F], &FixedPathWhirProof)]| -> Vec<Vec<F>> {
        chunk
            .iter()
            .map(|(statement, proof)| {
                let mut assignment = Assignment::default();
                verify_gadget(&mut assignment, &relation.params, statement, proof);
                assignment.values
            })
            .collect()
    };
    #[cfg(feature = "std")]
    let assignments = crate::map_chunks_bounded_with_limit(&inputs, children.len(), build)
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    #[cfg(not(feature = "std"))]
    let assignments = build(&inputs);
    let mut z = Vec::with_capacity(relation.shape.num_vars);
    z.push(F::ONE);
    z.extend_from_slice(&public);
    z.extend(root);
    for assignment in assignments {
        z.extend(assignment);
    }
    let mut merged = Assignment::default();
    merged_gadget(&mut merged, &public);
    z.extend(merged.values);
    if z.len() != relation.shape.mask_var_base {
        return Err(RecursiveWhirError::InvalidParameters);
    }
    z.resize(relation.shape.num_vars, F::ZERO);
    Ok(z)
}

/// Prove every child's complete fixed-path WHIR verification inside one committed outer
/// relation. No native-verification Boolean is trusted or inserted as a witness.
pub fn prove_succinct_children_whir_merge(
    relation: &ChildWhirMergeRelation,
    children: &[ChildWhirStatement],
    proofs: &[FixedPathWhirProof],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
) -> Result<SuccinctChildWhirMerge, RecursiveWhirError> {
    if !regime.meets_qrom_128_floor()
        || children.len() != relation.children
        || proofs.len() != relation.children
    {
        return Err(RecursiveWhirError::InvalidParameters);
    }
    if !children
        .iter()
        .zip(proofs)
        .all(|(c, p)| relation.params.well_formed(c, p))
    {
        return Err(RecursiveWhirError::MalformedProof);
    }
    let merged_root = merged_child_whir_root(children);
    let z = merge_assignment(relation, children, proofs, merged_root)?;
    let proof = protocol::prove_public(&relation.shape, z, MERGE_LABEL, regime, seed)
        .map_err(RecursiveWhirError::ZkHem)?;
    Ok(SuccinctChildWhirMerge { merged_root, proof })
}

/// Verify using only the public child headers/opening statements and the one parent proof.
pub fn verify_succinct_children_whir_merge(
    relation: &ChildWhirMergeRelation,
    children: &[ChildWhirStatement],
    regime: WhirSecurityRegime,
    parent: &SuccinctChildWhirMerge,
) -> bool {
    if !regime.meets_qrom_128_floor()
        || children.len() != relation.children
        || children
            .iter()
            .any(|c| Some(c.point.len()) != relation.params.num_vars())
        || parent.merged_root != merged_child_whir_root(children)
    {
        return false;
    }
    let mut public = statement_words(children);
    public.extend(parent.merged_root);
    protocol::verify_public(&relation.shape, &public, MERGE_LABEL, regime, &parent.proof)
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use std::time::Instant;
    const REGIME: WhirSecurityRegime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
    fn sample(i: usize) -> E {
        E::from_limbs(core::array::from_fn(
            |j| f((19 + i * 7919 + j * 313) as u64),
        ))
    }
    fn child(params: &FixedPathWhirParams, tag: u8) -> (ChildWhirStatement, FixedPathWhirProof) {
        let nv = params.num_vars().unwrap();
        let values: Vec<_> = (0..1 << nv)
            .map(|i| f((i * i + usize::from(tag) * 7919 + 11) as u64))
            .collect();
        let point: Vec<_> = (0..nv).map(|i| sample(i + usize::from(tag))).collect();
        let out = prove_for_recursion(params, [tag; 32], &values, &point).unwrap();
        assert_eq!(
            out.0.value,
            crate::field::mle_eval_base_at_ext4(&values, &point)
        );
        out
    }
    fn relation_for_child(
        params: &FixedPathWhirParams,
        child: &ChildWhirStatement,
        proof: &FixedPathWhirProof,
    ) -> (Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        let public: Vec<Lc> = child
            .words()
            .into_iter()
            .map(|x| cs.public_input(x).into())
            .collect();
        verify_gadget(&mut cs, params, &public, proof);
        cs.finish()
    }

    /// Witness-crafting backend: chosen allocations take forged values and every later
    /// wire is derived from them, so only rows that bind a forged wire can fail.
    #[derive(Default)]
    struct Forger {
        cs: ConstraintSystem,
        allocated: Vec<F>,
        forged: alloc::collections::BTreeMap<usize, F>,
    }
    impl Backend for Forger {
        type W = Lc;
        fn alloc(&mut self, v: F) -> Lc {
            let v = *self.forged.get(&self.allocated.len()).unwrap_or(&v);
            self.allocated.push(v);
            self.cs.alloc(v).into()
        }
        fn value(&self, v: &Lc) -> F {
            self.cs.eval(v)
        }
        fn mul(&mut self, a: &Lc, b: &Lc) -> Lc {
            self.cs.mul(a, b).into()
        }
        fn equal(&mut self, a: &Lc, b: &Lc) {
            self.cs.enforce_equal(a, b);
        }
        fn product(&mut self, a: &Lc, b: &Lc, c: &Lc) {
            self.cs.enforce_mul(a.clone(), b.clone(), c.clone());
        }
        fn perm(&mut self, s: &mut [Lc; 12]) {
            poseidon2_perm(&mut self.cs, s);
        }
    }
    fn forge(forged: &[(usize, F)], run: impl FnOnce(&mut Forger)) -> (Shape, Vec<F>, Vec<F>) {
        let mut forger = Forger {
            forged: forged.iter().copied().collect(),
            ..Forger::default()
        };
        run(&mut forger);
        let (shape, z) = forger.cs.finish();
        (shape, z, forger.allocated)
    }
    fn violated(shape: &Shape, z: &[F]) -> Vec<usize> {
        (0..shape.num_rows())
            .filter(|&i| {
                let a = shape.a.row_dot(i, z);
                let c = shape.c.row_dot(i, z);
                if i < shape.num_sbox {
                    crate::sponge::poseidon2_sbox7(a) != c
                } else {
                    a.const_mul(shape.b.row_dot(i, z)) != c
                }
            })
            .collect()
    }
    #[test]
    fn recorded_assignment_matches_symbolic_synthesis_exactly() {
        let params = FixedPathWhirParams::new(REGIME, 2).unwrap();
        let (children, proofs): (Vec<_>, Vec<_>) = (0..2).map(|i| child(&params, 7 + i)).unzip();
        let root = merged_child_whir_root(&children);
        let relation = ChildWhirMergeRelation::new(params.clone()).unwrap();
        let (shape, expected, _) = synthesize_merge(&params, &children, &proofs, root);
        assert_eq!(shape, relation.shape);
        let actual = merge_assignment(&relation, &children, &proofs, root).unwrap();
        assert_eq!(actual, expected);
        assert!(shape.is_satisfied(&actual));
    }

    #[test]
    fn seven_product_extension_gadget_matches_tower_arithmetic() {
        for i in 0..64 {
            let a = sample(i);
            let c = sample(i + 71);
            let mut cs = ConstraintSystem::new();
            let x = Ext::alloc(&mut cs, a);
            let y = Ext::alloc(&mut cs, c);
            let product = x.mul(&mut cs, &y);
            assert_eq!(product.value(&cs), a * c);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
        }
        for i in 0..4 {
            for j in 0..4 {
                let mut a = [F::ZERO; 4];
                a[i] = F::ONE;
                let mut c = [F::ZERO; 4];
                c[j] = F::ONE;
                let (a, c) = (E::from_limbs(a), E::from_limbs(c));
                let mut b = Native::default();
                assert_eq!(
                    Ext::constant(a).mul(&mut b, &Ext::constant(c)).value(&b),
                    a * c
                );
            }
        }
    }

    #[test]
    fn ext4_tower_arithmetic_matches_native_and_constrains_outputs() {
        for i in 0..12 {
            let mut cs = ConstraintSystem::new();
            let a = Ext::alloc(&mut cs, sample(i));
            let c = Ext::alloc(&mut cs, sample(i + 17));
            let mul = a.mul(&mut cs, &c);
            assert_eq!(mul.value(&cs), sample(i) * sample(i + 17));
            assert_eq!(a.add(&c).value(&cs), sample(i) + sample(i + 17));
            let output = mul.0[0].terms()[0].0 as usize;
            let (shape, mut z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            z[output] += F::ONE;
            assert!(!shape.is_satisfied(&z));
        }
    }
    #[test]
    fn fixed_path_native_handles_rate_escalation_and_both_pow_profiles() {
        for (regime, nv) in [
            (REGIME, 2),
            (REGIME, 7),
            (REGIME, 12),
            (WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128, 2),
        ] {
            let params = FixedPathWhirParams::new(regime, nv).unwrap();
            let (statement, proof) = child(&params, 5);
            assert!(verify_fixed_path(&params, &statement, &proof), "nv={nv}");
            let wire = proof.to_bytes();
            assert_eq!(
                FixedPathWhirProof::from_bytes(&wire, &params),
                Some(proof.clone())
            );
            let mut trailing = wire.clone();
            trailing.push(0);
            assert!(FixedPathWhirProof::from_bytes(&trailing, &params).is_none());
            assert!(FixedPathWhirProof::from_bytes(&wire[..wire.len() - 1], &params).is_none());
            let mut alias = wire;
            alias[8..16].copy_from_slice(&crate::field::GOLDILOCKS_PRIME.to_le_bytes());
            assert!(FixedPathWhirProof::from_bytes(&alias, &params).is_none());
            let mut bad = proof.clone();
            bad.query_nonces[0][0] ^= 1;
            assert!(!verify_fixed_path(&params, &statement, &bad));
            let mut bad = proof.clone();
            bad.final_coeffs[0] += E::V;
            assert!(!verify_fixed_path(&params, &statement, &bad));
            if proof.stage_roots.len() > 1 {
                let mut bad = proof.clone();
                bad.stage_roots[1][2] += F::ONE;
                assert!(!verify_fixed_path(&params, &statement, &bad));
                let mut bad = proof.clone();
                bad.ood_evals[1][0] += E::ONE;
                assert!(!verify_fixed_path(&params, &statement, &bad));
            }
        }
    }
    #[test]
    fn fixed_path_relation_has_no_witness_dependent_topology() {
        let params = FixedPathWhirParams::new(REGIME, 7).unwrap();
        let (a, pa) = child(&params, 1);
        let (b, pb) = child(&params, 2);
        let (shape, za) = relation_for_child(&params, &a, &pa);
        assert!(shape.is_satisfied(&za));
        let (other, zb) = relation_for_child(&params, &b, &pb);
        assert_eq!(shape, other);
        assert!(shape.is_satisfied(&zb));
        // Actual queried indices differ, including partial Fisher-Yates replacements.
        assert_ne!(pa.queries, pb.queries);
    }
    #[test]
    fn pow_and_canonical_bits_are_enforced_in_relation() {
        let mut native = Native::default();
        let mut tr = Transcript::new();
        tr.absorb(&mut native, 77, &[f(123)]);
        let nonce = grind(&tr, 16);
        let mut cs = ConstraintSystem::new();
        let mut circuit = Transcript::new();
        circuit.absorb(&mut cs, 77, &[Lc::constant(f(123))]);
        pow(&mut cs, &mut circuit, nonce, 16);
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        let mut wrong = nonce;
        wrong[0] ^= 1;
        // Select a nonce whose PoW is actually invalid (valid nonces are not unique).
        loop {
            let mut b = Native::default();
            let mut check = tr.clone();
            pow(&mut b, &mut check, wrong, 16);
            if b.failed {
                break;
            }
            wrong[0] = wrong[0].wrapping_add(1);
        }
        let mut cs = ConstraintSystem::new();
        let mut circuit = Transcript::new();
        circuit.absorb(&mut cs, 77, &[Lc::constant(f(123))]);
        pow(&mut cs, &mut circuit, wrong, 16);
        let (other, z) = cs.finish();
        assert_eq!(shape, other);
        assert!(!shape.is_satisfied(&z));
    }

    #[test]
    fn forged_bit_two_violates_booleanity() {
        // 2 = 0b10. The forgery (bit0, bit1) = (2, 0) keeps the weighted sum intact.
        let run = |b: &mut Forger| {
            let input = b.alloc(f(2));
            bits(b, &input, 8);
        };
        let (shape, z, _) = forge(&[], run);
        assert!(violated(&shape, &z).is_empty());
        let (other, z, _) = forge(&[(1, f(2)), (2, F::ZERO)], run);
        assert_eq!(shape, other);
        assert_eq!(violated(&shape, &z), [0]);

        // The same forged direction bit inside a Merkle canopy/path.
        let values = [sample(1), sample(2)].map(Ext::constant);
        let mut native = Native::default();
        let leaves: [Digest; 4] = core::array::from_fn(|idx| {
            if idx == 2 {
                leaf(&mut native, 1, &f(2), &values)
            } else {
                [f(10 + idx as u64), f(20 + idx as u64), f(30), f(40)]
            }
        });
        let n01 = compress(&mut native, &leaves[0], &leaves[1], 1, 0);
        let n23 = compress(&mut native, &leaves[2], &leaves[3], 1, 0);
        let root = compress(&mut native, &n01, &n23, 1, 1);
        let run = |b: &mut Forger| {
            let index = b.alloc(f(2));
            let binary = bits(b, &index, 2);
            let values: Vec<_> = [sample(1), sample(2)]
                .iter()
                .map(|&v| Ext::alloc(b, v))
                .collect();
            let mut canopy = Canopy::new(binary.len());
            canopy.path(b, 1, &index, &binary, &values, &[]);
            canopy.finish(b, 1, &leaves, &root.map(Lc::constant));
        };
        let (shape, z, _) = forge(&[], run);
        assert!(violated(&shape, &z).is_empty());
        let (other, z, _) = forge(&[(1, f(2)), (2, F::ZERO)], run);
        assert_eq!(shape, other);
        let rows = violated(&shape, &z);
        // The first multiplication row is bit zero's booleanity check.
        assert!(rows.contains(&shape.num_sbox));
    }

    #[test]
    fn forged_noncanonical_limb_cannot_spoof_pow_bits() {
        // w = 2^16 - 1 fails a 16-bit PoW, but w + p = 2^64 - 2^32 + 2^16 fits in 64 bits
        // and has sixteen trailing zeros.
        let word = (1u64 << 16) - 1;
        let alias = u128::from(word) + u128::from(crate::field::GOLDILOCKS_PRIME);
        assert!(alias < 1u128 << 64 && alias.trailing_zeros() == 16);
        let run = |b: &mut Forger| {
            let input = b.alloc(f(word));
            low_bits_zero(b, &input, 16);
        };
        let (shape, z, _) = forge(&[], run);
        // The short quotient cannot reconstruct a word with nonzero low bits.
        assert_eq!(violated(&shape, &z), [49]);
        let high = (alias >> 16) as u64;
        let mut forged = vec![(1, f(high))];
        forged.extend((0..48).map(|t| (2 + t, f((high >> t) & 1))));
        let (other, z, _) = forge(&forged, run);
        assert_eq!(shape, other);
        // The forged quotient and its bits reconstruct the alias modulo p;
        // only the canonical upper-bound constraint rejects it.
        assert_eq!(violated(&shape, &z), [48 + 1 + 1 + 31]);
    }

    #[test]
    fn forged_challenge_wire_and_header_limb_break_the_relation() {
        let params = FixedPathWhirParams::new(REGIME, 2).unwrap();
        let (statement, proof) = child(&params, 3);
        // Replay the transcript natively up to the first fold challenge.
        let mut b = Native::default();
        let mut tr = start(&mut b, &params, &statement.words());
        tr.absorb(&mut b, 3, &statement.commitment);
        let _ = [tr.ext(&mut b, 4), tr.ext(&mut b, 4)];
        tr.absorb_exts(&mut b, 5, &proof.ood_evals[0].map(Ext::constant));
        let _ = [tr.ext(&mut b, 6), tr.ext(&mut b, 6)];
        tr.absorb_exts(&mut b, 10, &proof.fold_polys[0].map(Ext::constant)[..3]);
        let phi = tr.ext(&mut b, 11).value(&b).to_limbs();

        let words = statement.words();
        let run = |b: &mut Forger| {
            let public: Vec<Lc> = words.iter().map(|&x| b.cs.public_input(x).into()).collect();
            verify_gadget(b, &params, &public, &proof);
        };
        let (shape, z, allocated) = forge(&[], run);
        assert!(violated(&shape, &z).is_empty());
        // The challenge is a pinned transcript lane, hence one of the allocations.
        let at = allocated
            .windows(4)
            .position(|w| w == phi)
            .expect("fold challenge is a transcript wire");
        // A prover that picks its own challenge and derives everything after it honestly.
        let (other, z, _) = forge(&[(at, phi[0] + F::ONE)], run);
        assert_eq!(shape, other);
        let rows = violated(&shape, &z);
        assert!(!rows.is_empty() && rows.iter().all(|&row| row >= shape.num_sbox));

        // Public header limbs: a changed limb and an out-of-range alias both reject.
        let (shape, z) = relation_for_child(&params, &statement, &proof);
        let mut bad = z.clone();
        bad[1] += F::ONE;
        assert!(!shape.is_satisfied(&bad));
        let mut cs = ConstraintSystem::new();
        let mut aliased = statement.words();
        aliased[0] += f(1 << 32);
        let public: Vec<Lc> = aliased
            .into_iter()
            .map(|x| cs.public_input(x).into())
            .collect();
        verify_gadget(&mut cs, &params, &public, &proof);
        let (other, z) = cs.finish();
        assert_eq!(shape, other);
        // Thirty-two Boolean rows of limb zero, then its weighted-sum row.
        assert!(violated(&shape, &z).contains(&(shape.num_sbox + 32)));
    }

    #[test]
    fn shuffle_is_distinct_and_modulo_constraints_exclude_aliases() {
        let mut cs = ConstraintSystem::new();
        let input: Lc = cs.alloc(f(crate::field::GOLDILOCKS_PRIME - 1)).into();
        let r = remainder(&mut cs, &input, 127);
        assert_eq!(
            cs.eval(&r).to_canonical_u64(),
            (crate::field::GOLDILOCKS_PRIME - 1) % 127
        );
        let (shape, mut z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        // Alter the allocated quotient, retaining the claimed remainder.
        z[2] += F::ONE;
        assert!(!shape.is_satisfied(&z));
        for groups in [128, 256, 1024] {
            let mut b = Native::default();
            let mut tr = Transcript::new();
            let mut sampler = QuerySampler { swaps: Vec::new() };
            let count = 109;
            let mut selected = alloc::collections::BTreeSet::new();
            for q in 0..count {
                let (index, _) = sampler.next(&mut b, &mut tr, groups, count, q);
                assert!(selected.insert(index.to_canonical_u64()));
                assert!(index.to_canonical_u64() < groups as u64);
            }
            assert!(!b.failed);
        }
    }
    #[test]
    fn merkle_and_recomputed_fake_sumcheck_claim_fail_inside_relation() {
        let params = FixedPathWhirParams::new(REGIME, 2).unwrap();
        let (statement, proof) = child(&params, 3);
        let (shape, z) = relation_for_child(&params, &statement, &proof);
        assert!(shape.is_satisfied(&z));
        for kind in 0..4 {
            let mut bad = proof.clone();
            match kind {
                0 => bad.queries[0][0].values[0] += E::ONE,
                1 => bad.canopy_leaves[0][0][0] += F::ONE,
                2 => bad.fold_polys[0][2] += E::V,
                _ => bad.final_coeffs[1] += E::ONE,
            }
            assert!(!verify_fixed_path(&params, &statement, &bad));
            let (other, z) = relation_for_child(&params, &statement, &bad);
            assert_eq!(shape, other);
            assert!(!shape.is_satisfied(&z), "tamper kind={kind}");
        }
        // Also tamper a bottom-tree sibling below the canopy at nv = 7 (`path_depth = 7 > 5`).
        let params7 = FixedPathWhirParams::new(REGIME, 7).unwrap();
        let (stmt7, mut proof7) = child(&params7, 9);
        assert!(!proof7.queries[0][0].siblings.is_empty());
        proof7.queries[0][0].siblings[0][0] += F::ONE;
        assert!(!verify_fixed_path(&params7, &stmt7, &proof7));
        let (_, z7) = relation_for_child(&params7, &stmt7, &proof7);
        assert!(
            !relation_for_child(&params7, &stmt7, &child(&params7, 9).1)
                .0
                .is_satisfied(&z7)
        );

        // Solve the affine bridge for a fake input claim after changing a polynomial.
        // Keeping the original challenges can make the final algebraic equation true,
        // but the altered claim is part of Fiat-Shamir, so the real replay must reject.
        let mut b = Native::default();
        let mut tr = start(&mut b, &params, &statement.words());
        tr.absorb(&mut b, 3, &statement.commitment);
        let zs = [tr.ext(&mut b, 4), tr.ext(&mut b, 4)];
        let ood = proof.ood_evals[0].map(Ext::constant);
        tr.absorb_exts(&mut b, 5, &ood);
        let mut ood_sum = E::ZERO;
        let mut kernels = vec![Kernel::initial(
            statement.point.iter().copied().map(Ext::constant).collect(),
        )];
        for (z, e) in zs.into_iter().zip(&ood) {
            let weight = tr.ext(&mut b, 6);
            ood_sum += weight.value(&b) * e.value(&b);
            kernels.push(geometric(&mut b, 0, weight, z, 2));
        }
        let wire = proof.fold_polys[0].map(Ext::constant);
        tr.absorb_exts(&mut b, 10, &wire[..3]);
        let phi = tr.ext(&mut b, 11);
        tr.absorb_exts(&mut b, 12, &wire[3..]);
        pow(&mut b, &mut tr, proof.fold_nonces[0], 0);
        let chals = [tr.ext(&mut b, 13), tr.ext(&mut b, 14), tr.ext(&mut b, 15)];
        let coeffs: Vec<_> = proof
            .final_coeffs
            .iter()
            .copied()
            .map(Ext::constant)
            .collect();
        let target = terminal(&mut b, &coeffs, core::slice::from_ref(&phi), &kernels).value(&b);
        let mut fake = proof.clone();
        fake.fold_polys[0][0] += E::ONE;
        let fw = fake.fold_polys[0].map(Ext::constant);
        let zero = bridge(&mut b, &fw, &Ext::zero(), &phi, &chals).value(&b);
        let one = bridge(&mut b, &fw, &Ext::one(), &phi, &chals).value(&b);
        let fake_claim = (target - zero) * (one - zero).inv() - ood_sum;
        assert_ne!(fake_claim, statement.value);
        let mut altered = statement;
        altered.value = fake_claim;
        assert!(!verify_fixed_path(&params, &altered, &fake));
        let (other, z) = relation_for_child(&params, &altered, &fake);
        assert_eq!(shape, other);
        assert!(!shape.is_satisfied(&z));
    }
    #[test]
    fn begkn91_query_sampler_and_correlated3_opening_soundness() {
        // 1. Exercise the O(Q) BEGKN91 offline-memory sampler (`count = 24 > 20`, `groups = 64`)
        //    and verify parity with direct `QuerySampler` plus forgery rejection.
        let mut b_direct = Native::default();
        let mut tr_direct = Transcript::new();
        tr_direct.absorb(&mut b_direct, 99, &[f(42)]);
        let mut direct = QuerySampler { swaps: Vec::new() };
        let expected: Vec<F> = (0..24)
            .map(|q| direct.next(&mut b_direct, &mut tr_direct, 64, 24, q).0)
            .collect();

        let mut b_mem = Native::default();
        let mut tr_mem = Transcript::new();
        tr_mem.absorb(&mut b_mem, 99, &[f(42)]);
        let got: Vec<F> = sample_queries(&mut b_mem, &mut tr_mem, 64, 24)
            .into_iter()
            .map(|(idx, _)| idx)
            .collect();
        assert!(!b_mem.failed);
        assert_eq!(got, expected);
        assert_eq!(tr_mem.state, tr_direct.state);

        let run = |b: &mut Forger| {
            let mut tr = Transcript::new();
            tr.absorb(b, 99, &[Lc::constant(f(42))]);
            let out = sample_queries(b, &mut tr, 64, 24);
            for ((idx, _), &want) in out.iter().zip(&expected) {
                b.equal(idx, &Lc::constant(want));
            }
        };
        let (shape, z, allocated) = forge(&[], run);
        assert!(violated(&shape, &z).is_empty());
        // Forging the first sorted address wire breaks strict ordering / multiset balance.
        let at_addr = allocated
            .iter()
            .enumerate()
            .skip(200)
            .find(|&(_, &v)| v.to_canonical_u64() < 64)
            .map(|(i, _)| i)
            .unwrap();
        let (other, z_bad, _) = forge(&[(at_addr, allocated[at_addr] + F::ONE)], run);
        assert_eq!(shape, other);
        assert!(!violated(&shape, &z_bad).is_empty());

        // 2. Correlated 3-oracle WHIR opening at nv = 7 (exercises multi-stage + O(Q) sampler!).
        let params = FixedPathWhirParams::new(REGIME, 7).unwrap();
        let nv = 7;
        let t0: Vec<F> = (0..1 << nv).map(|i| f((i * 13 + 3) as u64)).collect();
        let t1: Vec<F> = (0..1 << nv).map(|i| f((i * i + 17) as u64)).collect();
        let t2: Vec<F> = (0..1 << nv).map(|i| f((i * 29 + 5) as u64)).collect();
        let w0 = commit_for_recursion(&params, &t0).unwrap();
        let w1 = PublicRecursionCommitment::commit(&params, &t1).unwrap();
        let w2 = commit_for_recursion(&params, &t2).unwrap();
        let roots0 = [w0.root(), w1.root(), w2.root()];
        let pts: [Vec<E>; 3] =
            core::array::from_fn(|j| (0..nv).map(|i| sample(j * 11 + i)).collect());
        let claims = [
            [
                Some(crate::field::mle_eval_base_at_ext4(&t0, &pts[0])),
                None,
                None,
            ],
            [
                None,
                Some(crate::field::mle_eval_base_at_ext4(&t1, &pts[1])),
                Some(crate::field::mle_eval_base_at_ext4(&t1, &pts[2])),
            ],
            [
                None,
                Some(crate::field::mle_eval_base_at_ext4(&t2, &pts[1])),
                Some(crate::field::mle_eval_base_at_ext4(&t2, &pts[2])),
            ],
        ];
        let mut tr_p = Transcript::new();
        let proof = open_correlated3_for_recursion(&params, &mut tr_p, w0, &w1, w2, &pts).unwrap();
        assert!(params.well_formed_correlated3(&proof));

        let mut b_v = Native::default();
        let mut tr_v = Transcript::new();
        let pts_c: [Vec<Ext<F>>; 3] =
            core::array::from_fn(|j| pts[j].iter().copied().map(Ext::constant).collect());
        let claims_c: [[Option<Ext<F>>; 3]; 3] =
            core::array::from_fn(|m| core::array::from_fn(|j| claims[m][j].map(Ext::constant)));
        verify_correlated3_gadget(
            &mut b_v, &params, &mut tr_v, &roots0, &pts_c, &claims_c, &proof,
        );
        assert!(!b_v.failed);

        let mut cs = ConstraintSystem::new();
        let mut tr_cs = Transcript::new();
        let roots_cs: [[Lc; 4]; 3] = roots0.map(|r| r.map(|x| cs.public_input(x).into()));
        let pts_cs: [Vec<Ext<Lc>>; 3] =
            core::array::from_fn(|j| pts[j].iter().copied().map(Ext::constant).collect());
        let claims_cs: [[Option<Ext<Lc>>; 3]; 3] =
            core::array::from_fn(|m| core::array::from_fn(|j| claims[m][j].map(Ext::constant)));
        verify_correlated3_gadget(
            &mut cs, &params, &mut tr_cs, &roots_cs, &pts_cs, &claims_cs, &proof,
        );
        let (c_shape, c_z) = cs.finish();
        assert!(c_shape.is_satisfied(&c_z));

        let mut bad_proof = proof.clone();
        bad_proof.stage0_queries[0][1].values[0] += E::ONE;
        let mut b_bad = Native::default();
        let mut tr_bad = Transcript::new();
        verify_correlated3_gadget(
            &mut b_bad,
            &params,
            &mut tr_bad,
            &roots0,
            &pts_c,
            &claims_c,
            &bad_proof,
        );
        assert!(b_bad.failed);
    }

    #[test]
    fn succinct_merge_public_binding_for_two_and_four_children() {
        measure_children(2, 2);
        measure_children(2, 4);
    }

    #[test]
    #[ignore = "explicit release benchmark: three-stage 4096-cell child oracles"]
    fn two_child_multistage_release_benchmark() {
        measure_children(12, 2);
    }

    #[test]
    #[ignore = "explicit release benchmark: four 4096-cell children, parent below their sum"]
    fn four_child_multistage_compression_benchmark() {
        let (parent, children) = measure_children(12, 4);
        assert!(parent < children, "parent={parent} children={children}");
    }

    /// Cost of the fixed-path format at a real shard size: `QSAG_PROBE_NV` variables
    /// (24 is one 128-signer Jorts shard). Prints the one-child verifier relation and, unless
    /// `QSAG_PROBE_PROVE=0`, times the child commit-and-open.
    #[test]
    #[ignore = "measurement: QSAG_PROBE_NV, QSAG_PROBE_PROVE"]
    fn fixed_path_scale_probe() {
        let nv: usize = std::env::var("QSAG_PROBE_NV")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(16);
        let params = FixedPathWhirParams::new(REGIME, nv).unwrap();
        let start = Instant::now();
        let relation = ChildWhirMergeRelation::with_children(params.clone(), 1).unwrap();
        std::println!(
            "FIXED_PATH_PROBE nv={nv} stages={:?} early_stop={} sbox_rows={} multiplication_rows={} padded_rows={} setup_ms={:.1}",
            params.geometries(),
            params.schedule.early_stop_vars,
            relation.stats.sbox_rows,
            relation.stats.multiplication_rows,
            relation.stats.padded_rows,
            start.elapsed().as_secs_f64() * 1000.
        );
        if std::env::var("QSAG_PROBE_PROVE").as_deref() == Ok("0") {
            return;
        }
        let table: Vec<F> = (0..1u64 << nv).map(|i| f(i * i + 5)).collect();
        let point: Vec<E> = (0..nv).map(sample).collect();
        let start = Instant::now();
        let (statement, proof) = prove_for_recursion(&params, [7; 32], &table, &point).unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.;
        let start = Instant::now();
        assert!(verify_fixed_path(&params, &statement, &proof));
        std::println!(
            "FIXED_PATH_PROBE nv={nv} child_prove_ms={prove_ms:.1} child_verify_ms={:.1} child_bytes={}",
            start.elapsed().as_secs_f64() * 1000.,
            proof.to_bytes().len()
        );
    }

    /// Returns `(parent bytes, summed child proof bytes)`.
    fn measure_children(nv: usize, arity: usize) -> (usize, usize) {
        let params = FixedPathWhirParams::new(REGIME, nv).unwrap();
        let start = Instant::now();
        let (children, proofs): (Vec<_>, Vec<_>) =
            (0..arity).map(|i| child(&params, 7 + i as u8)).unzip();
        let child_time = start.elapsed();
        let child_bytes: usize = proofs.iter().map(|p| p.to_bytes().len()).sum();
        let setup = Instant::now();
        let relation = ChildWhirMergeRelation::with_children(params, arity).unwrap();
        let setup_time = setup.elapsed();
        assert_eq!(relation.num_children(), arity);
        let start = Instant::now();
        let parent =
            prove_succinct_children_whir_merge(&relation, &children, &proofs, REGIME, &[42; 32])
                .unwrap();
        let prove_time = start.elapsed();
        let bytes = parent.to_bytes();
        // Precisely the magic, merged digest and ONE committed outer proof.
        assert_eq!(bytes.len(), 40 + parent.proof.to_bytes().len());
        let decoded = SuccinctChildWhirMerge::from_bytes(&bytes, &relation, REGIME).unwrap();
        let start = Instant::now();
        assert!(verify_succinct_children_whir_merge(
            &relation, &children, REGIME, &decoded
        ));
        let verify_time = start.elapsed();
        assert_eq!(parent, decoded);
        std::println!(
            "FIXED_PATH_MERGE child_nv={nv} arity={arity} sbox_rows={} multiplication_rows={} padded_rows={} variables={} parent_bytes={} children_bytes={child_bytes} children_prove_ms={:.3} setup_ms={:.3} prove_ms={:.3} verify_ms={:.3}",
            relation.stats.sbox_rows,
            relation.stats.multiplication_rows,
            relation.stats.padded_rows,
            relation.stats.variables,
            bytes.len(),
            child_time.as_secs_f64() * 1000.,
            setup_time.as_secs_f64() * 1000.,
            prove_time.as_secs_f64() * 1000.,
            verify_time.as_secs_f64() * 1000.
        );

        let mut bad_children = children.clone();
        bad_children[arity - 1].shard_header[0] ^= 1;
        assert!(!verify_succinct_children_whir_merge(
            &relation,
            &bad_children,
            REGIME,
            &parent
        ));
        let mut rerooted = parent.clone();
        rerooted.merged_root = merged_child_whir_root(&bad_children);
        // Even recomputing the public root cannot bypass the relation's public-cell checks.
        assert!(!verify_succinct_children_whir_merge(
            &relation,
            &bad_children,
            REGIME,
            &rerooted
        ));
        // Order and count of the children are part of the statement.
        let mut swapped = children.clone();
        swapped.swap(0, 1);
        assert!(!verify_succinct_children_whir_merge(
            &relation, &swapped, REGIME, &parent
        ));
        assert!(!verify_succinct_children_whir_merge(
            &relation,
            &children[..arity - 1],
            REGIME,
            &parent
        ));
        assert_eq!(
            prove_succinct_children_whir_merge(
                &relation,
                &children[..arity - 1],
                &proofs[..arity - 1],
                REGIME,
                &[42; 32]
            ),
            Err(RecursiveWhirError::InvalidParameters)
        );
        let mut bad = parent.clone();
        bad.proof.row_rounds[0][0] += E::ONE;
        assert!(!verify_succinct_children_whir_merge(
            &relation, &children, REGIME, &bad
        ));
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(SuccinctChildWhirMerge::from_bytes(&trailing, &relation, REGIME).is_none());
        assert!(
            SuccinctChildWhirMerge::from_bytes(&bytes[..bytes.len() - 1], &relation, REGIME)
                .is_none()
        );
        assert!(!verify_succinct_children_whir_merge(
            &relation,
            &children,
            WhirSecurityRegime::BciksJohnsonClassical128,
            &parent
        ));
        (bytes.len(), child_bytes)
    }
}

impl FixedPathWhirProof {
    /// Fixed-width field encoding. Lengths come exclusively from the externally pinned
    /// parameters; there are no prover-supplied vector lengths or query indices.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = b"QSAGFWP1".to_vec();
        for root in &self.stage_roots {
            for x in root {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        for leaves in &self.canopy_leaves {
            for d in leaves {
                for x in d {
                    out.extend_from_slice(&x.to_le_bytes());
                }
            }
        }
        for e in self
            .ood_evals
            .iter()
            .flatten()
            .chain(self.fold_polys.iter().flatten())
        {
            out.extend_from_slice(&e.to_le_bytes());
        }
        for n in self.fold_nonces.iter().chain(&self.query_nonces) {
            for limb in n {
                out.extend_from_slice(&limb.to_le_bytes());
            }
        }
        for (stage, queries) in self.queries.iter().enumerate() {
            for q in queries {
                for e in &q.values {
                    if stage == 0 {
                        out.extend_from_slice(&e.to_limbs()[0].to_le_bytes());
                    } else {
                        out.extend_from_slice(&e.to_le_bytes());
                    }
                }
                for d in &q.siblings {
                    for x in d {
                        out.extend_from_slice(&x.to_le_bytes());
                    }
                }
            }
        }
        for e in &self.final_coeffs {
            out.extend_from_slice(&e.to_le_bytes());
        }
        out
    }

    /// Strict canonical parsing with a size check before allocating any proof vectors.
    pub fn from_bytes(bytes: &[u8], params: &FixedPathWhirParams) -> Option<Self> {
        let nv = params.num_vars()?;
        let stages = params.schedule.stages.len();
        let rounds = nv - params.schedule.early_stop_vars;
        let mut size = 8 + stages * 32 + stages * 64 + rounds * 160 + (rounds + stages) * 8;
        for (stage, (arity, groups, count)) in params.geometries().into_iter().enumerate() {
            let (depth, base_level) = canopy_split(groups.trailing_zeros() as usize);
            size += (1usize << depth) * 32;
            let val_bytes = if stage == 0 { 8 } else { 32 };
            size += count * (arity * val_bytes + base_level * 32);
        }
        size += ((1usize << params.schedule.early_stop_vars) + 2) * 32;
        if bytes.len() != size || bytes.get(..8)? != b"QSAGFWP1" {
            return None;
        }
        struct Reader<'a>(&'a [u8]);
        impl Reader<'_> {
            fn word<const N: usize>(&mut self) -> Option<[u8; N]> {
                let (head, tail) = self.0.split_at_checked(N)?;
                self.0 = tail;
                head.try_into().ok()
            }
            fn base(&mut self) -> Option<F> {
                let w = u64::from_le_bytes(self.word()?);
                (w < crate::field::GOLDILOCKS_PRIME).then(|| f(w))
            }
            fn ext(&mut self) -> Option<E> {
                E::from_le_bytes_canonical(self.word()?)
            }
        }
        let mut r = Reader(&bytes[8..]);
        let mut proof = params.placeholder();
        for root in &mut proof.stage_roots {
            for x in root {
                *x = r.base()?;
            }
        }
        for leaves in &mut proof.canopy_leaves {
            for d in leaves {
                for x in d {
                    *x = r.base()?;
                }
            }
        }
        for e in proof
            .ood_evals
            .iter_mut()
            .flatten()
            .chain(proof.fold_polys.iter_mut().flatten())
        {
            *e = r.ext()?;
        }
        for n in proof.fold_nonces.iter_mut().chain(&mut proof.query_nonces) {
            for limb in n {
                *limb = u32::from_le_bytes(r.word()?);
            }
        }
        for (stage, queries) in proof.queries.iter_mut().enumerate() {
            for q in queries {
                for e in &mut q.values {
                    *e = if stage == 0 {
                        E::from_base(r.base()?)
                    } else {
                        r.ext()?
                    };
                }
                for d in &mut q.siblings {
                    for x in d {
                        *x = r.base()?;
                    }
                }
            }
        }
        for e in &mut proof.final_coeffs {
            *e = r.ext()?;
        }
        r.0.is_empty().then_some(proof)
    }
}
