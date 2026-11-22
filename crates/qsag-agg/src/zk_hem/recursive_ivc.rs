//! Binary proof-carrying data over Goldilocks with quintic WHIR challenges.
//!
//! [`prove_ivc_tree`] proves a power-of-two run of contiguous Jorts shards.
//! [`verify_ivc_tree`] accepts the subtree statement and its canonical root
//! proof. It selects the two compiled relations from the local profile.
//! [`SuccinctIvcStep`] also accepts two previously encoded internal proofs.
//!
//! Leaves execute the Jorts multisignature predicate and a directory path.
//! Every internal node checks both children’s complete WHIR opening and
//! row/column sumchecks. A degree-two sumcheck reduces evaluations of the
//! fixed public matrices to one evaluation claim for the parent. The root
//! scans the two compiled matrices, so verification cost is independent of
//! the number of shards and linear in the fixed relation description.
//!
//! The default proof type uses the v2 DKT26 query schedule. The distinct
//! `SuccinctIvcProof<true>` type selects the low-query diagnostic schedule.
//! The public row sumchecks expose witness evaluations. A composed QROM
//! knowledge-extraction analysis for this recursive transcript is open.
use super::recursive_whir::{Backend, Base, Native, bits, equal_bit, f, remainder, select};
use super::v2::{
    field5::Fp5 as E,
    hash::Channel,
    params::{self, Schedule, StageSpec},
    pcs::{self, StageDims},
};
use crate::field::{Goldilocks as F, GoldilocksOps as _};
use alloc::{vec, vec::Vec};
use arithmetic::{Duplex, Quint, Wide, compress};
mod arithmetic;
mod leaf;
mod matrix;
mod octopus;
mod r1cs;
mod tree;
mod verifier;
mod wire;
pub use tree::{
    IvcPolicyRegistry, IvcShard, IvcTreeStepRelation, SuccinctIvcProof, SuccinctIvcStep,
    ivc_signing_message, prove_ivc_tree, verify_ivc_tree,
};

pub type IvcCommitment = [F; 7];
type Digest = IvcCommitment;

/// The half-open shard interval and its authenticated public context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IvcSubtreeStatement {
    pub policy_registry_root: [u8; 32],
    pub shard_lo: u64,
    pub shard_hi: u64,
    pub total_quorums: u64,
    pub message_digest: [u8; 32],
}
impl IvcSubtreeStatement {
    /// Eight u32 limbs per digest and two per u64, all in little-endian order.
    pub fn public_inputs(&self) -> [F; 22] {
        let mut bytes = [0u8; 88];
        bytes[..32].copy_from_slice(&self.policy_registry_root);
        bytes[32..40].copy_from_slice(&self.shard_lo.to_le_bytes());
        bytes[40..48].copy_from_slice(&self.shard_hi.to_le_bytes());
        bytes[48..56].copy_from_slice(&self.total_quorums.to_le_bytes());
        bytes[56..].copy_from_slice(&self.message_digest);
        core::array::from_fn(|i| f(u32::from_le_bytes(bytes.as_chunks::<4>().0[i]) as u64))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IvcStepConfig {
    log_cells: usize,
    schedule: Schedule,
}
impl IvcStepConfig {
    /// Query counts from the quintic DKT26 parameter calculator. The calculator
    /// bounds the v2 IOP. Instantiating its transcript with Poseidon2 is an
    /// additional cryptographic assumption.
    pub fn dkt26(log_cells: usize) -> Option<Self> {
        Some(Self {
            log_cells,
            schedule: params::schedule(log_cells)?,
        })
    }
    /// Low-query geometry for execution and differential tests.
    pub fn diagnostic(log_cells: usize) -> Option<Self> {
        if !(4..=24).contains(&log_cells) {
            return None;
        }
        let mut stages = Vec::new();
        let mut remaining = log_cells - 2;
        while remaining > 0 {
            let step_vars = remaining.min(if stages.is_empty() {
                2.min(remaining - 1)
            } else {
                4
            });
            stages.push(StageSpec {
                step_vars,
                blowup: 2,
                num_queries: 2,
            });
            remaining -= step_vars;
        }
        Some(Self {
            log_cells,
            schedule: Schedule {
                early_stop_vars: 2,
                stages,
            },
        })
    }
    fn dims(&self) -> Vec<StageDims> {
        pcs::stage_dims(self.log_cells, &self.schedule).expect("validated schedule")
    }
    fn transcript(&self) -> Duplex<F> {
        let mut tr = Duplex::new();
        let mut words = vec![
            f(self.log_cells as u64),
            f(self.schedule.early_stop_vars as u64),
        ];
        for s in &self.schedule.stages {
            words.extend([s.step_vars, s.blowup, s.num_queries].map(|n| f(n as u64)));
        }
        tr.frame(&mut Native::default(), b"IVC-WHIR-v1", &words);
        tr
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Stage {
    root: Digest,
    ood: Vec<E>,
    folds: Vec<[E; 5]>,
    fibers: Vec<Vec<F>>,
    siblings: Vec<Digest>,
}
/// Salted, masked PCS opening. The verifier derives the complete geometry
/// from its configuration before reading proof data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixedPathWhirW24 {
    stages: Vec<Stage>,
    mask_claim: E,
    final_coeffs: Vec<E>,
}
impl FixedPathWhirW24 {
    fn blank(cfg: &IvcStepConfig) -> Self {
        Self {
            stages: cfg
                .dims()
                .iter()
                .enumerate()
                .map(|(i, d)| Stage {
                    root: [F::ZERO; 7],
                    ood: vec![E::ZERO; if i == 0 { 5 } else { 2 }],
                    folds: vec![[E::ZERO; 5]; d.step_vars],
                    fibers: vec![vec![F::ZERO; fiber_len(i, d)]; d.queries],
                    siblings: vec![[F::ZERO; 7]; octopus::frontier_len(d.fibers, d.queries)],
                })
                .collect(),
            mask_claim: E::ZERO,
            final_coeffs: vec![E::ZERO; (1 << cfg.schedule.early_stop_vars) + 2],
        }
    }
    fn fits(&self, cfg: &IvcStepConfig) -> bool {
        let dims = cfg.dims();
        self.stages.len() == dims.len()
            && self.final_coeffs.len() == (1 << cfg.schedule.early_stop_vars) + 2
            && self.stages.iter().zip(dims).enumerate().all(|(i, (s, d))| {
                s.ood.len() == if i == 0 { 5 } else { 2 }
                    && s.folds.len() == d.step_vars
                    && s.fibers.len() == d.queries
                    && s.fibers.iter().all(|q| q.len() == fiber_len(i, &d))
                    && s.siblings.len() == octopus::frontier_len(d.fibers, d.queries)
            })
    }
}
fn fiber_len(i: usize, d: &StageDims) -> usize {
    if i == 0 {
        4 + 5 + d.arity()
    } else {
        5 * d.arity()
    }
}
fn leaf<B: Wide>(b: &mut B, i: usize, index: B::W, words: &[B::W], nonce: &[B::W; 4]) -> [B::W; 7] {
    let mut tr = Duplex::new();
    let mut data = vec![B::W::constant(f(i as u64)), index];
    if i == 0 {
        data.extend_from_slice(nonce);
    }
    data.extend_from_slice(words);
    tr.frame(b, b"IVC-LEAF-v1", &data);
    core::array::from_fn(|j| tr.0[j].clone())
}
fn sample<B: Wide>(b: &mut B, tr: &mut Duplex<B::W>, d: StageDims) -> Vec<(B::W, Vec<B::W>)> {
    if d.queries > 16 && d.queries < d.fibers {
        return sample_log(b, tr, d);
    }
    let mut swaps = Vec::<(B::W, B::W)>::new();
    let mut indices = Vec::with_capacity(d.queries);
    for q in 0..d.queries {
        let index = if d.queries == d.fibers {
            B::W::constant(f(q as u64))
        } else {
            if q % 16 == 0 {
                tr.frame(b, b"IVC-QUERY-v1", &[]);
            }
            let key = remainder(b, &tr.0[q % 16], (d.fibers - q) as u64);
            let mut read = |k: &B::W| {
                swaps.iter().fold(k.clone(), |v, (addr, data)| {
                    let same = equal_bit(b, k, addr);
                    select(b, &same, data, &v)
                })
            };
            let index = read(&key);
            let replacement = read(&B::W::constant(f((d.fibers - 1 - q) as u64)));
            swaps.push((key, replacement));
            index
        };
        let binary = bits(b, &index, d.log_leaves());
        indices.push((index, binary));
    }
    indices
}

// Offline partial Fisher-Yates. Each read of the tail precedes the write to
// the sampled rank. A Boolean switch network permutes every event exactly
// once. Strictly increasing (address,time) keys enforce the address histories.
fn sample_log<B: Wide>(b: &mut B, tr: &mut Duplex<B::W>, d: StageDims) -> Vec<(B::W, Vec<B::W>)> {
    use alloc::collections::BTreeMap;
    let mut mem = BTreeMap::new();
    let mut events = Vec::new();
    let mut order = Vec::new();
    let mut out = Vec::new();
    let stride = (2 * d.queries).next_power_of_two();
    let key_bits = d.log_leaves() + stride.trailing_zeros() as usize;
    let one = B::W::constant(F::ONE);
    for q in 0..d.queries {
        if q % 16 == 0 {
            tr.frame(b, b"IVC-QUERY-v1", &[]);
        }
        let tail = d.fibers - 1 - q;
        let rank = remainder(b, &tr.0[q % 16], (tail + 1) as u64);
        let j = b.value(&rank).to_canonical_u64() as usize;
        let old = *mem.get(&j).unwrap_or(&j);
        let rep = *mem.get(&tail).unwrap_or(&tail);
        mem.insert(j, rep);
        let index = b.alloc(f(old as u64));
        let replacement = b.alloc(f(rep as u64));
        let binary = bits(b, &index, d.log_leaves());
        out.push((index.clone(), binary));
        for (time, addr, addr_wire, before, after) in [
            (
                2 * q,
                tail,
                B::W::constant(f(tail as u64)),
                replacement.clone(),
                replacement.clone(),
            ),
            (2 * q + 1, j, rank, index, replacement),
        ] {
            let key = addr_wire
                .scale(f(stride as u64))
                .plus(&B::W::constant(f(time as u64)));
            events.push([addr_wire, key, before, after]);
            order.push((addr, time));
        }
    }
    order.sort_unstable();
    let mut dest = vec![0; order.len()];
    for (i, &(_, time)) in order.iter().enumerate() {
        dest[time] = i;
    }
    let sorted = octopus::route(b, events, &dest);
    b.equal(&sorted[0][0], &sorted[0][2]);
    for pair in sorted.windows(2) {
        let [prev, cur] = [&pair[0], &pair[1]];
        bits(b, &cur[1].minus(&prev[1]).minus(&one), key_bits);
        let same = equal_bit(b, &cur[0], &prev[0]);
        let want = select(b, &same, &prev[3], &cur[0]);
        b.equal(&cur[2], &want);
    }
    out
}

impl Channel for Duplex<F> {
    fn absorb(&mut self, label: &[u8], payload: &[u8]) {
        let mut words = vec![f(payload.len() as u64)];
        crate::sponge::push_packed_bytes_7_limbs(&mut words, payload);
        self.frame(&mut Native::default(), label, &words);
    }
    fn squeeze_fp5(&mut self, label: &[u8]) -> E {
        E(self.challenge(&mut Native::default(), label).0)
    }
    fn squeeze_fp5_nonzero(&mut self, label: &[u8]) -> E {
        self.squeeze_fp5(label)
    }
    fn absorb_fp5_slice(&mut self, label: &[u8], xs: &[E]) {
        let limbs: Vec<_> = xs.iter().flat_map(|x| x.0).collect();
        self.frame(&mut Native::default(), label, &limbs);
    }
    fn squeeze_distinct_indices(&mut self, _: &[u8], n: usize, count: usize) -> Vec<usize> {
        let d = StageDims {
            vars: 0,
            step_vars: 0,
            log_domain: n.trailing_zeros() as usize,
            fibers: n,
            queries: count,
        };
        sample(&mut Native::default(), self, d)
            .into_iter()
            .map(|(i, _)| i.to_canonical_u64() as usize)
            .collect()
    }
}

struct Oracle {
    tree: Vec<Vec<Digest>>,
    words: Vec<Vec<F>>,
}
impl Drop for Oracle {
    fn drop(&mut self) {
        for fiber in &mut self.words {
            qsag_asm::volatile_fill(fiber, F::ZERO);
        }
    }
}
impl Oracle {
    fn new(i: usize, words: Vec<Vec<F>>, nonce: [F; 4]) -> Self {
        let mut hashes = vec![[F::ZERO; 7]; words.len()];
        crate::pcs::fill_indexed(&mut hashes, |j| {
            leaf(&mut Native::default(), i, f(j as u64), &words[j], &nonce)
        });
        Self {
            tree: octopus::build(i, hashes),
            words,
        }
    }
    fn root(&self) -> Digest {
        self.tree.last().unwrap()[0]
    }
    fn query(
        &self,
        tr: &mut Duplex<F>,
        s: &mut Stage,
        d: StageDims,
        i: usize,
        chals: &[[E; 3]],
        beta: E,
    ) -> Vec<(F, E)> {
        let idx = tr.squeeze_distinct_indices(b"QUERY", d.fibers, d.queries);
        s.fibers = idx.iter().map(|&j| self.words[j].clone()).collect();
        s.siblings = octopus::open(&self.tree, idx.clone());
        idx.into_iter()
            .zip(&s.fibers)
            .map(|(j, fiber)| {
                let x = F::NON_RESIDUE.const_mul(F::two_adic_generator(d.log_domain).pow(j as u64));
                let (vals, mask) = if i == 0 {
                    (
                        fiber[9..].iter().copied().map(E::from_base).collect(),
                        beta * E(fiber[4..9].try_into().unwrap()),
                    )
                } else {
                    (
                        fiber.as_chunks::<5>().0.iter().copied().map(E).collect(),
                        E::ZERO,
                    )
                };
                (
                    x.pow(d.arity() as u64),
                    pcs::fold_fiber(vals, x, chals) + mask,
                )
            })
            .collect()
    }
}

/// Commit before deriving the point of a relation's sumcheck. Keep the mask
/// and the salt source private. Domain-separated randomness is drawn from seed.
pub struct IvcTableCommitment {
    cfg: IvcStepConfig,
    coeffs: Vec<F>,
    mask: Vec<E>,
    nonce: [F; 4],
    oracle: Oracle,
}
impl Drop for IvcTableCommitment {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.coeffs, F::ZERO);
        qsag_asm::volatile_fill(&mut self.mask, E::ZERO);
    }
}
impl IvcTableCommitment {
    pub fn commit(cfg: &IvcStepConfig, table: &[F], seed: &[u8; 32]) -> Option<Self> {
        if table.len() != 1 << cfg.log_cells {
            return None;
        }
        let d = cfg.dims()[0];
        let coeffs = crate::pcs::hypercube_to_monomial_coeffs(table);
        let mut stream = super::SeedStream::new(b"IVC-W24-MASK-v1", seed);
        let nonce = core::array::from_fn(|_| stream.next_base());
        let mask: Vec<_> = (0..pcs::mask_len(cfg.log_cells, d.step_vars))
            .map(|_| E(core::array::from_fn(|_| stream.next_base())))
            .collect();
        let mut z = pcs::encode_base(&coeffs, d.log_domain);
        let mut r = pcs::encode_ext_folded(&mask, d.log_domain, d.step_vars);
        let words = (0..d.fibers)
            .map(|j| {
                let mut words: Vec<_> = (0..4).map(|_| stream.next_base()).collect();
                words.extend(r[j].0);
                words.extend(pcs::fiber(&z, &d, j));
                words
            })
            .collect();
        qsag_asm::volatile_fill(&mut z, F::ZERO);
        qsag_asm::volatile_fill(&mut r, E::ZERO);
        Some(Self {
            cfg: cfg.clone(),
            coeffs,
            mask,
            nonce,
            oracle: Oracle::new(0, words, nonce),
        })
    }
    pub fn root(&self) -> Digest {
        self.oracle.root()
    }
    pub fn nonce(&self) -> [F; 4] {
        self.nonce
    }
    pub fn open(&self, context: &[F], point: &[E]) -> Option<(E, FixedPathWhirW24)> {
        let cfg = &self.cfg;
        if point.len() != cfg.log_cells {
            return None;
        }
        let mut kernel = vec![E::ONE];
        for x in point {
            let n = kernel.len();
            kernel.extend_from_within(..);
            for v in &mut kernel[n..] {
                *v *= *x;
            }
        }
        let value = kernel
            .iter()
            .zip(&self.coeffs)
            .fold(E::ZERO, |a, (x, c)| a + x.mul_base(*c));
        let mut tr = cfg.transcript();
        bind(
            &mut Native::default(),
            &mut tr,
            context,
            &self.nonce,
            &self.root(),
            &point
                .iter()
                .copied()
                .map(Quint::constant)
                .collect::<Vec<_>>(),
            &Quint::constant(value),
        );
        let dims = cfg.dims();
        let red = pcs::stage0_reduce(
            &self.coeffs,
            &self.mask,
            dims[0].step_vars,
            5,
            kernel,
            value,
            &mut tr,
        )
        .ok()?;
        if red.beta_r.is_zero() {
            return None;
        }
        let mut proof = FixedPathWhirW24::blank(cfg);
        proof.stages[0].root = self.root();
        proof.stages[0].ood = red.mask_evals;
        proof.stages[0].folds = red.folds;
        proof.mask_claim = red.mask_claim;
        let (mut poly, mut st, mut chals) = (red.g, red.st, red.chals);
        let mut prev = None;
        for (i, d) in dims.iter().copied().enumerate().skip(1) {
            let mut code = pcs::encode_ext(&poly, d.log_domain);
            let words = (0..d.fibers)
                .map(|j| {
                    pcs::fiber(&code, &d, j)
                        .into_iter()
                        .flat_map(|x| x.0)
                        .collect()
                })
                .collect();
            qsag_asm::volatile_fill(&mut code, E::ZERO);
            let oracle = Oracle::new(i, words, self.nonce);
            proof.stages[i].root = oracle.root();
            tr.frame(&mut Native::default(), b"STAGE_ROOT", &oracle.root());
            let xs = core::array::from_fn(|_| tr.squeeze_fp5(b"OOD_POINT"));
            let ood = pcs::eval_poly(&poly, xs);
            proof.stages[i].ood = ood.to_vec();
            tr.absorb_fp5_slice(b"OOD_EVAL", &ood);
            let shifts = prev.as_ref().unwrap_or(&self.oracle).query(
                &mut tr,
                &mut proof.stages[i - 1],
                dims[i - 1],
                i - 1,
                &chals,
                red.beta_r,
            );
            let (terms, delta) = pcs::stage_claims(xs, &ood, &shifts, &mut tr);
            pcs::add_points(&mut st.kernel, &terms);
            st.points.extend(terms);
            st.claim += delta;
            chals.clear();
            for j in 0..d.step_vars {
                let (next, wire, c) = pcs::prove_fold(&poly, &mut st, 0, &mut tr).ok()?;
                qsag_asm::volatile_fill(&mut poly, E::ZERO);
                poly = next;
                proof.stages[i].folds[j] = wire;
                chals.push(c);
            }
            prev = Some(oracle);
        }
        tr.absorb_fp5_slice(b"FINAL_POLY", &poly);
        let last = dims.len() - 1;
        prev?.query(
            &mut tr,
            &mut proof.stages[last],
            dims[last],
            last,
            &chals,
            red.beta_r,
        );
        proof.final_coeffs = poly;
        Some((value, proof))
    }
}
fn bind<B: Wide>(
    b: &mut B,
    tr: &mut Duplex<B::W>,
    context: &[B::W],
    nonce: &[B::W; 4],
    root: &[B::W; 7],
    point: &[Quint<B::W>],
    value: &Quint<B::W>,
) {
    tr.frame(b, b"CONTEXT", context);
    tr.frame(b, b"TREE_NONCE", nonce);
    tr.frame(b, b"ROOT", root);
    tr.exts(b, b"POINT", point);
    tr.exts(b, b"VALUE", core::slice::from_ref(value));
}

/// Unpadded constraint counts for the complete opening verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IvcRowCensus {
    pub permutations: usize,
    pub sbox_rows: usize,
    pub multiplication_rows: usize,
    /// Allocations made inside this gadget, excluding its supplied inputs.
    pub witness_variables: usize,
}
impl IvcRowCensus {
    /// Rank-one quadratic expansion with four products for each native S-box.
    pub fn quadratic_rows(self) -> usize {
        4 * self.sbox_rows + self.multiplication_rows
    }
    pub fn total_rows(self) -> usize {
        self.sbox_rows + self.multiplication_rows
    }
}
impl IvcStepConfig {
    pub fn opening_row_census(&self, context_words: usize) -> IvcRowCensus {
        let mut b = arithmetic::Counter::default();
        verifier::check(
            &mut b,
            self,
            &vec![F::ZERO; context_words],
            &[F::ZERO; 4],
            &[F::ZERO; 7],
            &vec![Quint::constant(E::ZERO); self.log_cells],
            &Quint::constant(E::ZERO),
            &FixedPathWhirW24::blank(self),
        );
        IvcRowCensus {
            permutations: b.permutations,
            sbox_rows: b.permutations * crate::sponge::POSEIDON2_GL24_SBOX_COUNT,
            multiplication_rows: b.products,
            witness_variables: b.allocated,
        }
    }
}
#[cfg(test)]
mod tests;
