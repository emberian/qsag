//! Binary proof-carrying data over Goldilocks with quintic `[DKT26]` WHIR challenges.
//!
//! [`prove_ivc_tree`] proves ordered contiguous shards, combining overlapping signer groups within each shard.
//! [`verify_ivc_tree`] accepts the subtree statement and its canonical `[DKT26]` `< 2^{-128}`
//! QROM root proof (`QSAGIVC1\x00`, `639,673` bytes).
//! [`SuccinctIvcStep`] also accepts two previously encoded internal proofs.
//!
//! Leaves execute the Jorts multisignature predicate and a directory path.
//! Every internal node checks both children’s complete WHIR opening and
//! row/column sumchecks. A degree-two sumcheck reduces evaluations of the
//! fixed public matrices to one evaluation claim for the parent. The root
//! scans the two compiled matrices, so verification cost is independent of
//! the number of shards and linear in the fixed relation description.
//!
//! [`SuccinctIvcProof`] exclusively uses the `[DKT26]` `< 2^{-128}` QROM query schedule
//! (`IvcStepConfig::dkt26(23)`), with zero wire-level profile polymorphism; custom geometries
//! are agreed out of band. Internal PCD exposes row, column, and matrix evaluations; zero
//! knowledge requires a ZK outer layer. `Qsag.Protocol.Aggregation.RecursiveIvcPublicRowQrom`
//! proves public-round mass `< 2^-160` and a spine budget `< 2^-128` for `d ≤ 64, Q ≤ 2^64`.
//! Quorum-forgery extraction assumes selected-node and collision bounds. The whole-tree budget
//! clears 128 bits for `d ≤ 7, Q ≤ 2^64` or `d ≤ 20, Q ≤ 2^57`.
pub mod high_arity_ivc;
pub use high_arity_ivc::{HighArityProof, prove_high_arity_tree, verify_high_arity_tree};
mod gadgets;
#[cfg(test)]
use super::v2::params::StageSpec;
use super::v2::{
    field5::Fp5 as E,
    hash::Channel,
    params::{self, Schedule},
    pcs::{self, StageDims},
};
use crate::field::{Goldilocks as F, GoldilocksOps as _};
use alloc::{vec, vec::Vec};
use arithmetic::{Duplex, Quint, Wide, compress};
use gadgets::{Backend, Base, Native, bits, bits_canonical_u64, equal_bit, f, remainder, select};
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

/// Fixed-width signer bitmap for a shard with up to 256 validators.
pub const IVC_BITMAP_BYTES: usize = 32;
const STATEMENT_WORDS: usize = 31;
const STEP_WORDS: usize = STATEMENT_WORDS + 7;

/// The half-open shard interval and its authenticated public context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IvcSubtreeStatement {
    pub policy_registry_root: [u8; 32],
    pub shard_lo: u64,
    pub shard_hi: u64,
    /// Unique signers counted per shard, summed across the interval.
    pub total_signers: u64,
    /// Authenticated policy threshold on a single shard, zero across shards.
    pub shard_threshold: u32,
    /// Member i occupies bit i % 8 of byte i / 8. Multi-shard intervals use all zeroes.
    pub signer_bitmap: [u8; IVC_BITMAP_BYTES],
    pub message_digest: [u8; 32],
}
impl IvcSubtreeStatement {
    /// Width of the authenticated half-open interval.
    pub fn completed_shards(&self) -> u64 {
        self.shard_hi.saturating_sub(self.shard_lo)
    }

    /// Eight u32 limbs per digest and two per u64, all in little-endian order.
    pub fn public_inputs(&self) -> [F; STATEMENT_WORDS] {
        let mut bytes = [0u8; STATEMENT_WORDS * 4];
        bytes[..32].copy_from_slice(&self.policy_registry_root);
        bytes[32..40].copy_from_slice(&self.shard_lo.to_le_bytes());
        bytes[40..48].copy_from_slice(&self.shard_hi.to_le_bytes());
        bytes[48..56].copy_from_slice(&self.total_signers.to_le_bytes());
        bytes[56..60].copy_from_slice(&self.shard_threshold.to_le_bytes());
        bytes[60..92].copy_from_slice(&self.signer_bitmap);
        bytes[92..].copy_from_slice(&self.message_digest);
        core::array::from_fn(|i| f(u32::from_le_bytes(bytes.as_chunks::<4>().0[i]) as u64))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IvcStepConfig {
    log_cells: usize,
    schedule: Schedule,
}
impl IvcStepConfig {
    pub fn log_cells(&self) -> usize {
        self.log_cells
    }

    fn is_dkt26(&self) -> bool {
        Self::dkt26(self.log_cells).as_ref() == Some(self)
    }

    /// Query counts from the quintic DKT26 parameter calculator. The calculator
    /// bounds the v2 IOP. Instantiating its transcript with Poseidon2 is an
    /// additional cryptographic assumption.
    pub fn dkt26(log_cells: usize) -> Option<Self> {
        Some(Self {
            log_cells,
            schedule: params::schedule(log_cells)?,
        })
    }
    /// Low-query geometry restricted strictly to crate-internal unit tests (`#[cfg(test)]`).
    #[cfg(test)]
    pub(crate) fn diagnostic(log_cells: usize) -> Option<Self> {
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
    // Ensure `cur_key - prev_key - 1 in [0, 2^key_bits)` cannot wrap modulo Goldilocks (`2^(key_bits+1) < p`).
    assert!(
        key_bits <= 62,
        "offline Fisher-Yates key width exceeds Goldilocks no-wrap bound"
    );
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
    /// Fixed-topology R1CS circuits cannot loop a data-dependent number of times: draw once,
    /// abort proving if zero (`red.beta_r.is_zero()`), and enforce `x * inv_or_zero(x) == 1`
    /// in the circuit (`verifier::check`).
    fn squeeze_fp5_nonzero(&mut self, label: &[u8]) -> E {
        self.squeeze_fp5(label)
    }
    fn absorb_fp5_slice(&mut self, label: &[u8], xs: &[E]) {
        let limbs: Vec<_> = xs.iter().flat_map(|x| x.0).collect();
        self.frame(&mut Native::default(), label, &limbs);
    }
    fn squeeze_distinct_indices(&mut self, label: &[u8], n: usize, count: usize) -> Vec<usize> {
        assert_eq!(
            label, b"QUERY",
            "Duplex fixed-topology query sampler only supports the QUERY phase label"
        );
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
    #[cfg(feature = "vulkan")]
    fn from_heap(words: Vec<Vec<F>>, heap: Vec<[u64; 7]>) -> Self {
        let mut tree = Vec::new();
        let mut n = heap.len() / 2;
        while n > 0 {
            tree.push(
                heap[n..2 * n]
                    .iter()
                    .map(|d| d.map(F::from_u64_reduced))
                    .collect(),
            );
            n /= 2;
        }
        Self { words, tree }
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
        Self::commit_inner(
            cfg,
            table,
            seed,
            #[cfg(feature = "vulkan")]
            None,
        )
    }
    fn commit_inner(
        cfg: &IvcStepConfig,
        table: &[F],
        seed: &[u8; 32],
        #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
    ) -> Option<Self> {
        use qsag_core::wipe::SecretBuffer;
        if table.len() != 1 << cfg.log_cells {
            return None;
        }
        let d = cfg.dims()[0];
        let coeffs = SecretBuffer::new(crate::pcs::hypercube_to_monomial_coeffs(table));
        let mut stream = super::SeedStream::new(b"IVC-W24-MASK-v1", seed);
        let nonce = core::array::from_fn(|_| stream.next_base());
        let mask: Vec<_> = (0..pcs::mask_len(cfg.log_cells, d.step_vars))
            .map(|_| E(core::array::from_fn(|_| stream.next_base())))
            .collect();
        let mask = SecretBuffer::new(mask);
        let cpu_encode = || {
            (
                SecretBuffer::new(pcs::encode_base(&coeffs, d.log_domain)),
                SecretBuffer::new(pcs::encode_ext_folded(&mask, d.log_domain, d.step_vars)),
            )
        };
        #[cfg(feature = "vulkan")]
        let (z, r) = if let Some(gpu) = gpu {
            crate::vulkan::encode_stage0(gpu, &coeffs, &mask, d.log_domain, d.step_vars).ok()?
        } else {
            cpu_encode()
        };
        #[cfg(not(feature = "vulkan"))]
        let (z, r) = cpu_encode();
        let words: Vec<Vec<F>> = (0..d.fibers)
            .map(|j| {
                let mut words = Vec::with_capacity(9 + d.arity());
                words.extend((0..4).map(|_| stream.next_base()));
                words.extend(r[j].0);
                words.extend(pcs::fiber(&z, &d, j));
                words
            })
            .collect();
        #[cfg(feature = "vulkan")]
        let oracle = if let Some(gpu) = gpu {
            let words = SecretBuffer::new(words);
            let salts = qsag_core::wipe::SecretBuffer::new(
                words
                    .iter()
                    .map(|v| core::array::from_fn(|j| v[j].to_canonical_u64()))
                    .collect::<Vec<_>>(),
            );
            let mask = crate::vulkan::ext_words(&r);
            let profile = qsag_accel::vulkan::CanopyProfile::IvcStage0 {
                nonce: nonce.map(F::to_canonical_u64),
                salts: &salts,
                mask_code: &mask,
            };
            let heap = gpu
                .canopy(profile, 0, d.arity(), &crate::vulkan::base_words(&z))
                .ok()?;
            Oracle::from_heap(words.into_inner(), heap)
        } else {
            Oracle::new(0, words, nonce)
        };
        #[cfg(not(feature = "vulkan"))]
        let oracle = Oracle::new(0, words, nonce);
        Some(Self {
            cfg: cfg.clone(),
            coeffs: coeffs.into_inner(),
            mask: mask.into_inner(),
            nonce,
            oracle,
        })
    }
    pub fn root(&self) -> Digest {
        self.oracle.root()
    }
    pub fn nonce(&self) -> [F; 4] {
        self.nonce
    }
    pub fn open(&self, context: &[F], point: &[E]) -> Option<(E, FixedPathWhirW24)> {
        self.open_inner(
            context,
            point,
            #[cfg(feature = "vulkan")]
            None,
        )
    }
    fn open_inner(
        &self,
        context: &[F],
        point: &[E],
        #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
    ) -> Option<(E, FixedPathWhirW24)> {
        use qsag_core::wipe::SecretBuffer;
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
        let (mut poly, mut st, mut chals) = (SecretBuffer::new(red.g), red.st, red.chals);
        let mut prev = None;
        for (i, d) in dims.iter().copied().enumerate().skip(1) {
            #[cfg(feature = "vulkan")]
            let code = if let Some(gpu) = gpu {
                crate::vulkan::encode_ext(gpu, &poly, d.log_domain, F::NON_RESIDUE).ok()?
            } else {
                pcs::encode_ext(&poly, d.log_domain)
            };
            #[cfg(not(feature = "vulkan"))]
            let code = pcs::encode_ext(&poly, d.log_domain);
            let code = SecretBuffer::new(code);
            let words: Vec<Vec<F>> = (0..d.fibers)
                .map(|j| {
                    pcs::fiber(&code, &d, j)
                        .into_iter()
                        .flat_map(|x| x.0)
                        .collect()
                })
                .collect();
            #[cfg(feature = "vulkan")]
            let oracle = if let Some(gpu) = gpu {
                let words = SecretBuffer::new(words);
                let heap = gpu
                    .canopy(
                        qsag_accel::vulkan::CanopyProfile::IvcExtension,
                        i as u8,
                        d.arity(),
                        &crate::vulkan::ext_words(&code),
                    )
                    .ok()?;
                Oracle::from_heap(words.into_inner(), heap)
            } else {
                Oracle::new(i, words, self.nonce)
            };
            #[cfg(not(feature = "vulkan"))]
            let oracle = Oracle::new(i, words, self.nonce);
            drop(code);
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
                poly = SecretBuffer::new(next);
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
        proof.final_coeffs = poly.into_inner();
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
