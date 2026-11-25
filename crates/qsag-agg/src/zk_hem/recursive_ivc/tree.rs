//! The recursive step has one circuit at every internal depth. Each child has a
//! Boolean witness selecting its fixed signature or step matrix. Both child
//! arguments are replayed before the new public matrix claim is derived.
use super::super::multisig::MultisigParams;
use super::super::relation::{ConstraintSystem, Shape};
use super::*;
use super::{
    leaf::Witness,
    r1cs::{Acc, Argument, Claim},
};
use alloc::sync::Arc;
pub use leaf::{IvcPolicyRegistry, IvcShard, ivc_signing_message};

pub(super) fn add64<B: Backend>(b: &mut B, a: &[B::W], v: &[B::W], out: &[B::W], increment: bool) {
    let one = B::W::constant(F::ONE);
    let z = B::W::constant(F::ZERO);
    let radix = f(1 << 32);
    let lo = a[0].plus(&v[0]).plus(&B::W::constant(f(increment as u64)));
    let carry = b.alloc(f(b.value(&lo).to_canonical_u64() >> 32));
    b.product(&carry, &one.minus(&carry), &z);
    b.equal(&lo, &out[0].plus(&carry.scale(radix)));
    b.equal(&a[1].plus(&v[1]).plus(&carry), &out[1]);
}
pub(super) fn split<B: Wide>(
    b: &mut B,
    public: &[B::W],
    children: &[IvcSubtreeStatement; 2],
) -> [Vec<B::W>; 2] {
    let zero = B::W::constant(F::ZERO);
    let one = B::W::constant(F::ONE);
    let same = b.alloc(f((children[0].shard_lo == children[1].shard_lo) as u64));
    let cross = one.minus(&same);
    b.product(&same, &cross, &zero);
    let mut bitmaps = Vec::with_capacity(2);
    let c = children.each_ref().map(|s| {
        let w = s.public_inputs().map(|x| b.alloc(x));
        for v in w[..15].iter().chain(&w[23..]) {
            bits(b, v, 32);
        }
        bitmaps.push(
            w[15..23]
                .iter()
                .flat_map(|v| bits(b, v, 32))
                .collect::<Vec<_>>(),
        );
        let gap = s.shard_hi.saturating_sub(s.shard_lo).saturating_sub(1);
        let g = [gap as u32, (gap >> 32) as u32].map(|k| b.alloc(f(k as u64)));
        for x in &g {
            bits(b, x, 32);
        }
        add64(b, &w[8..10], &g, &w[10..12], true);
        // Each gap limb is an unsigned u32, so their sum vanishes exactly
        // for a single shard, including across the 32-bit carry boundary.
        let gap_sum = g[0].plus(&g[1]);
        b.product(&same, &gap_sum, &zero);
        let single = equal_bit(b, &gap_sum, &zero);
        b.product(&single, &w[13], &zero);
        let completing = b.mul(&cross, &single);
        let slack = b.mul(&completing, &w[12].minus(&w[14]));
        bits(b, &slack, 32);
        b.product(&same, &w[14].minus(&public[14]), &zero);
        for i in (0..8).chain(23..STATEMENT_WORDS) {
            b.equal(&w[i], &public[i]);
        }
        w.to_vec()
    });
    for i in 0..2 {
        let start = select(b, &same, &c[0][8 + i], &c[0][10 + i]);
        b.equal(&start, &c[1][8 + i]);
        b.equal(&c[0][8 + i], &public[8 + i]);
        b.equal(&c[1][10 + i], &public[10 + i]);
    }
    b.product(&cross, &public[14], &zero);
    let mut weight = zero.clone();
    for (i, limb) in public[15..23].iter().enumerate() {
        b.product(&cross, limb, &zero);
        for (k, parent) in bits(b, limb, 32).iter().enumerate() {
            let j = 32 * i + k;
            let (l, r) = (&bitmaps[0][j], &bitmaps[1][j]);
            let union = l.plus(r).minus(&b.mul(l, r));
            b.product(&same, &parent.minus(&union), &zero);
            weight = weight.plus(&union);
        }
    }
    let left = [
        select(b, &same, &weight, &c[0][12]),
        b.mul(&cross, &c[0][13]),
    ];
    let right = [b.mul(&cross, &c[1][12]), b.mul(&cross, &c[1][13])];
    add64(b, &left, &right, &public[12..14], false);
    c
}
impl IvcSubtreeStatement {
    pub(super) fn blank() -> Self {
        Self {
            policy_registry_root: [0; 32],
            shard_lo: 0,
            shard_hi: 1,
            total_signers: 0,
            shard_threshold: 0,
            signer_bitmap: [0; IVC_BITMAP_BYTES],
            message_digest: [0; 32],
        }
    }

    fn consistent(&self, depth: usize) -> bool {
        match self.shard_hi.checked_sub(self.shard_lo) {
            Some(1) => {
                let members = 1usize << depth;
                (1..=members).contains(&(self.shard_threshold as usize))
                    && self.total_signers > 0
                    && self.total_signers
                        == self
                            .signer_bitmap
                            .iter()
                            .map(|b| u64::from(b.count_ones()))
                            .sum()
                    && (members..8 * IVC_BITMAP_BYTES)
                        .all(|i| self.signer_bitmap[i / 8] & (1 << (i % 8)) == 0)
            }
            Some(2..) => self.shard_threshold == 0 && self.signer_bitmap == [0; IVC_BITMAP_BYTES],
            _ => false,
        }
    }

    fn complete(&self) -> bool {
        self.total_signers >= u64::from(self.shard_threshold)
    }

    /// Union signer sets on one shard, or join adjacent quorum-complete intervals.
    pub fn merge(l: &Self, r: &Self) -> Option<Self> {
        if l.policy_registry_root != r.policy_registry_root
            || l.message_digest != r.message_digest
            || !l.consistent(8)
            || !r.consistent(8)
        {
            return None;
        }
        let (signer_bitmap, shard_threshold, total_signers) = if l.shard_lo == r.shard_lo
            && l.shard_threshold > 0
            && l.shard_threshold == r.shard_threshold
        {
            let union: [u8; IVC_BITMAP_BYTES] =
                core::array::from_fn(|i| l.signer_bitmap[i] | r.signer_bitmap[i]);
            let total = union.iter().map(|b| u64::from(b.count_ones())).sum();
            (union, l.shard_threshold, total)
        } else if l.shard_hi == r.shard_lo && l.complete() && r.complete() {
            (
                [0; IVC_BITMAP_BYTES],
                0,
                l.total_signers.checked_add(r.total_signers)?,
            )
        } else {
            return None;
        };
        Some(Self {
            policy_registry_root: l.policy_registry_root,
            message_digest: l.message_digest,
            shard_lo: l.shard_lo,
            shard_hi: r.shard_hi,
            total_signers,
            shard_threshold,
            signer_bitmap,
        })
    }
}
struct Step<'a> {
    kinds: [bool; 2],
    stmts: [IvcSubtreeStatement; 2],
    children: [&'a Argument; 2],
    rounds: Vec<Vec<E>>,
    answer: E,
}
fn circuit<B: Wide>(
    b: &mut B,
    cfg: &IvcStepConfig,
    sboxes: [usize; 2],
    public: &[B::W],
    w: &Step<'_>,
) {
    for x in public[..15].iter().chain(&public[23..STATEMENT_WORDS]) {
        bits(b, x, 32);
    }
    let children = split(b, public, &w.stmts);
    let mut claims = Vec::new();
    for ((stmt, arg), kind) in children.iter().zip(w.children).zip(w.kinds) {
        let mode = b.alloc(f(kind as u64));
        b.product(
            &mode,
            &B::W::constant(F::ONE).minus(&mode),
            &B::W::constant(F::ZERO),
        );
        let (old, new) = r1cs::verify(b, cfg, sboxes, &mode, stmt, arg);
        claims.extend([old, new]);
    }
    let out = matrix::check(b, &claims, &w.rounds, w.answer).digest(b);
    for (v, x) in out.iter().zip(&public[STATEMENT_WORDS..]) {
        b.equal(v, x);
    }
}
fn step_words(s: &IvcSubtreeStatement, a: &Acc) -> Vec<F> {
    let mut p = s.public_inputs().to_vec();
    p.extend(Claim::from_acc(a).digest(&mut Native::default()));
    p
}
fn skeleton<'a>(cfg: &IvcStepConfig, arg: &'a Argument) -> Step<'a> {
    Step {
        kinds: [true; 2],
        stmts: core::array::from_fn(|_| IvcSubtreeStatement::blank()),
        children: [arg, arg],
        rounds: vec![vec![E::ZERO; 3]; 2 * cfg.log_cells + 3],
        answer: E::ZERO,
    }
}
impl IvcStepConfig {
    /// Both complete WHIR/R1CS verifiers, interval constraints, and the
    /// fixed-matrix claim reduction. Closing adds padding separately.
    pub fn row_census(&self) -> IvcRowCensus {
        let arg = Argument::blank(self);
        let w = skeleton(self, &arg);
        let mut b = arithmetic::Counter::default();
        circuit(&mut b, self, [0; 2], &[F::ZERO; STEP_WORDS], &w);
        IvcRowCensus {
            permutations: b.permutations,
            sbox_rows: b.permutations * 236,
            multiplication_rows: b.products,
            witness_variables: b.allocated,
        }
    }
}

/// Recursive binary tree step relation over quintic DKT26 WHIR, with a default of `2^23` cells.
pub struct IvcTreeStepRelation {
    cfg: IvcStepConfig,
    committee: MultisigParams,
    leaf: Arc<Shape>,
    step: Arc<Shape>,
}

struct Node {
    stmt: IvcSubtreeStatement,
    proof: Argument,
    internal: bool,
}
impl Node {
    fn borrow(&self) -> (&IvcSubtreeStatement, &Argument, bool) {
        (&self.stmt, &self.proof, self.internal)
    }
}

impl IvcTreeStepRelation {
    pub fn new() -> Option<Self> {
        let cfg = profile();
        #[cfg(feature = "std")]
        let (leaf, step) = {
            type Keys = std::sync::OnceLock<Option<(Arc<Shape>, Arc<Shape>)>>;
            static PRODUCTION: Keys = Keys::new();
            PRODUCTION
                .get_or_init(|| Self::compile(&cfg, leaf::COMMITTEE))
                .clone()?
        };
        #[cfg(not(feature = "std"))]
        let (leaf, step) = Self::compile(&cfg, leaf::COMMITTEE)?;
        Some(Self {
            cfg,
            committee: leaf::COMMITTEE,
            leaf,
            step,
        })
    }

    /// Compile the two matrices for this DKT26 schedule and committee.
    /// Returns `None` if either matrix exceeds the configured cell budget.
    pub fn with_config_and_committee(
        cfg: IvcStepConfig,
        committee: MultisigParams,
    ) -> Option<Self> {
        if !cfg.is_dkt26() {
            return None;
        }
        if committee == leaf::COMMITTEE && cfg == profile() {
            return Self::new();
        }
        Self::with_parameters(cfg, committee)
    }

    pub fn committee(&self) -> MultisigParams {
        self.committee
    }
    pub fn config(&self) -> &IvcStepConfig {
        &self.cfg
    }

    pub(super) fn with_parameters(cfg: IvcStepConfig, committee: MultisigParams) -> Option<Self> {
        let (leaf, step) = Self::compile(&cfg, committee)?;
        Some(Self {
            cfg,
            committee,
            leaf,
            step,
        })
    }

    fn compile(cfg: &IvcStepConfig, committee: MultisigParams) -> Option<(Arc<Shape>, Arc<Shape>)> {
        if !committee.valid() || committee.depth > 8 {
            return None;
        }
        let census = cfg.row_census();
        let n = 1 << cfg.log_cells;
        if census.total_rows() + 12 > n || 1 + STEP_WORDS + census.witness_variables + 12 > n {
            return None;
        }
        let mut cs = ConstraintSystem::with_row_templates();
        leaf::populate(
            &mut cs,
            cfg,
            &IvcSubtreeStatement::blank(),
            &Witness::blank(committee),
        );
        let (leaf, _) = cs.finish();
        if leaf.num_vars > n || leaf.num_rows() > n {
            return None;
        }
        let mut cs = ConstraintSystem::with_row_templates();
        let pub_wires: Vec<_> = (0..STEP_WORDS)
            .map(|_| cs.public_input(F::ZERO).into())
            .collect();
        let arg = Argument::blank(cfg);
        circuit(
            &mut cs,
            cfg,
            [leaf.num_sbox, census.sbox_rows],
            &pub_wires,
            &skeleton(cfg, &arg),
        );
        if cs.num_rows() != census.total_rows() {
            return None;
        }
        let (step, _) = cs.finish();
        if step.num_sbox != census.sbox_rows
            || step.num_vars != 1 + STEP_WORDS + census.witness_variables + 12
            || step.num_vars > n
            || step.num_rows() > n
        {
            return None;
        }
        Some((Arc::new(leaf), Arc::new(step)))
    }

    pub fn shape(&self) -> &Shape {
        &self.step
    }
    fn shapes(&self) -> [&Shape; 2] {
        [&self.leaf, &self.step]
    }
    fn sboxes(&self) -> [usize; 2] {
        [self.leaf.num_sbox, self.step.num_sbox]
    }
    fn child_claims(
        &self,
        kind: bool,
        stmt: &IvcSubtreeStatement,
        p: &Argument,
    ) -> Option<[Claim<F>; 2]> {
        if !p.fits(&self.cfg) {
            return None;
        }
        let mut b = Native::default();
        let (a, c) = r1cs::verify(
            &mut b,
            &self.cfg,
            self.sboxes(),
            &f(kind as u64),
            &stmt.public_inputs(),
            p,
        );
        (!b.failed).then_some([a, c])
    }
    fn fold(
        &self,
        left: &Node,
        right: &Node,
        seed: &[u8; 32],
        #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
    ) -> Option<Node> {
        self.fold_children(
            [left.borrow(), right.borrow()],
            seed,
            #[cfg(feature = "vulkan")]
            gpu,
        )
    }

    fn fold_children(
        &self,
        children: [(&IvcSubtreeStatement, &Argument, bool); 2],
        seed: &[u8; 32],
        #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
    ) -> Option<Node> {
        let [(s, l, kind_l), (t, r, kind_r)] = children;
        let stmt = IvcSubtreeStatement::merge(s, t)?;
        let [a, b] = self.child_claims(kind_l, s, l)?;
        let [c, d] = self.child_claims(kind_r, t, r)?;
        let (rounds, acc) = matrix::prove(self.shapes(), self.cfg.log_cells, &[a, b, c, d]);
        let w = Step {
            kinds: [kind_l, kind_r],
            stmts: [s.clone(), t.clone()],
            children: [l, r],
            rounds,
            answer: acc.value,
        };
        let mut cs = ConstraintSystem::witness_only();
        let public: Vec<_> = step_words(&stmt, &acc)
            .iter()
            .map(|&v| cs.public_input(v).into())
            .collect();
        circuit(&mut cs, &self.cfg, self.sboxes(), &public, &w);
        let z = cs.finish_assignment(&self.step)?;
        let p = r1cs::prove(
            &self.cfg,
            &self.step,
            true,
            &stmt,
            acc,
            z,
            seed,
            #[cfg(feature = "vulkan")]
            gpu,
        )?;
        Some(Node {
            stmt,
            proof: p,
            internal: true,
        })
    }

    fn reduce(
        &self,
        mut nodes: Vec<Node>,
        rng: &mut super::super::SeedStream,
        #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
    ) -> Option<Node> {
        while nodes.len() > 1 {
            let mut parents = Vec::with_capacity(nodes.len().div_ceil(2));
            let mut iter = nodes.into_iter();
            while let Some(left) = iter.next() {
                parents.push(match iter.next() {
                    Some(right) => self.fold(
                        &left,
                        &right,
                        &rng.next_bytes32(),
                        #[cfg(feature = "vulkan")]
                        gpu,
                    )?,
                    None => left,
                });
            }
            nodes = parents;
        }
        nodes.pop()
    }

    pub fn prove(
        &self,
        reg: &IvcPolicyRegistry,
        message_digest: [u8; 32],
        leaves: &[IvcShard<'_>],
        seed: &[u8; 32],
    ) -> Option<(IvcSubtreeStatement, SuccinctIvcProof)> {
        self.prove_inner(
            reg,
            message_digest,
            leaves,
            seed,
            #[cfg(feature = "vulkan")]
            None,
        )
    }

    #[cfg(feature = "vulkan")]
    pub fn prove_with_vulkan(
        &self,
        gpu: &qsag_accel::vulkan::VulkanFp5Session<'_>,
        reg: &IvcPolicyRegistry,
        message_digest: [u8; 32],
        leaves: &[IvcShard<'_>],
        seed: &[u8; 32],
    ) -> Option<(IvcSubtreeStatement, SuccinctIvcProof)> {
        self.prove_inner(reg, message_digest, leaves, seed, Some(gpu))
    }
    fn prove_inner(
        &self,
        reg: &IvcPolicyRegistry,
        message_digest: [u8; 32],
        leaves: &[IvcShard<'_>],
        seed: &[u8; 32],
        #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
    ) -> Option<(IvcSubtreeStatement, SuccinctIvcProof)> {
        if leaves.is_empty() || reg.committee != self.committee {
            return None;
        }
        let mut rng = super::super::SeedStream::new(b"IVC-TREE-SEEDS-v1", seed);
        let mut shards = Vec::new();
        for run in leaves.chunk_by(|a, b| a.shard_id == b.shard_id) {
            let mut nodes = Vec::with_capacity(run.len());
            for l in run {
                let mut signer_bitmap = [0u8; IVC_BITMAP_BYTES];
                for signer in l.signers {
                    *signer_bitmap.get_mut(signer.member_index / 8)? |=
                        1 << (signer.member_index % 8);
                }
                let stmt = IvcSubtreeStatement {
                    policy_registry_root: reg.root(),
                    shard_lo: l.shard_id,
                    shard_hi: l.shard_id.checked_add(1)?,
                    total_signers: l.signers.len() as u64,
                    shard_threshold: l.policy.threshold(),
                    signer_bitmap,
                    message_digest,
                };
                let w = Witness::new(reg, &stmt, l)?;
                let mut cs = ConstraintSystem::witness_only();
                leaf::populate(&mut cs, &self.cfg, &stmt, &w);
                let z = cs.finish_assignment(&self.leaf)?;
                let proof = r1cs::prove(
                    &self.cfg,
                    &self.leaf,
                    false,
                    &stmt,
                    Acc::dummy(self.cfg.log_cells),
                    z,
                    &rng.next_bytes32(),
                    #[cfg(feature = "vulkan")]
                    gpu,
                )?;
                nodes.push(Node {
                    stmt,
                    proof,
                    internal: false,
                });
            }
            shards.push(self.reduce(
                nodes,
                &mut rng,
                #[cfg(feature = "vulkan")]
                gpu,
            )?);
        }
        let mut root = self.reduce(
            shards,
            &mut rng,
            #[cfg(feature = "vulkan")]
            gpu,
        )?;
        if !root.internal {
            // The wire carries an internal proof even for a single gossip leaf.
            root = self.fold(
                &root,
                &root,
                &rng.next_bytes32(),
                #[cfg(feature = "vulkan")]
                gpu,
            )?;
        }
        Some((root.stmt, SuccinctIvcProof(root.proof)))
    }

    /// Verify a completed shard or interval for acceptance by the application.
    pub fn verify(&self, stmt: &IvcSubtreeStatement, p: &SuccinctIvcProof) -> bool {
        stmt.complete() && self.verify_partial(stmt, p)
    }

    /// Verify a gossip proof, including a single shard still collecting signatures.
    pub fn verify_partial(&self, stmt: &IvcSubtreeStatement, p: &SuccinctIvcProof) -> bool {
        stmt.consistent(self.committee.depth)
            && self.child_claims(true, stmt, &p.0).is_some_and(|claims| {
                claims
                    .iter()
                    .all(|c| matrix::evaluate(self.shapes(), self.cfg.log_cells, &c.native()))
            })
    }
}

pub(super) fn profile() -> IvcStepConfig {
    IvcStepConfig::dkt26(23).unwrap()
}

/// Canonical `[DKT26]` `< 2^{-128}` QROM recursive IVC root proof (`QSAGIVC1\x00`, `639,673` bytes).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SuccinctIvcProof(pub(super) Argument);

/// A binary step over previously serialized internal proofs. The child
/// statements and proofs are prover inputs; the result is independently verifiable.
pub struct SuccinctIvcStep<'a> {
    pub children: [(&'a IvcSubtreeStatement, &'a SuccinctIvcProof); 2],
}

impl SuccinctIvcStep<'_> {
    pub fn prove(
        &self,
        relation: &IvcTreeStepRelation,
        seed: &[u8; 32],
    ) -> Option<(IvcSubtreeStatement, SuccinctIvcProof)> {
        let [(s, l), (t, r)] = self.children;
        let node = relation.fold_children(
            [(s, &l.0, true), (t, &r.0, true)],
            seed,
            #[cfg(feature = "vulkan")]
            None,
        )?;
        Some((node.stmt, SuccinctIvcProof(node.proof)))
    }
}

/// Prove the ordered shards under one registry and application-message digest.
/// Supply fresh private seed material for each independently generated tree.
pub fn prove_ivc_tree(
    registry: &IvcPolicyRegistry,
    message_digest: [u8; 32],
    shards: &[IvcShard<'_>],
    seed: &[u8; 32],
) -> Option<(IvcSubtreeStatement, SuccinctIvcProof)> {
    IvcTreeStepRelation::new()?.prove(registry, message_digest, shards, seed)
}

/// Verify a canonical `[DKT26]` `< 2^{-128}` QROM recursive IVC root proof.
pub fn verify_ivc_tree(stmt: &IvcSubtreeStatement, proof: &SuccinctIvcProof) -> bool {
    stmt.complete()
        && stmt.consistent(leaf::COMMITTEE.depth)
        && IvcTreeStepRelation::new().is_some_and(|rel| rel.verify(stmt, proof))
}
