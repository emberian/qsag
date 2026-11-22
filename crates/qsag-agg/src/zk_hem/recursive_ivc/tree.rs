//! The recursive step has one circuit at every internal depth. The mode is a
//! Boolean witness selecting the fixed signature or step matrices. Both child
//! arguments are replayed before the new public matrix claim is derived.
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
    let c = children.each_ref().map(|s| {
        let w = s.public_inputs().map(|x| b.alloc(x));
        for v in &w {
            bits(b, v, 32);
        }
        let lo = s.shard_lo;
        let hi = s.shard_hi;
        let gap = hi.saturating_sub(lo).saturating_sub(1);
        let g = [gap as u32, (gap >> 32) as u32].map(|k| b.alloc(f(k as u64)));
        for x in &g {
            bits(b, x, 32);
        }
        add64(b, &w[8..10], &g, &w[10..12], true);
        for i in (0..8).chain(14..22) {
            b.equal(&w[i], &public[i]);
        }
        w.to_vec()
    });
    for i in 0..2 {
        b.equal(&c[0][10 + i], &c[1][8 + i]);
        b.equal(&c[0][8 + i], &public[8 + i]);
        b.equal(&c[1][10 + i], &public[10 + i]);
    }
    add64(b, &c[0][12..14], &c[1][12..14], &public[12..14], false);
    c
}
impl IvcSubtreeStatement {
    fn blank() -> Self {
        Self {
            policy_registry_root: [0; 32],
            shard_lo: 0,
            shard_hi: 1,
            total_quorums: 0,
            message_digest: [0; 32],
        }
    }
    fn merge(l: &Self, r: &Self) -> Option<Self> {
        if l.shard_hi != r.shard_lo
            || l.policy_registry_root != r.policy_registry_root
            || l.message_digest != r.message_digest
        {
            return None;
        }
        Some(Self {
            policy_registry_root: l.policy_registry_root,
            message_digest: l.message_digest,
            shard_lo: l.shard_lo,
            shard_hi: r.shard_hi,
            total_quorums: l.total_quorums.checked_add(r.total_quorums)?,
        })
    }
}
struct Step<'a> {
    mode: bool,
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
    for x in &public[..22] {
        bits(b, x, 32);
    }
    let mode = b.alloc(f(w.mode as u64));
    b.product(
        &mode,
        &B::W::constant(F::ONE).minus(&mode),
        &B::W::constant(F::ZERO),
    );
    let children = split(b, public, &w.stmts);
    let mut claims = Vec::new();
    for (stmt, arg) in children.iter().zip(w.children) {
        let (old, new) = r1cs::verify(b, cfg, sboxes, &mode, stmt, arg);
        claims.extend([old, new]);
    }
    let out = matrix::check(b, &claims, &w.rounds, w.answer).digest(b);
    for (v, x) in out.iter().zip(&public[22..]) {
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
        mode: true,
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
        circuit(&mut b, self, [0; 2], &[F::ZERO; 29], &w);
        IvcRowCensus {
            permutations: b.permutations,
            sbox_rows: b.permutations * 236,
            multiplication_rows: b.products,
            witness_variables: b.allocated,
        }
    }
}
pub struct IvcTreeStepRelation<const DIAGNOSTIC: bool = false> {
    cfg: IvcStepConfig,
    leaf: Arc<Shape>,
    step: Arc<Shape>,
}
impl<const D: bool> IvcTreeStepRelation<D> {
    pub fn new() -> Option<Self> {
        let cfg = profile::<D>();
        #[cfg(feature = "std")]
        let (leaf, step) = {
            type Keys = std::sync::OnceLock<Option<(Arc<Shape>, Arc<Shape>)>>;
            static DIAGNOSTIC: Keys = Keys::new();
            static PRODUCTION: Keys = Keys::new();
            (if D { &DIAGNOSTIC } else { &PRODUCTION })
                .get_or_init(|| Self::compile(&cfg))
                .clone()?
        };
        #[cfg(not(feature = "std"))]
        let (leaf, step) = Self::compile(&cfg)?;
        Some(Self { cfg, leaf, step })
    }
    fn compile(cfg: &IvcStepConfig) -> Option<(Arc<Shape>, Arc<Shape>)> {
        let mut cs = ConstraintSystem::new();
        leaf::populate(
            &mut cs,
            &cfg,
            &IvcSubtreeStatement::blank(),
            &Witness::blank(),
        );
        let (leaf, _) = cs.finish();
        let census = cfg.row_census();
        let n = 1 << cfg.log_cells;
        if census.total_rows() + 12 > n || leaf.num_vars > n || leaf.num_rows() > n {
            return None;
        }
        let mut cs = ConstraintSystem::new();
        let pub_wires: Vec<_> = (0..29).map(|_| cs.public_input(F::ZERO).into()).collect();
        let arg = Argument::blank(&cfg);
        circuit(
            &mut cs,
            &cfg,
            [leaf.num_sbox, census.sbox_rows],
            &pub_wires,
            &skeleton(&cfg, &arg),
        );
        if cs.num_rows() != census.total_rows() {
            return None;
        }
        let (step, _) = cs.finish();
        if step.num_sbox != census.sbox_rows
            || step.num_vars != 1 + 29 + census.witness_variables + 12
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
        mode: bool,
        s: &IvcSubtreeStatement,
        l: &Argument,
        t: &IvcSubtreeStatement,
        r: &Argument,
        seed: &[u8; 32],
    ) -> Option<(IvcSubtreeStatement, Argument)> {
        let stmt = IvcSubtreeStatement::merge(s, t)?;
        let [a, b] = self.child_claims(mode, s, l)?;
        let [c, d] = self.child_claims(mode, t, r)?;
        let (rounds, acc) = matrix::prove(self.shapes(), self.cfg.log_cells, &[a, b, c, d]);
        let w = Step {
            mode,
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
        let p = r1cs::prove(&self.cfg, &self.step, true, &stmt, acc, z, seed)?;
        Some((stmt, p))
    }
    pub fn prove(
        &self,
        reg: &IvcPolicyRegistry,
        message_digest: [u8; 32],
        leaves: &[IvcShard<'_>],
        seed: &[u8; 32],
    ) -> Option<(IvcSubtreeStatement, SuccinctIvcProof<D>)> {
        if leaves.len() < 2 || !leaves.len().is_power_of_two() {
            return None;
        }
        let mut rng = super::super::SeedStream::new(b"IVC-TREE-SEEDS-v1", seed);
        let mut nodes = Vec::new();
        for l in leaves {
            let stmt = IvcSubtreeStatement {
                policy_registry_root: reg.root(),
                shard_lo: l.shard_id,
                shard_hi: l.shard_id.checked_add(1)?,
                total_quorums: l.signers.len() as u64,
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
            )?;
            nodes.push((stmt, proof));
        }
        let mut mode = false;
        while nodes.len() > 1 {
            let mut parents = Vec::with_capacity(nodes.len() / 2);
            for pair in nodes.chunks_exact(2) {
                let (s, l) = &pair[0];
                let (t, r) = &pair[1];
                parents.push(self.fold(mode, s, l, t, r, &rng.next_bytes32())?);
            }
            mode = true;
            nodes = parents;
        }
        let (s, p) = nodes.pop()?;
        Some((s, SuccinctIvcProof(p)))
    }
    pub fn verify(&self, stmt: &IvcSubtreeStatement, p: &SuccinctIvcProof<D>) -> bool {
        self.child_claims(true, stmt, &p.0).is_some_and(|claims| {
            claims
                .iter()
                .all(|c| matrix::evaluate(self.shapes(), self.cfg.log_cells, &c.native()))
        })
    }
}
pub(super) fn profile<const D: bool>() -> IvcStepConfig {
    if D {
        IvcStepConfig::diagnostic(19).unwrap()
    } else {
        IvcStepConfig::dkt26(23).unwrap()
    }
}
/// Profile selection is a verifier-chosen Rust type parameter. A production
/// decoder accepts only the production wire tag.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SuccinctIvcProof<const DIAGNOSTIC: bool = false>(pub(super) Argument);
/// A binary step over previously serialized internal proofs. The child
/// statements and proofs are prover inputs; the result is independently verifiable.
pub struct SuccinctIvcStep<'a, const D: bool = false> {
    pub children: [(&'a IvcSubtreeStatement, &'a SuccinctIvcProof<D>); 2],
}
impl<const D: bool> SuccinctIvcStep<'_, D> {
    pub fn prove(
        &self,
        relation: &IvcTreeStepRelation<D>,
        seed: &[u8; 32],
    ) -> Option<(IvcSubtreeStatement, SuccinctIvcProof<D>)> {
        let [(s, l), (t, r)] = self.children;
        let (stmt, p) = relation.fold(true, s, &l.0, t, &r.0, seed)?;
        Some((stmt, SuccinctIvcProof(p)))
    }
}
/// Prove the ordered shards under one registry and application-message digest.
/// Supply fresh private seed material for each independently generated tree.
pub fn prove_ivc_tree<const D: bool>(
    registry: &IvcPolicyRegistry,
    message_digest: [u8; 32],
    shards: &[IvcShard<'_>],
    seed: &[u8; 32],
) -> Option<(IvcSubtreeStatement, SuccinctIvcProof<D>)> {
    IvcTreeStepRelation::<D>::new()?.prove(registry, message_digest, shards, seed)
}
/// Verify a root with locally selected parameters. Callers accepting the DKT26
/// profile decode as `SuccinctIvcProof<false>` (the default).
pub fn verify_ivc_tree<const D: bool>(
    stmt: &IvcSubtreeStatement,
    proof: &SuccinctIvcProof<D>,
) -> bool {
    IvcTreeStepRelation::<D>::new().is_some_and(|rel| rel.verify(stmt, proof))
}
