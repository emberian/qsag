//! Split subtree recursion with an explicit deferred-PCS ledger.
//!
//! Internal circuits check the entire algebraic IOP and roster transition. They commit
//! to the exact remaining PCS claims and to both children's ledgers. Acceptance requires
//! a root proof AND every deferred WHIR opening. This contracts the circuit, but the
//! ledger and verifier work grow with the number of edges; it is not a succinct PCS
//! accumulator or a DuetFold implementation. Keep this cost visible in callers.

use super::*;
use crate::zk_hem::protocol::{
    DeferredPcsClaim, HologramPublicProof, RecursivePublicHemProof, ShapeHologram,
    ShapeVerifierKey, prove_public_for_recursion, prove_public_hologram,
    verify_public_algebraic_gadget, verify_public_hologram,
};
use crate::zk_hem::recursive_whir::{
    Assignment, Backend, Base, Correlated3WhirProof, Native, Transcript, bits,
};
use crate::zk_hem::relation::{ConstraintSystem, Lc, Shape};
use alloc::collections::BTreeSet;

type F = Goldilocks;
const PUBLIC_WORDS: usize = SUBTREE_PUBLIC_WORDS + 4;
const EMPTY: [F; 4] = [F::ZERO; 4];
const LEDGER_TAG: u64 = 0x5350_4C54_0001;

#[derive(Clone)]
struct Edge {
    claim: DeferredPcsClaim<F>,
    opening: Correlated3WhirProof,
    prior: [F; 4],
}

#[derive(Clone)]
struct LedgerNode {
    edges: [Edge; 2],
}

type ClaimAndPrior<W> = ([W; 4], [W; 4]);

fn ledger_root<B: Backend>(b: &mut B, edges: &[ClaimAndPrior<B::W>; 2]) -> [B::W; 4] {
    let mut words = Vec::with_capacity(16);
    for (claim, prior) in edges {
        words.extend_from_slice(claim);
        words.extend_from_slice(prior);
    }
    let mut tr = Transcript::new();
    tr.absorb(b, LEDGER_TAG, &words);
    core::array::from_fn(|i| b.pin(tr.state[i].clone()))
}

impl LedgerNode {
    fn root(&self) -> [F; 4] {
        let mut b = Native::default();
        let edges = core::array::from_fn(|i| (self.edges[i].claim.digest(&mut b), self.edges[i].prior));
        ledger_root(&mut b, &edges)
    }
}

/// A recursive proof and all PCS obligations inherited from its descendants.
/// Fields are private so a leaf cannot claim a nonempty, unauthenticated ledger.
#[derive(Clone)]
pub struct SplitSubtreeProof {
    public: SubtreePublic,
    proof: RecursivePublicHemProof,
    ledger: Vec<LedgerNode>,
}

impl SplitSubtreeProof {
    /// Wrap an existing leaf relation proof. Its key must have the original 14 publics.
    /// Cryptographic verification occurs in the parent relation and its PCS decider.
    pub fn leaf(public: SubtreePublic, proof: RecursivePublicHemProof) -> Self {
        Self { public, proof, ledger: Vec::new() }
    }

    pub fn public(&self) -> SubtreePublic { self.public }

    fn accumulator_root(&self) -> [F; 4] {
        self.ledger.last().map_or(EMPTY, LedgerNode::root)
    }
}

/// Binary internal relation; 18 public words at every internal level.
/// Its children are either 14-word leaves or 18-word split internal nodes, as fixed by
/// the trusted child verification key. The root verifier must also check the ledger.
pub struct SplitSubtreeRelation {
    child_vk: ShapeVerifierKey,
    base_merkle_level: usize,
    shared_roster_root: bool,
    shape: Shape,
    hologram: ShapeHologram,
    stats: FullShardRelationStats,
}

impl SplitSubtreeRelation {
    pub fn new(
        child_vk: ShapeVerifierKey,
        base_merkle_level: usize,
        shared_roster_root: bool,
        regime: WhirSecurityRegime,
    ) -> Result<Self, FullShardError> {
        if !matches!(child_vk.num_public, SUBTREE_PUBLIC_WORDS | PUBLIC_WORDS)
            || base_merkle_level > 57
            || !child_vk.regime.uses_poseidon2_canopy()
            || !regime.meets_qrom_128_floor()
        { return Err(FullShardError::InvalidParameters); }
        let placeholder = RecursivePublicHemProof::placeholder(&child_vk)
            .ok_or(FullShardError::InvalidParameters)?;
        let dummy = SubtreePublic {
            subtree_registry_root: EMPTY, epoch_floor: F::ZERO,
            message_digest: [F::ZERO; 5], total_active_signers: F::ONE,
            min_key_idx: 0, max_key_idx: 0, total_active_weight: 1,
        };
        let children = [(dummy, &placeholder, EMPTY), (dummy, &placeholder, EMPTY)];
        let mut cs = ConstraintSystem::new_hologram_aligned();
        let public: Vec<Lc> = (0..PUBLIC_WORDS).map(|_| cs.public_input(F::ZERO).into()).collect();
        merge_gadget(&mut cs, &child_vk, base_merkle_level, shared_roster_root, &public, &children);
        let used = cs.num_rows();
        let (shape, mut z) = cs.finish();
        qsag_asm::volatile_fill(&mut z, F::ZERO);
        let stats = FullShardRelationStats {
            sbox_rows: shape.num_sbox, multiplication_rows: used - shape.num_sbox,
            padded_rows: shape.num_rows(), variables: shape.num_vars,
        };
        // Enforce the intended ceiling as an API invariant, not just a benchmark claim.
        if stats.padded_rows > (1 << 20) { return Err(FullShardError::InvalidParameters); }
        let hologram = ShapeHologram::compile(&shape, regime)
            .map_err(|_| FullShardError::InvalidParameters)?;
        Ok(Self { child_vk, base_merkle_level, shared_roster_root, shape, hologram, stats })
    }

    pub fn verifier_key(&self) -> &ShapeVerifierKey { self.hologram.verifier_key() }
    pub fn stats(&self) -> FullShardRelationStats { self.stats }

    fn assignment(&self, children: &[SplitSubtreeProof; 2]) -> Result<(SubtreePublic, Vec<LedgerNode>, Vec<F>), FullShardError> {
        let [left, right] = children;
        let lp = left.public;
        let rp = right.public;
        if lp.epoch_floor != rp.epoch_floor || lp.message_digest != rp.message_digest
            || lp.max_key_idx >= rp.min_key_idx
        { return Err(FullShardError::InvalidStatement); }
        for c in children {
            if !c.proof.well_formed(&self.child_vk)
                || (self.child_vk.num_public == SUBTREE_PUBLIC_WORDS && !c.ledger.is_empty())
                || (self.child_vk.num_public == PUBLIC_WORDS && c.ledger.is_empty())
                || c.public.min_key_idx > c.public.max_key_idx
                || c.public.max_key_idx >= (1 << 58)
                || c.public.total_active_signers.to_canonical_u64() == 0
                || c.public.total_active_signers.to_canonical_u64() >= (1 << 62)
                || c.public.total_active_weight == 0 || c.public.total_active_weight >= (1 << 62)
            { return Err(FullShardError::InvalidChild); }
        }
        let total = lp.total_active_signers.to_canonical_u64()
            .checked_add(rp.total_active_signers.to_canonical_u64())
            .filter(|&n| n < (1 << 62)).ok_or(FullShardError::InvalidStatement)?;
        let weight = lp.total_active_weight.checked_add(rp.total_active_weight)
            .filter(|&n| n < (1 << 62)).ok_or(FullShardError::InvalidStatement)?;
        let mut b = Native::default();
        let roots = [lp.subtree_registry_root, rp.subtree_registry_root];
        let root = if self.shared_roster_root {
            if roots[0] != roots[1] { return Err(FullShardError::InvalidStatement); }
            roots[0]
        } else { subtree_fold_merkle_gadget(&mut b, self.base_merkle_level, &roots) };
        let public = SubtreePublic {
            subtree_registry_root: root, epoch_floor: lp.epoch_floor, message_digest: lp.message_digest,
            total_active_signers: F::from_u64_reduced(total), min_key_idx: lp.min_key_idx,
            max_key_idx: rp.max_key_idx, total_active_weight: weight,
        };
        let mut edges = Vec::with_capacity(2);
        for c in children {
            let mut words = c.public.words().to_vec();
            let prior = c.accumulator_root();
            if self.child_vk.num_public == PUBLIC_WORDS { words.extend(prior); }
            let claim = verify_public_algebraic_gadget(&mut b, &self.child_vk, SUBTREE_REC_TAG, &words, &c.proof);
            if b.failed { return Err(FullShardError::InvalidChild); }
            edges.push(Edge { claim, opening: c.proof.opening.clone(), prior });
        }
        let node = LedgerNode { edges: edges.try_into().map_err(|_| FullShardError::InvalidChild)? };
        let mut pub_words = public.words().to_vec();
        pub_words.extend(node.root());
        let refs = core::array::from_fn(|i| (children[i].public, &children[i].proof, children[i].accumulator_root()));
        let mut a = Assignment::hologram_aligned();
        merge_gadget(&mut a, &self.child_vk, self.base_merkle_level, self.shared_roster_root, &pub_words, &refs);
        let mut z = vec![F::ONE];
        z.extend_from_slice(&pub_words);
        z.resize(128 * self.shape.hologram_meta().pub_var_blocks, F::ZERO);
        z.extend_from_slice(&a.p2_values);
        z.extend_from_slice(&a.values);
        if z.len() != self.shape.mask_var_base { return Err(FullShardError::InvalidParameters); }
        z.resize(self.shape.num_vars, F::ZERO);
        let mut ledger = left.ledger.clone();
        ledger.extend(right.ledger.clone());
        ledger.push(node);
        Ok((public, ledger, z))
    }

    pub fn prove_for_recursion(&self, children: &[SplitSubtreeProof; 2]) -> Result<SplitSubtreeProof, FullShardError> {
        let (public, ledger, z) = self.assignment(children)?;
        let proof = prove_public_for_recursion(&self.shape, &self.hologram, z, SUBTREE_REC_TAG)
            .map_err(|_| FullShardError::InvalidChild)?;
        Ok(SplitSubtreeProof { public, proof, ledger })
    }

    pub fn prove_root(&self, children: &[SplitSubtreeProof; 2], seed: &[u8; 32]) -> Result<SplitSubtreeAggregate, FullShardError> {
        let (public, ledger, z) = self.assignment(children)?;
        let proof = prove_public_hologram(&self.shape, &self.hologram, z, SUBTREE_ROOT_LABEL, seed)
            .map_err(|_| FullShardError::InvalidChild)?;
        Ok(SplitSubtreeAggregate { public, proof, ledger })
    }
}

fn merge_gadget<B: Backend>(
    b: &mut B, vk: &ShapeVerifierKey, level: usize, shared: bool, parent: &[B::W],
    children: &[(SubtreePublic, &RecursivePublicHemProof, [F; 4]); 2],
) {
    let mut roots = Vec::new();
    let mut counts = Vec::new();
    let mut weights = Vec::new();
    let mut mins = Vec::new();
    let mut maxs = Vec::new();
    let mut edges = Vec::new();
    for (cp, proof, prior) in children {
        let root: [B::W; 4] = cp.subtree_registry_root.map(|v| b.alloc(v));
        let count = b.alloc(cp.total_active_signers);
        let weight = b.alloc(F::from_u64_reduced(cp.total_active_weight));
        bits(b, &count, 62);
        bits(b, &weight, 62);
        // Strict positivity, without field wrap at zero.
        bits(b, &count.minus(&B::W::constant(F::ONE)), 62);
        bits(b, &weight.minus(&B::W::constant(F::ONE)), 62);
        let min = b.alloc(F::from_u64_reduced(cp.min_key_idx));
        let max = b.alloc(F::from_u64_reduced(cp.max_key_idx));
        let mut pub_words = root.to_vec();
        pub_words.extend_from_slice(&parent[4..10]);
        pub_words.extend([count.clone(), min.clone(), max.clone(), weight.clone()]);
        let prior = if vk.num_public == PUBLIC_WORDS {
            let words = prior.map(|v| b.alloc(v));
            pub_words.extend_from_slice(&words);
            words
        } else { core::array::from_fn(|_| B::W::constant(F::ZERO)) };
        let claim = verify_public_algebraic_gadget(b, vk, SUBTREE_REC_TAG, &pub_words, proof);
        edges.push((claim.digest(b), prior));
        roots.push(root); counts.push(count); weights.push(weight); mins.push(min); maxs.push(max);
    }
    let root = if shared {
        for r in &roots { for i in 0..4 { b.equal(&r[i], &parent[i]); } }
        roots[0].clone()
    } else { subtree_fold_merkle_gadget(b, level, &roots) };
    for i in 0..4 { b.equal(&root[i], &parent[i]); }
    for (terms, want) in [(&counts, &parent[10]), (&weights, &parent[13])] {
        let sum = terms[0].plus(&terms[1]);
        bits(b, &sum, 62); b.equal(&sum, want);
    }
    enforce_subtree_intervals(b, &mins, &maxs, &parent[11], &parent[12]);
    let edges = [edges[0].clone(), edges[1].clone()];
    let accumulator = ledger_root(b, &edges);
    for i in 0..4 { b.equal(&accumulator[i], &parent[SUBTREE_PUBLIC_WORDS + i]); }
}

/// One constant-depth root SNARK plus a linear-size deferred PCS ledger.
#[derive(Clone)]
pub struct SplitSubtreeAggregate {
    public: SubtreePublic,
    proof: HologramPublicProof,
    ledger: Vec<LedgerNode>,
}

impl SplitSubtreeAggregate {
    pub fn public(&self) -> SubtreePublic { self.public }
    pub fn deferred_openings(&self) -> usize { self.ledger.len() * 2 }

    /// Verify all deferred edges, rejecting omissions, duplicates, reordering across
    /// dependencies and orphan nodes. Every nonempty prior root is consumed exactly once.
    fn verify_ledger(&self) -> bool {
        let mut pending = BTreeSet::new();
        for node in &self.ledger {
            for edge in &node.edges {
                if edge.prior != EMPTY && !pending.remove(&edge.prior.map(|v| v.to_canonical_u64())) { return false; }
                if !edge.claim.verify(&edge.opening) { return false; }
            }
            if !pending.insert(node.root().map(|v| v.to_canonical_u64())) { return false; }
        }
        pending.len() == 1
    }

    pub fn verify_against_roster_root(&self, vk: &ShapeVerifierKey, statement: &RosterRootStatement<'_>) -> bool {
        let p = self.public;
        if vk.num_public != PUBLIC_WORDS || self.ledger.is_empty()
            || statement.minimum_global_quorums == 0
            || statement.epoch_floor >= crate::field::GOLDILOCKS_PRIME
            || p.epoch_floor.to_canonical_u64() != statement.epoch_floor
            || p.message_digest != subtree_message_digest(statement.message)
            || p.total_active_signers.to_canonical_u64() < statement.minimum_global_quorums
            || p.total_active_signers.to_canonical_u64() >= (1 << 62)
            || p.total_active_weight < statement.minimum_active_weight
            || p.total_active_weight == 0 || p.total_active_weight >= (1 << 62)
            || p.min_key_idx != statement.min_key_idx || p.max_key_idx != statement.max_key_idx
            || p.min_key_idx > p.max_key_idx || p.max_key_idx >= (1 << 58)
        { return false; }
        for (i, r) in p.subtree_registry_root.iter().enumerate() {
            if r.to_le_bytes() != statement.roster_root[i * 8..i * 8 + 8] { return false; }
        }
        let mut words = p.words().to_vec();
        words.extend(self.ledger.last().unwrap().root());
        verify_public_hologram(vk, &words, SUBTREE_ROOT_LABEL, &self.proof) && self.verify_ledger()
    }
}

impl SplitSubtreeAggregate {
    /// Encode the proof and complete ledger. This experimental carrier has no stable
    /// wire compatibility promise; the length includes every deferred opening.
    pub fn to_bytes(&self) -> Vec<u8> {
        fn fields(out: &mut Vec<u8>, words: impl IntoIterator<Item = F>) {
            for word in words { out.extend_from_slice(&word.to_le_bytes()); }
        }
        fn exts(out: &mut Vec<u8>, words: impl IntoIterator<Item = GoldilocksExt4>) {
            for word in words { fields(out, word.to_limbs()); }
        }
        fn len(out: &mut Vec<u8>, n: usize) { out.extend_from_slice(&(n as u64).to_le_bytes()); }
        fn queries(out: &mut Vec<u8>, qs: &[crate::zk_hem::recursive_whir::FixedPathQuery]) {
            len(out, qs.len());
            for q in qs {
                len(out, q.values.len()); exts(out, q.values.iter().copied());
                len(out, q.siblings.len()); fields(out, q.siblings.iter().flatten().copied());
            }
        }
        let mut out = b"QSAGSPD1".to_vec();
        fields(&mut out, self.public.words());
        let root = self.proof.to_bytes();
        len(&mut out, root.len()); out.extend(root);
        len(&mut out, self.ledger.len());
        for node in &self.ledger {
            for edge in &node.edges {
                let c = &edge.claim;
                out.push(c.regime as u8); len(&mut out, c.num_vars);
                fields(&mut out, c.transcript);
                fields(&mut out, c.roots.iter().flatten().copied());
                for point in &c.points {
                    len(&mut out, point.len());
                    fields(&mut out, point.iter().flat_map(|e| e.0));
                }
                for claim in c.claims.iter().flatten() {
                    out.push(u8::from(claim.is_some()));
                    if let Some(e) = claim { fields(&mut out, e.0); }
                }
                fields(&mut out, edge.prior);
                let p = &edge.opening;
                exts(&mut out, p.cross_evals.iter().flatten().copied());
                for leaves in &p.stage0_canopy_leaves {
                    len(&mut out, leaves.len()); fields(&mut out, leaves.iter().flatten().copied());
                }
                len(&mut out, p.stage0_queries.len());
                for triple in &p.stage0_queries { queries(&mut out, triple); }
                len(&mut out, p.later_stage_roots.len());
                fields(&mut out, p.later_stage_roots.iter().flatten().copied());
                len(&mut out, p.later_canopy_leaves.len());
                for leaves in &p.later_canopy_leaves {
                    len(&mut out, leaves.len()); fields(&mut out, leaves.iter().flatten().copied());
                }
                len(&mut out, p.ood_evals.len()); exts(&mut out, p.ood_evals.iter().flatten().copied());
                len(&mut out, p.fold_polys.len()); exts(&mut out, p.fold_polys.iter().flatten().copied());
                for nonces in [&p.fold_nonces, &p.query_nonces] {
                    len(&mut out, nonces.len());
                    for n in nonces.iter().flatten() { out.extend_from_slice(&n.to_le_bytes()); }
                }
                len(&mut out, p.later_queries.len());
                for qs in &p.later_queries { queries(&mut out, qs); }
                len(&mut out, p.final_coeffs.len()); exts(&mut out, p.final_coeffs.iter().copied());
            }
        }
        out
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use std::time::Instant;
    use crate::ValidatorKeypair;

    #[test]
    fn split_depth_two_real_signatures_and_deferred_tampering() { real_tree(2); }

    #[test]
    fn split_depth_three_real_signatures_and_deferred_tampering() { real_tree(3); }

    fn real_tree(depth: usize) {
        let _permit = crate::prover_admission::acquire();
        let regime = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128;
        let params = FullShardParams::new(regime, 2).unwrap();
        let count = 1 << (depth - 1);
        let epoch = 2026_1116;
        let message = b"split-subtree real signature test";
        let keys: Vec<Vec<ValidatorKeypair>> = (0..count).map(|s| {
            (0..2).map(|i| ValidatorKeypair::keygen_deterministic(
                AggSigProfile::JortsPoseidon2, &[(90 + s) as u8; 32], i,
            )).collect()
        }).collect();
        let policies: Vec<_> = keys.iter().enumerate().map(|(s, k)| ShardHemPolicy {
            shard_id: 100 + s as u64, custodian_cluster: [(120 + s) as u8; 32],
            quorum_keys: k.iter().map(|k| k.pk).collect(), minimum_quorums: 1,
        }).collect();
        let roster = PreparedSubtreeRegistry::new(&params, &policies).unwrap().roster_root;
        let start = Instant::now();
        let leaf = SubtreeLeafMergeRelation::new(params, 1).unwrap();
        let mut vk = leaf.verifier_key().clone();
        std::println!("SPLIT depth={depth} leaf_rows={} setup_ms={:.1}", leaf.stats().padded_rows, start.elapsed().as_secs_f64() * 1000.0);
        let mut children = Vec::new();
        for s in 0..count {
            let sign_msg = subtree_signing_message(leaf.params(), &policies[s], epoch, message).unwrap();
            let sigs = vec![keys[s][0].sign_stateful_for_unit_test(&sign_msg, s as u32).unwrap()];
            let bitmap = SignerBitmap::from_active_indices(2, &[0]).unwrap();
            let witness = ShardHemWitness { bitmap: &bitmap, signatures: &sigs };
            let t = Instant::now();
            let (public, proof) = prove_subtree_leaf_merge_for_recursion(
                &leaf, core::slice::from_ref(&policies[s]), epoch, message,
                &[witness], &[(s + 1) as u8; 32],
            ).unwrap();
            std::println!("SPLIT depth={depth} leaf={s} prove_ms={:.1}", t.elapsed().as_secs_f64() * 1000.0);
            children.push(SplitSubtreeProof::leaf(public, proof));
        }
        drop(leaf);
        for level in 2..=depth {
            let t = Instant::now();
            let relation = SplitSubtreeRelation::new(vk, level - 2, false,
                if level == depth { WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128 } else { regime }
            ).unwrap();
            std::println!("SPLIT depth={depth} level={level} rows={} setup_ms={:.1}", relation.stats().padded_rows, t.elapsed().as_secs_f64() * 1000.0);
            assert!(relation.stats().padded_rows <= 1 << 20);
            if level < depth {
                let t = Instant::now();
                let mut next = Vec::new();
                for pair in children.chunks_exact(2) {
                    next.push(relation.prove_for_recursion(&[pair[0].clone(), pair[1].clone()]).unwrap());
                }
                std::println!("SPLIT depth={depth} level={level} prove_ms={:.1}", t.elapsed().as_secs_f64() * 1000.0);
                children = next;
                vk = relation.verifier_key().clone();
                continue;
            }
            let t = Instant::now();
            let aggregate = relation.prove_root(&[children[0].clone(), children[1].clone()], &[72; 32]).unwrap();
            let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
            let statement = RosterRootStatement {
                roster_root: roster, epoch_floor: epoch, message, minimum_global_quorums: count as u64,
                minimum_active_weight: count as u64, min_key_idx: 100, max_key_idx: 100 + count as u64 - 1,
            };
            let t = Instant::now();
            assert!(aggregate.verify_against_roster_root(relation.verifier_key(), &statement));
            std::println!("SPLIT depth={depth} root_prove_ms={prove_ms:.1} root_bytes={} total_bytes={} openings={} verify_ms={:.2} total_ms={:.1}",
                aggregate.proof.to_bytes().len(), aggregate.to_bytes().len(), aggregate.deferred_openings(),
                t.elapsed().as_secs_f64() * 1000.0, start.elapsed().as_secs_f64() * 1000.0);
            for node in 0..aggregate.ledger.len() {
                for edge in 0..2 {
                    let mut bad = aggregate.clone();
                    bad.ledger[node].edges[edge].opening.stage0_queries[0][0].values[0] += GoldilocksExt4::ONE;
                    assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
                    let mut bad = aggregate.clone();
                    bad.ledger[node].edges[edge].claim.transcript[0] += F::ONE;
                    assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
                }
            }
            let mut bad = aggregate.clone();
            bad.ledger.remove(0);
            assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
            let mut bad = aggregate.clone();
            bad.public.total_active_weight += 1;
            assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
            let mut bad = aggregate.clone();
            bad.proof.m_sparse_claim += GoldilocksExt4::ONE;
            assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
            break;
        }
    }
}
