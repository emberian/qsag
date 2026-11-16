//! Split subtree recursion with a succinct `[CWYZ26]` homogeneous-level folded PCS accumulator.
//!
//! Internal circuits verify every child's algebraic Spark/LogUp-GKR hologram IOP and roster
//! transition in `<= 2^20` rows, binding each child's `DeferredPcsClaim` digest and prior
//! accumulator root into `accumulator_root`. At the root, `prove_root` folds all `M_l`
//! homogeneous deferred PCS claims at each tree level `l in 0..depth-1` via a `[CWYZ26]`
//! multilinear point-reduction sumcheck + correlated codeword combination into **at most one
//! `FoldedLevelWhirProof` per tree level (`O(depth)` WHIR cascades instead of `O(N)` cascades)**,
//! authenticated against every committed child Merkle root via Steiner-deduplicated multi-proofs.
//! The cascade count is logarithmic in the leaf count; total proof bytes are not. The claim
//! ledger and authenticated Stage-0 fibers still grow with the number of child commitments.

mod codec;

use super::*;
use crate::zk_hem::protocol::{
    DeferredPcsClaim, HologramPublicProof, RecursivePublicHemProof, ShapeHologram,
    ShapeVerifierKey, SplitDeferredWitness, prove_folded_level_from_split, prove_public_for_split,
    prove_public_hologram, verify_folded_level_claims, verify_public_algebraic_gadget,
    verify_public_hologram,
};
use crate::zk_hem::recursive_whir::{
    Assignment, Backend, Base, FoldedLevelWhirProof, Native, Transcript, bits,
};
use crate::zk_hem::relation::{ConstraintSystem, Lc, Shape};
use alloc::collections::BTreeMap;
use alloc::sync::Arc;

type F = Goldilocks;
const PUBLIC_WORDS: usize = SUBTREE_PUBLIC_WORDS + 4;
const EMPTY: [F; 4] = [F::ZERO; 4];
const LEDGER_TAG: u64 = 0x5350_4C54_0001;

#[derive(Clone)]
struct Edge {
    claim: DeferredPcsClaim<F>,
    prior: [F; 4],
    witness: Option<Arc<SplitDeferredWitness>>,
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
        let edges =
            core::array::from_fn(|i| (self.edges[i].claim.digest(&mut b), self.edges[i].prior));
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
    /// Cryptographic verification occurs in the parent relation and its level PCS decider.
    pub fn leaf(public: SubtreePublic, proof: RecursivePublicHemProof) -> Self {
        Self {
            public,
            proof,
            ledger: Vec::new(),
        }
    }

    /// Prove a Level-1 subtree leaf directly for split recursion, skipping redundant per-leaf
    /// WHIR cascades that `prove_root` folds per homogeneous tree level.
    pub fn prove_leaf(
        relation: &SubtreeLeafMergeRelation,
        policies: &[ShardHemPolicy],
        epoch_floor: u64,
        message: &[u8],
        witnesses: &[ShardHemWitness<'_>],
        seed: &[u8; 32],
    ) -> Result<Self, FullShardError> {
        let (public, z) =
            relation.build_assignment(policies, epoch_floor, message, witnesses, seed)?;
        let proof = prove_public_for_split(
            &relation.shape,
            &relation.hologram,
            z,
            SUBTREE_REC_TAG,
        )
        .map_err(|_| FullShardError::InvalidChild)?;
        Ok(Self {
            public,
            proof,
            ledger: Vec::new(),
        })
    }

    /// Prove a Level-1 sparse-roster subtree leaf directly for split recursion, skipping
    /// redundant per-leaf WHIR cascades.
    pub fn prove_roster_leaf(
        relation: &SubtreeLeafMergeRelation,
        policies: &[ShardHemPolicy],
        openings: &[SubtreeRosterOpening],
        epoch_floor: u64,
        message: &[u8],
        witnesses: &[ShardHemWitness<'_>],
        seed: &[u8; 32],
    ) -> Result<Self, FullShardError> {
        let (public, z) = relation.build_roster_assignment(
            policies,
            epoch_floor,
            message,
            witnesses,
            seed,
            Some(openings),
        )?;
        let proof = prove_public_for_split(
            &relation.shape,
            &relation.hologram,
            z,
            SUBTREE_REC_TAG,
        )
        .map_err(|_| FullShardError::InvalidChild)?;
        Ok(Self {
            public,
            proof,
            ledger: Vec::new(),
        })
    }

    pub fn public(&self) -> SubtreePublic {
        self.public
    }

    fn accumulator_root(&self) -> [F; 4] {
        self.ledger.last().map_or(EMPTY, LedgerNode::root)
    }
}

/// Binary internal relation; 18 public words at every internal level.
/// Its children are either 14-word leaves or 18-word split internal nodes, as fixed by
/// the trusted child verification key. The root verifier checks both the root SNARK and
/// the succinct per-level folded WHIR openings.
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
        {
            return Err(FullShardError::InvalidParameters);
        }
        let placeholder = RecursivePublicHemProof::placeholder(&child_vk)
            .ok_or(FullShardError::InvalidParameters)?;
        let dummy = SubtreePublic {
            subtree_registry_root: EMPTY,
            epoch_floor: F::ZERO,
            message_digest: [F::ZERO; 5],
            total_active_signers: F::ONE,
            min_key_idx: 0,
            max_key_idx: 0,
            total_active_weight: 1,
        };
        let children = [(dummy, &placeholder, EMPTY), (dummy, &placeholder, EMPTY)];
        let mut cs = ConstraintSystem::new_hologram_aligned();
        let public: Vec<Lc> = (0..PUBLIC_WORDS)
            .map(|_| cs.public_input(F::ZERO).into())
            .collect();
        merge_gadget(
            &mut cs,
            &child_vk,
            base_merkle_level,
            shared_roster_root,
            &public,
            &children,
        );
        let used = cs.num_rows();
        let (shape, mut z) = cs.finish();
        qsag_asm::volatile_fill(&mut z, F::ZERO);
        drop(z);
        let stats = FullShardRelationStats {
            sbox_rows: shape.num_sbox,
            multiplication_rows: used - shape.num_sbox,
            padded_rows: shape.num_rows(),
            variables: shape.num_vars,
        };
        // Enforce the intended ceiling as an API invariant, not just a benchmark claim.
        if stats.padded_rows > (1 << 20) {
            return Err(FullShardError::InvalidParameters);
        }
        let hologram = ShapeHologram::compile(&shape, regime)
            .map_err(|_| FullShardError::InvalidParameters)?;
        Ok(Self {
            child_vk,
            base_merkle_level,
            shared_roster_root,
            shape,
            hologram,
            stats,
        })
    }

    pub fn verifier_key(&self) -> &ShapeVerifierKey {
        self.hologram.verifier_key()
    }
    pub fn stats(&self) -> FullShardRelationStats {
        self.stats
    }

    fn assignment(
        &self,
        children: &[SplitSubtreeProof; 2],
    ) -> Result<(SubtreePublic, Vec<LedgerNode>, Vec<F>), FullShardError> {
        let [left, right] = children;
        let lp = left.public;
        let rp = right.public;
        if lp.epoch_floor != rp.epoch_floor
            || lp.message_digest != rp.message_digest
            || lp.max_key_idx >= rp.min_key_idx
        {
            return Err(FullShardError::InvalidStatement);
        }
        for c in children {
            if !c.proof.well_formed(&self.child_vk)
                || c.proof.split_witness.0.is_none()
                || (self.child_vk.num_public == SUBTREE_PUBLIC_WORDS && !c.ledger.is_empty())
                || (self.child_vk.num_public == PUBLIC_WORDS && c.ledger.is_empty())
                || c.public.min_key_idx > c.public.max_key_idx
                || c.public.max_key_idx >= (1 << 58)
                || c.public.total_active_signers.to_canonical_u64() == 0
                || c.public.total_active_signers.to_canonical_u64() >= (1 << 62)
                || c.public.total_active_weight == 0
                || c.public.total_active_weight >= (1 << 62)
            {
                return Err(FullShardError::InvalidChild);
            }
        }
        let total = lp
            .total_active_signers
            .to_canonical_u64()
            .checked_add(rp.total_active_signers.to_canonical_u64())
            .filter(|&n| n < (1 << 62))
            .ok_or(FullShardError::InvalidStatement)?;
        let weight = lp
            .total_active_weight
            .checked_add(rp.total_active_weight)
            .filter(|&n| n < (1 << 62))
            .ok_or(FullShardError::InvalidStatement)?;
        let mut b = Native::default();
        let roots = [lp.subtree_registry_root, rp.subtree_registry_root];
        let root = if self.shared_roster_root {
            if roots[0] != roots[1] {
                return Err(FullShardError::InvalidStatement);
            }
            roots[0]
        } else {
            subtree_fold_merkle_gadget(&mut b, self.base_merkle_level, &roots)
        };
        let public = SubtreePublic {
            subtree_registry_root: root,
            epoch_floor: lp.epoch_floor,
            message_digest: lp.message_digest,
            total_active_signers: F::from_u64_reduced(total),
            min_key_idx: lp.min_key_idx,
            max_key_idx: rp.max_key_idx,
            total_active_weight: weight,
        };
        let mut edges = Vec::with_capacity(2);
        for c in children {
            let mut words = c.public.words().to_vec();
            let prior = c.accumulator_root();
            if self.child_vk.num_public == PUBLIC_WORDS {
                words.extend(prior);
            }
            let claim = verify_public_algebraic_gadget(
                &mut b,
                &self.child_vk,
                SUBTREE_REC_TAG,
                &words,
                &c.proof,
            );
            if b.failed {
                return Err(FullShardError::InvalidChild);
            }
            edges.push(Edge {
                claim,
                prior,
                witness: c.proof.split_witness.0.clone(),
            });
        }
        let node = LedgerNode {
            edges: edges.try_into().map_err(|_| FullShardError::InvalidChild)?,
        };
        let mut pub_words = public.words().to_vec();
        pub_words.extend(node.root());
        let refs = core::array::from_fn(|i| {
            (
                children[i].public,
                &children[i].proof,
                children[i].accumulator_root(),
            )
        });
        let mut a = Assignment::hologram_aligned();
        merge_gadget(
            &mut a,
            &self.child_vk,
            self.base_merkle_level,
            self.shared_roster_root,
            &pub_words,
            &refs,
        );
        let mut z = vec![F::ONE];
        z.extend_from_slice(&pub_words);
        z.resize(128 * self.shape.hologram_meta().pub_var_blocks, F::ZERO);
        z.extend_from_slice(&a.p2_values);
        z.extend_from_slice(&a.values);
        if z.len() != self.shape.mask_var_base {
            return Err(FullShardError::InvalidParameters);
        }
        z.resize(self.shape.num_vars, F::ZERO);
        let mut ledger = left.ledger.clone();
        ledger.extend(right.ledger.clone());
        ledger.push(node);
        Ok((public, ledger, z))
    }

    pub fn prove_for_recursion(
        &self,
        children: &[SplitSubtreeProof; 2],
    ) -> Result<SplitSubtreeProof, FullShardError> {
        let (public, ledger, z) = self.assignment(children)?;
        let proof = prove_public_for_split(&self.shape, &self.hologram, z, SUBTREE_REC_TAG)
            .map_err(|_| FullShardError::InvalidChild)?;
        Ok(SplitSubtreeProof {
            public,
            proof,
            ledger,
        })
    }

    pub fn prove_root(
        &self,
        children: &[SplitSubtreeProof; 2],
        seed: &[u8; 32],
    ) -> Result<SplitSubtreeAggregate, FullShardError> {
        let (public, mut ledger, z) = self.assignment(children)?;
        let proof = prove_public_hologram(&self.shape, &self.hologram, z, SUBTREE_ROOT_LABEL, seed)
            .map_err(|_| FullShardError::InvalidChild)?;

        let top_root = ledger
            .last()
            .ok_or(FullShardError::InvalidChild)?
            .root();
        let mut pending: BTreeMap<[u64; 4], usize> = BTreeMap::new();
        let mut by_level: Vec<Vec<(&DeferredPcsClaim<F>, &SplitDeferredWitness)>> = Vec::new();
        for node in &ledger {
            let mut edge_levels = [0usize; 2];
            for (slot, edge) in edge_levels.iter_mut().zip(&node.edges) {
                *slot = if edge.prior == EMPTY {
                    0
                } else {
                    pending
                        .remove(&edge.prior.map(|v| v.to_canonical_u64()))
                        .ok_or(FullShardError::InvalidChild)?
                };
            }
            if edge_levels[0] != edge_levels[1] {
                return Err(FullShardError::InvalidChild);
            }
            let level = edge_levels[0];
            if level > by_level.len() {
                return Err(FullShardError::InvalidChild);
            }
            if level == by_level.len() {
                by_level.push(Vec::new());
            }
            for edge in &node.edges {
                let wit = edge
                    .witness
                    .as_deref()
                    .ok_or(FullShardError::InvalidChild)?;
                by_level[level].push((&edge.claim, wit));
            }
            if pending
                .insert(node.root().map(|v| v.to_canonical_u64()), level + 1)
                .is_some()
            {
                return Err(FullShardError::InvalidChild);
            }
        }
        if pending.len() != 1 {
            return Err(FullShardError::InvalidChild);
        }

        let mut level_openings = Vec::with_capacity(by_level.len());
        for (level, items) in by_level.iter().enumerate() {
            let opening = prove_folded_level_from_split(level, top_root, items)
                .map_err(|_| FullShardError::InvalidChild)?;
            level_openings.push(opening);
        }
        drop(by_level);
        for node in &mut ledger {
            for edge in &mut node.edges {
                edge.witness = None;
            }
        }

        Ok(SplitSubtreeAggregate {
            public,
            proof,
            ledger,
            level_openings,
        })
    }
}

fn merge_gadget<B: Backend>(
    b: &mut B,
    vk: &ShapeVerifierKey,
    level: usize,
    shared: bool,
    parent: &[B::W],
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
        } else {
            core::array::from_fn(|_| B::W::constant(F::ZERO))
        };
        let claim = verify_public_algebraic_gadget(b, vk, SUBTREE_REC_TAG, &pub_words, proof);
        edges.push((claim.digest(b), prior));
        roots.push(root);
        counts.push(count);
        weights.push(weight);
        mins.push(min);
        maxs.push(max);
    }
    let root = if shared {
        for r in &roots {
            for i in 0..4 {
                b.equal(&r[i], &parent[i]);
            }
        }
        roots[0].clone()
    } else {
        subtree_fold_merkle_gadget(b, level, &roots)
    };
    for i in 0..4 {
        b.equal(&root[i], &parent[i]);
    }
    for (terms, want) in [(&counts, &parent[10]), (&weights, &parent[13])] {
        let sum = terms[0].plus(&terms[1]);
        bits(b, &sum, 62);
        b.equal(&sum, want);
    }
    enforce_subtree_intervals(b, &mins, &maxs, &parent[11], &parent[12]);
    let edges = [edges[0].clone(), edges[1].clone()];
    let accumulator = ledger_root(b, &edges);
    for i in 0..4 {
        b.equal(&accumulator[i], &parent[SUBTREE_PUBLIC_WORDS + i]);
    }
}

/// One constant-depth root SNARK plus `O(depth)` `[CWYZ26]` per-level folded WHIR openings.
#[derive(Clone)]
pub struct SplitSubtreeAggregate {
    pub(super) public: SubtreePublic,
    pub(super) proof: HologramPublicProof,
    ledger: Vec<LedgerNode>,
    level_openings: Vec<FoldedLevelWhirProof>,
}

impl SplitSubtreeAggregate {
    pub fn public(&self) -> SubtreePublic {
        self.public
    }

    /// Number of WHIR PCS opening cascades carried by this aggregate (`depth - 1`: `1` per
    /// homogeneous tree level below the root!).
    pub fn deferred_openings(&self) -> usize {
        self.level_openings.len()
    }

    /// Verify the authenticated DAG topology and discharge every homogeneous tree level's
    /// deferred PCS claims with its single `[CWYZ26]` [`FoldedLevelWhirProof`], rejecting
    /// omissions, duplicates, level mismatches, reordered dependencies, and orphan nodes.
    fn verify_ledger(&self) -> bool {
        let Some(last_node) = self.ledger.last() else {
            return false;
        };
        let top_root = last_node.root();
        let mut pending: BTreeMap<[u64; 4], usize> = BTreeMap::new();
        let mut by_level: Vec<Vec<&DeferredPcsClaim<F>>> = Vec::new();
        for node in &self.ledger {
            let mut edge_levels = [0usize; 2];
            for (slot, edge) in edge_levels.iter_mut().zip(&node.edges) {
                if edge.prior == EMPTY {
                    *slot = 0;
                } else {
                    let Some(lvl) = pending.remove(&edge.prior.map(|v| v.to_canonical_u64()))
                    else {
                        return false;
                    };
                    *slot = lvl;
                }
            }
            if edge_levels[0] != edge_levels[1] {
                return false;
            }
            let level = edge_levels[0];
            if level > by_level.len() {
                return false;
            }
            if level == by_level.len() {
                by_level.push(Vec::new());
            }
            by_level[level].push(&node.edges[0].claim);
            by_level[level].push(&node.edges[1].claim);
            if pending
                .insert(node.root().map(|v| v.to_canonical_u64()), level + 1)
                .is_some()
            {
                return false;
            }
        }
        if pending.len() != 1 || self.level_openings.len() != by_level.len() {
            return false;
        }
        for (level, (claims, opening)) in by_level.iter().zip(&self.level_openings).enumerate() {
            if !verify_folded_level_claims(level, top_root, claims, opening) {
                return false;
            }
        }
        true
    }

    pub fn verify_against_roster_root(
        &self,
        vk: &ShapeVerifierKey,
        statement: &RosterRootStatement<'_>,
    ) -> bool {
        let p = self.public;
        if vk.num_public != PUBLIC_WORDS
            || self.ledger.is_empty()
            || self.level_openings.is_empty()
            || statement.minimum_global_quorums == 0
            || statement.epoch_floor >= crate::field::GOLDILOCKS_PRIME
            || p.epoch_floor.to_canonical_u64() != statement.epoch_floor
            || p.message_digest != subtree_message_digest(statement.message)
            || p.total_active_signers.to_canonical_u64() < statement.minimum_global_quorums
            || p.total_active_signers.to_canonical_u64() >= (1 << 62)
            || p.total_active_weight < statement.minimum_active_weight
            || p.total_active_weight == 0
            || p.total_active_weight >= (1 << 62)
            || p.min_key_idx != statement.min_key_idx
            || p.max_key_idx != statement.max_key_idx
            || p.min_key_idx > p.max_key_idx
            || p.max_key_idx >= (1 << 58)
        {
            return false;
        }
        for (i, r) in p.subtree_registry_root.iter().enumerate() {
            if r.to_le_bytes() != statement.roster_root[i * 8..i * 8 + 8] {
                return false;
            }
        }
        let mut words = p.words().to_vec();
        words.extend(self.ledger.last().unwrap().root());
        verify_public_hologram(vk, &words, SUBTREE_ROOT_LABEL, &self.proof) && self.verify_ledger()
    }
}

impl SplitSubtreeAggregate {
    /// Decode the canonical root proof, claim DAG, and succinct per-level folded WHIR openings.
    pub fn from_bytes_canonical(vk: &ShapeVerifierKey, bytes: &[u8]) -> Option<Self> {
        codec::decode(vk, bytes)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        fn fields(out: &mut Vec<u8>, words: impl IntoIterator<Item = F>) {
            for word in words {
                out.extend_from_slice(&word.to_le_bytes());
            }
        }
        fn exts(out: &mut Vec<u8>, words: impl IntoIterator<Item = GoldilocksExt4>) {
            for word in words {
                fields(out, word.to_limbs());
            }
        }
        fn len(out: &mut Vec<u8>, n: usize) {
            out.extend_from_slice(&(n as u64).to_le_bytes());
        }
        let mut out = b"QSAGSPD2".to_vec();
        fields(&mut out, self.public.words());
        let root = self.proof.to_bytes();
        len(&mut out, root.len());
        out.extend(root);
        len(&mut out, self.ledger.len());
        for node in &self.ledger {
            for edge in &node.edges {
                let c = &edge.claim;
                out.push(c.regime as u8);
                len(&mut out, c.num_vars);
                fields(&mut out, c.transcript);
                fields(&mut out, c.roots.iter().flatten().copied());
                for point in &c.points {
                    len(&mut out, point.len());
                    fields(&mut out, point.iter().flat_map(|e| e.0));
                }
                for claim in c.claims.iter().flatten() {
                    out.push(u8::from(claim.is_some()));
                    if let Some(e) = claim {
                        fields(&mut out, e.0);
                    }
                }
                fields(&mut out, edge.prior);
            }
        }
        len(&mut out, self.level_openings.len());
        for p in &self.level_openings {
            len(&mut out, p.point_rounds.len());
            exts(&mut out, p.point_rounds.iter().flatten().copied());
            len(&mut out, p.poly_evals.len());
            exts(&mut out, p.poly_evals.iter().copied());
            len(&mut out, p.stage0_fibers.len());
            for f_vec in &p.stage0_fibers {
                len(&mut out, f_vec.len());
                fields(&mut out, f_vec.iter().copied());
            }
            len(&mut out, p.stage0_siblings.len());
            for s_vec in &p.stage0_siblings {
                len(&mut out, s_vec.len());
                fields(&mut out, s_vec.iter().flatten().copied());
            }
            len(&mut out, p.later_stage_roots.len());
            fields(&mut out, p.later_stage_roots.iter().flatten().copied());
            len(&mut out, p.ood_evals.len());
            exts(&mut out, p.ood_evals.iter().flatten().copied());
            len(&mut out, p.fold_polys.len());
            exts(&mut out, p.fold_polys.iter().flatten().copied());
            for nonces in [&p.fold_nonces, &p.query_nonces] {
                len(&mut out, nonces.len());
                for n in nonces.iter().flatten() {
                    out.extend_from_slice(&n.to_le_bytes());
                }
            }
            len(&mut out, p.later_fibers.len());
            for f_vec in &p.later_fibers {
                len(&mut out, f_vec.len());
                exts(&mut out, f_vec.iter().copied());
            }
            len(&mut out, p.later_siblings.len());
            for s_vec in &p.later_siblings {
                len(&mut out, s_vec.len());
                fields(&mut out, s_vec.iter().flatten().copied());
            }
            len(&mut out, p.final_coeffs.len());
            exts(&mut out, p.final_coeffs.iter().copied());
        }
        out
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use crate::ValidatorKeypair;
    use std::time::Instant;

    #[test]
    fn split_depth_two_and_three_succinct_folded_openings_and_tamper_rejection() {
        real_tree(2, 1, false);
        real_tree(3, 1, false);
    }

    #[test]
    fn split_legacy_leaf_wrapper_and_two_shard_per_leaf_under_memory_cap() {
        // 1. Verify `SplitSubtreeProof::leaf(public, proof)` compatibility on `prove_subtree_leaf_merge_for_recursion`.
        real_tree(2, 1, true);
        // 2. Verify 2-shard-per-leaf (`fan_in = 2`, `nv = 26`, which previously OOM'd at 16 GiB) succeeds cleanly!
        real_tree(2, 2, false);
    }

    fn real_tree(depth: usize, shards_per_leaf: usize, use_legacy_leaf_wrap: bool) {
        let _permit = crate::prover_admission::acquire();
        let regime = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128;
        let params = FullShardParams::new(regime, 2).unwrap();
        let leaf_nodes = 1 << (depth - 1);
        let count = leaf_nodes * shards_per_leaf;
        let epoch = 2026_1116;
        let message = b"split-subtree real signature test";
        let mut keys: Vec<Vec<ValidatorKeypair>> = (0..count)
            .map(|s| {
                (0..2)
                    .map(|i| {
                        ValidatorKeypair::keygen_deterministic(
                            AggSigProfile::JortsPoseidon2,
                            &[(90 + s) as u8; 32],
                            i,
                        )
                    })
                    .collect()
            })
            .collect();
        let policies: Vec<_> = keys
            .iter()
            .enumerate()
            .map(|(s, k)| ShardHemPolicy {
                shard_id: 100 + s as u64,
                custodian_cluster: [(120 + s) as u8; 32],
                quorum_keys: k.iter().map(|k| k.pk).collect(),
                minimum_quorums: 1,
            })
            .collect();
        let roster = PreparedSubtreeRegistry::new(&params, &policies)
            .unwrap()
            .roster_root;
        let start = Instant::now();
        let leaf = SubtreeLeafMergeRelation::new(params, shards_per_leaf).unwrap();
        let mut vk = leaf.verifier_key().clone();
        std::println!(
            "SPLIT depth={depth} fan_in={shards_per_leaf} leaf_rows={} setup_ms={:.1}",
            leaf.stats().padded_rows,
            start.elapsed().as_secs_f64() * 1000.0
        );
        let bitmap = SignerBitmap::from_active_indices(2, &[0]).unwrap();
        let mut children = Vec::with_capacity(leaf_nodes);
        for l_idx in 0..leaf_nodes {
            let base_s = l_idx * shards_per_leaf;
            let mut leaf_sigs = Vec::with_capacity(shards_per_leaf);
            for off in 0..shards_per_leaf {
                let s = base_s + off;
                let sign_msg =
                    subtree_signing_message(leaf.params(), &policies[s], epoch, message).unwrap();
                leaf_sigs.push(vec![
                    keys[s][0]
                        .sign_stateful_for_unit_test(&sign_msg, s as u32)
                        .unwrap(),
                ]);
            }
            if l_idx == 0 {
                let mut bad_sigs = leaf_sigs.clone();
                bad_sigs[0][0].r_rand[0] += F::ONE;
                let bad_wits: Vec<_> = bad_sigs
                    .iter()
                    .map(|sigs| ShardHemWitness {
                        bitmap: &bitmap,
                        signatures: sigs,
                    })
                    .collect();
                assert!(
                    SplitSubtreeProof::prove_leaf(
                        &leaf,
                        &policies[base_s..base_s + shards_per_leaf],
                        epoch,
                        message,
                        &bad_wits,
                        &[91; 32],
                    )
                    .is_err()
                );
            }

            let wits: Vec<_> = leaf_sigs
                .iter()
                .map(|sigs| ShardHemWitness {
                    bitmap: &bitmap,
                    signatures: sigs,
                })
                .collect();
            let t = Instant::now();
            let child = if use_legacy_leaf_wrap {
                let (public, proof) = prove_subtree_leaf_merge_for_recursion(
                    &leaf,
                    &policies[base_s..base_s + shards_per_leaf],
                    epoch,
                    message,
                    &wits,
                    &[(l_idx + 1) as u8; 32],
                )
                .unwrap();
                SplitSubtreeProof::leaf(public, proof)
            } else {
                SplitSubtreeProof::prove_leaf(
                    &leaf,
                    &policies[base_s..base_s + shards_per_leaf],
                    epoch,
                    message,
                    &wits,
                    &[(l_idx + 1) as u8; 32],
                )
                .unwrap()
            };
            std::println!(
                "SPLIT depth={depth} fan_in={shards_per_leaf} leaf={l_idx} prove_ms={:.1}",
                t.elapsed().as_secs_f64() * 1000.0
            );
            children.push(child);
        }
        drop(leaf);
        let base_shift = shards_per_leaf.trailing_zeros() as usize;
        for level in 2..=depth {
            let t = Instant::now();
            let relation = SplitSubtreeRelation::new(
                vk,
                base_shift + level - 2,
                false,
                if level == depth {
                    WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128
                } else {
                    regime
                },
            )
            .unwrap();
            std::println!(
                "SPLIT depth={depth} fan_in={shards_per_leaf} level={level} rows={} setup_ms={:.1}",
                relation.stats().padded_rows,
                t.elapsed().as_secs_f64() * 1000.0
            );
            assert!(relation.stats().padded_rows <= 1 << 20);
            if level < depth {
                let t = Instant::now();
                let mut next = Vec::new();
                for pair in children.as_chunks::<2>().0 {
                    next.push(
                        relation
                            .prove_for_recursion(&[pair[0].clone(), pair[1].clone()])
                            .unwrap(),
                    );
                }
                std::println!(
                    "SPLIT depth={depth} fan_in={shards_per_leaf} level={level} prove_ms={:.1}",
                    t.elapsed().as_secs_f64() * 1000.0
                );
                children = next;
                vk = relation.verifier_key().clone();
                continue;
            }
            let t = Instant::now();
            let aggregate = relation
                .prove_root(&[children[0].clone(), children[1].clone()], &[72; 32])
                .unwrap();
            let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
            // Succinctness invariant: exactly `depth - 1` folded WHIR openings (`1` per level)!
            assert_eq!(aggregate.deferred_openings(), depth - 1);

            let bytes = aggregate.to_bytes();
            let decoded =
                SplitSubtreeAggregate::from_bytes_canonical(relation.verifier_key(), &bytes)
                    .unwrap();
            assert_eq!(decoded.to_bytes(), bytes);
            let mut trailing = bytes.clone();
            trailing.push(0);
            assert!(
                SplitSubtreeAggregate::from_bytes_canonical(relation.verifier_key(), &trailing)
                    .is_none()
            );
            assert!(
                SplitSubtreeAggregate::from_bytes_canonical(
                    relation.verifier_key(),
                    &bytes[..bytes.len() - 1]
                )
                .is_none()
            );

            let statement = RosterRootStatement {
                roster_root: roster,
                epoch_floor: epoch,
                message,
                minimum_global_quorums: count as u64,
                minimum_active_weight: count as u64,
                min_key_idx: 100,
                max_key_idx: 100 + count as u64 - 1,
            };
            let t = Instant::now();
            assert!(verify_succinct_subtree_aggregate_against_roster_root(
                relation.verifier_key(),
                &statement,
                &aggregate
            ));
            std::println!(
                "SPLIT depth={depth} fan_in={shards_per_leaf} root_prove_ms={prove_ms:.1} root_bytes={} total_bytes={} openings={} verify_ms={:.2} total_ms={:.1}",
                aggregate.proof.to_bytes().len(),
                bytes.len(),
                aggregate.deferred_openings(),
                t.elapsed().as_secs_f64() * 1000.0,
                start.elapsed().as_secs_f64() * 1000.0
            );

            // Adversarial tamper suite across every ledger edge and every folded level opening:
            for node in 0..aggregate.ledger.len() {
                for edge in 0..2 {
                    let mut bad = aggregate.clone();
                    bad.ledger[node].edges[edge].claim.transcript[0] += F::ONE;
                    assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
                    let mut bad = aggregate.clone();
                    bad.ledger[node].edges[edge].claim.roots[0][0] += F::ONE;
                    assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
                }
            }
            for lvl in 0..aggregate.level_openings.len() {
                // Tampered Stage-0 fiber value in H, Z_0, or E_0.
                for poly_idx in 0..aggregate.level_openings[lvl].stage0_fibers.len() {
                    let mut bad = aggregate.clone();
                    bad.level_openings[lvl].stage0_fibers[poly_idx][0] += F::ONE;
                    assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
                }
                // Tampered Stage-0 Steiner Merkle sibling & trailing sibling injection.
                let mut bad = aggregate.clone();
                bad.level_openings[lvl].stage0_siblings[1][0][0] += F::ONE;
                assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
                let mut bad = aggregate.clone();
                bad.level_openings[lvl].stage0_siblings[1].push([F::ZERO; 4]);
                assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
                // Tampered `[CWYZ26]` point-reduction sumcheck round & poly_evals.
                let mut bad = aggregate.clone();
                bad.level_openings[lvl].point_rounds[0][0] += GoldilocksExt4::ONE;
                assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
                let mut bad = aggregate.clone();
                bad.level_openings[lvl].poly_evals[1] += GoldilocksExt4::ONE;
                assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
            }
            let mut bad_roster = statement;
            bad_roster.roster_root[0] ^= 1;
            assert!(!aggregate.verify_against_roster_root(relation.verifier_key(), &bad_roster));
            let mut bad = aggregate.clone();
            bad.ledger.remove(0);
            assert!(!bad.verify_against_roster_root(relation.verifier_key(), &statement));
            let mut bad = aggregate.clone();
            bad.level_openings.pop();
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
