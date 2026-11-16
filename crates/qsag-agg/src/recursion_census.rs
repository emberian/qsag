//! Hash-work census of the `Hem` child verifiers.
//!
//! [`crate::recursive`] carries a compact hierarchy commitment whose outer AIR proves a public
//! Poseidon2 chain over shard summaries and child-proof digests. It does not execute a child
//! verifier, so quorum authorization needs [`crate::VerifiedHierarchicalHemEvidence`]. Closing
//! that gap means proving, inside an outer relation, every check a child verifier performs.
//! [`crate::zk_hem::full_shard`] does so for shards proved in the recursion format; the counts
//! below are for the byte-transcript proofs, which no relation verifies.
//!
//! This module measures the largest fixed part of that work on real proof objects: the
//! Merkle-Canopy authentication of each WHIR opening. Counts are derived only from
//! public wire fields and the schedule, so they can be recomputed for any proof.
//! [`whir_opening_merkle_census`] counts the cSHAKE backend;
//! [`poseidon2_opening_merkle_census`] counts the Poseidon2 backend, including leaf framing,
//! per-tree key derivation and root binding. Neither counts transcript or arithmetic work.
//!
//! What is counted, per Merkle tree with `k` opened leaves and `S` Steiner siblings:
//! * leaf hashes: `k` evaluations of `cSHAKE256` over the canonical leaf frame, each costing
//!   `floor(frame_bytes / 136) + 1` `Keccak-f[1600]` permutations from the precomputed midstate;
//! * internal nodes: exactly `k + S - 1` single-permutation hashes (every recomputed node has two
//!   children, each a recomputed node, an opened leaf or a proof sibling, and only the top node
//!   is nobody's child);
//! * one root-binding permutation.
//!
//! What is not counted: Fiat-Shamir transcript permutations, proof-of-work checks, salt
//! handling, sumcheck and fold arithmetic over `GoldilocksExt4`, the row-constraint evaluation
//! and the byte-level child-proof digest. The totals are therefore lower bounds on a recursive
//! verifier relation.

use crate::arithmetize::ShardBatchProof;
use crate::pcs::{CanopyCommitment, CanopyMultiProof, HemWhirOpeningProof, WhirSchedule};
use crate::recursive::HierarchicalHemAggregate;
use crate::{HemAggregatedProof, MergeNode};

/// `cSHAKE256` rate in bytes.
pub const CSHAKE256_RATE_BYTES: usize = 136;

/// Nonlinear bit operations in one `Keccak-f[1600]`: one `Chi` output bit per state bit per round.
///
/// An arithmetization that materializes every round's `Chi` output as a separate committed
/// bit uses at least this many cells per permutation (`Theta` and input columns excluded).
/// This is a floor for that explicit representation, not for all lookup-free circuits:
/// eliminating intermediate wires, increasing degree, packing bits, or chunking proofs
/// changes the tradeoff. It is not a measured AIR width or an impossibility result.
pub const KECCAK_F1600_CHI_BITS: usize = 24 * 1600;

/// Merkle-authentication hash work of one or more WHIR openings.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MerkleHashCensus {
    /// WHIR openings covered.
    pub whir_openings: usize,
    /// Merkle-Canopy trees authenticated (one per WHIR stage per opening).
    pub merkle_trees: usize,
    /// Distinct opened leaves across all trees.
    pub opened_leaves: usize,
    /// `Goldilocks` limbs carried by the opened leaves.
    pub leaf_field_limbs: usize,
    /// `Keccak-f[1600]` permutations spent hashing opened leaves.
    pub leaf_permutations: usize,
    /// `Keccak-f[1600]` permutations spent on recomputed internal nodes.
    pub internal_node_permutations: usize,
    /// `Keccak-f[1600]` permutations spent binding top nodes to tree depths.
    pub root_permutations: usize,
    /// Width-12, rate-8 sponge blocks needed to absorb the same leaves limb by limb.
    pub leaf_rate8_blocks: usize,
}

impl MerkleHashCensus {
    /// Total counted `Keccak-f[1600]` permutations (`None` on overflow).
    pub fn keccak_permutations(&self) -> Option<usize> {
        self.leaf_permutations
            .checked_add(self.internal_node_permutations)?
            .checked_add(self.root_permutations)
    }

    /// Floor on committed cells when every `Chi` output bit is separately materialized,
    /// covering the counted permutations: [`KECCAK_F1600_CHI_BITS`] per permutation.
    pub fn bitwise_keccak_cells(&self) -> Option<u128> {
        (self.keccak_permutations()? as u128).checked_mul(KECCAK_F1600_CHI_BITS as u128)
    }

    /// Smallest `num_vars` whose hypercube holds [`Self::bitwise_keccak_cells`].
    /// Compare with [`crate::pcs::MAX_PCS_NUM_VARS`].
    pub fn bitwise_keccak_num_vars(&self) -> Option<u32> {
        let cells = self.bitwise_keccak_cells()?;
        Some(if cells <= 1 {
            0
        } else {
            128 - (cells - 1).leading_zeros()
        })
    }

    /// Permutation count if the same trees used a width-12, rate-8 algebraic sponge for leaves
    /// and a two-to-one compression for nodes. This historical estimate omits framing and
    /// tree-key derivation; use [`poseidon2_opening_merkle_census`] for actual Poseidon2 proofs.
    pub fn algebraic_rate8_permutations(&self) -> Option<usize> {
        self.leaf_rate8_blocks
            .checked_add(self.internal_node_permutations)?
            .checked_add(self.root_permutations)
    }

    /// Field-wise sum of two censuses (`None` on overflow).
    pub fn checked_add(&self, other: &Self) -> Option<Self> {
        Some(Self {
            whir_openings: self.whir_openings.checked_add(other.whir_openings)?,
            merkle_trees: self.merkle_trees.checked_add(other.merkle_trees)?,
            opened_leaves: self.opened_leaves.checked_add(other.opened_leaves)?,
            leaf_field_limbs: self.leaf_field_limbs.checked_add(other.leaf_field_limbs)?,
            leaf_permutations: self
                .leaf_permutations
                .checked_add(other.leaf_permutations)?,
            internal_node_permutations: self
                .internal_node_permutations
                .checked_add(other.internal_node_permutations)?,
            root_permutations: self
                .root_permutations
                .checked_add(other.root_permutations)?,
            leaf_rate8_blocks: self
                .leaf_rate8_blocks
                .checked_add(other.leaf_rate8_blocks)?,
        })
    }

    fn add_tree(
        &mut self,
        commitment: &CanopyCommitment,
        opened_leaves: usize,
        leaf_frame_bytes: usize,
        limbs_per_leaf: usize,
        multiproof: &CanopyMultiProof,
    ) -> Option<()> {
        if opened_leaves == 0
            || commitment.log_leaves > 28
            || opened_leaves > 1usize << commitment.log_leaves
        {
            return None;
        }
        let leaf_perms = opened_leaves.checked_mul(leaf_frame_bytes / CSHAKE256_RATE_BYTES + 1)?;
        let internal = opened_leaves
            .checked_add(multiproof.auth_siblings.len())?
            .checked_sub(1)?;
        self.merkle_trees = self.merkle_trees.checked_add(1)?;
        self.opened_leaves = self.opened_leaves.checked_add(opened_leaves)?;
        self.leaf_field_limbs = self
            .leaf_field_limbs
            .checked_add(opened_leaves.checked_mul(limbs_per_leaf)?)?;
        self.leaf_permutations = self.leaf_permutations.checked_add(leaf_perms)?;
        self.internal_node_permutations = self.internal_node_permutations.checked_add(internal)?;
        self.root_permutations = self.root_permutations.checked_add(1)?;
        self.leaf_rate8_blocks = self
            .leaf_rate8_blocks
            .checked_add(opened_leaves.checked_mul(limbs_per_leaf.div_ceil(8))?)?;
        Some(())
    }
}

/// Census of one WHIR opening against `stage0_commitment` under `schedule`.
///
/// Returns `None` for Poseidon2 or when the proof's shape does not match the schedule. This is a shape check
/// only: it neither verifies the opening nor samples the query indices.
pub fn whir_opening_merkle_census(
    schedule: &WhirSchedule,
    stage0_commitment: &CanopyCommitment,
    proof: &HemWhirOpeningProof,
) -> Option<MerkleHashCensus> {
    if schedule.regime.uses_poseidon2_canopy() {
        return None;
    }
    let (st0, later) = schedule.stages.split_first()?;
    if later.len() != proof.folded_layers.len() || st0.step_vars == 0 || st0.step_vars > 6 {
        return None;
    }
    let mut census = MerkleHashCensus {
        whir_openings: 1,
        ..MerkleHashCensus::default()
    };

    // Stage 0: salted base-field leaves, `num_polys * arity_0` limbs each.
    let arity_0 = 1usize << st0.step_vars;
    let opened_0 = proof.round0_salts.len();
    if opened_0 == 0 || !proof.round0_vals.len().is_multiple_of(opened_0) {
        return None;
    }
    let limbs_0 = proof.round0_vals.len() / opened_0;
    if limbs_0 == 0 || !limbs_0.is_multiple_of(arity_0) {
        return None;
    }
    let frame_0 = if limbs_0 == arity_0 {
        22 + 8 * arity_0
    } else {
        23usize.checked_add(limbs_0.checked_mul(8)?)?
    };
    census.add_tree(
        stage0_commitment,
        opened_0,
        frame_0,
        limbs_0,
        &proof.round0_multiproof,
    )?;

    // Stages `1..M`: `GoldilocksExt4` fibers, four limbs per value.
    for (spec, layer) in later.iter().zip(&proof.folded_layers) {
        if spec.step_vars == 0 || spec.step_vars > 6 {
            return None;
        }
        let arity = 1usize << spec.step_vars;
        if layer.opened_vals.is_empty() || !layer.opened_vals.len().is_multiple_of(arity) {
            return None;
        }
        census.add_tree(
            &layer.commitment,
            layer.opened_vals.len() / arity,
            7 + 32 * arity,
            4 * arity,
            &layer.multiproof,
        )?;
    }
    Some(census)
}

/// Exact number of width-12 Poseidon2 permutations used for Merkle authentication only.
/// This is a work count, not an execution proof or a measurement of a recursive circuit.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Poseidon2MerkleCensus {
    pub merkle_trees: usize,
    pub opened_leaves: usize,
    pub leaf_permutations: usize,
    pub internal_node_permutations: usize,
    pub tree_key_permutations: usize,
    pub root_permutations: usize,
}

impl Poseidon2MerkleCensus {
    pub fn checked_add(&self, other: &Self) -> Option<Self> {
        Some(Self {
            merkle_trees: self.merkle_trees.checked_add(other.merkle_trees)?,
            opened_leaves: self.opened_leaves.checked_add(other.opened_leaves)?,
            leaf_permutations: self
                .leaf_permutations
                .checked_add(other.leaf_permutations)?,
            internal_node_permutations: self
                .internal_node_permutations
                .checked_add(other.internal_node_permutations)?,
            tree_key_permutations: self
                .tree_key_permutations
                .checked_add(other.tree_key_permutations)?,
            root_permutations: self
                .root_permutations
                .checked_add(other.root_permutations)?,
        })
    }

    pub fn permutations(&self) -> Option<usize> {
        self.leaf_permutations
            .checked_add(self.internal_node_permutations)?
            .checked_add(self.tree_key_permutations)?
            .checked_add(self.root_permutations)
    }

    fn add_tree(
        &mut self,
        commitment: &CanopyCommitment,
        leaves: usize,
        input_limbs: usize,
        proof: &CanopyMultiProof,
    ) -> Option<()> {
        if leaves == 0 || commitment.log_leaves > 28 || leaves > 1usize << commitment.log_leaves {
            return None;
        }
        let internal = leaves
            .checked_add(proof.auth_siblings.len())?
            .checked_sub(1)?;
        if internal >= 1usize << commitment.log_leaves {
            return None;
        }
        // poseidon2_sponge_hash_limbs prepends domain and length (two limbs).
        let leaf_perms = leaves.checked_mul(input_limbs.checked_add(2)?.div_ceil(8))?;
        self.merkle_trees = self.merkle_trees.checked_add(1)?;
        self.opened_leaves = self.opened_leaves.checked_add(leaves)?;
        self.leaf_permutations = self.leaf_permutations.checked_add(leaf_perms)?;
        self.internal_node_permutations = self.internal_node_permutations.checked_add(internal)?;
        // Tree key: domain, length, stage, depth. Root: those four plus the four digest limbs.
        self.tree_key_permutations = self.tree_key_permutations.checked_add(1)?;
        self.root_permutations = self.root_permutations.checked_add(1)?;
        Some(())
    }
}

/// Count actual Poseidon2 Merkle verification work; reject cSHAKE schedules and malformed
/// fiber shapes. Authentication and Fiat-Shamir challenges must still be checked separately.
pub fn poseidon2_opening_merkle_census(
    schedule: &WhirSchedule,
    stage0_commitment: &CanopyCommitment,
    proof: &HemWhirOpeningProof,
) -> Option<Poseidon2MerkleCensus> {
    if !schedule.regime.uses_poseidon2_canopy() {
        return None;
    }
    let (stage0, later) = schedule.stages.split_first()?;
    if later.len() != proof.folded_layers.len() || !(1..=6).contains(&stage0.step_vars) {
        return None;
    }
    let leaves = proof.round0_salts.len();
    if leaves == 0 || !proof.round0_vals.len().is_multiple_of(leaves) {
        return None;
    }
    let limbs = proof.round0_vals.len() / leaves;
    let arity = 1usize << stage0.step_vars;
    if !limbs.is_multiple_of(arity) || !(1..=crate::pcs::MAX_BATCH_POLYS).contains(&(limbs / arity))
    {
        return None;
    }
    let mut census = Poseidon2MerkleCensus::default();
    // The 16-byte salt is encoded as three canonical limbs before the base-field values.
    census.add_tree(
        stage0_commitment,
        leaves,
        limbs.checked_add(3)?,
        &proof.round0_multiproof,
    )?;
    for (spec, layer) in later.iter().zip(&proof.folded_layers) {
        if !(1..=6).contains(&spec.step_vars) {
            return None;
        }
        let arity = 1usize << spec.step_vars;
        if layer.opened_vals.is_empty() || !layer.opened_vals.len().is_multiple_of(arity) {
            return None;
        }
        census.add_tree(
            &layer.commitment,
            layer.opened_vals.len() / arity,
            4 * arity,
            &layer.multiproof,
        )?;
    }
    Some(census)
}

/// Merkle work in every child opening of a Poseidon2 aggregate, including all fan-in leaves.
pub fn poseidon2_aggregate_merkle_census(
    proof: &HemAggregatedProof,
) -> Option<Poseidon2MerkleCensus> {
    fn visit(node: &MergeNode, depth: usize) -> Option<Poseidon2MerkleCensus> {
        if depth == 0 {
            return None;
        }
        match node {
            MergeNode::Leaf(batch) => poseidon2_opening_merkle_census(
                &batch.schedule,
                &batch.witness_comm,
                &batch.pcs_opening.opening,
            ),
            MergeNode::Branch { left, right, .. } => {
                visit(left, depth - 1)?.checked_add(&visit(right, depth - 1)?)
            }
        }
    }
    visit(&proof.root, crate::MAX_MERGE_TREE_DEPTH)
}

/// Census of one shard batch: its single batched WHIR opening.
pub fn shard_batch_merkle_census(batch: &ShardBatchProof) -> Option<MerkleHashCensus> {
    whir_opening_merkle_census(
        &batch.schedule,
        &batch.witness_comm,
        &batch.pcs_opening.opening,
    )
}

fn merge_node_census(node: &MergeNode, rem_depth: usize) -> Option<MerkleHashCensus> {
    match node {
        MergeNode::Leaf(batch) => shard_batch_merkle_census(batch),
        MergeNode::Branch { left, right, .. } if rem_depth > 0 => {
            merge_node_census(left, rem_depth - 1)?
                .checked_add(&merge_node_census(right, rem_depth - 1)?)
        }
        MergeNode::Branch { .. } => None,
    }
}

/// Census of every shard batch a verifier of `proof` authenticates.
pub fn aggregate_merkle_census(proof: &HemAggregatedProof) -> Option<MerkleHashCensus> {
    merge_node_census(&proof.root, 64)
}

/// Census of every child proof in a full hierarchy: the Merkle work a recursive outer relation
/// would have to reproduce to replace [`crate::verify_hierarchical_hem_evidence`].
pub fn hierarchy_merkle_census(aggregate: &HierarchicalHemAggregate) -> Option<MerkleHashCensus> {
    aggregate
        .shards
        .iter()
        .try_fold(MerkleHashCensus::default(), |acc, shard| {
            acc.checked_add(&aggregate_merkle_census(&shard.proof)?)
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::{MerkleCanopyTree, verify_canopy_multiproof};
    use alloc::collections::BTreeSet;
    use alloc::vec::Vec;

    fn leaf(i: usize) -> [u8; 32] {
        let mut h = [0u8; 32];
        h[..8].copy_from_slice(&(i as u64).to_le_bytes());
        h[31] = 0x5a;
        h
    }

    /// The internal-node identity `k + S - 1` equals a direct count of the distinct ancestors
    /// of the opened leaves, on real Steiner multiproofs that the verifier accepts.
    #[test]
    fn internal_node_identity_matches_distinct_ancestor_count() {
        for log_leaves in [1usize, 2, 5, 9] {
            let n = 1usize << log_leaves;
            let tree = MerkleCanopyTree::build((0..n).map(leaf).collect());
            let commitment = tree.commitment();
            let patterns: Vec<Vec<usize>> = alloc::vec![
                alloc::vec![0],
                alloc::vec![n - 1],
                (0..n).collect(),
                (0..n).step_by(3).collect(),
                (0..n).filter(|i| i % 7 == 1 || i % 5 == 4).collect(),
                (n / 2..n).collect(),
            ];
            for indices in patterns {
                if indices.is_empty() {
                    continue;
                }
                let proof = tree.open_multi_with_leaf_fn(&indices, leaf);
                let opened: Vec<(usize, [u8; 32])> =
                    indices.iter().map(|&i| (i, leaf(i))).collect();
                assert!(verify_canopy_multiproof(&commitment, &opened, &proof));

                let mut ancestors = BTreeSet::new();
                for &i in &indices {
                    let mut node = n + i;
                    while node > 1 {
                        node /= 2;
                        ancestors.insert(node);
                    }
                }
                let mut census = MerkleHashCensus::default();
                census
                    .add_tree(&commitment, indices.len(), 69, 4, &proof)
                    .unwrap();
                assert_eq!(
                    census.internal_node_permutations,
                    ancestors.len(),
                    "log_leaves={log_leaves} opened={}",
                    indices.len()
                );
                assert_eq!(census.root_permutations, 1);
            }
        }
    }

    #[test]
    fn census_arithmetic_and_shape_rejection() {
        let c = MerkleHashCensus {
            leaf_permutations: 400,
            internal_node_permutations: 30,
            root_permutations: 7,
            ..MerkleHashCensus::default()
        };
        assert_eq!(c.keccak_permutations(), Some(437));
        // 437 * 38_400 = 16_780_800 > 2^24 = 16_777_216: one more variable is needed.
        assert_eq!(c.bitwise_keccak_cells(), Some(16_780_800));
        assert_eq!(c.bitwise_keccak_num_vars(), Some(25));
        let fits = MerkleHashCensus {
            leaf_permutations: 436,
            ..MerkleHashCensus::default()
        };
        assert_eq!(fits.bitwise_keccak_num_vars(), Some(24));

        let tree = MerkleCanopyTree::build((0..4).map(leaf).collect());
        let proof = tree.open_multi_with_leaf_fn(&[1], leaf);
        let mut census = MerkleHashCensus::default();
        // No opened leaf, or more opened leaves than the tree holds, is not a valid opening.
        assert!(
            census
                .add_tree(&tree.commitment(), 0, 69, 4, &proof)
                .is_none()
        );
        assert!(
            census
                .add_tree(&tree.commitment(), 5, 69, 4, &proof)
                .is_none()
        );
        // A 135-byte frame fits one block; 136 bytes forces a second for the padding.
        census
            .add_tree(&tree.commitment(), 1, 135, 9, &proof)
            .unwrap();
        assert_eq!(census.leaf_permutations, 1);
        assert_eq!(census.leaf_rate8_blocks, 2);
        census
            .add_tree(&tree.commitment(), 1, 136, 8, &proof)
            .unwrap();
        assert_eq!(census.leaf_permutations, 3);
        assert_eq!(census.leaf_rate8_blocks, 3);
    }

    #[test]
    fn poseidon2_census_counts_framing_and_rejects_the_other_backend() {
        use crate::field::{Goldilocks, GoldilocksExt4};
        use crate::pcs::{WhirSecurityRegime, whir_commit_owned_with_schedule, whir_open};
        use crate::sponge::FiatShamirTranscript;
        use alloc::vec;
        let schedule = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128.schedule(8);
        let table: Vec<_> = (0..256).map(Goldilocks::from_u64_reduced).collect();
        let point = vec![GoldilocksExt4::V; 8];
        let value = crate::field::mle_eval_base_at_ext4(&table, &point);
        let (comm, state) = whir_commit_owned_with_schedule(table, &[9; 32], &schedule);
        let mut transcript = FiatShamirTranscript::new()
            .bind_relation(b"CENSUS", b"", &schedule)
            .bind_instance(&[b"framing"]);
        let proof = whir_open(&state, &point, value, &mut transcript);
        let census = poseidon2_opening_merkle_census(&schedule, &comm, &proof).unwrap();
        let r0_leaves = proof.round0_salts.len();
        let r0_arity = 1usize << schedule.stages[0].step_vars;
        let mut leaf_perms = r0_leaves * (5 + r0_arity).div_ceil(8);
        let mut internal = r0_leaves + proof.round0_multiproof.auth_siblings.len() - 1;
        for (stage, layer) in schedule.stages[1..].iter().zip(&proof.folded_layers) {
            let arity = 1usize << stage.step_vars;
            let leaves = layer.opened_vals.len() / arity;
            leaf_perms += leaves * (2 + 4 * arity).div_ceil(8);
            internal += leaves + layer.multiproof.auth_siblings.len() - 1;
        }
        assert_eq!(census.leaf_permutations, leaf_perms);
        assert_eq!(
            census.permutations(),
            Some(leaf_perms + internal + 2 * schedule.stages.len())
        );
        assert!(whir_opening_merkle_census(&schedule, &comm, &proof).is_none());
        let other = WhirSecurityRegime::Cdhz25ZeroPowQrom128.schedule(8);
        assert!(poseidon2_opening_merkle_census(&other, &comm, &proof).is_none());
        let mut malformed = proof.clone();
        malformed.round0_vals.pop();
        assert!(poseidon2_opening_merkle_census(&schedule, &comm, &malformed).is_none());
    }
}
