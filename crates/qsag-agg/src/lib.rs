//! `qsag-agg`: `Hem` Succinct Non-Interactive $K$-to-$1$ Post-Quantum Multi-Signature Aggregation
//! (`#![no_std]` + `alloc`, `#![forbid(unsafe_code)]`, `0` external deps).
//!
//! Aggregates $K$ independent hash-based validator signatures (`JortsPoseidon2` stateful 256-bit
//! `WOTS+C` + XMSS, or `CorduroyPoseidon2` stateless 256-bit `FORS` + 16-layer `WOTS+C` hypertree)
//! into a succinct post-quantum argument of knowledge over `Goldilocks` / `GoldilocksExt4`
//! ($\mathbb{F}_{p^4}$, $|\mathbb{F}_{p^4}| > 2^{255.99}$):
//! - **Zero Raw Signature Shipping:** [`HemAggregator`] arithmetizes all $K$ parallel `Poseidon2`
//!   $x^7$ S-box chains, constant-sum digit decompositions, and Merkle authentication paths into
//!   $256$-column multilinear execution traces and proves zero-residual satisfaction via degree-8
//!   `GoldilocksExt4` Sumcheck + `[P0-01]`-hardened `Hem` WHIR rate-escalated Reed–Solomon /
//!   `CANOPY_MIDSTATE` Steiner-deduplicated Merkle-Canopy PCS.
//!
//! # What an aggregate proof is, and how it scales
//!
//! Signers are packed into *shards* (at most [`max_shard_signers`] signers each, the largest
//! trace the PCS accepts) and shards into *shard batches*. A [`HemAggregatedProof`] (aliased as
//! [`QsagAggregateProof`]) is a binary [`MergeNode`] tree whose leaves are [`ShardBatchProof`]s.
//!
//! - **Inside a shard batch the opening is accumulated.** One prover holding every shard's
//!   witness commits them under one Merkle tree and reduces all shards' evaluation claims to a
//!   single opening: a sumcheck over a random `GoldilocksExt4` linear combination brings the claims
//!   to a common point, and one `Hem` WHIR rate-escalated opening of a second random combination
//!   settles them (see [`pcs`], "Batched Opening"). Every batching challenge is squeezed from a
//!   transcript that has already absorbed the batch's signer bitmap, shard signer counts, joint
//!   commitment, and every shard's sumcheck messages and claim. A batch of $S$ shards therefore
//!   carries one query schedule, one Round-0 Steiner Merkle multi-proof, and one chain of
//!   escalated-rate WHIR layers.
//! - **Across shard batches nothing is compressed.** [`HemAggregator::merge`] ([`merge_aggregates`])
//!   takes two finished proofs. The merging party holds no witness, and this crate has no recursive
//!   verifier circuit, so it cannot produce a new opening for the children's committed polynomials.
//!   A [`MergeNode::Branch`] is therefore plain concatenation: it adds no proof content, the merged
//!   proof contains both children in full, and [`HemAggregator::verify`] ([`verify_aggregate`])
//!   verifies every leaf. What a `Branch` enforces is the statement-level structure: its children's
//!   signer sets are disjoint, and the child holding the lowest signer index comes first, so
//!   swapping two subtrees never yields a second valid encoding.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod arithmetize;
pub mod field;
pub mod pcs;
pub mod sig;
pub mod sponge;
pub mod trace;

use alloc::boxed::Box;
use alloc::vec::Vec;

/// Preserve a worker's original panic payload rather than replacing it at join.
#[cfg(feature = "std")]
fn join_worker<T>(handle: std::thread::ScopedJoinHandle<'_, T>) -> T {
    match handle.join() {
        Ok(value) => value,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}


pub use arithmetize::{
    ShardBatchProof, ShardRowProof, compute_signing_mode_digest, max_shard_signers,
    prove_shard_batch, verify_shard_batch,
};
pub use field::{Goldilocks, GoldilocksExt2, GoldilocksExt4, RoundPolyExt4};
pub use pcs::{
    CanopyCommitment, CanopyMultiProof, EARLY_STOP_VARS, FoldedOracleProof,
    HemWhirBatchOpeningProof, HemWhirOpeningProof, HemWhirProverState, MAX_BATCH_POLYS,
    MAX_PCS_NUM_VARS, NUM_PCS_QUERIES, PCS_POW_BITS, RS_BLOWUP, WhirSchedule, WhirSecurityRegime,
    WhirStageProof, WhirStageSpec, whir_commit, whir_commit_batch_owned, whir_commit_owned,
    whir_open, whir_open_batch, whir_stage_schedule, whir_verify, whir_verify_batch,
};
pub use pcs::{
    whir_commit_batch_owned_with_schedule, whir_commit_owned_with_schedule,
    whir_commit_with_schedule, whir_verify_batch_with_schedule, whir_verify_with_schedule,
};
pub use sig::{
    AggSigProfile, Digest4, Digest5, EpochWalSink, SigError, SignerBitmap, SigningMode,
    StatefulEpochLatch, StatelessBudgetWalSink, CORDUROY_MAX_STATELESS_SIGS_PER_KEY,
    ValidatorKeypair, ValidatorPublicKey, ValidatorSignature, bytes32_to_limbs56,
    compute_committee_root, limbs56_to_bytes32_canonical, validate_unique_active_committee,
    verify_individual_signature, verify_signature_batch,
};
#[cfg(feature = "std")]
pub use sig::{FsStatelessBudgetWal, FsWalEpochSink};
pub use sponge::{FiatShamirTranscript, InstanceBound, RelationBound, Unbound};

/// Canonical 8-byte wire header for [`HemAggregatedProof`] (`v5`: regime/schedule-bound `GoldilocksExt4` WHIR).
pub const AGG_WIRE_MAGIC: &[u8; 8] = b"QSAGAGG\x05";

/// Hard upper bound on merge tree depth (`2^16 = 65,536` shard batches).
pub const MAX_MERGE_TREE_DEPTH: usize = 16;

/// Default (and maximum) active signers per `JortsPoseidon2` shard.
pub const DEFAULT_MAX_SHARD_SIGNERS_JORTS: usize =
    max_shard_signers(AggSigProfile::JortsPoseidon2);

/// Default (and maximum) active signers per `CorduroyPoseidon2` shard.
pub const DEFAULT_MAX_SHARD_SIGNERS_CORDUROY: usize =
    max_shard_signers(AggSigProfile::CorduroyPoseidon2);

/// Default shards per batch.
pub const DEFAULT_MAX_SHARDS_PER_BATCH: usize = 2;

/// Configuration parameters for [`HemAggregator::aggregate_with_config`] (`aggregate_signatures_with_config`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemAggConfig {
    pub regime: WhirSecurityRegime,
    /// Optional explicit schedule; must match the regime and each batch dimension.
    pub whir_schedule: Option<WhirSchedule>,
    /// Maximum active signers packed into a single shard (`1..=max_shard_signers(profile)`).
    pub max_signers_per_shard: usize,
    /// Maximum shards proven under one commitment and one WHIR opening (`1..=MAX_BATCH_POLYS`).
    pub max_shards_per_batch: usize,
    /// Cryptographic blinding seed for `Idle` trace rows and Round-0 Merkle-Canopy salts.
    pub blinding_seed: [u8; 32],
}

/// Compatibility alias for [`HemAggConfig`].
pub type AggConfig = HemAggConfig;

impl HemAggConfig {
    pub fn default_for(profile: AggSigProfile, blinding_seed: [u8; 32]) -> Self {
        Self {
            regime: WhirSecurityRegime::default(),
            whir_schedule: None,
            max_signers_per_shard: max_shard_signers(profile),
            max_shards_per_batch: DEFAULT_MAX_SHARDS_PER_BATCH,
            blinding_seed,
        }
    }
}

/// Errors returned by [`HemAggregator`], `aggregate_signatures`, `merge_aggregates`, or canonical
/// wire deserialization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HemAggError {
    EmptySigners,
    CommitteeMismatch,
    DuplicateValidatorOrProfileMismatch,
    SignatureCountMismatch,
    MessageCountMismatch,
    InvalidIndividualSignature,
    InvalidShardConfig,
    OverlappingSigners,
    ProfileMismatch,
    RegimeMismatch,
    TreeDepthExceeded,
    InvalidChildProof,
    MalformedWireBytes,
}

/// Compatibility alias for [`HemAggError`].
pub type AggError = HemAggError;

/// Node of the binary tree inside a [`HemAggregatedProof`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MergeNode {
    Leaf(Box<ShardBatchProof>),
    Branch {
        /// Disjoint union of the children's signer sets. Not on the wire; `from_bytes_canonical`
        /// recomputes it and `verify_aggregate` rechecks it.
        bitmap: SignerBitmap,
        /// The child containing the lowest signer index.
        left: Box<MergeNode>,
        right: Box<MergeNode>,
    },
}

impl MergeNode {
    /// Check every leaf, bounding recursion even for directly constructed trees.
    fn homogeneous_regime(&self, rem_depth: usize) -> Option<WhirSecurityRegime> {
        match self {
            Self::Leaf(leaf) => Some(leaf.schedule.regime),
            Self::Branch { left, right, .. } if rem_depth > 0 => {
                let regime = left.homogeneous_regime(rem_depth - 1)?;
                (right.homogeneous_regime(rem_depth - 1)? == regime).then_some(regime)
            }
            Self::Branch { .. } => None,
        }
    }

    pub fn bitmap(&self) -> &SignerBitmap {
        match self {
            Self::Leaf(leaf) => &leaf.bitmap,
            Self::Branch { bitmap, .. } => bitmap,
        }
    }

    pub fn depth(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Branch { left, right, .. } => 1 + left.depth().max(right.depth()),
        }
    }

    /// Number of leaves, i.e. independently verified shard batches.
    pub fn num_shard_batches(&self) -> usize {
        match self {
            Self::Leaf(_) => 1,
            Self::Branch { left, right, .. } => {
                left.num_shard_batches() + right.num_shard_batches()
            }
        }
    }

    /// Total number of shards across all leaves.
    pub fn num_leaf_shards(&self) -> usize {
        match self {
            Self::Leaf(leaf) => leaf.num_shards(),
            Self::Branch { left, right, .. } => left.num_leaf_shards() + right.num_leaf_shards(),
        }
    }

    /// Join two subtrees over disjoint signer sets in canonical order.
    fn branch(a: MergeNode, b: MergeNode) -> Result<Self, HemAggError> {
        let regime = a.homogeneous_regime(MAX_MERGE_TREE_DEPTH)
            .ok_or(HemAggError::RegimeMismatch)?;
        if b.homogeneous_regime(MAX_MERGE_TREE_DEPTH) != Some(regime) {
            return Err(HemAggError::RegimeMismatch);
        }
        let bitmap = a
            .bitmap()
            .union_disjoint(b.bitmap())
            .ok_or(HemAggError::OverlappingSigners)?;
        let (left, right) = if a.bitmap().first_active() <= b.bitmap().first_active() {
            (a, b)
        } else {
            (b, a)
        };
        Ok(Self::Branch {
            bitmap,
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    /// The union a `Branch` over `left` and `right` must carry, or `None` if the children overlap,
    /// span different committees, are empty, or are not in canonical order.
    fn canonical_union(left: &MergeNode, right: &MergeNode) -> Option<SignerBitmap> {
        let first_left = left.bitmap().first_active()?;
        let first_right = right.bitmap().first_active()?;
        if first_left >= first_right {
            return None;
        }
        left.bitmap().union_disjoint(right.bitmap())
    }

    fn push_bytes(&self, out: &mut Vec<u8>) {
        match self {
            Self::Leaf(leaf) => {
                out.push(0x01);
                leaf.push_bytes(out);
            }
            Self::Branch { left, right, .. } => {
                out.push(0x02);
                left.push_bytes(out);
                right.push_bytes(out);
            }
        }
    }

    fn from_bytes_canonical(
        profile: AggSigProfile,
        bytes: &[u8],
        rem_depth: usize,
    ) -> Option<(Self, usize)> {
        match *bytes.first()? {
            0x01 => {
                let (leaf, used) = ShardBatchProof::from_bytes_canonical(profile, &bytes[1..])?;
                Some((Self::Leaf(Box::new(leaf)), 1 + used))
            }
            0x02 => {
                if rem_depth == 0 {
                    return None;
                }
                let mut pos = 1usize;
                let (left, used_l) =
                    Self::from_bytes_canonical(profile, &bytes[pos..], rem_depth - 1)?;
                pos += used_l;
                let (right, used_r) =
                    Self::from_bytes_canonical(profile, &bytes[pos..], rem_depth - 1)?;
                pos += used_r;
                let regime = left.homogeneous_regime(rem_depth - 1)?;
                if right.homogeneous_regime(rem_depth - 1)? != regime {
                    return None;
                }
                let bitmap = Self::canonical_union(&left, &right)?;
                Some((
                    Self::Branch {
                        bitmap,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    pos,
                ))
            }
            _ => None,
        }
    }
}

/// Succinct `Hem` post-quantum aggregate multi-signature proof over an ordered validator committee.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemAggregatedProof {
    pub profile: AggSigProfile,
    pub committee_root: [u8; 32],
    pub root: MergeNode,
}

/// Compatibility alias for [`HemAggregatedProof`].
pub type QsagAggregateProof = HemAggregatedProof;

impl HemAggregatedProof {
    #[inline]
    pub fn bitmap(&self) -> &SignerBitmap {
        self.root.bitmap()
    }

    #[inline]
    pub fn num_signers(&self) -> usize {
        self.bitmap().count_ones()
    }

    /// Total number of shards across all shard batches.
    #[inline]
    pub fn num_leaf_shards(&self) -> usize {
        self.root.num_leaf_shards()
    }

    /// Number of independently verified shard batches (tree leaves).
    #[inline]
    pub fn num_shard_batches(&self) -> usize {
        self.root.num_shard_batches()
    }

    /// Serialize to canonical self-delimiting wire bytes (`AGG_WIRE_MAGIC` header).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(AGG_WIRE_MAGIC);
        out.push(self.profile as u8);
        out.extend_from_slice(&self.committee_root);
        self.root.push_bytes(&mut out);
        out
    }

    /// Deserialize strictly canonical wire bytes, rejecting trailing bytes, non-canonical limbs,
    /// depth overflows, and branches whose children overlap or are out of canonical order.
    pub fn from_bytes_canonical(bytes: &[u8]) -> Result<Self, HemAggError> {
        if bytes.len() < 41 || &bytes[0..8] != AGG_WIRE_MAGIC {
            return Err(HemAggError::MalformedWireBytes);
        }
        let profile = AggSigProfile::from_u8(bytes[8]).ok_or(HemAggError::MalformedWireBytes)?;
        let mut committee_root = [0u8; 32];
        committee_root.copy_from_slice(&bytes[9..41]);
        let (root, used) =
            MergeNode::from_bytes_canonical(profile, &bytes[41..], MAX_MERGE_TREE_DEPTH)
                .ok_or(HemAggError::MalformedWireBytes)?;
        if 41 + used != bytes.len() {
            return Err(HemAggError::MalformedWireBytes);
        }
        Ok(Self {
            profile,
            committee_root,
            root,
        })
    }
}

/// Pants-themed `Hem` succinct `GoldilocksExt4` WHIR signature aggregator facade.
#[derive(Clone, Copy, Debug, Default)]
pub struct HemAggregator;

impl HemAggregator {
    /// Non-interactively aggregate $K \ge 1$ valid committee signatures into a [`HemAggregatedProof`].
    #[inline]
    pub fn aggregate(
        pks: &[ValidatorPublicKey],
        bitmap: &SignerBitmap,
        mode: &SigningMode<'_>,
        sigs: &[ValidatorSignature],
        blinding_seed: [u8; 32],
    ) -> Result<HemAggregatedProof, HemAggError> {
        aggregate_signatures(pks, bitmap, mode, sigs, blinding_seed)
    }

    /// Aggregate $K \ge 1$ valid committee signatures with explicit [`HemAggConfig`] shard/batch limits.
    #[inline]
    pub fn aggregate_with_config(
        pks: &[ValidatorPublicKey],
        bitmap: &SignerBitmap,
        mode: &SigningMode<'_>,
        sigs: &[ValidatorSignature],
        cfg: &HemAggConfig,
    ) -> Result<HemAggregatedProof, HemAggError> {
        aggregate_signatures_with_config(pks, bitmap, mode, sigs, cfg)
    }

    /// Verify with an application-selected regime, rejecting downgrade or mixed-regime leaves.
    pub fn verify_with_regime(
        pks: &[ValidatorPublicKey],
        mode: &SigningMode<'_>,
        proof: &HemAggregatedProof,
        regime: WhirSecurityRegime,
    ) -> bool {
        verify_aggregate_with_regime(pks, mode, proof, regime)
    }

    /// Join two valid [`HemAggregatedProof`]s over disjoint signer subsets of the same committee.
    #[inline]
    pub fn merge(
        pks: &[ValidatorPublicKey],
        merged_mode: &SigningMode<'_>,
        proof_a: &HemAggregatedProof,
        proof_b: &HemAggregatedProof,
    ) -> Result<HemAggregatedProof, HemAggError> {
        merge_aggregates(pks, merged_mode, proof_a, proof_b)
    }

    /// Owned counterpart to [`HemAggregator::merge`].
    #[inline]
    pub fn merge_owned(
        pks: &[ValidatorPublicKey],
        merged_mode: &SigningMode<'_>,
        proof_a: HemAggregatedProof,
        proof_b: HemAggregatedProof,
    ) -> Result<HemAggregatedProof, HemAggError> {
        merge_aggregates_owned(pks, merged_mode, proof_a, proof_b)
    }

    /// Verify a [`HemAggregatedProof`] against `pks` and `mode`.
    #[inline]
    pub fn verify(
        pks: &[ValidatorPublicKey],
        mode: &SigningMode<'_>,
        proof: &HemAggregatedProof,
    ) -> bool {
        verify_aggregate(pks, mode, proof)
    }
}

// ============================================================================
// Tree Verification & Construction Helpers
// ============================================================================

struct AggStatement<'a> {
    pks: &'a [ValidatorPublicKey],
    committee_root: &'a [u8; 32],
    profile: AggSigProfile,
    mode: &'a SigningMode<'a>,
    root_active: Vec<usize>,
}

impl AggStatement<'_> {
    fn verify_leaf(&self, leaf: &ShardBatchProof) -> bool {
        match self.mode {
            SigningMode::SharedMessage(_) => {
                verify_shard_batch(self.pks, self.committee_root, self.profile, self.mode, leaf)
            }
            SigningMode::PerSignerMessages(root_msgs) => {
                if root_msgs.len() != self.root_active.len() {
                    return false;
                }
                let mut leaf_msgs = Vec::with_capacity(leaf.bitmap.count_ones());
                for idx in leaf.bitmap.active_indices() {
                    let Ok(pos) = self.root_active.binary_search(&idx) else {
                        return false;
                    };
                    leaf_msgs.push(root_msgs[pos]);
                }
                let leaf_mode = SigningMode::PerSignerMessages(&leaf_msgs);
                verify_shard_batch(
                    self.pks,
                    self.committee_root,
                    self.profile,
                    &leaf_mode,
                    leaf,
                )
            }
        }
    }

    fn verify_node(&self, node: &MergeNode, rem_depth: usize) -> bool {
        match node {
            MergeNode::Leaf(leaf) => self.verify_leaf(leaf),
            MergeNode::Branch {
                bitmap,
                left,
                right,
            } => {
                rem_depth > 0
                    && MergeNode::canonical_union(left, right).as_ref() == Some(bitmap)
                    && self.verify_node(left, rem_depth - 1)
                    && self.verify_node(right, rem_depth - 1)
            }
        }
    }
}

fn build_merge_tree(mut layer: Vec<MergeNode>) -> Result<MergeNode, HemAggError> {
    let mut depth = 0usize;
    while layer.len() > 1 {
        depth += 1;
        if depth > MAX_MERGE_TREE_DEPTH {
            return Err(HemAggError::TreeDepthExceeded);
        }
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        let mut iter = layer.into_iter();
        while let Some(left) = iter.next() {
            match iter.next() {
                Some(right) => next.push(MergeNode::branch(left, right)?),
                None => next.push(left),
            }
        }
        layer = next;
    }
    layer.pop().ok_or(HemAggError::EmptySigners)
}

// ============================================================================
// Public Top-Level Aggregation, Merging, and Verification API
// ============================================================================

/// Non-interactively aggregate $K \ge 1$ valid hash-based signatures (`JortsPoseidon2` or
/// `CorduroyPoseidon2`) from active committee members marked in `bitmap`.
pub fn aggregate_signatures(
    pks: &[ValidatorPublicKey],
    bitmap: &SignerBitmap,
    mode: &SigningMode<'_>,
    sigs: &[ValidatorSignature],
    blinding_seed: [u8; 32],
) -> Result<HemAggregatedProof, HemAggError> {
    let first_active = bitmap.first_active().ok_or(HemAggError::EmptySigners)?;
    if pks.len() != bitmap.num_validators() as usize {
        return Err(HemAggError::CommitteeMismatch);
    }
    let cfg = HemAggConfig::default_for(pks[first_active].profile, blinding_seed);
    aggregate_signatures_with_config(pks, bitmap, mode, sigs, &cfg)
}

/// Non-interactively aggregate $K \ge 1$ signatures using explicit shard and batch sizing.
pub fn aggregate_signatures_with_config(
    pks: &[ValidatorPublicKey],
    bitmap: &SignerBitmap,
    mode: &SigningMode<'_>,
    sigs: &[ValidatorSignature],
    cfg: &HemAggConfig,
) -> Result<HemAggregatedProof, HemAggError> {
    let active = bitmap.active_indices();
    if active.is_empty() {
        return Err(HemAggError::EmptySigners);
    }
    if pks.len() != bitmap.num_validators() as usize {
        return Err(HemAggError::CommitteeMismatch);
    }
    if sigs.len() != active.len() {
        return Err(HemAggError::SignatureCountMismatch);
    }
    if let SigningMode::PerSignerMessages(ms) = mode {
        if ms.len() != active.len() {
            return Err(HemAggError::MessageCountMismatch);
        }
    }

    let profile = pks[active[0]].profile;
    if cfg.max_signers_per_shard == 0
        || cfg.max_signers_per_shard > max_shard_signers(profile)
        || cfg.max_shards_per_batch == 0
        || cfg.max_shards_per_batch > MAX_BATCH_POLYS
    {
        return Err(HemAggError::InvalidShardConfig);
    }
    if !validate_unique_active_committee(pks, bitmap, profile) {
        return Err(HemAggError::DuplicateValidatorOrProfileMismatch);
    }

    let committee_root = compute_committee_root(pks);
    let num_validators = bitmap.num_validators();

    let slots_for = |signers: usize| signers.next_power_of_two().max(2);
    let mut batches: Vec<Vec<u32>> = Vec::new();
    for chunk in active.chunks(cfg.max_signers_per_shard) {
        match batches.last_mut() {
            Some(batch)
                if batch.len() < cfg.max_shards_per_batch
                    && slots_for(batch[0] as usize) == slots_for(chunk.len()) =>
            {
                batch.push(chunk.len() as u32);
            }
            _ => batches.push(alloc::vec![chunk.len() as u32]),
        }
    }

    let mut leaves = Vec::with_capacity(batches.len());
    let mut start = 0usize;
    for (batch_idx, shard_signer_counts) in batches.iter().enumerate() {
        let end = start
            + shard_signer_counts
                .iter()
                .map(|&c| c as usize)
                .sum::<usize>();
        let batch_bitmap = SignerBitmap::from_active_indices(num_validators, &active[start..end])
            .ok_or(HemAggError::OverlappingSigners)?;
        let mut seed_in = [0u8; 40];
        seed_in[0..32].copy_from_slice(&cfg.blinding_seed);
        seed_in[32..40].copy_from_slice(&(batch_idx as u64).to_le_bytes());
        let batch_seed = sponge::cshake256_32(b"QSAG.BATCH.BLIND/v4", &seed_in);

        let batch_msgs;
        let batch_mode = match mode {
            SigningMode::SharedMessage(msg) => SigningMode::SharedMessage(msg),
            SigningMode::PerSignerMessages(ms) => {
                batch_msgs = &ms[start..end];
                SigningMode::PerSignerMessages(batch_msgs)
            }
        };
        let leaf = arithmetize::prove_shard_batch_with_config(
            pks,
            &committee_root,
            &batch_bitmap,
            shard_signer_counts,
            &batch_mode,
            &sigs[start..end],
            &HemAggConfig {
                blinding_seed: batch_seed,
                ..cfg.clone()
            },
        )
        .ok_or(HemAggError::InvalidIndividualSignature)?;
        leaves.push(MergeNode::Leaf(Box::new(leaf)));
        start = end;
    }

    Ok(HemAggregatedProof {
        profile,
        committee_root,
        root: build_merge_tree(leaves)?,
    })
}

/// Join two valid `HemAggregatedProof`s over the same validator committee `pks` into one proof
/// for the union of their signers, strictly rejecting overlapping `SignerBitmap`s.
pub fn merge_aggregates(
    pks: &[ValidatorPublicKey],
    merged_mode: &SigningMode<'_>,
    proof_a: &HemAggregatedProof,
    proof_b: &HemAggregatedProof,
) -> Result<HemAggregatedProof, HemAggError> {
    let committee_root = check_mergeable(pks, merged_mode, proof_a, proof_b)?;
    Ok(HemAggregatedProof {
        profile: proof_a.profile,
        committee_root,
        root: MergeNode::branch(proof_a.root.clone(), proof_b.root.clone())?,
    })
}

/// [`merge_aggregates`] taking the two proofs by value.
pub fn merge_aggregates_owned(
    pks: &[ValidatorPublicKey],
    merged_mode: &SigningMode<'_>,
    proof_a: HemAggregatedProof,
    proof_b: HemAggregatedProof,
) -> Result<HemAggregatedProof, HemAggError> {
    let committee_root = check_mergeable(pks, merged_mode, &proof_a, &proof_b)?;
    Ok(HemAggregatedProof {
        profile: proof_a.profile,
        committee_root,
        root: MergeNode::branch(proof_a.root, proof_b.root)?,
    })
}

fn check_mergeable(
    pks: &[ValidatorPublicKey],
    merged_mode: &SigningMode<'_>,
    proof_a: &HemAggregatedProof,
    proof_b: &HemAggregatedProof,
) -> Result<[u8; 32], HemAggError> {
    let regime = proof_a.root.homogeneous_regime(MAX_MERGE_TREE_DEPTH)
        .ok_or(HemAggError::RegimeMismatch)?;
    if proof_b.root.homogeneous_regime(MAX_MERGE_TREE_DEPTH) != Some(regime) {
        return Err(HemAggError::RegimeMismatch);
    }
    if proof_a.profile != proof_b.profile {
        return Err(HemAggError::ProfileMismatch);
    }
    let committee_root = compute_committee_root(pks);
    if proof_a.committee_root != committee_root || proof_b.committee_root != committee_root {
        return Err(HemAggError::CommitteeMismatch);
    }
    let merged_bitmap = proof_a
        .bitmap()
        .union_disjoint(proof_b.bitmap())
        .ok_or(HemAggError::OverlappingSigners)?;

    if !validate_unique_active_committee(pks, &merged_bitmap, proof_a.profile) {
        return Err(HemAggError::DuplicateValidatorOrProfileMismatch);
    }
    let new_depth = 1 + proof_a.root.depth().max(proof_b.root.depth());
    if new_depth > MAX_MERGE_TREE_DEPTH {
        return Err(HemAggError::TreeDepthExceeded);
    }

    let statement = AggStatement {
        pks,
        committee_root: &committee_root,
        profile: proof_a.profile,
        mode: merged_mode,
        root_active: merged_bitmap.active_indices(),
    };
    if !statement.verify_node(&proof_a.root, MAX_MERGE_TREE_DEPTH - 1)
        || !statement.verify_node(&proof_b.root, MAX_MERGE_TREE_DEPTH - 1)
    {
        return Err(HemAggError::InvalidChildProof);
    }
    Ok(committee_root)
}

/// Verify a `HemAggregatedProof` against `pks` and `mode` without ever seeing any individual
/// `ValidatorSignature`. Every leaf must use the same regime meeting the QROM-128 floor.
pub fn verify_aggregate(
    pks: &[ValidatorPublicKey],
    mode: &SigningMode<'_>,
    proof: &HemAggregatedProof,
) -> bool {
    let Some(regime) = proof.root.homogeneous_regime(MAX_MERGE_TREE_DEPTH) else {
        return false;
    };
    regime.meets_qrom_128_floor() && verify_aggregate_with_regime(pks, mode, proof, regime)
}

/// Verify every leaf under exactly the explicitly selected regime, including legacy budgets.
