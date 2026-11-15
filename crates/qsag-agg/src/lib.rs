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
//!
//! Heavy proof batches are admitted before witness allocation. With `std`,
//! `QSAG_PROVER_JOBS` defaults to one active batch process-wide; `QSAG_WORKERS`
//! still controls arithmetic parallelism inside it. Increasing prover jobs trades memory
//! for cross-batch concurrency. This bounds active witnesses, not each witness's byte size;
//! `HemAggConfig::max_shards_per_batch` separately controls joint-batch width.
//!
//! # Zero-knowledge relations
//!
//! [`zk_hem::protocol`] is a separate zero-knowledge argument over the same commitment scheme
//! for relations built from S-box and multiplication rows ([`zk_hem::relation`]). Sumcheck
//! masks and companion words are committed with the witness, and WHIR opens only their blend.
//! [`zk_hem::blind_vc`] and [`zk_hem::multisig`] are the two relations defined on it. Aggregate
//! proofs above are not zero-knowledge and do not use it.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod arithmetize;
pub mod field;
pub mod pcs;
#[cfg(feature = "std")]
mod pool;
pub mod recursive;
pub use recursive::{
    HIERARCHICAL_HEM_WIRE_MAGIC, HierarchicalHemAggregate, MAX_HIERARCHY_SHARDS,
    OuterHemChainProof, PreparedPolicyRegistry, SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC,
    ShardHemBatch, ShardHemPolicy, ShardHemSummary, ShardHemWitness,
    SuccinctHierarchicalHemAggregate, VerifiedHierarchicalHemEvidence,
    check_hierarchical_hem_commitment, check_hierarchical_hem_commitment_with_regime,
    checked_sum_usize, compact_summary_chain_digest, compress_verified_hierarchical_hem,
    compress_hierarchical_hem_evidence, prove_hierarchical_hem_prepared,
    compute_framed_message_digest,
    compute_policy_registry_root, encode_policy_registry,
    hierarchical_hem_message, prove_hierarchical_hem, prove_succinct_hierarchical_hem,
    verify_hierarchical_hem, verify_hierarchical_hem_evidence,
    verify_hierarchical_hem_evidence_prepared, verify_hierarchical_hem_prepared,
    verify_succinct_hierarchical_hem, verify_succinct_hierarchical_hem_prepared,
    verify_succinct_hierarchical_hem_with_regime,
};
pub mod recursion_census;
pub mod recursive_fold;
#[cfg(feature = "std")]
mod prover_admission;
#[cfg(feature = "std")]
use prover_admission::prover_parallel_jobs;
pub mod sig;
pub mod sponge;
pub mod trace;
pub mod zk_hem;

use alloc::boxed::Box;
use alloc::vec::Vec;

/// A scoped result is either computed by a permitted worker or on the caller.
#[cfg(feature = "std")]
pub(crate) enum ScopedWorker<'scope, T> {
    Spawned(std::thread::ScopedJoinHandle<'scope, T>),
    Inline(T),
}

#[cfg(feature = "std")]
impl<T> ScopedWorker<'_, T> {
    fn join(self) -> std::thread::Result<T> {
        match self {
            Self::Spawned(handle) => handle.join(),
            Self::Inline(value) => Ok(value),
        }
    }
}

/// Bound all nested arithmetic, proving, and verification kernels by the same
/// permit counter. Retain the closure if the OS refuses to create a thread.
#[cfg(feature = "std")]
pub(crate) fn spawn_bounded<'scope, 'env, F, T>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    f: F,
) -> ScopedWorker<'scope, T>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    let Some(permit) = try_acquire_worker_permit() else {
        return ScopedWorker::Inline(f());
    };
    let job = std::sync::Arc::new(std::sync::Mutex::new(Some(f)));
    let worker_job = std::sync::Arc::clone(&job);
    match std::thread::Builder::new().stack_size(1024 * 1024).spawn_scoped(scope, move || {
        let _permit = permit;
        let f = worker_job
            .lock()
            .expect("worker job lock")
            .take()
            .expect("worker job");
        f()
    }) {
        Ok(handle) => ScopedWorker::Spawned(handle),
        Err(_) => {
            let f = job
                .lock()
                .expect("worker job lock")
                .take()
                .expect("worker job");
            ScopedWorker::Inline(f())
        }
    }
}

/// Preserve a worker's original panic payload rather than replacing it at join.
#[cfg(feature = "std")]
fn join_worker<T>(handle: ScopedWorker<'_, T>) -> T {
    match handle.join() {
        Ok(value) => value,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

/// Dynamic worker-limit override (`0` = unrestricted up to `base_parallel_workers()`).
#[cfg(feature = "std")]
static WORKER_LIMIT_OVERRIDE: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

#[cfg(feature = "std")]
#[inline]
pub(crate) fn base_parallel_workers() -> usize {
    static WORKERS: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *WORKERS.get_or_init(|| {
        let available = std::thread::available_parallelism()
            .map(usize::from)
            .unwrap_or(1)
            .max(1);
        std::env::var("QSAG_WORKERS")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|&workers| workers > 0)
            .map_or(available, |workers| workers.min(available))
    })
}

/// Cached worker budget (`1..=available_parallelism`), optionally restricted by `QSAG_WORKERS` or
/// [`with_worker_limit`].
#[cfg(feature = "std")]
#[inline]
pub(crate) fn parallel_workers() -> usize {
    let base = base_parallel_workers();
    let cap = WORKER_LIMIT_OVERRIDE.load(std::sync::atomic::Ordering::Relaxed);
    if cap == 0 { base } else { base.min(cap) }
}

/// Execute `f` with `qsag-agg` worker concurrency clamped to `max_workers.max(1)` (for example
/// `max_workers = 1` for deterministic single-core latency measurement alongside multi-core runs).
#[cfg(feature = "std")]
pub fn with_worker_limit<R>(max_workers: usize, f: impl FnOnce() -> R) -> R {
    struct ResetGuard(usize);
    impl Drop for ResetGuard {
        fn drop(&mut self) {
            WORKER_LIMIT_OVERRIDE.store(self.0, std::sync::atomic::Ordering::Release);
        }
    }
    let clamped = max_workers.clamp(1, base_parallel_workers());
    let prev = WORKER_LIMIT_OVERRIDE.swap(clamped, std::sync::atomic::Ordering::AcqRel);
    let _guard = ResetGuard(prev);
    f()
}

/// Global counter of active extra OS threads spawned across recursive/nested `qsag-agg` scopes,
/// strictly bounded by `parallel_workers().saturating_sub(1)`.
#[cfg(feature = "std")]
static ACTIVE_EXTRA_WORKERS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// Count of currently active extra OS worker threads spawned in outer `qsag-agg` scopes.
#[cfg(feature = "std")]
#[inline]
pub(crate) fn active_scoped_workers() -> usize {
    ACTIVE_EXTRA_WORKERS.load(std::sync::atomic::Ordering::Relaxed)
}

/// Best-effort count of currently unreserved worker slots (including the calling thread).
#[cfg(feature = "std")]
#[inline]
pub(crate) fn available_worker_budget() -> usize {
    let cap = parallel_workers();
    let busy = active_scoped_workers();
    cap.saturating_sub(busy).max(1)
}

#[cfg(feature = "std")]
pub(crate) struct WorkerPermit(());

#[cfg(feature = "std")]
impl Drop for WorkerPermit {
    fn drop(&mut self) {
        ACTIVE_EXTRA_WORKERS.fetch_sub(1, std::sync::atomic::Ordering::AcqRel);
    }
}

/// Non-blockingly acquire one global extra-worker permit (`None` when budget is saturated).
#[cfg(feature = "std")]
#[inline]
pub(crate) fn try_acquire_worker_permit() -> Option<WorkerPermit> {
    use std::sync::atomic::Ordering;
    let cap = parallel_workers().saturating_sub(1);
    if cap == 0 {
        return None;
    }
    let mut cur = ACTIVE_EXTRA_WORKERS.load(Ordering::Relaxed);
    while cur < cap {
        match ACTIVE_EXTRA_WORKERS.compare_exchange_weak(
            cur,
            cur + 1,
            Ordering::AcqRel,
            Ordering::Relaxed,
        ) {
            Ok(_) => return Some(WorkerPermit(())),
            Err(actual) => cur = actual,
        }
    }
    None
}

/// Partition `items` across at most `parallel_workers()` chunks, running chunk 0 on the caller
/// thread and spawning remaining chunks under `WorkerPermit` + non-panicking `Builder::spawn_scoped`.
#[cfg(all(feature = "std", any(test, feature = "vulkan")))]
pub(crate) fn map_chunks_bounded<'a, T, R, F>(items: &'a [T], f: F) -> Vec<R>
where
    T: Sync,
    R: Send,
    F: Fn(&'a [T]) -> R + Sync,
{
    map_chunks_bounded_with_limit(items, parallel_workers(), f)
}

#[cfg(feature = "std")]
pub(crate) fn map_chunks_bounded_with_limit<'a, T, R, F>(items: &'a [T], max_jobs: usize, f: F) -> Vec<R>
where T: Sync, R: Send, F: Fn(&'a [T]) -> R + Sync,
{
    if items.is_empty() {
        return Vec::new();
    }
    let workers = parallel_workers().min(max_jobs.max(1)).min(items.len());
    if workers <= 1 {
        return alloc::vec![f(items)];
    }
    let chunk = items.len().div_ceil(workers);
    let slices: Vec<&'a [T]> = items.chunks(chunk).collect();
    let f_ref = &f;
    std::thread::scope(|scope| {
        let tails: Vec<_> = slices[1..]
            .iter()
            .map(|&sub| spawn_bounded(scope, move || f_ref(sub)))
            .collect();
        let mut out = Vec::with_capacity(slices.len());
        out.push(f_ref(slices[0]));
        out.extend(tails.into_iter().map(join_worker));
        out
    })
}

/// Largest power-of-two worker count `<= parallel_workers().min(max_units.max(1))`.
#[cfg(feature = "std")]
#[inline]
pub(crate) fn parallel_pow2_workers(max_units: usize) -> usize {
    let cap = parallel_workers().min(max_units.max(1));
    1usize << cap.ilog2()
}

pub use arithmetize::{
    DEFAULT_SHARD_PCS_NUM_VARS, ShardBatchProof, ShardRowProof, compute_signing_mode_digest,
    default_shard_signers, max_shard_signers,
    prove_shard_batch, verify_shard_batch, verify_shard_batch_with_regime,
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
    AggSigProfile, CORDUROY_MAX_STATELESS_SIGS_PER_KEY, Digest4, Digest5, EpochWalSink, SigError,
    SignerBitmap, SigningMode, StatelessBudgetWalSink, ValidatorKeypair,
    ValidatorPublicKey, ValidatorSignature, bytes32_to_limbs56, compute_committee_root,
    limbs56_to_bytes32_canonical, validate_unique_active_committee, verify_individual_signature,
    verify_signature_batch,
};
#[cfg(feature = "std")]
pub use sig::{FsStatelessBudgetWal, FsWalEpochSink};
pub use qsag_core::tsw_baggy::{EpochLatchError, MonotonicEpochLatch, StatefulEpochLatch};
pub use sponge::{FiatShamirTranscript, InstanceBound, RelationBound, Unbound};

/// Canonical 8-byte wire header for [`HemAggregatedProof`] (`v6`: affine monomial `GoldilocksExt4` WHIR).
pub const AGG_WIRE_MAGIC: &[u8; 8] = b"QSAGAGG\x06";

/// Hard upper bound on merge tree depth (`2^16 = 65,536` shard batches).
pub const MAX_MERGE_TREE_DEPTH: usize = 16;

/// Default active signers per `JortsPoseidon2` shard (a `DEFAULT_SHARD_PCS_NUM_VARS`-variable
/// witness). [`max_shard_signers`] is the hard cap.
pub const DEFAULT_MAX_SHARD_SIGNERS_JORTS: usize =
    default_shard_signers(AggSigProfile::JortsPoseidon2);

/// Default active signers per `CorduroyPoseidon2` shard. [`max_shard_signers`] is the hard cap.
pub const DEFAULT_MAX_SHARD_SIGNERS_CORDUROY: usize =
    default_shard_signers(AggSigProfile::CorduroyPoseidon2);

/// Default shards per batch.
pub const DEFAULT_MAX_SHARDS_PER_BATCH: usize = 2;

/// Configuration parameters for [`HemAggregator::aggregate_with_config`] (`aggregate_signatures_with_config`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HemAggConfig {
    /// Query-accounting regime; proofs always use its canonical schedule.
    pub regime: WhirSecurityRegime,
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
            max_signers_per_shard: default_shard_signers(profile),
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
            Self::Leaf(leaf) => (leaf.pcs_opening.common_point_evals.len()
                == leaf.pcs_opening.shifted_evals.len())
            .then_some(leaf.schedule.regime),
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
        let regime = a
            .homogeneous_regime(MAX_MERGE_TREE_DEPTH)
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

    /// Append canonical self-delimiting wire bytes (`AGG_WIRE_MAGIC` header) to `out`.
    pub(crate) fn push_wire_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(AGG_WIRE_MAGIC);
        out.push(self.profile as u8);
        out.extend_from_slice(&self.committee_root);
        self.root.push_bytes(out);
    }

    /// Serialize to canonical self-delimiting wire bytes (`AGG_WIRE_MAGIC` header).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(65_536);
        self.push_wire_bytes(&mut out);
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
    /// The one regime every leaf must use, with its canonical schedule.
    regime: WhirSecurityRegime,
    root_active: Vec<usize>,
}

impl AggStatement<'_> {
    fn verify_leaf(&self, leaf: &ShardBatchProof) -> bool {
        match self.mode {
            SigningMode::SharedMessage(_) => verify_shard_batch_with_regime(
                self.pks,
                self.committee_root,
                self.profile,
                self.mode,
                leaf,
                self.regime,
            ),
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
                verify_shard_batch_with_regime(
                    self.pks,
                    self.committee_root,
                    self.profile,
                    &leaf_mode,
                    leaf,
                    self.regime,
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
                if rem_depth == 0
                    || MergeNode::canonical_union(left, right).as_ref() != Some(bitmap)
                {
                    return false;
                }
                #[cfg(feature = "std")]
                if let Some(permit) = try_acquire_worker_permit() {
                    let right_ref = right.as_ref();
                    let branched = std::thread::scope(|scope| {
                        match std::thread::Builder::new().stack_size(1024 * 1024).spawn_scoped(scope, move || {
                            let _permit = permit;
                            self.verify_node(right_ref, rem_depth - 1)
                        }) {
                            Ok(right_h) => {
                                let left_ok = self.verify_node(left, rem_depth - 1);
                                let right_ok = join_worker(ScopedWorker::Spawned(right_h));
                                Some(left_ok && right_ok)
                            }
                            Err(_) => None,
                        }
                    });
                    if let Some(res) = branched {
                        return res;
                    }
                }
                self.verify_node(left, rem_depth - 1) && self.verify_node(right, rem_depth - 1)
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
    aggregate_signatures_with_committee_root(pks, None, bitmap, mode, sigs, cfg)
}

pub(crate) fn aggregate_signatures_with_committee_root(
    pks: &[ValidatorPublicKey],
    precomputed_committee_root: Option<[u8; 32]>,
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
    if let SigningMode::PerSignerMessages(ms) = mode
        && ms.len() != active.len()
    {
        return Err(HemAggError::MessageCountMismatch);
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

    let committee_root = precomputed_committee_root.unwrap_or_else(|| compute_committee_root(pks));
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

    let mut batch_jobs = Vec::with_capacity(batches.len());
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
        batch_jobs.push((
            start,
            end,
            shard_signer_counts.as_slice(),
            batch_bitmap,
            batch_seed,
        ));
        start = end;
    }

    let prove_one = |(b_start, b_end, shard_signer_counts, batch_bitmap, batch_seed): &(
        usize,
        usize,
        &[u32],
        SignerBitmap,
        [u8; 32],
    )|
     -> Result<MergeNode, HemAggError> {
        let batch_msgs;
        let batch_mode = match mode {
            SigningMode::SharedMessage(msg) => SigningMode::SharedMessage(msg),
            SigningMode::PerSignerMessages(ms) => {
                batch_msgs = &ms[*b_start..*b_end];
                SigningMode::PerSignerMessages(batch_msgs)
            }
        };
        let leaf = arithmetize::prove_shard_batch_with_config(
            pks,
            &committee_root,
            batch_bitmap,
            shard_signer_counts,
            &batch_mode,
            &sigs[*b_start..*b_end],
            &HemAggConfig {
                blinding_seed: *batch_seed,
                ..cfg.clone()
            },
        )
        .ok_or(HemAggError::InvalidIndividualSignature)?;
        Ok(MergeNode::Leaf(Box::new(leaf)))
    };

    #[cfg(feature = "std")]
    let leaves: Vec<MergeNode> = if batch_jobs.len() > 1 && parallel_workers() > 1 {
        let groups: Vec<Result<Vec<MergeNode>, HemAggError>> =
            map_chunks_bounded_with_limit(&batch_jobs, prover_parallel_jobs(), |sub| sub.iter().map(&prove_one).collect());
        let mut flat_leaves = Vec::with_capacity(batch_jobs.len());
        for group in groups {
            flat_leaves.extend(group?);
        }
        flat_leaves
    } else {
        batch_jobs
            .iter()
            .map(prove_one)
            .collect::<Result<Vec<_>, _>>()?
    };

    #[cfg(not(feature = "std"))]
    let leaves: Vec<MergeNode> = batch_jobs
        .iter()
        .map(prove_one)
        .collect::<Result<Vec<_>, _>>()?;

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
    let regime = proof_a
        .root
        .homogeneous_regime(MAX_MERGE_TREE_DEPTH)
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
        regime,
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
/// `ValidatorSignature`. Every leaf must use the default Johnson QROM regime.
pub fn verify_aggregate(
    pks: &[ValidatorPublicKey],
    mode: &SigningMode<'_>,
    proof: &HemAggregatedProof,
) -> bool {
    verify_aggregate_with_regime(pks, mode, proof, WhirSecurityRegime::default())
}

/// Verify every leaf under exactly the explicitly selected QROM-128 regime.
pub fn verify_aggregate_with_regime(
    pks: &[ValidatorPublicKey],
    mode: &SigningMode<'_>,
    proof: &HemAggregatedProof,
    expected_regime: WhirSecurityRegime,
) -> bool {
    verify_aggregate_with_committee_root(pks, None, mode, proof, expected_regime)
}

pub(crate) fn verify_aggregate_with_committee_root(
    pks: &[ValidatorPublicKey],
    precomputed_committee_root: Option<[u8; 32]>,
    mode: &SigningMode<'_>,
    proof: &HemAggregatedProof,
    expected_regime: WhirSecurityRegime,
) -> bool {
    let _phase = crate::profile::span("verify_aggregate");
    if proof.root.homogeneous_regime(MAX_MERGE_TREE_DEPTH) != Some(expected_regime) {
        return false;
    }
    if pks.len() != proof.bitmap().num_validators() as usize {
        return false;
    }
    if !validate_unique_active_committee(pks, proof.bitmap(), proof.profile) {
        return false;
    }
    let committee_root = precomputed_committee_root.unwrap_or_else(|| compute_committee_root(pks));
    if proof.committee_root != committee_root {
        return false;
    }
    let statement = AggStatement {
        pks,
        committee_root: &committee_root,
        profile: proof.profile,
        mode,
        regime: expected_regime,
        root_active: proof.bitmap().active_indices(),
    };
    statement.verify_node(&proof.root, MAX_MERGE_TREE_DEPTH)
}

impl core::fmt::Display for HemAggError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for HemAggError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetize::{
        ROW_SUMCHECK_COEFFS, build_shift_tables_ext4, eval_eq_not_last_ext4,
        eval_shift_kernel_ext4, interpolate_deg8_from_evals_ext4,
    };
    use crate::field::{mle_eval_base_at_ext4, mle_eval_ext4};
    use crate::pcs::{
        whir_commit, whir_commit_batch_owned, whir_open, whir_open_batch, whir_verify,
        whir_verify_batch,
    };
    use alloc::vec;

    fn make_seed(tag: u64) -> [u8; 32] {
        let mut s = [0u8; 32];
        s[0..8].copy_from_slice(&tag.to_le_bytes());
        s[8..16].copy_from_slice(&(tag.wrapping_mul(0x9E37_79B9_7F4A_7C15)).to_le_bytes());
        s
    }

    fn fresh_test_transcript() -> FiatShamirTranscript<InstanceBound> {
        FiatShamirTranscript::new()
            .bind_relation(b"TEST.P0_01", b"v5", &whir_stage_schedule(12))
            .bind_instance(&[b"inst"])
    }

    fn gen_jorts_kp(tag: u64, idx: u32) -> ValidatorKeypair {
        ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &make_seed(tag), idx)
    }

    fn ext4_sample(a: u64, b: u64, c: u64, d: u64) -> GoldilocksExt4 {
        GoldilocksExt4::from_limbs([
            Goldilocks::from_u64_reduced(a),
            Goldilocks::from_u64_reduced(b),
            Goldilocks::from_u64_reduced(c),
            Goldilocks::from_u64_reduced(d),
        ])
    }

    #[test]
    fn test_shift_kernel_mle_and_deg8_interpolation() {
        let tau = [
            ext4_sample(17, 42, 101, 203),
            ext4_sample(99, 7, 307, 409),
            ext4_sample(123456, 654321, 777777, 888888),
            ext4_sample(5, 11, 13, 19),
        ];
        let rx = [
            ext4_sample(31, 13, 29, 37),
            ext4_sample(77, 88, 91, 97),
            ext4_sample(9, 3, 27, 81),
            ext4_sample(50, 60, 70, 80),
        ];

        let (_, not_last_tbl, shift_tbl) = build_shift_tables_ext4(&tau);
        assert_eq!(
            eval_eq_not_last_ext4(&tau, &rx),
            mle_eval_ext4(&not_last_tbl, &rx)
        );
        assert_eq!(
            eval_shift_kernel_ext4(&tau, &rx),
            mle_eval_ext4(&shift_tbl, &rx)
        );

        let expected_coeffs: [GoldilocksExt4; ROW_SUMCHECK_COEFFS] = core::array::from_fn(|k| {
            ext4_sample(
                (k as u64 + 3) * 1009,
                (k as u64 + 7) * 2027,
                (k as u64 + 11) * 3037,
                (k as u64 + 13) * 4049,
            )
        });
        let poly = RoundPolyExt4 {
            coeffs: expected_coeffs.to_vec(),
        };
        let evals: [GoldilocksExt4; ROW_SUMCHECK_COEFFS] =
            core::array::from_fn(|t| poly.evaluate(GoldilocksExt4::from_u64(t as u64)));
        let got_coeffs = interpolate_deg8_from_evals_ext4(&evals);
        assert_eq!(got_coeffs, expected_coeffs);
    }

    #[test]
    fn test_p0_01_whir_interleaved_soundness_and_forgery_rejection() {
        let num_vars = 12usize;
        let evals: Vec<Goldilocks> = (0..(1usize << num_vars))
            .map(|i| Goldilocks::from_u64_reduced((i as u64).wrapping_mul(7919).wrapping_add(13)))
            .collect();
        let salt_seed = make_seed(101);
        let (comm, state) = whir_commit(&evals, &salt_seed);

        let point: Vec<GoldilocksExt4> = (0..num_vars)
            .map(|k| {
                ext4_sample(
                    (k as u64 + 1) * 31337,
                    (k as u64 + 5) * 4242,
                    (k as u64 + 9) * 1717,
                    (k as u64 + 13) * 9001,
                )
            })
            .collect();
        let honest_val = mle_eval_base_at_ext4(&evals, &point);

        let mut tr_p = fresh_test_transcript();
        let proof = whir_open(&state, &point, honest_val, &mut tr_p);

        let mut tr_v = fresh_test_transcript();
        assert!(whir_verify(
            &comm, num_vars, &point, honest_val, &proof, &mut tr_v
        ));

        let mut wrong_comm0 = comm;
        wrong_comm0.root[0] ^= 0x80;
        let mut tr_wrong_c0 = fresh_test_transcript();
        assert!(!whir_verify(
            &wrong_comm0,
            num_vars,
            &point,
            honest_val,
            &proof,
            &mut tr_wrong_c0
        ));

        let forged_val = honest_val + GoldilocksExt4::ONE;
        let mut tr_bad = fresh_test_transcript();
        assert!(!whir_verify(
            &comm,
            num_vars,
            &point,
            forged_val,
            &proof,
            &mut tr_bad
        ));

        let mut mutated_proof = proof.clone();
        assert!(!mutated_proof.folded_layers.is_empty());
        mutated_proof.folded_layers[0].commitment.root[0] ^= 0x01;
        let mut tr_mut = fresh_test_transcript();
        assert!(!whir_verify(
            &comm,
            num_vars,
            &point,
            honest_val,
            &mutated_proof,
            &mut tr_mut
        ));
    }

    #[test]
    fn test_lean_kat_vectors_conformance() {
        use crate::sponge::{
            cshake256_32, poseidon2_hash32, poseidon2_perm12, poseidon2_sbox7, shake256_into,
        };

        fn to_hex(bytes: &[u8]) -> alloc::string::String {
            const HEX: &[u8; 16] = b"0123456789abcdef";
            let mut s = alloc::string::String::with_capacity(bytes.len() * 2);
            for &b in bytes {
                s.push(HEX[(b >> 4) as usize] as char);
                s.push(HEX[(b & 0x0F) as usize] as char);
            }
            s
        }

        let kat_json = include_str!("../../../tests/kat_vectors.json");
        assert!(kat_json.contains("\"generator\": \"lean-4.35.0-Qsag\""));

        let mut out32 = [0u8; 32];
        shake256_into(&[], &mut out32);
        let h_empty = to_hex(&out32);
        assert_eq!(
            h_empty,
            "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
        );
        assert!(kat_json.contains(&h_empty));

        shake256_into(b"abc", &mut out32);
        let h_abc = to_hex(&out32);
        assert_eq!(
            h_abc,
            "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739"
        );
        assert!(kat_json.contains(&h_abc));

        let seq64_in: Vec<u8> = (0..64u8).collect();
        let mut out64 = [0u8; 64];
        shake256_into(&seq64_in, &mut out64);
        let h_seq64 = to_hex(&out64);
        assert_eq!(
            h_seq64,
            "755e8863a2b2bc067f51c1637a71c819d524dc37c17ba7a29c6ee3767c996a49e39d3f402bd2452d01f3977dea88467ac2aff4207f8a70ca32a3c345123a5875"
        );
        assert!(kat_json.contains(&h_seq64));

        let h_cshake = to_hex(&cshake256_32(
            b"QSAG.KAT.v1",
            b"quantum-signature-aggregation",
        ));
        assert_eq!(
            h_cshake,
            "fc3c9ce4073822b1cc20a0c4ad065ac386d7cbcbe256fb23ac97bd00e8c924eb"
        );
        assert!(kat_json.contains(&h_cshake));

        assert_eq!(crate::field::GOLDILOCKS_PRIME, 18446744069414584321);
        let ga = Goldilocks::from_u64_reduced(0xFFFF_FFFF_0000_0000);
        let gb = Goldilocks::from_u64_reduced(0x1234_5678_9ABC_DEF0);
        assert_eq!((ga + gb).to_canonical_u64(), 1311768467463790319);
        assert_eq!((ga - gb).to_canonical_u64(), 17134975601950794000);
        assert_eq!((ga * gb).to_canonical_u64(), 17134975601950794001);
        assert_eq!(gb.inv().to_canonical_u64(), 14736413637906284881);
        assert_eq!(poseidon2_sbox7(gb).to_canonical_u64(), 11853639751010147186);

        let ea = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(0xCAFE_BABE_1234_5678),
            Goldilocks::from_u64_reduced(0x0FED_CBA9_8765_4321),
        );
        let eb = GoldilocksExt2::new(
            Goldilocks::from_u64_reduced(0x1122_3344_5566_7788),
            Goldilocks::from_u64_reduced(0x99AA_BBCC_DDEE_FF00),
        );
        let emul = ea * eb;
        assert_eq!(emul.c0.to_canonical_u64(), 18303635595367899322);
        assert_eq!(emul.c1.to_canonical_u64(), 878009080216790377);
        let einv = ea.inv().unwrap();
        assert_eq!(einv.c0.to_canonical_u64(), 16277753096187779739);
        assert_eq!(einv.c1.to_canonical_u64(), 5492336065856852107);

        let mut p_zero = [Goldilocks::ZERO; 12];
        poseidon2_perm12(&mut p_zero);
        let expected_zero: [u64; 12] = [
            17528629447354354351,
            5014055130248055117,
            10679077121839038553,
            431078547345611051,
            7807009921345120310,
            2413869689279715014,
            11875300792986830377,
            1872634884137602556,
            15069512080271275672,
            14253608580209913153,
            14550618143248480092,
            107036164978639472,
        ];
        for i in 0..12 {
            assert_eq!(p_zero[i].to_canonical_u64(), expected_zero[i]);
            assert!(kat_json.contains(&alloc::format!("\"{}\"", expected_zero[i])));
        }

        let mut p_seq: [Goldilocks; 12] =
            core::array::from_fn(|i| Goldilocks::from_u64_reduced(i as u64));
        poseidon2_perm12(&mut p_seq);
        let expected_seq: [u64; 12] = [
            13782584570844608145,
            13136387643152332171,
            7171133015474200819,
            7643370872200861694,
            14144755201299840503,
            16470027036684692562,
            1748465969625202405,
            1718729118078964347,
            6141020819996733037,
            16322330185628708898,
            11650380702735067362,
            2734959974607798415,
        ];
        for i in 0..12 {
            assert_eq!(p_seq[i].to_canonical_u64(), expected_seq[i]);
        }

        assert_eq!(
            to_hex(&poseidon2_hash32(&[])),
            "b6a8416a0036177c167477c74bfdca917b0d73c8ba8fcf42a2a1c609dc25b0a2"
        );
        assert_eq!(
            to_hex(&poseidon2_hash32(&[0x00])),
            "744f0f5f11f8caf02d7ec0b559c1b9a162a7c726d68d04166122df851003aa68"
        );
        assert_eq!(
            to_hex(&poseidon2_hash32(&[0x01, 0x02, 0x03])),
            "954faba00031a63ccc79f1476682181123a272f9c2fe782e126ffe1b6a51b2e3"
        );
        assert_eq!(
            to_hex(&poseidon2_hash32(b"qsag-poseidon2-kat")),
            "e49c8c937c0a64c5676aa807fec4fab7d482111a028beb0fdb2ec1ee9432ece5"
        );

        let mut abc_digest = [0u8; 32];
        shake256_into(b"abc", &mut abc_digest);
        let d5 = bytes32_to_limbs56(&abc_digest);
        let expected_d5: [u64; 5] = [
            47393432425345864,
            55182325602327671,
            69858870164278545,
            15739046436200945,
            962038759,
        ];
        for i in 0..5 {
            assert_eq!(d5[i].to_canonical_u64(), expected_d5[i]);
            assert!(kat_json.contains(&alloc::format!("\"{}\"", expected_d5[i])));
        }
    }

    #[test]
    #[cfg(feature = "std")]
    fn nested_workers_fall_back_when_budget_is_exhausted() {
        let mut permits = Vec::new();
        while let Some(permit) = try_acquire_worker_permit() {
            permits.push(permit);
        }
        std::thread::scope(|scope| {
            let result = spawn_bounded(scope, || {
                std::thread::scope(|inner| join_worker(spawn_bounded(inner, || 42)))
            });
            assert_eq!(join_worker(result), 42);
        });
        drop(permits);
        let inputs: Vec<usize> = (0..257).collect();
        let output: Vec<usize> =
            map_chunks_bounded(&inputs, |xs| xs.iter().map(|x| x * x).collect::<Vec<_>>())
                .into_iter()
                .flatten()
                .collect();
        assert_eq!(output, inputs.iter().map(|x| x * x).collect::<Vec<_>>());
    }

    #[test]
    #[cfg(feature = "std")]
    fn merge_tree_verification_respects_global_worker_budget() {
        let msg = b"bounded-worker-merge-tree-test";
        let mode = SigningMode::SharedMessage(msg);
        let n = 16usize;
        let (pks, sigs) = bench_keys_and_sigs(AggSigProfile::JortsPoseidon2, n, msg);

        // Build 8 disjoint 2-signer leaves and fold them into a balanced 3-level merge tree.
        let mut level: Vec<QsagAggregateProof> = (0..8)
            .map(|leaf_idx| {
                let idxs = [2 * leaf_idx, 2 * leaf_idx + 1];
                let bm = SignerBitmap::from_active_indices(n as u32, &idxs).unwrap();
                aggregate_signatures(
                    &pks,
                    &bm,
                    &mode,
                    &sigs[2 * leaf_idx..2 * leaf_idx + 2],
                    make_seed(200 + leaf_idx as u64),
                )
                .unwrap()
            })
            .collect();
        while level.len() > 1 {
            let mut next = Vec::with_capacity(level.len() / 2);
            for pair in level.chunks(2) {
                next.push(merge_aggregates(&pks, &mode, &pair[0], &pair[1]).unwrap());
            }
            level = next;
        }
        let merged = level.pop().unwrap();
        assert!(verify_aggregate(&pks, &mode, &merged));
    }

    #[test]
    fn test_p0_04_and_p1_02_epoch_latch_and_limbs56_bijection() {
        let all_ff = [0xFFu8; 32];
        let limbs = bytes32_to_limbs56(&all_ff);
        let roundtrip = limbs56_to_bytes32_canonical(&limbs).expect("canonical 56-bit limbs");
        assert_eq!(roundtrip, all_ff);

        let mut kp = gen_jorts_kp(7, 0);
        let dbg_str = alloc::format!("{:?}", kp);
        assert!(dbg_str.contains("[REDACTED]"));

        let sig1 = kp
            .sign_stateful_for_unit_test(b"block-proposal-A", 0)
            .expect("epoch 0 ok");
        let sig1_retry = kp
            .sign_stateful_for_unit_test(b"block-proposal-A", 0)
            .expect("crash-retry on identical (epoch, msg) must be idempotent");
        assert_eq!(sig1, sig1_retry);
        assert_eq!(
            kp.sign_stateful_for_unit_test(b"equivocating-block-B", 0),
            Err(SigError::EpochReuseDifferentMessage)
        );
        let _sig2 = kp
            .sign_stateful_for_unit_test(b"epoch-2", 2)
            .expect("advance to epoch 2");
        assert_eq!(
            kp.sign_stateful_for_unit_test(b"rewind-to-epoch-1", 1),
            Err(SigError::EpochMonotonicityViolation)
        );

        #[cfg(feature = "std")]
        {
            let wal_path = std::env::temp_dir().join(std::format!(
                "qsag_agg_test_epoch_wal_{}.bin",
                std::process::id()
            ));
            let _ = std::fs::remove_file(&wal_path);
            let mut kp_wal = gen_jorts_kp(99, 0);
            let pk_root_bytes = sig::digest4_to_bytes(&kp_wal.pk.pk_root);
            let (mut sink, init_state) =
                FsWalEpochSink::create_new_for_fresh_key(&wal_path, &pk_root_bytes, [0x57; 32])
                    .unwrap();
            assert!(init_state.is_none());
            let sig_w = kp_wal
                .sign_stateful_with_wal(b"wal-persisted-msg", 3, &mut sink)
                .unwrap();

            drop(sink);
            let (mut sink2, recovered) =
                FsWalEpochSink::open_or_recover(&wal_path, &pk_root_bytes, [0x57; 32]).unwrap();
            let mut kp_restarted = ValidatorKeypair::from_master_seed_with_wal(
                AggSigProfile::JortsPoseidon2,
                &make_seed(99),
                0,
                &sink2,
            )
            .unwrap();
            assert_eq!(kp_restarted.next_unused_epoch(), 4);
            let (next_ep, latched_ep, mu_b) = recovered.expect("WAL must recover latched epoch");
            kp_restarted
                .restore_from_wal(next_ep, latched_ep, mu_b)
                .unwrap();
            assert!(
                kp_restarted
                    .restore_from_wal(next_ep - 1, latched_ep - 1, mu_b)
                    .is_err()
            );
            assert!(
                kp_restarted
                    .restore_from_wal(next_ep, latched_ep, [0xff; 32])
                    .is_err()
            );
            assert_eq!(
                kp_restarted.sign_stateful_with_wal(b"equivocating-after-crash", 3, &mut sink2),
                Err(SigError::EpochReuseDifferentMessage)
            );
            assert_eq!(
                kp_restarted
                    .sign_stateful_with_wal(b"wal-persisted-msg", 3, &mut sink2)
                    .unwrap(),
                sig_w
            );
            let _ = std::fs::remove_file(&wal_path);
        }
    }

    #[test]
    fn test_jorts_aggregate_merge_and_adversarial_tampering() {
        let mut kps: Vec<ValidatorKeypair> = (0..8u32).map(|i| gen_jorts_kp(1000, i)).collect();
        let pks: Vec<ValidatorPublicKey> = kps.iter().map(|kp| kp.pk).collect();
        let msg = b"consensus-slot-42-finality-vote";

        let sigs_a = vec![
            kps[0].sign_stateful_for_unit_test(msg, 0).unwrap(),
            kps[1].sign_stateful_for_unit_test(msg, 1).unwrap(),
        ];
        let sigs_b = vec![
            kps[2].sign_stateful_for_unit_test(msg, 0).unwrap(),
            kps[3].sign_stateful_for_unit_test(msg, 2).unwrap(),
        ];

        let bm_a = SignerBitmap::from_active_indices(8, &[0, 1]).unwrap();
        let bm_b = SignerBitmap::from_active_indices(8, &[2, 3]).unwrap();
        let mode = SigningMode::SharedMessage(msg);

        let proof_a =
            aggregate_signatures(&pks, &bm_a, &mode, &sigs_a, make_seed(9001)).expect("agg A");
        let proof_b =
            aggregate_signatures(&pks, &bm_b, &mode, &sigs_b, make_seed(9002)).expect("agg B");

        assert!(verify_aggregate(&pks, &mode, &proof_a));
        assert!(verify_aggregate(&pks, &mode, &proof_b));

        let merged = merge_aggregates(&pks, &mode, &proof_a, &proof_b).expect("disjoint merge");
        assert_eq!(merged.num_signers(), 4);
        assert!(verify_aggregate(&pks, &mode, &merged));

        let wire = merged.to_bytes();
        let parsed = QsagAggregateProof::from_bytes_canonical(&wire).expect("canonical wire");
        assert_eq!(parsed, merged);
        assert!(verify_aggregate(&pks, &mode, &parsed));

        let mut trailing = wire.clone();
        trailing.push(0x00);
        assert_eq!(
            QsagAggregateProof::from_bytes_canonical(&trailing),
            Err(AggError::MalformedWireBytes)
        );

        assert!(!verify_aggregate(
            &pks,
            &SigningMode::SharedMessage(b"forged-slot-42"),
            &merged
        ));

        let bm_overlap = SignerBitmap::from_active_indices(8, &[1, 2]).unwrap();
        let sigs_ov = vec![sigs_a[1].clone(), sigs_b[0].clone()];
        let proof_ov =
            aggregate_signatures(&pks, &bm_overlap, &mode, &sigs_ov, make_seed(9003)).unwrap();
        assert_eq!(
            merge_aggregates(&pks, &mode, &proof_a, &proof_ov),
            Err(AggError::OverlappingSigners)
        );

        let mut dup_pks = pks.clone();
        dup_pks[1] = dup_pks[0];
        assert_eq!(
            aggregate_signatures(&dup_pks, &bm_a, &mode, &sigs_a, make_seed(9004)),
            Err(AggError::DuplicateValidatorOrProfileMismatch)
        );

        if let MergeNode::Leaf(mut leaf_box) = proof_a.root.clone() {
            leaf_box.shards[0].col_evals[0] += GoldilocksExt4::ONE;
            let tampered = QsagAggregateProof {
                profile: proof_a.profile,
                committee_root: proof_a.committee_root,
                root: MergeNode::Leaf(leaf_box),
            };
            assert!(!verify_aggregate(&pks, &mode, &tampered));
        }
    }

    #[test]
    fn test_aggregate_security_regimes_end_to_end() {
        let mut keys: Vec<_> = (0..2).map(|i| gen_jorts_kp(709, i)).collect();
        let pks: Vec<_> = keys.iter().map(|k| k.pk).collect();
        let msg = b"regime integration";
        let sigs: Vec<_> = keys
            .iter_mut()
            .map(|k| k.sign_stateful_for_unit_test(msg, 0).unwrap())
            .collect();
        for sig in &sigs {
            assert_eq!(
                ValidatorSignature::from_bytes_canonical(sig.profile, &sig.to_bytes()).unwrap(),
                *sig
            );
        }
        let bitmap = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
        let mode = SigningMode::SharedMessage(msg);
        let regime = WhirSecurityRegime::BciksJohnsonQrom128;
        let wrong = WhirSecurityRegime::BciksJohnsonClassical128;
        let mut cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, make_seed(710));
        cfg.regime = regime;
        let start = std::time::Instant::now();
        let proof =
            HemAggregator::aggregate_with_config(&pks, &bitmap, &mode, &sigs, &cfg).unwrap();
        let prove = start.elapsed();
        let wire = proof.to_bytes();
        assert_eq!(
            HemAggregatedProof::from_bytes_canonical(&wire).unwrap(),
            proof
        );
        let start = std::time::Instant::now();
        assert!(HemAggregator::verify_with_regime(
            &pks, &mode, &proof, regime
        ));
        std::eprintln!(
            "aggregate {regime:?}: K=2, bytes={}, prove={prove:?}, verify={:?}",
            wire.len(),
            start.elapsed()
        );
        assert!(HemAggregator::verify(&pks, &mode, &proof));
        assert!(verify_aggregate(&pks, &mode, &proof));
        assert!(!verify_aggregate_with_regime(&pks, &mode, &proof, wrong));

        // Mutating the serialized schedule's regime tag to retired capacity tags (`0`, `1`, `3`),
        // classical-only Johnson (`2`), another regime whose query table differs (`5`), or
        // unknown (`9`) must fail closed during canonical decode.
        let leaf = leaf_of(&proof);
        let regime_offset =
            41 + 1 + leaf.bitmap.to_bytes().len() + 1 + 4 * leaf.shard_signer_counts.len();
        assert_eq!(wire[regime_offset], regime as u8);
        for bad_tag in [0u8, 1, 2, 3, 5, 9] {
            let mut mutated = wire.clone();
            mutated[regime_offset] = bad_tag;
            assert_eq!(
                HemAggregatedProof::from_bytes_canonical(&mutated),
                Err(HemAggError::MalformedWireBytes)
            );
        }

        // Both prover (`aggregate_with_config`) and verifier/wire-decoder must refuse
        // classical-only Johnson (`BciksJohnsonClassical128`, fails QROM-128 floor).
        let mut classical_cfg = cfg.clone();
        classical_cfg.regime = wrong;
        assert!(
            HemAggregator::aggregate_with_config(&pks, &bitmap, &mode, &sigs, &classical_cfg)
                .is_err()
        );
        let mut classical_leaf = leaf_of(&proof);
        classical_leaf.schedule = wrong.schedule(
            classical_leaf.pcs_opening.opening.fold_sumcheck_polys.len()
                + classical_leaf.schedule.early_stop_vars,
        );
        let classical_proof = with_leaf(&proof, classical_leaf);
        assert!(!HemAggregator::verify(&pks, &mode, &classical_proof));
        assert!(!verify_aggregate_with_regime(
            &pks,
            &mode,
            &classical_proof,
            wrong
        ));
        assert!(!verify_aggregate_with_regime(
            &pks,
            &mode,
            &classical_proof,
            regime
        ));
        assert_eq!(
            HemAggregatedProof::from_bytes_canonical(&classical_proof.to_bytes()),
            Err(HemAggError::MalformedWireBytes)
        );

        let mut unframed = leaf_of(&proof);
        unframed
            .pcs_opening
            .common_point_evals
            .push(GoldilocksExt4::ONE);
        let unframed = with_leaf(&proof, unframed);
        assert!(!verify_aggregate_with_regime(
            &pks, &mode, &unframed, regime
        ));
        assert!(std::panic::catch_unwind(|| unframed.to_bytes()).is_err());

        let mut bad = leaf_of(&proof);
        bad.schedule.stages[0].num_queries = 1;
        assert!(!HemAggregator::verify(&pks, &mode, &with_leaf(&proof, bad)));

        // The leaf verifier itself enforces the QROM-128 floor and exact regime parity.
        let committee_root = compute_committee_root(&pks);
        let profile = AggSigProfile::JortsPoseidon2;
        assert!(verify_shard_batch(
            &pks,
            &committee_root,
            profile,
            &mode,
            &leaf
        ));
        assert!(verify_shard_batch_with_regime(
            &pks,
            &committee_root,
            profile,
            &mode,
            &leaf,
            regime
        ));
        assert!(!verify_shard_batch_with_regime(
            &pks,
            &committee_root,
            profile,
            &mode,
            &leaf,
            wrong
        ));
        // A structurally valid schedule that is not the regime's canonical one (one extra
        // Stage-0 query) is refused before any transcript work.
        let num_vars =
            leaf.pcs_opening.opening.fold_sumcheck_polys.len() + leaf.schedule.early_stop_vars;
        assert!(leaf.schedule.validate(num_vars) && leaf.schedule.is_canonical(num_vars));
        let mut padded = leaf.schedule.clone();
        padded.stages[0].num_queries += 1;
        assert!(!padded.validate(num_vars) && !padded.is_canonical(num_vars));
    }

    #[test]
    fn mixed_regime_merges_are_rejected() {
        let mut keys: Vec<_> = (0..2).map(|i| gen_jorts_kp(711, i)).collect();
        let pks: Vec<_> = keys.iter().map(|k| k.pk).collect();
        let msg = b"mixed regimes";
        let mode = SigningMode::SharedMessage(msg);
        let sigs: Vec<_> = keys
            .iter_mut()
            .map(|k| k.sign_stateful_for_unit_test(msg, 0).unwrap())
            .collect();
        let make = |index| {
            let mut cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, make_seed(712));
            cfg.regime = WhirSecurityRegime::BciksJohnsonQrom128;
            HemAggregator::aggregate_with_config(
                &pks,
                &SignerBitmap::from_active_indices(2, &[index]).unwrap(),
                &mode,
                &sigs[index..index + 1],
                &cfg,
            )
            .unwrap()
        };
        let mut a_leaf = leaf_of(&make(0));
        a_leaf.schedule.regime = WhirSecurityRegime::BciksJohnsonClassical128;
        let a = with_leaf(&make(0), a_leaf);
        {
            let regime = WhirSecurityRegime::BciksJohnsonQrom128;
            let b = make(1);
            assert_eq!(
                HemAggregator::merge(&pks, &mode, &a, &b),
                Err(HemAggError::RegimeMismatch)
            );
            assert_eq!(
                HemAggregator::merge_owned(&pks, &mode, a.clone(), b.clone()),
                Err(HemAggError::RegimeMismatch)
            );
            let mixed = HemAggregatedProof {
                profile: a.profile,
                committee_root: a.committee_root,
                root: MergeNode::Branch {
                    bitmap: a.bitmap().union_disjoint(b.bitmap()).unwrap(),
                    left: Box::new(a.root.clone()),
                    right: Box::new(b.root),
                },
            };
            assert!(!HemAggregator::verify(&pks, &mode, &mixed));
            assert!(!HemAggregator::verify_with_regime(
                &pks, &mode, &mixed, regime
            ));
            assert!(!HemAggregator::verify_with_regime(
                &pks,
                &mode,
                &mixed,
                WhirSecurityRegime::BciksJohnsonClassical128
            ));
            assert_eq!(
                HemAggregatedProof::from_bytes_canonical(&mixed.to_bytes()),
                Err(HemAggError::MalformedWireBytes)
            );
        }
        let regime = WhirSecurityRegime::BciksJohnsonQrom128;
        let merged = HemAggregator::merge_owned(&pks, &mode, make(0), make(1)).unwrap();
        assert!(HemAggregator::verify_with_regime(
            &pks, &mode, &merged, regime
        ));
        assert!(HemAggregator::verify(&pks, &mode, &merged));
    }

    #[test]
    fn test_hem_aggregator_api_and_adversarial_whir_soundness() {
        // Test the Pants-themed `HemAggregator` API at `K = 8` (`JortsPoseidon2`), checking
        // proof size (`<= 300 KB`), OOD claims, Ext4 folding claims, per-stage PoW nonces, Steiner
        // multiproofs, and truncated wire transcripts.
        let mut kps: Vec<ValidatorKeypair> = (0..8u32).map(|i| gen_jorts_kp(7777, i)).collect();
        let pks: Vec<ValidatorPublicKey> = kps.iter().map(|kp| kp.pk).collect();
        let msg = b"hem-whir-k8-soundness-gate";
        let sigs: Vec<ValidatorSignature> = kps
            .iter_mut()
            .enumerate()
            .map(|(i, kp)| kp.sign_stateful_for_unit_test(msg, i as u32).unwrap())
            .collect();
        let bm = SignerBitmap::from_active_indices(8, &[0, 1, 2, 3, 4, 5, 6, 7]).unwrap();
        let mode = SigningMode::SharedMessage(msg);

        let proof = HemAggregator::aggregate(&pks, &bm, &mode, &sigs, make_seed(7778))
            .expect("HemAggregator::aggregate K=8");
        assert!(HemAggregator::verify(&pks, &mode, &proof));

        let wire = proof.to_bytes();
        assert!(
            wire.len() <= 300_000,
            "Hem Johnson QROM-128 K=8 proof must stay below 300 KB, got {} B",
            wire.len()
        );
        assert_eq!(
            HemAggregatedProof::from_bytes_canonical(&wire).unwrap(),
            proof
        );

        let leaf = leaf_of(&proof);
        assert_eq!(leaf.pcs_opening.opening.folded_layers.len(), 2);

        let rejects = |mutate: &dyn Fn(&mut ShardBatchProof)| {
            let mut bad = leaf.clone();
            mutate(&mut bad);
            !HemAggregator::verify(&pks, &mode, &with_leaf(&proof, bad))
        };

        // 1. Corrupted Ext4 Stage-0 and intermediate WHIR OOD claims:
        assert!(rejects(
            &|l| l.pcs_opening.opening.stage0_ood_evals[0] += GoldilocksExt4::V
        ));
        for st_idx in 0..leaf.pcs_opening.opening.folded_layers.len() {
            assert!(rejects(&|l| {
                l.pcs_opening.opening.folded_layers[st_idx].stage_ood_evals[0] += GoldilocksExt4::V;
            }));
        }

        // 2. Corrupted Ext4 WHIR sumcheck / folding polynomial coefficients (`c_0` and `c_2`):
        for round in [
            0usize,
            5,
            8,
            leaf.pcs_opening.opening.fold_sumcheck_polys.len() - 1,
        ] {
            assert!(rejects(&|l| {
                l.pcs_opening.opening.fold_sumcheck_polys[round][0] += GoldilocksExt4::ONE;
            }));
            assert!(rejects(&|l| {
                l.pcs_opening.opening.fold_sumcheck_polys[round][1] += GoldilocksExt4::V;
            }));
        }

        // 3. Corrupted terminal early-stop Ext4 polynomial evaluation:
        assert!(rejects(&|l| {
            l.pcs_opening.opening.final_coeffs[7] += GoldilocksExt4::V;
        }));

        // 4. Bad per-stage PoW nonces (Stage 0, Stage 1, and Final Stage 2):
        assert!(rejects(&|l| l.pcs_opening.opening.pow_nonce ^= 1));
        assert!(rejects(
            &|l| l.pcs_opening.opening.folded_layers[0].pow_nonce ^= 1
        ));
        assert!(rejects(
            &|l| l.pcs_opening.opening.folded_layers[1].pow_nonce ^= 1
        ));

        // 5. Tampered Steiner multiproofs (flipped sibling digest, missing sibling, extra sibling)
        //    across Round 0 and every escalated WHIR stage:
        assert!(rejects(&|l| l
            .pcs_opening
            .opening
            .round0_multiproof
            .auth_siblings[0][0] ^= 0x01));
        assert!(rejects(&|l| {
            l.pcs_opening.opening.round0_multiproof.auth_siblings.pop();
        }));
        assert!(rejects(&|l| {
            l.pcs_opening
                .opening
                .round0_multiproof
                .auth_siblings
                .push([0xAA; 32]);
        }));
        assert!(rejects(
            &|l| l.pcs_opening.opening.round0_salts[0][0] ^= 0x01
        ));
        for st_idx in 0..2 {
            assert!(rejects(&|l| {
                l.pcs_opening.opening.folded_layers[st_idx]
                    .multiproof
                    .auth_siblings[0][15] ^= 0x80;
            }));
            assert!(rejects(&|l| {
                l.pcs_opening.opening.folded_layers[st_idx]
                    .multiproof
                    .auth_siblings
                    .pop();
            }));
            assert!(rejects(&|l| {
                l.pcs_opening.opening.folded_layers[st_idx]
                    .multiproof
                    .auth_siblings
                    .push([0x55; 32]);
            }));
            assert!(rejects(&|l| {
                l.pcs_opening.opening.folded_layers[st_idx].opened_vals[0] += GoldilocksExt4::ONE;
            }));
        }

        // 6. Prover-supplied schedule mutations (`[AGG-03]`): `verify_shard_batch` and
        //    `verify_shard_batch_with_regime` must pin `proof.schedule == expected_regime.schedule(num_vars)`.
        assert!(crate::arithmetize::verify_shard_batch(
            &pks,
            &proof.committee_root,
            proof.profile,
            &mode,
            &leaf,
        ));
        assert!(rejects(&|l| {
            l.schedule.stages[0].num_queries -= 1;
        }));
        assert!(rejects(&|l| {
            l.schedule.early_stop_vars += 1;
        }));
        let mut weakened = leaf.clone();
        weakened.schedule.stages[0].num_queries -= 1;
        assert!(!crate::arithmetize::verify_shard_batch(
            &pks,
            &proof.committee_root,
            proof.profile,
            &mode,
            &weakened,
        ));
        let mut classical_sched = leaf.clone();
        classical_sched.schedule.regime = WhirSecurityRegime::BciksJohnsonClassical128;
        assert!(!crate::arithmetize::verify_shard_batch(
            &pks,
            &proof.committee_root,
            proof.profile,
            &mode,
            &classical_sched,
        ));
        assert!(!crate::arithmetize::verify_shard_batch_with_regime(
            &pks,
            &proof.committee_root,
            proof.profile,
            &mode,
            &classical_sched,
            WhirSecurityRegime::BciksJohnsonClassical128,
        ));

        // 7. Truncated transcripts across every wire section must cleanly return `MalformedWireBytes`
        //    with zero panics:
        for cut in [
            0usize,
            1,
            7,
            8,
            40,
            41,
            42,
            64,
            256,
            4096,
            wire.len() / 3,
            wire.len() / 2,
            wire.len() - 64,
            wire.len() - 1,
        ] {
            assert_eq!(
                HemAggregatedProof::from_bytes_canonical(&wire[..cut]),
                Err(HemAggError::MalformedWireBytes),
                "cut={cut}"
            );
        }
    }

    #[test]
    fn test_p0_03_stateless_corduroy_poseidon2_aggregate_end_to_end() {
        let mut keys: Vec<_> = (0..8)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(
                    AggSigProfile::CorduroyPoseidon2,
                    &make_seed(501),
                    i,
                )
            })
            .collect();
        let pks: Vec<_> = keys.iter().map(|k| k.pk).collect();
        let msgs: [&[u8]; 8] = [
            b"receipt-0",
            b"receipt-1",
            b"receipt-2",
            b"receipt-3",
            b"receipt-4",
            b"receipt-5",
            b"receipt-6",
            b"receipt-7",
        ];
        let sigs: Vec<_> = keys
            .iter_mut()
            .zip(msgs)
            .map(|(k, msg)| {
                let sig = k.sign_stateless_for_unit_test(msg).unwrap();
                assert!(verify_individual_signature(&k.pk, msg, &sig));
                sig
            })
            .collect();
        let bm = SignerBitmap::from_active_indices(8, &[0, 1, 2, 3, 4, 5, 6, 7]).unwrap();
        let mode = SigningMode::PerSignerMessages(&msgs);
        let agg = aggregate_signatures(&pks, &bm, &mode, &sigs, make_seed(700)).unwrap();
        let wire = agg.to_bytes();
        let raw_bytes = 8 * AggSigProfile::CorduroyPoseidon2.raw_signature_bytes();
        assert!(
            wire.len() < raw_bytes,
            "aggregate {} bytes, raw {}",
            wire.len(),
            raw_bytes
        );
        assert!(verify_aggregate(&pks, &mode, &agg));
    }

    fn test_point(num_vars: usize, tag: u64) -> Vec<GoldilocksExt4> {
        (0..num_vars)
            .map(|k| {
                ext4_sample(
                    (k as u64 + 1) * 31337 + tag * 1_000_003,
                    (k as u64 + 5) * 4242 + tag * 77_777,
                    (k as u64 + 7) * 9191 + tag * 33_331,
                    (k as u64 + 11) * 6161 + tag * 19_997,
                )
            })
            .collect()
    }

    #[test]
    fn test_pcs_batch_opening_binds_every_claim() {
        let num_vars = 12usize;
        let polys: Vec<Vec<Goldilocks>> = (0..3u64)
            .map(|p| {
                (0..(1u64 << num_vars))
                    .map(|i| {
                        Goldilocks::from_u64_reduced(
                            i.wrapping_mul(7919 + 2 * p).wrapping_add(13 + p),
                        )
                    })
                    .collect()
            })
            .collect();
        let points: Vec<Vec<GoldilocksExt4>> = (0..3).map(|p| test_point(num_vars, p)).collect();
        let evals: Vec<GoldilocksExt4> = polys
            .iter()
            .zip(&points)
            .map(|(poly, point)| mle_eval_base_at_ext4(poly, point))
            .collect();
        let point_refs: Vec<&[GoldilocksExt4]> = points.iter().map(Vec::as_slice).collect();

        let (comm, state) = whir_commit_batch_owned(polys.clone(), &make_seed(202));
        let (single_comm, _) = whir_commit(&polys[0], &make_seed(202));
        assert_ne!(comm, single_comm);

        let mut tr_p = fresh_test_transcript();
        let proof = whir_open_batch(&state, &point_refs, &evals, &mut tr_p);
        assert_eq!(proof.point_sumcheck_polys.len(), num_vars);
        assert_eq!(proof.common_point_evals.len(), 3);
        let check = |points: &[&[GoldilocksExt4]],
                     evals: &[GoldilocksExt4],
                     proof: &HemWhirBatchOpeningProof| {
            let mut tr_v = fresh_test_transcript();
            whir_verify_batch(&comm, num_vars, points, evals, proof, &mut tr_v)
        };
        assert!(check(&point_refs, &evals, &proof));

        let mut wire = Vec::new();
        proof.push_bytes(&mut wire);
        let (parsed, used) = HemWhirBatchOpeningProof::from_bytes_canonical(&wire).unwrap();
        assert_eq!((parsed, used), (proof.clone(), wire.len()));

        for bad in 0..3 {
            let mut wrong = evals.clone();
            wrong[bad] += GoldilocksExt4::ONE;
            assert!(!check(&point_refs, &wrong, &proof));
        }
        let mut swapped_evals = evals.clone();
        swapped_evals.swap(0, 2);
        assert!(!check(&point_refs, &swapped_evals, &proof));
        let mut swapped_points = point_refs.clone();
        swapped_points.swap(0, 1);
        assert!(!check(&swapped_points, &evals, &proof));

        for bad in 0..3 {
            let mut tampered = proof.clone();
            tampered.common_point_evals[bad] += GoldilocksExt4::ONE;
            assert!(!check(&point_refs, &evals, &tampered));
        }
        let mut tampered = proof.clone();
        tampered.point_sumcheck_polys[num_vars - 1][1] += GoldilocksExt4::ONE;
        assert!(!check(&point_refs, &evals, &tampered));

        let mut tampered = proof.clone();
        let last = tampered.opening.round0_vals.len() - 1;
        tampered.opening.round0_vals[last] += Goldilocks::ONE;
        assert!(!check(&point_refs, &evals, &tampered));

        let mut tampered = proof.clone();
        tampered.opening.round0_multiproof.auth_siblings[0][0] ^= 1;
        assert!(!check(&point_refs, &evals, &tampered));
        let mut tampered = proof.clone();
        tampered.opening.round0_multiproof.auth_siblings.pop();
        assert!(!check(&point_refs, &evals, &tampered));
        let mut tampered = proof.clone();
        tampered
            .opening
            .round0_multiproof
            .auth_siblings
            .push([0u8; 32]);
        assert!(!check(&point_refs, &evals, &tampered));
        let mut tampered = proof.clone();
        tampered.opening.folded_layers[0].opened_vals[3] += GoldilocksExt4::ONE;
        assert!(!check(&point_refs, &evals, &tampered));

        let (other_comm, _) = whir_commit_batch_owned(polys, &make_seed(203));
        let mut tr_v = fresh_test_transcript();
        assert!(!whir_verify_batch(
            &other_comm,
            num_vars,
            &point_refs,
            &evals,
            &proof,
            &mut tr_v
        ));
    }

    #[test]
    fn test_shard_caps_match_pcs_limit() {
        for profile in [
            AggSigProfile::JortsPoseidon2,
            AggSigProfile::CorduroyPoseidon2,
        ] {
            let rows = max_shard_signers(profile) * crate::trace::rows_per_signer(profile);
            assert_eq!(
                crate::trace::LOG_TRACE_COLS + rows.trailing_zeros() as usize,
                MAX_PCS_NUM_VARS
            );
        }

        let mut kps: Vec<ValidatorKeypair> = (0..2u32).map(|i| gen_jorts_kp(77, i)).collect();
        let pks: Vec<ValidatorPublicKey> = kps.iter().map(|kp| kp.pk).collect();
        let msg = b"shard-config";
        let sigs: Vec<ValidatorSignature> = kps
            .iter_mut()
            .map(|kp| kp.sign_stateful_for_unit_test(msg, 0).unwrap())
            .collect();
        let bm = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
        let mode = SigningMode::SharedMessage(msg);
        let default_cfg = AggConfig::default_for(AggSigProfile::JortsPoseidon2, make_seed(1));
        for bad_cfg in [
            AggConfig {
                max_signers_per_shard: 0,
                ..default_cfg.clone()
            },
            AggConfig {
                max_signers_per_shard: max_shard_signers(AggSigProfile::JortsPoseidon2) + 1,
                ..default_cfg.clone()
            },
            AggConfig {
                max_shards_per_batch: 0,
                ..default_cfg.clone()
            },
            AggConfig {
                max_shards_per_batch: MAX_BATCH_POLYS + 1,
                ..default_cfg.clone()
            },
        ] {
            assert_eq!(
                aggregate_signatures_with_config(&pks, &bm, &mode, &sigs, &bad_cfg),
                Err(AggError::InvalidShardConfig)
            );
        }
    }

    fn leaf_of(proof: &QsagAggregateProof) -> ShardBatchProof {
        match &proof.root {
            MergeNode::Leaf(leaf) => (**leaf).clone(),
            MergeNode::Branch { .. } => panic!("expected a single shard batch"),
        }
    }

    fn with_leaf(proof: &QsagAggregateProof, leaf: ShardBatchProof) -> QsagAggregateProof {
        QsagAggregateProof {
            profile: proof.profile,
            committee_root: proof.committee_root,
            root: MergeNode::Leaf(Box::new(leaf)),
        }
    }

    #[test]
    fn test_shard_batch_accumulation_and_tampering() {
        let mut kps: Vec<ValidatorKeypair> = (0..8u32).map(|i| gen_jorts_kp(2000, i)).collect();
        let pks: Vec<ValidatorPublicKey> = kps.iter().map(|kp| kp.pk).collect();
        let msg = b"batched-shards";
        let signer_ids = [0usize, 1, 3, 4, 6, 7];
        let sigs: Vec<ValidatorSignature> = signer_ids
            .iter()
            .map(|&i| kps[i].sign_stateful_for_unit_test(msg, i as u32).unwrap())
            .collect();
        let bm = SignerBitmap::from_active_indices(8, &signer_ids).unwrap();
        let mode = SigningMode::SharedMessage(msg);
        let cfg = AggConfig {
            regime: WhirSecurityRegime::default(),
            max_signers_per_shard: 2,
            max_shards_per_batch: 4,
            blinding_seed: make_seed(41),
        };
        let proof = aggregate_signatures_with_config(&pks, &bm, &mode, &sigs, &cfg).unwrap();
        assert_eq!((proof.num_shard_batches(), proof.num_leaf_shards()), (1, 3));
        assert!(verify_aggregate(&pks, &mode, &proof));
        assert!(!verify_aggregate(
            &pks,
            &SigningMode::SharedMessage(b"other"),
            &proof
        ));

        let unbatched_cfg = AggConfig {
            max_shards_per_batch: 1,
            ..cfg.clone()
        };
        let unbatched =
            aggregate_signatures_with_config(&pks, &bm, &mode, &sigs, &unbatched_cfg).unwrap();
        assert_eq!(
            (unbatched.num_shard_batches(), unbatched.num_leaf_shards()),
            (3, 3)
        );
        assert!(verify_aggregate(&pks, &mode, &unbatched));
        let (batched_len, unbatched_len) = (proof.to_bytes().len(), unbatched.to_bytes().len());
        assert!(
            batched_len < unbatched_len,
            "batched {batched_len} B, unbatched {unbatched_len} B"
        );

        let leaf = leaf_of(&proof);
        assert_eq!(leaf.pcs_opening.common_point_evals.len(), 3);
        let rejects = |mutate: &dyn Fn(&mut ShardBatchProof)| {
            let mut bad = leaf.clone();
            mutate(&mut bad);
            !verify_aggregate(&pks, &mode, &with_leaf(&proof, bad))
        };
        for shard in 0..3 {
            assert!(rejects(
                &|l| l.pcs_opening.common_point_evals[shard] += GoldilocksExt4::ONE
            ));
        }
        assert!(rejects(
            &|l| l.pcs_opening.point_sumcheck_polys[0][1] += GoldilocksExt4::ONE
        ));
        assert!(rejects(&|l| l.shards.swap(0, 1)));
        assert!(rejects(&|l| l.shards.swap(1, 2)));
        assert!(rejects(
            &|l| l.shards[2].col_evals[17] += GoldilocksExt4::ONE
        ));
        assert!(rejects(
            &|l| l.shards[1].row_sumcheck_polys[0][0] += GoldilocksExt4::ONE
        ));
        assert!(rejects(&|l| l.shard_signer_counts = vec![2, 3, 1]));
        assert!(rejects(&|l| l.shard_signer_counts = vec![2, 2]));
        assert!(rejects(&|l| {
            l.bitmap = SignerBitmap::from_active_indices(8, &[0, 1, 2, 4, 6, 7]).unwrap()
        }));
        assert!(rejects(&|l| l.witness_comm.root[5] ^= 1));

        let wire = proof.to_bytes();
        assert_eq!(
            QsagAggregateProof::from_bytes_canonical(&wire).unwrap(),
            proof
        );
        let malformed = |bytes: &[u8]| {
            QsagAggregateProof::from_bytes_canonical(bytes) == Err(AggError::MalformedWireBytes)
        };
        let mut trailing = wire.clone();
        trailing.push(0x00);
        assert!(malformed(&trailing));
        assert!(malformed(&wire[..wire.len() - 1]));
        let mut old_magic = wire.clone();
        old_magic[7] = 0x03;
        assert!(malformed(&old_magic));
        let needle = leaf.shards[0].col_evals[0].to_le_bytes();
        let at = wire.windows(32).position(|w| w == needle).unwrap();
        let mut non_canonical = wire.clone();
        non_canonical[at..at + 8].copy_from_slice(&[0xFF; 8]);
        assert!(malformed(&non_canonical));
        let count_at = 41 + 1 + leaf.bitmap.to_bytes().len();
        assert_eq!(wire[count_at], 3);
        let mut bad_count = wire.clone();
        bad_count[count_at] = 2;
        assert!(malformed(&bad_count));
    }

    #[test]
    fn test_merge_tree_structure_and_child_substitution() {
        let mut kps: Vec<ValidatorKeypair> = (0..4u32).map(|i| gen_jorts_kp(3000, i)).collect();
        let pks: Vec<ValidatorPublicKey> = kps.iter().map(|kp| kp.pk).collect();
        let msg = b"vote|slot=42";
        let other_msg = b"vote|slot=43";
        let mode = SigningMode::SharedMessage(msg);
        let other_mode = SigningMode::SharedMessage(other_msg);
        let bm_a = SignerBitmap::from_active_indices(4, &[0, 1]).unwrap();
        let bm_b = SignerBitmap::from_active_indices(4, &[2, 3]).unwrap();
        let sigs_a = vec![
            kps[0].sign_stateful_for_unit_test(msg, 0).unwrap(),
            kps[1].sign_stateful_for_unit_test(msg, 0).unwrap(),
        ];
        let sigs_b = vec![
            kps[2].sign_stateful_for_unit_test(msg, 0).unwrap(),
            kps[3].sign_stateful_for_unit_test(msg, 0).unwrap(),
        ];
        let sigs_b_other = vec![
            kps[2].sign_stateful_for_unit_test(other_msg, 1).unwrap(),
            kps[3].sign_stateful_for_unit_test(other_msg, 1).unwrap(),
        ];
        let proof_a = aggregate_signatures(&pks, &bm_a, &mode, &sigs_a, make_seed(51)).unwrap();
        let proof_b = aggregate_signatures(&pks, &bm_b, &mode, &sigs_b, make_seed(52)).unwrap();
        let proof_b_other =
            aggregate_signatures(&pks, &bm_b, &other_mode, &sigs_b_other, make_seed(53)).unwrap();
        assert!(verify_aggregate(&pks, &other_mode, &proof_b_other));

        let merged = merge_aggregates(&pks, &mode, &proof_a, &proof_b).unwrap();
        assert_eq!(
            merge_aggregates(&pks, &mode, &proof_b, &proof_a).unwrap(),
            merged
        );
        assert_eq!(
            merge_aggregates_owned(&pks, &mode, proof_b.clone(), proof_a.clone()).unwrap(),
            merged
        );
        assert!(verify_aggregate(&pks, &mode, &merged));
        assert_eq!(merged.num_shard_batches(), 2);
        assert_eq!(
            merged.to_bytes().len(),
            proof_a.to_bytes().len() + proof_b.to_bytes().len() - 41 + 1
        );
        let wire = merged.to_bytes();
        assert_eq!(
            QsagAggregateProof::from_bytes_canonical(&wire).unwrap(),
            merged
        );

        let branch =
            |bitmap: &SignerBitmap, left: &MergeNode, right: &MergeNode| QsagAggregateProof {
                profile: merged.profile,
                committee_root: merged.committee_root,
                root: MergeNode::Branch {
                    bitmap: bitmap.clone(),
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                },
            };
        let swapped = branch(merged.bitmap(), &proof_b.root, &proof_a.root);
        assert!(!verify_aggregate(&pks, &mode, &swapped));
        assert_eq!(
            QsagAggregateProof::from_bytes_canonical(&swapped.to_bytes()),
            Err(AggError::MalformedWireBytes)
        );
        let substituted = branch(merged.bitmap(), &proof_a.root, &proof_b_other.root);
        assert!(!verify_aggregate(&pks, &mode, &substituted));
        assert!(!verify_aggregate(&pks, &other_mode, &substituted));
        assert_eq!(
            merge_aggregates(&pks, &mode, &proof_a, &proof_b_other),
            Err(AggError::InvalidChildProof)
        );
        assert!(!verify_aggregate(
            &pks,
            &mode,
            &branch(&bm_a, &proof_a.root, &proof_b.root)
        ));
        assert!(!verify_aggregate(
            &pks,
            &mode,
            &branch(&bm_a, &proof_a.root, &proof_a.root)
        ));
        assert_eq!(
            merge_aggregates(&pks, &mode, &proof_a, &proof_a),
            Err(AggError::OverlappingSigners)
        );

        let per_msgs: [&[u8]; 4] = [b"m0", b"m1", b"m2", b"m3"];
        let bm_even = SignerBitmap::from_active_indices(4, &[0, 2]).unwrap();
        let bm_odd = SignerBitmap::from_active_indices(4, &[1, 3]).unwrap();
        let mut kps2: Vec<ValidatorKeypair> = (0..4u32).map(|i| gen_jorts_kp(3000, i)).collect();
        let sig_for = |kps: &mut Vec<ValidatorKeypair>, i: usize| {
            kps[i].sign_stateful_for_unit_test(per_msgs[i], 0).unwrap()
        };
        let sigs_even = vec![sig_for(&mut kps2, 0), sig_for(&mut kps2, 2)];
        let sigs_odd = vec![sig_for(&mut kps2, 1), sig_for(&mut kps2, 3)];
        let even_msgs = [per_msgs[0], per_msgs[2]];
        let odd_msgs = [per_msgs[1], per_msgs[3]];
        let proof_even = aggregate_signatures(
            &pks,
            &bm_even,
            &SigningMode::PerSignerMessages(&even_msgs),
            &sigs_even,
            make_seed(54),
        )
        .unwrap();
        let proof_odd = aggregate_signatures(
            &pks,
            &bm_odd,
            &SigningMode::PerSignerMessages(&odd_msgs),
            &sigs_odd,
            make_seed(55),
        )
        .unwrap();
        let all_mode = SigningMode::PerSignerMessages(&per_msgs);
        let interleaved = merge_aggregates(&pks, &all_mode, &proof_odd, &proof_even).unwrap();
        assert!(verify_aggregate(&pks, &all_mode, &interleaved));
        let shuffled: [&[u8]; 4] = [b"m1", b"m0", b"m2", b"m3"];
        assert!(!verify_aggregate(
            &pks,
            &SigningMode::PerSignerMessages(&shuffled),
            &interleaved
        ));

        let template = leaf_of(&proof_a);
        let chain = |num_leaves: usize| {
            let leaf_at = |j: usize| {
                MergeNode::Leaf(Box::new(ShardBatchProof {
                    bitmap: SignerBitmap::from_active_indices(64, &[2 * j, 2 * j + 1]).unwrap(),
                    ..template.clone()
                }))
            };
            let mut node = leaf_at(num_leaves - 1);
            for j in (0..num_leaves - 1).rev() {
                let left = leaf_at(j);
                let bitmap = left.bitmap().union_disjoint(node.bitmap()).unwrap();
                node = MergeNode::Branch {
                    bitmap,
                    left: Box::new(left),
                    right: Box::new(node),
                };
            }
            QsagAggregateProof {
                profile: merged.profile,
                committee_root: merged.committee_root,
                root: node,
            }
        };
        let deepest = chain(MAX_MERGE_TREE_DEPTH + 1);
        assert_eq!(deepest.root.depth(), MAX_MERGE_TREE_DEPTH);
        assert_eq!(
            QsagAggregateProof::from_bytes_canonical(&deepest.to_bytes()).unwrap(),
            deepest
        );
        let too_deep = chain(MAX_MERGE_TREE_DEPTH + 2);
        assert_eq!(
            QsagAggregateProof::from_bytes_canonical(&too_deep.to_bytes()),
            Err(AggError::MalformedWireBytes)
        );
    }

    fn hex32(bytes: &[u8; 32]) -> alloc::string::String {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut s = alloc::string::String::with_capacity(64);
        for &b in bytes {
            s.push(HEX[(b >> 4) as usize] as char);
            s.push(HEX[(b & 0x0F) as usize] as char);
        }
        s
    }

    /// Fixed-seed digests of (a) a standalone 12-variable `whir_open` proof and (b) a
    /// two-shard `JortsPoseidon2` aggregate merged with a second aggregate.
    fn fixed_seed_proof_digests() -> ([u8; 32], [u8; 32]) {
        let num_vars = 12usize;
        let evals: Vec<Goldilocks> = (0..(1usize << num_vars))
            .map(|i| Goldilocks::from_u64_reduced((i as u64).wrapping_mul(7919).wrapping_add(13)))
            .collect();
        let (_, state) = whir_commit(&evals, &make_seed(101));
        let point: Vec<GoldilocksExt4> = (0..num_vars)
            .map(|k| {
                ext4_sample(
                    (k as u64 + 1) * 31337,
                    (k as u64 + 5) * 4242,
                    (k as u64 + 9) * 1717,
                    (k as u64 + 13) * 9001,
                )
            })
            .collect();
        let val = mle_eval_base_at_ext4(&evals, &point);
        let mut tr = fresh_test_transcript();
        let pcs_proof = whir_open(&state, &point, val, &mut tr);
        let mut pcs_bytes = Vec::new();
        pcs_proof.push_bytes(&mut pcs_bytes);
        let pcs_digest = crate::sponge::cshake256_32(b"TEST.FIXED.PCS", &pcs_bytes);

        let mut kps: Vec<ValidatorKeypair> = (0..8u32).map(|i| gen_jorts_kp(4242, i)).collect();
        let pks: Vec<ValidatorPublicKey> = kps.iter().map(|kp| kp.pk).collect();
        let msg = b"fixed-seed-determinism-control";
        let sigs_a = vec![
            kps[0].sign_stateful_for_unit_test(msg, 0).unwrap(),
            kps[1].sign_stateful_for_unit_test(msg, 1).unwrap(),
            kps[2].sign_stateful_for_unit_test(msg, 0).unwrap(),
        ];
        let sigs_b = vec![
            kps[5].sign_stateful_for_unit_test(msg, 3).unwrap(),
            kps[7].sign_stateful_for_unit_test(msg, 2).unwrap(),
        ];
        let bm_a = SignerBitmap::from_active_indices(8, &[0, 1, 2]).unwrap();
        let bm_b = SignerBitmap::from_active_indices(8, &[5, 7]).unwrap();
        let mode = SigningMode::SharedMessage(msg);
        let cfg_a = AggConfig {
            regime: WhirSecurityRegime::default(),
            max_signers_per_shard: 2,
            max_shards_per_batch: 2,
            blinding_seed: make_seed(31),
        };
        let proof_a =
            aggregate_signatures_with_config(&pks, &bm_a, &mode, &sigs_a, &cfg_a).unwrap();
        let proof_b = aggregate_signatures(&pks, &bm_b, &mode, &sigs_b, make_seed(32)).unwrap();
        let merged = merge_aggregates(&pks, &mode, &proof_a, &proof_b).unwrap();
        assert!(verify_aggregate(&pks, &mode, &merged));
        let agg_digest = crate::sponge::cshake256_32(b"TEST.FIXED.AGG", &merged.to_bytes());
        (pcs_digest, agg_digest)
    }

    #[test]
    fn test_fixed_seed_proof_bytes_are_deterministic() {
        let (pcs_digest_1, agg_digest_1) = fixed_seed_proof_digests();
        let (pcs_digest_2, agg_digest_2) = fixed_seed_proof_digests();
        assert_eq!(pcs_digest_1, pcs_digest_2);
        assert_eq!(agg_digest_1, agg_digest_2);
        assert_eq!(
            (hex32(&pcs_digest_1).as_str(), hex32(&agg_digest_1).as_str()),
            (
                "250a1144b28c462516b6c5adb1125a47137c538f299642842a9f9e204e2c616e",
                "fac81f21997064833aeba90d1647e6272b4a5479b0d46f31b69226cc609fb2d5"
            )
        );
    }

    #[cfg(feature = "std")]
    fn bench_keys_and_sigs(
        profile: AggSigProfile,
        k: usize,
        msg: &[u8],
    ) -> (Vec<ValidatorPublicKey>, Vec<ValidatorSignature>) {
        let pairs: Vec<(ValidatorPublicKey, ValidatorSignature)> = std::thread::scope(|s| {
            let handles: Vec<_> = (0..k)
                .map(|i| {
                    s.spawn(move || {
                        let mut kp = ValidatorKeypair::keygen_deterministic(
                            profile,
                            &make_seed(60_000 + k as u64),
                            i as u32,
                        );
                        let sig = match profile {
                            AggSigProfile::JortsPoseidon2 => kp
                                .sign_stateful_for_unit_test(msg, (i % 64) as u32)
                                .unwrap(),
                            AggSigProfile::CorduroyPoseidon2 => {
                                kp.sign_stateless_for_unit_test(msg).unwrap()
                            }
                        };
                        (kp.pk, sig)
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        pairs.into_iter().unzip()
    }

    #[cfg(feature = "std")]
    fn median_verify_ms(
        pks: &[ValidatorPublicKey],
        mode: &SigningMode<'_>,
        proof: &QsagAggregateProof,
    ) -> f64 {
        let mut times = Vec::with_capacity(3);
        for _ in 0..3 {
            let t = std::time::Instant::now();
            assert!(verify_aggregate(pks, mode, proof));
            times.push(t.elapsed().as_secs_f64() * 1000.0);
        }
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        times[1]
    }

    #[cfg(feature = "std")]
    const SLH_DSA_128S_BYTES: usize = 7_856;
    #[cfg(feature = "std")]
    const SLH_DSA_128F_BYTES: usize = 17_088;

    #[cfg(feature = "std")]
    fn bench_header(title: &str) {
        std::println!("\n=== {title} ===");
        std::println!(
            "{:>3} | {:>6} | {:>7} | {:>12} | {:>10} | {:>11} | {:>12} | {:>12} | {:>12}",
            "K",
            "shards",
            "batches",
            "prove_ms",
            "verify_ms",
            "proof_B",
            "K*own_sig_B",
            "K*slh128s_B",
            "K*slh128f_B"
        );
    }

    #[cfg(feature = "std")]
    fn bench_row(
        profile: AggSigProfile,
        k: usize,
        shard_cap: Option<usize>,
        shards_per_batch: Option<usize>,
    ) -> QsagAggregateProof {
        let msg = b"agg-bench-shared-message";
        let (pks, sigs) = bench_keys_and_sigs(profile, k, msg);
        let indices: Vec<usize> = (0..k).collect();
        let bm = SignerBitmap::from_active_indices(k as u32, &indices).unwrap();
        let mode = SigningMode::SharedMessage(msg);
        let mut cfg = AggConfig::default_for(profile, make_seed(88_000 + k as u64));
        if let Some(cap) = shard_cap {
            cfg.max_signers_per_shard = cap;
        }
        if let Some(per_batch) = shards_per_batch {
            cfg.max_shards_per_batch = per_batch;
        }
        let t0 = std::time::Instant::now();
        let proof = aggregate_signatures_with_config(&pks, &bm, &mode, &sigs, &cfg).unwrap();
        let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let wire = proof.to_bytes();
        let verify_ms = median_verify_ms(&pks, &mode, &proof);
        assert_eq!(
            QsagAggregateProof::from_bytes_canonical(&wire).unwrap(),
            proof
        );
        std::println!(
            "{:>3} | {:>6} | {:>7} | {:>12.1} | {:>10.2} | {:>11} | {:>12} | {:>12} | {:>12}",
            k,
            proof.num_leaf_shards(),
            proof.num_shard_batches(),
            prove_ms,
            verify_ms,
            wire.len(),
            k * profile.raw_signature_bytes(),
            k * SLH_DSA_128S_BYTES,
            k * SLH_DSA_128F_BYTES
        );
        proof
    }

    #[test]
    fn test_cdhz25_and_poseidon2_aggregates_end_to_end() {
        let mut keys: Vec<_> = (0..3).map(|i| gen_jorts_kp(811, i)).collect();
        let pks: Vec<_> = keys.iter().map(|k| k.pk).collect();
        let msg = b"cdhz25 and poseidon2 regimes";
        let sigs: Vec<_> = keys
            .iter_mut()
            .map(|k| k.sign_stateful_for_unit_test(msg, 0).unwrap())
            .collect();
        let bitmap = SignerBitmap::from_active_indices(3, &[0, 1, 2]).unwrap();
        let mode = SigningMode::SharedMessage(msg);
        let other_msg = SigningMode::SharedMessage(b"another message");
        for regime in [
            WhirSecurityRegime::Cdhz25JohnsonQrom128,
            WhirSecurityRegime::Cdhz25ZeroPowQrom128,
            WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
            WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
        ] {
            // Two shards (2 + 1 signers) under one commitment and one batched opening.
            let mut cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, make_seed(812));
            cfg.regime = regime;
            cfg.max_signers_per_shard = 2;
            let proof =
                HemAggregator::aggregate_with_config(&pks, &bitmap, &mode, &sigs, &cfg).unwrap();
            assert_eq!(proof.num_leaf_shards(), 2);
            let wire = proof.to_bytes();
            assert_eq!(
                HemAggregatedProof::from_bytes_canonical(&wire).unwrap(),
                proof
            );
            assert!(verify_aggregate_with_regime(&pks, &mode, &proof, regime));
            for other in WhirSecurityRegime::ALL {
                if other != regime {
                    assert!(
                        !verify_aggregate_with_regime(&pks, &mode, &proof, other),
                        "{regime:?} aggregate accepted as {other:?}"
                    );
                }
            }
            assert!(!verify_aggregate_with_regime(&pks, &other_msg, &proof, regime));
            let mut other_pks = pks.clone();
            other_pks[2] = gen_jorts_kp(813, 2).pk;
            assert!(!verify_aggregate_with_regime(&other_pks, &mode, &proof, regime));

            let leaf = leaf_of(&proof);
            let rejects = |bad: ShardBatchProof| {
                !verify_aggregate_with_regime(&pks, &mode, &with_leaf(&proof, bad), regime)
            };
            let mut bad = leaf.clone();
            bad.pcs_opening.opening.round0_vals[0] += Goldilocks::ONE;
            assert!(rejects(bad), "{regime:?} leaf value");
            let mut bad = leaf.clone();
            bad.pcs_opening.opening.round0_multiproof.auth_siblings[0][0] ^= 1;
            assert!(rejects(bad), "{regime:?} sibling");
            let mut bad = leaf.clone();
            bad.pcs_opening.opening.folded_layers[0].opened_vals[0] += GoldilocksExt4::ONE;
            assert!(rejects(bad), "{regime:?} stage leaf");
            let mut bad = leaf.clone();
            bad.pcs_opening.opening.fold_sumcheck_polys[0][0] += GoldilocksExt4::ONE;
            assert!(rejects(bad), "{regime:?} fold sumcheck");
            let mut bad = leaf.clone();
            bad.witness_comm.root[0] ^= 1;
            assert!(rejects(bad), "{regime:?} witness commitment");
            // A regime tag swapped to the sibling backend with the same query table decodes
            // (the schedule is canonical for it) and must fail verification.
            let mut bad = leaf.clone();
            bad.schedule.regime = match regime {
                WhirSecurityRegime::Cdhz25JohnsonQrom128 => {
                    WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128
                }
                WhirSecurityRegime::Cdhz25ZeroPowQrom128 => {
                    WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128
                }
                WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128 => {
                    WhirSecurityRegime::Cdhz25JohnsonQrom128
                }
                _ => WhirSecurityRegime::Cdhz25ZeroPowQrom128,
            };
            let swapped = bad.schedule.regime;
            let swapped_proof = with_leaf(&proof, bad);
            assert!(!verify_aggregate_with_regime(&pks, &mode, &swapped_proof, regime));
            assert!(!verify_aggregate_with_regime(&pks, &mode, &swapped_proof, swapped));
        }
    }

    /// Deterministic keys and shared-message signatures, generated on at most
    /// `parallel_workers()` threads.
    #[cfg(feature = "std")]
    fn scale_keys_and_sigs(
        k: usize,
        msg: &'static [u8],
    ) -> (Vec<ValidatorPublicKey>, Vec<ValidatorSignature>) {
        let workers = parallel_workers().min(k).max(1);
        let chunk = k.div_ceil(workers);
        let mut pairs: Vec<(ValidatorPublicKey, ValidatorSignature)> = Vec::with_capacity(k);
        std::thread::scope(|s| {
            let handles: Vec<_> = (0..workers)
                .map(|w| {
                    s.spawn(move || {
                        (w * chunk..((w + 1) * chunk).min(k))
                            .map(|i| {
                                let mut kp = ValidatorKeypair::keygen_deterministic(
                                    AggSigProfile::JortsPoseidon2,
                                    &make_seed(70_000),
                                    i as u32,
                                );
                                let sig = kp.sign_stateful_for_unit_test(msg, 0).unwrap();
                                (kp.pk, sig)
                            })
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            for h in handles {
                pairs.extend(h.join().unwrap());
            }
        });
        pairs.into_iter().unzip()
    }

    /// Flat aggregate of `QSAG_BENCH_N` `JortsPoseidon2` signers (all signing), with
    /// `QSAG_BENCH_SHARD` signers per shard, `QSAG_BENCH_BATCH` shards per batch and regime wire
    /// tag `QSAG_BENCH_REGIME`. Prints proof bytes, prover time, and verifier time on all
    /// workers and on one worker.
    #[test]
    #[ignore]
    #[cfg(feature = "std")]
    fn bench_consensus_scale() {
        let env_usize = |name: &str, default: usize| {
            std::env::var(name)
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                .unwrap_or(default)
        };
        let n = env_usize("QSAG_BENCH_N", 128);
        let shard = env_usize("QSAG_BENCH_SHARD", DEFAULT_MAX_SHARD_SIGNERS_JORTS);
        let per_batch = env_usize("QSAG_BENCH_BATCH", 1);
        let regime =
            WhirSecurityRegime::from_u8(env_usize("QSAG_BENCH_REGIME", 4) as u8).unwrap();
        let msg: &'static [u8] = b"consensus-scale-benchmark";
        let t = std::time::Instant::now();
        let (pks, sigs) = scale_keys_and_sigs(n, msg);
        let keygen_s = t.elapsed().as_secs_f64();
        let indices: Vec<usize> = (0..n).collect();
        let bm = SignerBitmap::from_active_indices(n as u32, &indices).unwrap();
        let mode = SigningMode::SharedMessage(msg);
        let mut cfg = AggConfig::default_for(AggSigProfile::JortsPoseidon2, make_seed(91_000));
        cfg.regime = regime;
        cfg.max_signers_per_shard = shard;
        cfg.max_shards_per_batch = per_batch;
        let t = std::time::Instant::now();
        let proof = aggregate_signatures_with_config(&pks, &bm, &mode, &sigs, &cfg).unwrap();
        let prove_s = t.elapsed().as_secs_f64();
        let wire = proof.to_bytes();
        assert_eq!(
            QsagAggregateProof::from_bytes_canonical(&wire).unwrap(),
            proof
        );
        let median3 = |f: &dyn Fn() -> bool| {
            let mut times = [0f64; 3];
            for slot in &mut times {
                let t = std::time::Instant::now();
                assert!(f());
                *slot = t.elapsed().as_secs_f64() * 1000.0;
            }
            times.sort_by(|a, b| a.partial_cmp(b).unwrap());
            times[1]
        };
        let verify_all_ms = median3(&|| verify_aggregate_with_regime(&pks, &mode, &proof, regime));
        let verify_one_ms = median3(&|| {
            with_worker_limit(1, || {
                verify_aggregate_with_regime(&pks, &mode, &proof, regime)
            })
        });
        if regime.uses_poseidon2_canopy() {
            let census = recursion_census::poseidon2_aggregate_merkle_census(&proof).unwrap();
            std::println!("CHILD_MERKLE N={n} permutations={} trees={} leaves={} (excludes transcript and arithmetic)",
                census.permutations().unwrap(), census.merkle_trees, census.opened_leaves);
        }
        std::println!(
            "SCALE regime={regime:?} N={n} shard_signers={shard} shards={} batches={} \
             proof_bytes={} bytes_per_validator={:.1} keygen_sign_s={keygen_s:.1} \
             prove_s={prove_s:.2} verify_ms_all_workers={verify_all_ms:.2} \
             verify_ms_1_worker={verify_one_ms:.2} workers={} proof_digest={}",
            proof.num_leaf_shards(),
            proof.num_shard_batches(),
            wire.len(),
            wire.len() as f64 / n as f64,
            parallel_workers(),
            crate::sponge::cshake256_32(b"QSAG.BENCH.PROOF", &wire)
                .iter()
                .map(|b| alloc::format!("{b:02x}"))
                .collect::<alloc::string::String>()
        );
    }

    /// Release measurements include aggregation, serialization, and independent verification.
    #[test]
    #[ignore]
    #[cfg(feature = "std")]
    fn bench_affine_regimes() {
        let msg = b"affine-regime-benchmark";
        let mode = SigningMode::SharedMessage(msg);
        for profile in [
            AggSigProfile::JortsPoseidon2,
            AggSigProfile::CorduroyPoseidon2,
        ] {
            let (pks, sigs) = bench_keys_and_sigs(profile, 8, msg);
            let bm = SignerBitmap::from_active_indices(8, &[0, 1, 2, 3, 4, 5, 6, 7]).unwrap();
            let regime = WhirSecurityRegime::BciksJohnsonQrom128;
            let mut cfg = AggConfig::default_for(profile, make_seed(909));
            cfg.regime = regime;
            let start = std::time::Instant::now();
            let proof = aggregate_signatures_with_config(&pks, &bm, &mode, &sigs, &cfg).unwrap();
            let prove_ms = start.elapsed().as_secs_f64() * 1000.0;
            let wire = proof.to_bytes();
            let verify_ms = median_verify_ms(&pks, &mode, &proof);
            assert_eq!(
                QsagAggregateProof::from_bytes_canonical(&wire).unwrap(),
                proof
            );
            std::println!(
                "AFFINE {profile:?} {regime:?} K=8 bytes={} prove_ms={prove_ms:.3} verify_median3_ms={verify_ms:.3}",
                wire.len()
            );
        }
    }

    #[test]
    #[ignore]
    #[cfg(feature = "std")]
    fn bench_pcs_open_verify() {
        for num_vars in [18usize, 20, 22] {
            let evals: Vec<Goldilocks> = (0..(1usize << num_vars))
                .map(|i| {
                    Goldilocks::from_u64_reduced((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15))
                })
                .collect();
            let t = std::time::Instant::now();
            let (comm, state) = whir_commit(&evals, &make_seed(5));
            let commit_ms = t.elapsed().as_secs_f64() * 1000.0;
            let point: Vec<GoldilocksExt4> = (0..num_vars)
                .map(|k| {
                    ext4_sample(
                        (k as u64 + 1) * 31337,
                        (k as u64 + 5) * 4242,
                        (k as u64 + 9) * 1717,
                        (k as u64 + 13) * 9001,
                    )
                })
                .collect();
            let val = mle_eval_base_at_ext4(&evals, &point);
            let mut open_ms = f64::MAX;
            let mut proof = None;
            for _ in 0..5 {
                let mut tr = fresh_test_transcript();
                let t = std::time::Instant::now();
                let p = whir_open(&state, &point, val, &mut tr);
                open_ms = open_ms.min(t.elapsed().as_secs_f64() * 1000.0);
                proof = Some(p);
            }
            let proof = proof.unwrap();
            let mut verify_ms = f64::MAX;
            for _ in 0..50 {
                let mut tr = fresh_test_transcript();
                let t = std::time::Instant::now();
                assert!(whir_verify(&comm, num_vars, &point, val, &proof, &mut tr));
                verify_ms = verify_ms.min(t.elapsed().as_secs_f64() * 1000.0);
            }
            let mut bytes = Vec::new();
            proof.push_bytes(&mut bytes);
            std::println!(
                "PCS num_vars={num_vars}: commit_ms={commit_ms:.1} open_ms(min of 5)={open_ms:.1} verify_ms(min of 50)={verify_ms:.3} proof_B={}",
                bytes.len()
            );
        }
    }

    #[test]
    #[ignore]
    #[cfg(feature = "std")]
    fn bench_agg_jorts() {
        let profile = AggSigProfile::JortsPoseidon2;
        bench_header("JortsPoseidon2, default config (one shard)");
        for k in [8usize, 16, 32] {
            bench_row(profile, k, None, None);
        }
        bench_header("JortsPoseidon2, max_signers_per_shard = 4, one shard per batch");
        for k in [8usize, 16, 32] {
            bench_row(profile, k, Some(4), Some(1));
        }
        bench_header("JortsPoseidon2, max_signers_per_shard = 4, up to 8 shards per batch");
        for k in [8usize, 16, 32] {
            bench_row(profile, k, Some(4), Some(8));
        }

        let msg = b"agg-bench-shared-message";
        let (pks, sigs) = bench_keys_and_sigs(profile, 16, msg);
        let mode = SigningMode::SharedMessage(msg);
        let idx_l: Vec<usize> = (0..8).collect();
        let idx_r: Vec<usize> = (8..16).collect();
        let bm_l = SignerBitmap::from_active_indices(16, &idx_l).unwrap();
        let bm_r = SignerBitmap::from_active_indices(16, &idx_r).unwrap();
        let pa = aggregate_signatures(&pks, &bm_l, &mode, &sigs[0..8], make_seed(1)).unwrap();
        let pb = aggregate_signatures(&pks, &bm_r, &mode, &sigs[8..16], make_seed(2)).unwrap();
        let tm = std::time::Instant::now();
        let pm = merge_aggregates(&pks, &mode, &pa, &pb).unwrap();
        let merge_ms = tm.elapsed().as_secs_f64() * 1000.0;
        let verify_ms = median_verify_ms(&pks, &mode, &pm);
        std::println!(
            "\nmerge_aggregates(K=8, K=8): merge_ms={:.2} verify_ms={:.2} left_B={} right_B={} merged_B={}",
            merge_ms,
            verify_ms,
            pa.to_bytes().len(),
            pb.to_bytes().len(),
            pm.to_bytes().len()
        );
    }

    #[test]
    #[ignore]
    #[cfg(feature = "std")]
    fn bench_agg_corduroy_k8() {
        bench_header("CorduroyPoseidon2, default config (8 signers per shard, 2 shards per batch)");
        bench_row(AggSigProfile::CorduroyPoseidon2, 8, None, None);
    }

    #[test]
    #[ignore]
    #[cfg(feature = "std")]
    fn bench_agg_corduroy_k16() {
        bench_header("CorduroyPoseidon2, default config (8 signers per shard, 2 shards per batch)");
        bench_row(AggSigProfile::CorduroyPoseidon2, 16, None, None);
    }

    #[test]
    #[ignore]
    #[cfg(feature = "std")]
    fn bench_agg_corduroy_k32() {
        bench_header("CorduroyPoseidon2, default config (8 signers per shard, 2 shards per batch)");
        bench_row(AggSigProfile::CorduroyPoseidon2, 32, None, None);
    }
}

mod profile;

#[cfg(feature = "vulkan")]
mod acceleration;

#[cfg(feature = "vulkan")]
pub use acceleration::vulkan_execution_counts;
