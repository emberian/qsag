//! `qsag-agg`: `Hem` Succinct Non-Interactive Post-Quantum Multi-Signature Aggregation,
//! Zero-Knowledge Committed-Mask SNARKs, and Recursive IVC over Quintic `Fp5`
//! (`#![no_std]` + `alloc`, `#![forbid(unsafe_code)]`, `[DKT26]` `< 2^{-128}` QROM).
//!
//! All public aggregation, zero-knowledge, and recursive proof formats operate exclusively over
//! the quintic extension $\mathbb{F}_{p^5} = \mathbb{F}_p[X]/(X^5 - 3)$ ($p = 2^{64} - 2^{32} + 1$,
//! $|\mathbb{F}_{p^5}| > 2^{319.99}$) at `< 2^{-128}` QROM security:
//! - **Public $K$-to-$1$ Committee Aggregation (`QSAGHQM2`)**: [`prove_hem_quintic_128`] and
//!   [`verify_hem_quintic_128`] over [`HemQuinticProfile::TurboShake400`] (`400`-bit digests) or
//!   [`HemQuinticProfile::Poseidon2Gl24`] (`448`-bit width-24 Poseidon2 Jive digests), supporting
//!   both stateful `JortsPoseidon2` (`WOTS+C` + XMSS) and stateless `CorduroyPoseidon2`
//!   (`FORS` + 16-layer `WOTS+C` hypertree).
//! - **Regional Quorum Hierarchy (`QSAGHEM\x04`)**: [`HierarchicalHemAggregate`] binding regional
//!   [`HemQuinticProof`] batches to a Poseidon2-committed [`PreparedPolicyRegistry`].
//! - **Committed-Mask Zero-Knowledge SNARK (`QSAGZKH2` / `QSAGZKS2`)**: [`zk_hem::v2`] (`256`-bit
//!   per-leaf salts, `32`-byte per-tree nonces, `5` Stage-0 OOD masks, `[DKT26]` Theorem 5.12),
//!   backing [`zk_hem::blind_vc`], [`zk_hem::multisig`], and [`zk_hem::capability`].
//! - **Succinct Binary Recursive IVC (`QSAGIVC1`)**: [`prove_ivc_tree`] and [`verify_ivc_tree`]
//!   producing constant `639,673`-byte `[DKT26]` `< 2^{-128}` QROM proofs ([`SuccinctIvcProof`]).

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod arithmetize;
pub mod field;
pub mod hem_quintic;
pub use hem_quintic::{
    HemQuinticProfile, HemQuinticProof, QuinticFp5, prove_hem_quintic_128, verify_hem_quintic_128,
};
pub mod pcs;
#[cfg(feature = "std")]
mod pool;
mod profile;
#[cfg(feature = "std")]
mod prover_admission;
pub mod recursive;
pub use recursive::{
    FixedPathWhirW24, HIERARCHICAL_HEM_WIRE_MAGIC, HierarchicalHemAggregate, IvcPolicyRegistry,
    IvcRowCensus, IvcShard, IvcStepConfig, IvcSubtreeStatement, IvcTableCommitment,
    IvcTreeStepRelation, MAX_HIERARCHY_SHARDS, PreparedPolicyRegistry, ShardHemBatch,
    ShardHemPolicy, ShardHemWitness, SuccinctIvcProof, SuccinctIvcStep, checked_sum_usize,
    compute_framed_message_digest, compute_policy_registry_root, encode_policy_registry,
    hierarchical_hem_message, ivc_signing_message, prove_hierarchical_hem,
    prove_hierarchical_hem_prepared, prove_ivc_tree, verify_hierarchical_hem,
    verify_hierarchical_hem_prepared, verify_ivc_tree,
};
#[cfg(feature = "std")]
use prover_admission::prover_parallel_jobs;
pub mod sig;
pub mod sponge;
pub mod trace;
pub mod zk_hem;

#[cfg(feature = "std")]
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
    match std::thread::Builder::new()
        .stack_size(1024 * 1024)
        .spawn_scoped(scope, move || {
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
pub(crate) fn join_worker<T>(handle: ScopedWorker<'_, T>) -> T {
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

/// Execute `f` with `qsag-agg` worker concurrency clamped to `max_workers.max(1)`.
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

#[cfg(feature = "std")]
pub(crate) fn map_chunks_bounded_with_limit<'a, T, R, F>(
    items: &'a [T],
    max_jobs: usize,
    f: F,
) -> Vec<R>
where
    T: Sync,
    R: Send,
    F: Fn(&'a [T]) -> R + Sync,
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
    DEFAULT_SHARD_PCS_NUM_VARS, compute_signing_mode_digest, default_shard_signers,
    max_shard_signers,
};
pub use field::{Goldilocks, GoldilocksExt2};
pub use pcs::{EARLY_STOP_VARS, MAX_PCS_NUM_VARS};
pub use qsag_core::tsw_baggy::{EpochLatchError, MonotonicEpochLatch, StatefulEpochLatch};
pub use sig::{
    AggSigProfile, CORDUROY_MAX_STATELESS_SIGS_PER_KEY, Digest4, Digest5, EpochWalSink,
    JORTS_MAX_XMSS_HEIGHT, JORTS_MIN_XMSS_HEIGHT, JORTS_XMSS_HEIGHT, SigError, SignerBitmap,
    SigningMode, StatelessBudgetWalSink, ValidatorKeypair, ValidatorPublicKey, ValidatorSignature,
    bytes32_to_limbs56, compute_committee_root, limbs56_to_bytes32_canonical,
    validate_unique_active_committee, verify_individual_signature, verify_signature_batch,
};
#[cfg(feature = "std")]
pub use sig::{FsStatelessBudgetWal, FsWalEpochSink};

/// Default active signers per `JortsPoseidon2` shard (`DEFAULT_SHARD_PCS_NUM_VARS`-variable witness).
pub const DEFAULT_MAX_SHARD_SIGNERS_JORTS: usize =
    default_shard_signers(AggSigProfile::JortsPoseidon2);

/// Default active signers per `CorduroyPoseidon2` shard.
pub const DEFAULT_MAX_SHARD_SIGNERS_CORDUROY: usize =
    default_shard_signers(AggSigProfile::CorduroyPoseidon2);

/// Errors returned by [`prove_hierarchical_hem`] or canonical hierarchy wire deserialization.
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
    InvalidChildProof,
    MalformedWireBytes,
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

    #[test]
    fn quintic_agg_shared_and_per_signer_roundtrip_across_profiles() {
        let mut kp0 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[1; 32], 0);
        let mut kp1 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[2; 32], 1);
        let kp2 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[3; 32], 2);
        let pks = [kp0.pk, kp1.pk, kp2.pk];
        let bitmap = SignerBitmap::from_active_indices(3, &[0, 1]).unwrap();

        let msg0 = b"validator-0-slot-99";
        let msg1 = b"validator-1-slot-99";
        let sig0 = kp0.sign_stateful_for_unit_test(msg0, 0).unwrap();
        let sig1 = kp1.sign_stateful_for_unit_test(msg1, 0).unwrap();
        let mode = SigningMode::PerSignerMessages(&[msg0, msg1]);

        for profile in [
            HemQuinticProfile::TurboShake400,
            HemQuinticProfile::Poseidon2Gl24,
        ] {
            let proof = prove_hem_quintic_128(
                profile,
                &pks,
                &bitmap,
                &mode,
                &[sig0.clone(), sig1.clone()],
            )
            .unwrap();
            assert_eq!(proof.num_signers(), 2);
            let wire = proof.to_bytes();
            let decoded = HemQuinticProof::from_bytes(&wire).unwrap();
            assert!(verify_hem_quintic_128(&pks, &mode, &decoded));
            assert!(!verify_hem_quintic_128(
                &pks,
                &SigningMode::PerSignerMessages(&[msg1, msg0]),
                &decoded
            ));
        }
    }
}
