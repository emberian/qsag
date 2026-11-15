//! Two-layer `Hem` composition across regional quorum shards (`JortsPoseidon2` stateful XMSS,
//! `CorduroyPoseidon2` stateless FORS + hypertree, or mixed-profile regional hierarchies),
//! supporting both:
//! 1. Direct hierarchical verification ([`HierarchicalHemAggregate`]), where every regional `Hem`
//!    proof is carried and verified in full under a length-prefixed root commitment, and
//! 2. Compact hierarchy commitments ([`SuccinctHierarchicalHemAggregate`]), where regional
//!    headers and child-proof digests are folded inside one outer Sumcheck + WHIR proof.
//!    That proof certifies the commitment chain, not execution of the child verifiers.
//!    Quorum verification therefore requires locally checked [`VerifiedHierarchicalHemEvidence`].
//!    Recipients without that evidence must obtain and verify the full child hierarchy.
//!    [`crate::recursion_census`] measures the child-verifier hash work an outer relation
//!    would have to absorb to remove that requirement.

use crate::arithmetize::{
    ROW_SUMCHECK_COEFFS, ROW_SUMCHECK_WIRE_COEFFS, build_shift_tables_ext4, eval_eq_not_last_ext4,
    eval_shift_kernel_ext4, interpolate_deg8_from_evals_ext4,
};
use crate::field::{
    Goldilocks, GoldilocksExt4, build_eq_table_ext4, eq_poly_ext4, eval_univariate_ext4,
    mle_eval_ext4,
};
use crate::pcs::{
    CanopyCommitment, HemWhirOpeningProof, WhirSchedule, whir_commit_owned_with_schedule,
    whir_open, whir_verify_with_schedule,
};
use crate::sponge::{
    FiatShamirTranscript, InstanceBound, POSEIDON2_HALF_EXT_ROUNDS, POSEIDON2_INT_ROUNDS,
    cshake256_from_midstate_32, cshake256_from_midstate_32_x4, cshake256_static_midstate,
    encode_multi_frame, poseidon2_apply_me_ext4, poseidon2_apply_mi_ext4, poseidon2_const_at,
    poseidon2_hash32, poseidon2_sbox7_ext4, push_leb128, shake256_into,
};
use crate::trace::{
    COL_SBOX_OUT, COL_ST_IN, LOG_TRACE_COLS, NUM_TRACE_COLS, record_poseidon2_perm12,
};
use crate::{
    AggSigProfile, HemAggConfig, HemAggError, HemAggregatedProof, SignerBitmap, SigningMode,
    ValidatorPublicKey, ValidatorSignature, WhirSecurityRegime,
    aggregate_signatures_with_committee_root, compute_committee_root, max_shard_signers,
    verify_aggregate_with_committee_root,
};
use alloc::{collections::BTreeSet, vec, vec::Vec};

/// Canonical v3 wire magic (cSHAKE256 outer byte commitment) for [`HierarchicalHemAggregate`].
pub const HIERARCHICAL_HEM_WIRE_MAGIC: &[u8; 8] = b"QSAGHEM\x03";

/// Canonical wire magic for compact [`SuccinctHierarchicalHemAggregate`] commitments.
pub const SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC: &[u8; 8] = b"QSAGSHM\x01";

/// Largest regional shard count: the outer chain trace has two rows per shard and
/// `LOG_TRACE_COLS + log2(rows)` variables, which must not exceed
/// [`crate::pcs::MAX_PCS_NUM_VARS`]. Wire decoding additionally requires the body to hold
/// every claimed shard header before allocating.
pub const MAX_HIERARCHY_SHARDS: usize =
    1usize << (crate::pcs::MAX_PCS_NUM_VARS - LOG_TRACE_COLS - 1);

/// Trusted regional registry entry, supplied independently of the proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardHemPolicy {
    pub shard_id: u64,
    pub custodian_cluster: [u8; 32],
    pub quorum_keys: Vec<ValidatorPublicKey>,
    pub minimum_quorums: usize,
}

impl ShardHemPolicy {
    /// Homogeneous `AggSigProfile` of this shard's quorum committee, or `None` if empty or mixed.
    pub fn profile(&self) -> Option<AggSigProfile> {
        let first = self.quorum_keys.first()?.profile;
        self.quorum_keys
            .iter()
            .all(|k| k.profile == first)
            .then_some(first)
    }
}

/// Verified regional shard batch inside a [`HierarchicalHemAggregate`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardHemBatch {
    pub shard_id: u64,
    pub custodian_cluster: [u8; 32],
    pub shard_quorum_set_root: [u8; 32],
    pub minimum_quorums: u64,
    pub epoch_floor: u64,
    pub message_digest: [u8; 32],
    pub proof: HemAggregatedProof,
}

/// Two-layer hierarchical `Hem` aggregate over an ordered regional policy registry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HierarchicalHemAggregate {
    pub policy_registry_root: [u8; 32],
    pub shards: Vec<ShardHemBatch>,
    pub root_commitment: [u8; 32],
}

impl HierarchicalHemAggregate {
    /// Total verified quorum signers across all regional shards (`None` on `u64`/`usize` overflow).
    pub fn checked_total_quorums(&self) -> Option<usize> {
        checked_sum_usize(self.shards.iter().map(|s| s.proof.num_signers()))
    }

    /// Serialize to canonical length-prefixed wire bytes (`HIERARCHICAL_HEM_WIRE_MAGIC`).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(76 + self.shards.len().saturating_mul(65_664));
        out.extend_from_slice(HIERARCHICAL_HEM_WIRE_MAGIC);
        out.extend_from_slice(&self.policy_registry_root);
        out.extend_from_slice(&self.root_commitment);
        out.extend_from_slice(&(self.shards.len() as u32).to_le_bytes());
        for s in &self.shards {
            out.extend_from_slice(&s.shard_id.to_le_bytes());
            out.extend_from_slice(&s.custodian_cluster);
            out.extend_from_slice(&s.shard_quorum_set_root);
            out.extend_from_slice(&s.minimum_quorums.to_le_bytes());
            out.extend_from_slice(&s.epoch_floor.to_le_bytes());
            out.extend_from_slice(&s.message_digest);
            let len_pos = out.len();
            out.extend_from_slice(&0u32.to_le_bytes());
            s.proof.push_wire_bytes(&mut out);
            let proof_len = (out.len() - (len_pos + 4)) as u32;
            out[len_pos..len_pos + 4].copy_from_slice(&proof_len.to_le_bytes());
        }
        out
    }

    /// Strictly canonical wire decoder rejecting trailing bytes, truncated frames, or malformed leaves.
    pub fn from_bytes_canonical(bytes: &[u8]) -> Result<Self, HemAggError> {
        if bytes.len() < 76 || &bytes[0..8] != HIERARCHICAL_HEM_WIRE_MAGIC {
            return Err(HemAggError::MalformedWireBytes);
        }
        let mut policy_registry_root = [0u8; 32];
        policy_registry_root.copy_from_slice(&bytes[8..40]);
        let mut root_commitment = [0u8; 32];
        root_commitment.copy_from_slice(&bytes[40..72]);
        let mut cnt_bytes = [0u8; 4];
        cnt_bytes.copy_from_slice(&bytes[72..76]);
        let num_shards = u32::from_le_bytes(cnt_bytes) as usize;
        let min_body = num_shards
            .checked_mul(124)
            .ok_or(HemAggError::MalformedWireBytes)?;
        if num_shards == 0
            || num_shards > MAX_HIERARCHY_SHARDS
            || bytes.len().saturating_sub(76) < min_body
        {
            return Err(HemAggError::MalformedWireBytes);
        }
        let mut pos = 76usize;
        let mut shards = Vec::with_capacity(num_shards);
        for _ in 0..num_shards {
            let meta_end = pos
                .checked_add(124)
                .ok_or(HemAggError::MalformedWireBytes)?;
            let meta = bytes
                .get(pos..meta_end)
                .ok_or(HemAggError::MalformedWireBytes)?;
            let shard_id = u64::from_le_bytes(meta[0..8].try_into().unwrap());
            let mut custodian_cluster = [0u8; 32];
            custodian_cluster.copy_from_slice(&meta[8..40]);
            let mut shard_quorum_set_root = [0u8; 32];
            shard_quorum_set_root.copy_from_slice(&meta[40..72]);
            let minimum_quorums = u64::from_le_bytes(meta[72..80].try_into().unwrap());
            let epoch_floor = u64::from_le_bytes(meta[80..88].try_into().unwrap());
            let mut message_digest = [0u8; 32];
            message_digest.copy_from_slice(&meta[88..120]);
            let proof_len = u32::from_le_bytes(meta[120..124].try_into().unwrap()) as usize;
            pos = meta_end;
            let proof_end = pos
                .checked_add(proof_len)
                .ok_or(HemAggError::MalformedWireBytes)?;
            let proof_slice = bytes
                .get(pos..proof_end)
                .ok_or(HemAggError::MalformedWireBytes)?;
            let proof = HemAggregatedProof::from_bytes_canonical(proof_slice)?;
            pos = proof_end;
            shards.push(ShardHemBatch {
                shard_id,
                custodian_cluster,
                shard_quorum_set_root,
                minimum_quorums,
                epoch_floor,
                message_digest,
                proof,
            });
        }
        if pos != bytes.len() {
            return Err(HemAggError::MalformedWireBytes);
        }
        Ok(Self {
            policy_registry_root,
            shards,
            root_commitment,
        })
    }
}

/// Overflow-free `usize` summation bounded simultaneously by `usize::MAX` and `u64::MAX`.
pub fn checked_sum_usize<I: IntoIterator<Item = usize>>(iter: I) -> Option<usize> {
    let mut acc: u64 = 0;
    for item in iter {
        let v = u64::try_from(item).ok()?;
        acc = acc.checked_add(v)?;
    }
    usize::try_from(acc).ok()
}

fn compute_committee_roots(policies: &[ShardHemPolicy]) -> Vec<[u8; 32]> {
    #[cfg(feature = "std")]
    let total_keys: usize = policies.iter().map(|p| p.quorum_keys.len()).sum();
    #[cfg(feature = "std")]
    if policies.len() > 1 && total_keys > 64 && crate::parallel_workers() > 1 {
        let workers = crate::available_worker_budget().min(policies.len());
        if workers > 1 {
            let chunk = policies.len().div_ceil(workers);
            let mut roots = alloc::vec![[0u8; 32]; policies.len()];
            std::thread::scope(|scope| {
                let mut rest_policies = policies;
                let mut rest_roots = roots.as_mut_slice();
                let (head_p, tail_p) = rest_policies.split_at(chunk.min(rest_policies.len()));
                let (head_r, tail_r) = rest_roots.split_at_mut(head_p.len());
                rest_policies = tail_p;
                rest_roots = tail_r;

                let mut handles = Vec::with_capacity(workers.saturating_sub(1));
                while !rest_policies.is_empty() {
                    let take = chunk.min(rest_policies.len());
                    let (sub_p, next_p) = rest_policies.split_at(take);
                    let (sub_r, next_r) = rest_roots.split_at_mut(take);
                    rest_policies = next_p;
                    rest_roots = next_r;
                    handles.push(crate::spawn_bounded(scope, move || {
                        for (dst, p) in sub_r.iter_mut().zip(sub_p.iter()) {
                            *dst = compute_committee_root(&p.quorum_keys);
                        }
                    }));
                }
                for (dst, p) in head_r.iter_mut().zip(head_p.iter()) {
                    *dst = compute_committee_root(&p.quorum_keys);
                }
                for h in handles {
                    crate::join_worker(h);
                }
            });
            return roots;
        }
    }
    policies
        .iter()
        .map(|p| compute_committee_root(&p.quorum_keys))
        .collect()
}

fn encode_policy_registration_with_root(
    policy: &ShardHemPolicy,
    committee_root: &[u8; 32],
) -> Vec<u8> {
    let mut committee_frame = Vec::with_capacity(8 + policy.quorum_keys.len() * 70);
    push_leb128(&mut committee_frame, policy.quorum_keys.len());
    for pk in &policy.quorum_keys {
        let raw = pk.to_bytes();
        // Exact `encode_multi_frame(&[&raw[0..1], &raw[1..33], &raw[33..65]])` (`69` bytes):
        committee_frame.push(69);
        committee_frame.push(3);
        committee_frame.push(1);
        committee_frame.push(raw[0]);
        committee_frame.push(32);
        committee_frame.extend_from_slice(&raw[1..33]);
        committee_frame.push(32);
        committee_frame.extend_from_slice(&raw[33..65]);
    }
    let profile_tag = [policy.profile().map_or(0u8, |p| p as u8)];
    let shard_id_bytes = policy.shard_id.to_le_bytes();
    let min_q_bytes = (policy.minimum_quorums as u64).to_le_bytes();
    encode_multi_frame(&[
        b"QSAG.HEM.POLICY.ROW/v2",
        &shard_id_bytes,
        &policy.custodian_cluster,
        &profile_tag,
        &min_q_bytes,
        committee_root,
        &committee_frame,
    ])
}

fn encode_policy_registry_with_roots(
    policies: &[ShardHemPolicy],
    committee_roots: &[[u8; 32]],
) -> Vec<u8> {
    debug_assert_eq!(policies.len(), committee_roots.len());
    let rows: Vec<Vec<u8>> = policies
        .iter()
        .zip(committee_roots.iter())
        .map(|(p, r)| encode_policy_registration_with_root(p, r))
        .collect();
    let mut fields: Vec<&[u8]> = Vec::with_capacity(1 + rows.len());
    fields.push(b"QSAG.HEM.POLICY.REGISTRY/v2");
    for row in &rows {
        fields.push(row.as_slice());
    }
    encode_multi_frame(&fields)
}

fn compute_policy_registry_root_with_roots(
    policies: &[ShardHemPolicy],
    committee_roots: &[[u8; 32]],
) -> [u8; 32] {
    poseidon2_hash32(&encode_policy_registry_with_roots(
        policies,
        committee_roots,
    ))
}

/// Self-delimiting `encode_multi_frame` serialization of the ordered shard policy registry,
/// matching `Qsag.encodeRegistry` (`encodeRegistry_injective`).
pub fn encode_policy_registry(policies: &[ShardHemPolicy]) -> Vec<u8> {
    let roots = compute_committee_roots(policies);
    encode_policy_registry_with_roots(policies, &roots)
}

/// Collision-bound 32-byte Poseidon2 commitment over [`encode_policy_registry`].
pub fn compute_policy_registry_root(policies: &[ShardHemPolicy]) -> [u8; 32] {
    poseidon2_hash32(&encode_policy_registry(policies))
}

/// Domain-separated length-framed Poseidon2 digest of an arbitrary message slice.
pub fn compute_framed_message_digest(message: &[u8]) -> [u8; 32] {
    poseidon2_hash32(&encode_multi_frame(&[b"QSAG.HEM.MSG/v2", message]))
}

fn hierarchical_hem_message_with_root(
    policy_registry_root: &[u8; 32],
    policy: &ShardHemPolicy,
    committee_root: &[u8; 32],
    epoch_floor: u64,
    message: &[u8],
) -> Vec<u8> {
    let profile_tag = [policy.profile().map_or(0u8, |p| p as u8)];
    let shard_id_bytes = policy.shard_id.to_le_bytes();
    let min_q_bytes = (policy.minimum_quorums as u64).to_le_bytes();
    let epoch_bytes = epoch_floor.to_le_bytes();
    encode_multi_frame(&[
        b"QSAG.HEM.REGION.BOUND/v2",
        policy_registry_root,
        &shard_id_bytes,
        &policy.custodian_cluster,
        &profile_tag,
        &min_q_bytes,
        committee_root,
        &epoch_bytes,
        message,
    ])
}

/// Exact length-framed regional statement signed by each quorum under `policy`. Every
/// variable-length and fixed-width slice is length-prefixed via [`encode_multi_frame`].
///
/// The statement binds `policy_registry_root` directly into the quorum signature, so a regional
/// batch cannot be spliced into any other global policy registry, even one that contains an
/// identical `ShardHemPolicy` and even if a verifier is handed the altered registry.
pub fn hierarchical_hem_message(
    policy_registry_root: &[u8; 32],
    policy: &ShardHemPolicy,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
) -> Vec<u8> {
    let committee_root = compute_committee_root(&policy.quorum_keys);
    hierarchical_hem_message_with_root(
        policy_registry_root,
        policy,
        &committee_root,
        epoch_floor,
        message.as_ref(),
    )
}

pub struct ShardHemWitness<'a> {
    pub bitmap: &'a SignerBitmap,
    pub signatures: &'a [ValidatorSignature],
}

fn valid_policies(policies: &[ShardHemPolicy]) -> bool {
    if policies.is_empty() || !policies.windows(2).all(|p| p[0].shard_id < p[1].shard_id) {
        return false;
    }
    let mut ids = BTreeSet::new();
    let mut clusters = BTreeSet::new();
    let mut key_identities = BTreeSet::new();
    let mut capacities = Vec::with_capacity(policies.len());
    let mut minimums = Vec::with_capacity(policies.len());

    for p in policies {
        let Some(shard_profile) = p.profile() else {
            return false;
        };
        if p.minimum_quorums == 0
            || p.minimum_quorums > p.quorum_keys.len()
            || !ids.insert(p.shard_id)
            || !clusters.insert(p.custodian_cluster)
        {
            return false;
        }
        for k in &p.quorum_keys {
            if k.profile != shard_profile || !key_identities.insert((k.pk_seed, k.pk_root)) {
                return false;
            }
        }
        let (Ok(cap_u64), Ok(min_u64)) = (
            u64::try_from(p.quorum_keys.len()),
            u64::try_from(p.minimum_quorums),
        ) else {
            return false;
        };
        capacities.push(cap_u64);
        minimums.push(min_u64);
    }

    let Some(total_cap) = qsag_whir_verified::checked_quorum_sum(&capacities, &minimums, 1) else {
        return false;
    };
    usize::try_from(total_cap).is_ok()
}

const HIERARCHY_SHARD_CUSTOM: &[u8] = b"QSAG.HEM.HIERARCHY.SHARD/v3";
const HIERARCHY_SHARD_MIDSTATE: [u64; 25] = cshake256_static_midstate(HIERARCHY_SHARD_CUSTOM);
const HIERARCHY_ROOT_CUSTOM: &[u8] = b"QSAG.HEM.HIERARCHY.ROOT/v3";
const HIERARCHY_ROOT_MIDSTATE: [u64; 25] = cshake256_static_midstate(HIERARCHY_ROOT_CUSTOM);

struct FramedShardBuf {
    buf: Vec<u8>,
    start: usize,
}

impl FramedShardBuf {
    #[inline]
    fn as_slice(&self) -> &[u8] {
        &self.buf[self.start..]
    }
}

fn write_shard_commitment_frame_into(s: &ShardHemBatch, buf: &mut Vec<u8>) -> usize {
    let shard_id_le = s.shard_id.to_le_bytes();
    let min_q_le = s.minimum_quorums.to_le_bytes();
    let epoch_le = s.epoch_floor.to_le_bytes();
    let mut header = Vec::with_capacity(168);
    push_leb128(&mut header, 8);
    for field in [
        HIERARCHY_SHARD_CUSTOM,
        &shard_id_le[..],
        &s.custodian_cluster[..],
        &s.shard_quorum_set_root[..],
        &min_q_le[..],
        &epoch_le[..],
        &s.message_digest[..],
    ] {
        push_leb128(&mut header, field.len());
        header.extend_from_slice(field);
    }
    let reserve = header.len() + 10;
    buf.clear();
    buf.reserve(reserve + 524_288);
    buf.resize(reserve, 0u8);
    s.proof.push_wire_bytes(buf);
    let proof_len = buf.len() - reserve;
    push_leb128(&mut header, proof_len);
    let start = reserve - header.len();
    buf[start..reserve].copy_from_slice(&header);
    start
}

// Per-thread frame buffers: a worker reuses its own allocations and never waits on another
// thread. A thread whose locals are already torn down allocates a fresh buffer.
#[cfg(feature = "std")]
std::thread_local! {
    static SHARD_FRAME_SCRATCH: core::cell::RefCell<Vec<Vec<u8>>> =
        const { core::cell::RefCell::new(Vec::new()) };
}

/// Frame buffers kept per thread (the widest digest path frames four shards at once).
#[cfg(feature = "std")]
const SHARD_FRAME_SCRATCH_PER_THREAD: usize = 8;

fn build_shard_commitment_frame(s: &ShardHemBatch) -> FramedShardBuf {
    #[cfg(feature = "std")]
    let mut buf = SHARD_FRAME_SCRATCH
        .try_with(|pool| pool.borrow_mut().pop())
        .ok()
        .flatten()
        .unwrap_or_default();
    #[cfg(not(feature = "std"))]
    let mut buf = Vec::new();
    let start = write_shard_commitment_frame_into(s, &mut buf);
    FramedShardBuf { buf, start }
}

#[inline]
fn recycle_shard_commitment_frame(frame: FramedShardBuf) {
    #[cfg(feature = "std")]
    {
        let mut buf = frame.buf;
        buf.clear();
        let _ = SHARD_FRAME_SCRATCH.try_with(|pool| {
            let mut pool = pool.borrow_mut();
            if pool.len() < SHARD_FRAME_SCRATCH_PER_THREAD {
                pool.push(buf);
            }
        });
    }
    #[cfg(not(feature = "std"))]
    let _ = frame;
}

/// Digest of one child of the hierarchy byte-hash tree. A byte-hash tree avoids a serial
/// algebraic sponge over the entire aggregate; each child binds every field of its shard,
/// including the full canonical proof bytes.
fn shard_commitment_digest(s: &ShardHemBatch) -> [u8; 32] {
    let _phase = crate::profile::span("hierarchy_shard_digest");
    let frame = build_shard_commitment_frame(s);
    let digest = cshake256_from_midstate_32(&HIERARCHY_SHARD_MIDSTATE, frame.as_slice());
    recycle_shard_commitment_frame(frame);
    digest
}

fn shard_commitment_digests_seq(shards: &[ShardHemBatch]) -> Vec<[u8; 32]> {
    let _phase = crate::profile::span("hierarchy_shard_digest");
    let mut out = Vec::with_capacity(shards.len());
    let (chunks, rem) = shards.as_chunks::<4>();
    for quad in chunks {
        let f0 = build_shard_commitment_frame(&quad[0]);
        let f1 = build_shard_commitment_frame(&quad[1]);
        let f2 = build_shard_commitment_frame(&quad[2]);
        let f3 = build_shard_commitment_frame(&quad[3]);
        let d4 = cshake256_from_midstate_32_x4(
            &HIERARCHY_SHARD_MIDSTATE,
            [f0.as_slice(), f1.as_slice(), f2.as_slice(), f3.as_slice()],
        );
        recycle_shard_commitment_frame(f0);
        recycle_shard_commitment_frame(f1);
        recycle_shard_commitment_frame(f2);
        recycle_shard_commitment_frame(f3);
        out.extend_from_slice(&d4);
    }
    for s in rem {
        let f = build_shard_commitment_frame(s);
        let d = cshake256_from_midstate_32(&HIERARCHY_SHARD_MIDSTATE, f.as_slice());
        recycle_shard_commitment_frame(f);
        out.push(d);
    }
    out
}

/// A proven shard with its child digest of the hierarchy commitment.
type CommittedShard = (ShardHemBatch, [u8; 32]);

/// Root of the hierarchy byte-hash tree over the ordered child digests.
fn root_commitment_from_digests(policy_registry_root: &[u8; 32], digests: &[[u8; 32]]) -> [u8; 32] {
    let mut fields: Vec<&[u8]> = Vec::with_capacity(2 + digests.len());
    fields.push(HIERARCHY_ROOT_CUSTOM);
    fields.push(policy_registry_root);
    fields.extend(digests.iter().map(|d| d.as_slice()));
    cshake256_from_midstate_32(&HIERARCHY_ROOT_MIDSTATE, &encode_multi_frame(&fields))
}

fn prove_hierarchical_hem_inner(
    policies: &[ShardHemPolicy],
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: &[u8],
    minimum_global_quorums: usize,
    config: &HemAggConfig,
) -> Result<HierarchicalHemAggregate, HemAggError> {
    if !valid_policies(policies) { return Err(HemAggError::InvalidShardConfig); }
    let committee_roots = compute_committee_roots(policies);
    let policy_registry_root = compute_policy_registry_root_with_roots(policies, &committee_roots);
    prove_hierarchical_hem_with_roots(policies, &committee_roots, policy_registry_root,
        witnesses, epoch_floor, message, minimum_global_quorums, config)
}

#[allow(clippy::too_many_arguments)]
fn prove_hierarchical_hem_with_roots(
    policies: &[ShardHemPolicy], committee_roots: &[[u8;32]], policy_registry_root: [u8;32],
    witnesses: &[ShardHemWitness<'_>], epoch_floor: u64, message: &[u8],
    minimum_global_quorums: usize, config: &HemAggConfig,
) -> Result<HierarchicalHemAggregate, HemAggError> {
    if !valid_policies(policies) || witnesses.len() != policies.len() || minimum_global_quorums == 0
    {
        return Err(HemAggError::InvalidShardConfig);
    }
    let min_global_u64 =
        u64::try_from(minimum_global_quorums).map_err(|_| HemAggError::InvalidShardConfig)?;
    let mut counts_u64 = Vec::with_capacity(policies.len());
    let mut minimums_u64 = Vec::with_capacity(policies.len());
    let mut precheck_under_min = false;
    for (p, w) in policies.iter().zip(witnesses) {
        let n = w.bitmap.count_ones();
        if n < p.minimum_quorums {
            precheck_under_min = true;
        }
        counts_u64.push(u64::try_from(n).map_err(|_| HemAggError::InvalidShardConfig)?);
        minimums_u64
            .push(u64::try_from(p.minimum_quorums).map_err(|_| HemAggError::InvalidShardConfig)?);
    }
    if precheck_under_min {
        return Err(HemAggError::EmptySigners);
    }
    let Some(total_u64) =
        qsag_whir_verified::checked_quorum_sum(&counts_u64, &minimums_u64, min_global_u64)
    else {
        let sum_no_global = qsag_whir_verified::checked_quorum_sum(&counts_u64, &minimums_u64, 1);
        return Err(if sum_no_global.is_some() {
            HemAggError::EmptySigners
        } else {
            HemAggError::InvalidShardConfig
        });
    };
    usize::try_from(total_u64).map_err(|_| HemAggError::InvalidShardConfig)?;

    let message_digest = compute_framed_message_digest(message);
    if config.max_signers_per_shard == 0 {
        return Err(HemAggError::InvalidShardConfig);
    }

    let prove_shard = |((p, w), c_root): ((&ShardHemPolicy, &ShardHemWitness<'_>), &[u8; 32])|
     -> Result<CommittedShard, HemAggError> {
        let shard_profile = p.profile().ok_or(HemAggError::InvalidShardConfig)?;
        let region_msg = hierarchical_hem_message_with_root(
            &policy_registry_root,
            p,
            c_root,
            epoch_floor,
            message,
        );
        let mut cfg = config.clone();
        cfg.max_signers_per_shard = cfg
            .max_signers_per_shard
            .min(max_shard_signers(shard_profile));
        let shard_id_bytes = p.shard_id.to_le_bytes();
        cfg.blinding_seed = poseidon2_hash32(&encode_multi_frame(&[
            b"QSAG.HEM.BLIND/v2",
            &config.blinding_seed,
            &policy_registry_root,
            &shard_id_bytes,
            &region_msg,
        ]));
        let proof = aggregate_signatures_with_committee_root(
            &p.quorum_keys,
            Some(*c_root),
            w.bitmap,
            &SigningMode::SharedMessage(&region_msg),
            w.signatures,
            &cfg,
        )?;
        let shard = ShardHemBatch {
            shard_id: p.shard_id,
            custodian_cluster: p.custodian_cluster,
            shard_quorum_set_root: *c_root,
            minimum_quorums: p.minimum_quorums as u64,
            epoch_floor,
            message_digest,
            proof,
        };
        let digest = shard_commitment_digest(&shard);
        Ok((shard, digest))
    };

    #[cfg(feature = "std")]
    let proved: Vec<CommittedShard> = if policies.len() > 1 && crate::parallel_workers() > 1 {
        let triples: Vec<_> = policies
            .iter()
            .zip(witnesses)
            .zip(committee_roots.iter())
            .collect();
        let groups: Vec<Result<Vec<CommittedShard>, HemAggError>> =
            crate::map_chunks_bounded_with_limit(&triples, crate::prover_parallel_jobs(), |sub| {
                sub.iter().copied().map(&prove_shard).collect()
            });
        let mut out = Vec::with_capacity(policies.len());
        for g in groups {
            out.extend(g?);
        }
        out
    } else {
        policies
            .iter()
            .zip(witnesses)
            .zip(committee_roots.iter())
            .map(prove_shard)
            .collect::<Result<Vec<_>, _>>()?
    };

    #[cfg(not(feature = "std"))]
    let proved: Vec<CommittedShard> = policies
        .iter()
        .zip(witnesses)
        .zip(committee_roots.iter())
        .map(prove_shard)
        .collect::<Result<Vec<_>, _>>()?;

    let (shards, digests): (Vec<ShardHemBatch>, Vec<[u8; 32]>) = proved.into_iter().unzip();
    Ok(HierarchicalHemAggregate {
        policy_registry_root,
        root_commitment: root_commitment_from_digests(&policy_registry_root, &digests),
        shards,
    })
}

/// Pre-validated regional policy registry with cached per-shard Merkle committee roots and
/// `policy_registry_root` for zero-rehash per-slot verification ([`verify_hierarchical_hem_prepared`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPolicyRegistry {
    policies: Vec<ShardHemPolicy>,
    committee_roots: Vec<[u8; 32]>,
    policy_registry_root: [u8; 32],
}

impl PreparedPolicyRegistry {
    /// Validate `policies` and precompute all regional committee roots and `policy_registry_root`.
    pub fn new(policies: Vec<ShardHemPolicy>) -> Option<Self> {
        if !valid_policies(&policies) {
            return None;
        }
        let committee_roots = compute_committee_roots(&policies);
        let policy_registry_root =
            compute_policy_registry_root_with_roots(&policies, &committee_roots);
        Some(Self {
            policies,
            committee_roots,
            policy_registry_root,
        })
    }

    /// Ordered regional policy slice.
    pub fn policies(&self) -> &[ShardHemPolicy] {
        &self.policies
    }

    /// Precomputed regional committee Merkle roots (`committee_roots()[i]` matches `policies()[i]`).
    pub fn committee_roots(&self) -> &[[u8; 32]] {
        &self.committee_roots
    }

    /// Precomputed 32-byte `policy_registry_root`.
    pub fn policy_registry_root(&self) -> [u8; 32] {
        self.policy_registry_root
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_hierarchical_hem_with_roots(
    policies: &[ShardHemPolicy],
    committee_roots: &[[u8; 32]],
    expected_registry_root: [u8; 32],
    epoch_floor: u64,
    message: &[u8],
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &HierarchicalHemAggregate,
) -> bool {
    if aggregate.shards.len() != policies.len()
        || committee_roots.len() != policies.len()
        || minimum_global_quorums == 0
    {
        return false;
    }
    let Ok(min_global_u64) = u64::try_from(minimum_global_quorums) else {
        return false;
    };
    if aggregate.policy_registry_root != expected_registry_root {
        return false;
    }
    let expected_msg_digest = compute_framed_message_digest(message);

    let mut counts_u64 = Vec::with_capacity(policies.len());
    let mut minimums_u64 = Vec::with_capacity(policies.len());
    for ((p, s), c_root) in policies
        .iter()
        .zip(&aggregate.shards)
        .zip(committee_roots.iter())
    {
        let Some(shard_profile) = p.profile() else {
            return false;
        };
        let Ok(expected_min_u64) = u64::try_from(p.minimum_quorums) else {
            return false;
        };
        let Ok(verified_signers_u64) = u64::try_from(s.proof.num_signers()) else {
            return false;
        };
        if s.shard_id != p.shard_id
            || s.custodian_cluster != p.custodian_cluster
            || s.shard_quorum_set_root != *c_root
            || s.minimum_quorums != expected_min_u64
            || s.epoch_floor != epoch_floor
            || s.message_digest != expected_msg_digest
            || s.proof.profile != shard_profile
            || s.proof.num_signers() < p.minimum_quorums
        {
            return false;
        }
        counts_u64.push(verified_signers_u64);
        minimums_u64.push(expected_min_u64);
    }

    let Some(total_u64) =
        qsag_whir_verified::checked_quorum_sum(&counts_u64, &minimums_u64, min_global_u64)
    else {
        return false;
    };
    if usize::try_from(total_u64).is_err() {
        return false;
    }

    let verify_shard_only =
        |((p, s), c_root): ((&ShardHemPolicy, &ShardHemBatch), &[u8; 32])| -> bool {
            // Reject unsafe framing/depth before hashing a directly constructed proof.
            if s.proof.root.homogeneous_regime(crate::MAX_MERGE_TREE_DEPTH) != Some(regime) {
                return false;
            }
            let region_msg = hierarchical_hem_message_with_root(
                &expected_registry_root,
                p,
                c_root,
                epoch_floor,
                message,
            );
            verify_aggregate_with_committee_root(
                &p.quorum_keys,
                Some(*c_root),
                &SigningMode::SharedMessage(&region_msg),
                &s.proof,
                regime,
            )
        };

    #[cfg(feature = "std")]
    let verify_shard =
        |triple: ((&ShardHemPolicy, &ShardHemBatch), &[u8; 32])| -> Option<[u8; 32]> {
            verify_shard_only(triple).then(|| shard_commitment_digest(triple.0.1))
        };

    #[cfg(feature = "std")]
    let digests: Option<Vec<[u8; 32]>> =
        if aggregate.shards.len() > 1 && crate::parallel_workers() > 1 {
            let triples: Vec<_> = policies
                .iter()
                .zip(&aggregate.shards)
                .zip(committee_roots.iter())
                .collect();
            let workers = crate::available_worker_budget().min(triples.len());
            if workers > 1 {
                let chunk = triples.len().div_ceil(workers);
                let verify_ref = &verify_shard;
                std::thread::scope(|scope| {
                    let slices: Vec<_> = triples.chunks(chunk).collect();
                    let tails: Vec<_> = slices[1..]
                        .iter()
                        .map(|&sub| {
                            crate::spawn_bounded(scope, move || {
                                sub.iter()
                                    .copied()
                                    .map(verify_ref)
                                    .collect::<Option<Vec<_>>>()
                            })
                        })
                        .collect();
                    let head = slices[0]
                        .iter()
                        .copied()
                        .map(verify_ref)
                        .collect::<Option<Vec<_>>>();
                    let tail_results: Vec<Option<Vec<[u8; 32]>>> =
                        tails.into_iter().map(crate::join_worker).collect();
                    let mut out = Vec::with_capacity(triples.len());
                    out.extend(head?);
                    for group in tail_results {
                        out.extend(group?);
                    }
                    Some(out)
                })
            } else {
                triples
                    .into_iter()
                    .all(verify_shard_only)
                    .then(|| shard_commitment_digests_seq(&aggregate.shards))
            }
        } else {
            policies
                .iter()
                .zip(&aggregate.shards)
                .zip(committee_roots.iter())
                .all(verify_shard_only)
                .then(|| shard_commitment_digests_seq(&aggregate.shards))
        };

    #[cfg(not(feature = "std"))]
    let digests: Option<Vec<[u8; 32]>> = policies
        .iter()
        .zip(&aggregate.shards)
        .zip(committee_roots.iter())
        .all(verify_shard_only)
        .then(|| shard_commitment_digests_seq(&aggregate.shards));

    let Some(digests) = digests else {
        return false;
    };
    root_commitment_from_digests(&expected_registry_root, &digests) == aggregate.root_commitment
}

fn verify_hierarchical_hem_inner(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: &[u8],
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &HierarchicalHemAggregate,
) -> bool {
    let _phase = crate::profile::span("verify_hierarchical_hem");
    if !valid_policies(policies)
        || aggregate.shards.len() != policies.len()
        || minimum_global_quorums == 0
    {
        return false;
    }
    let committee_roots = compute_committee_roots(policies);
    let expected_registry_root =
        compute_policy_registry_root_with_roots(policies, &committee_roots);
    verify_hierarchical_hem_with_roots(
        policies,
        &committee_roots,
        expected_registry_root,
        epoch_floor,
        message,
        minimum_global_quorums,
        regime,
        aggregate,
    )
}

/// Prove a two-layer hierarchical `Hem` aggregate across `policies` (`JortsPoseidon2`,
/// `CorduroyPoseidon2`, or mixed regional profiles). Every quorum signature must be over the
/// registry-pinned [`hierarchical_hem_message`].
pub fn prove_hierarchical_hem(
    policies: &[ShardHemPolicy],
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    config: &HemAggConfig,
) -> Result<HierarchicalHemAggregate, HemAggError> {
    prove_hierarchical_hem_inner(
        policies,
        witnesses,
        epoch_floor,
        message.as_ref(),
        minimum_global_quorums,
        config,
    )
}

/// Prove using the registry's validated policies and cached committee roots.
/// Shares the exact statement and transcript of [`prove_hierarchical_hem`].
pub fn prove_hierarchical_hem_prepared(
    registry: &PreparedPolicyRegistry,
    witnesses: &[ShardHemWitness<'_>], epoch_floor: u64, message: impl AsRef<[u8]>,
    minimum_global_quorums: usize, config: &HemAggConfig,
) -> Result<HierarchicalHemAggregate, HemAggError> {
    prove_hierarchical_hem_with_roots(&registry.policies, &registry.committee_roots,
        registry.policy_registry_root, witnesses, epoch_floor, message.as_ref(),
        minimum_global_quorums, config)
}

/// Verify a two-layer hierarchical `Hem` aggregate against `policies`, exact `epoch_floor` and
/// `message`, global quorum threshold, and `regime`. Child signatures are checked against the
/// registry-pinned [`hierarchical_hem_message`] of exactly this `policies` registry.
pub fn verify_hierarchical_hem(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &HierarchicalHemAggregate,
) -> bool {
    verify_hierarchical_hem_inner(
        policies,
        epoch_floor,
        message.as_ref(),
        minimum_global_quorums,
        regime,
        aggregate,
    )
}

/// Verify a two-layer hierarchical `Hem` aggregate against a pre-validated epoch
/// [`PreparedPolicyRegistry`], skipping redundant per-slot committee Merkle root and
/// `policy_registry_root` recomputation while preserving 100% identical verification semantics.
pub fn verify_hierarchical_hem_prepared(
    registry: &PreparedPolicyRegistry,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &HierarchicalHemAggregate,
) -> bool {
    let _phase = crate::profile::span("verify_hierarchical_hem");
    verify_hierarchical_hem_with_roots(
        &registry.policies,
        &registry.committee_roots,
        registry.policy_registry_root,
        epoch_floor,
        message.as_ref(),
        minimum_global_quorums,
        regime,
        aggregate,
    )
}

// ============================================================================
// Compact `Hem` commitment chains (`QSAGSHM\x01`)
// ============================================================================

const OUTER_COL_PREV_CHAIN: usize = 130; // 130..134
const OUTER_COL_NEXT_CHAIN: usize = 134; // 134..138
const OUTER_COL_ROW_IN: usize = 138; // 138..146 (8 canonical u32 limbs)
const OUTER_COL_BLIND: usize = 252; // 252..256 (idle-row blinding limbs)

/// Compact shard summary carried by [`SuccinctHierarchicalHemAggregate`] (zero child WHIR proofs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardHemSummary {
    pub shard_id: u64,
    pub custodian_cluster: [u8; 32],
    pub shard_quorum_set_root: [u8; 32],
    pub minimum_quorums: u64,
    pub epoch_floor: u64,
    pub message_digest: [u8; 32],
    pub bitmap: SignerBitmap,
    pub child_proof_digest: [u8; 32],
}

impl ShardHemSummary {
    #[inline]
    pub fn num_signers(&self) -> usize {
        self.bitmap.count_ones()
    }
}

/// Single outer `BciksJohnsonQrom128` 256-column width-12 `Poseidon2` $x^7$ Sumcheck + WHIR proof
/// compressing the $M$-shard commitment chain into $O(1)$ WHIR openings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OuterHemChainProof {
    pub witness_comm: CanopyCommitment,
    pub row_sumcheck_polys: Vec<[GoldilocksExt4; ROW_SUMCHECK_WIRE_COEFFS]>,
    pub col_evals: Vec<GoldilocksExt4>,
    pub pcs_opening: HemWhirOpeningProof,
}

/// Compact commitment to a hierarchy's summaries and child-proof digests.
///
/// The historical type name and wire format are retained. This is not a standalone
/// signature certificate: the outer relation proves hashing of public summaries, not child
/// verification. Use [`verify_succinct_hierarchical_hem`] with locally validated evidence;
/// [`check_hierarchical_hem_commitment`] checks only the commitment relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctHierarchicalHemAggregate {
    pub policy_registry_root: [u8; 32],
    pub shards: Vec<ShardHemSummary>,
    pub terminal_chain_digest: [Goldilocks; 4],
    pub outer_proof: OuterHemChainProof,
}

/// Immutable local evidence that all child proofs were verified in one exact context.
///
/// Only [`verify_hierarchical_hem_evidence`] can construct this value. It owns its checked
/// summaries, so later mutation of the original hierarchy cannot alter the evidence. It has
/// no wire decoder: receiving a serialized compact commitment does not establish this fact.
///
/// ```compile_fail
/// use qsag_agg::VerifiedHierarchicalHemEvidence;
/// let fabricated = VerifiedHierarchicalHemEvidence {};
/// ```
///
/// ```compile_fail
/// use qsag_agg::VerifiedHierarchicalHemEvidence;
/// fn change_context(evidence: &mut VerifiedHierarchicalHemEvidence) {
///     evidence.minimum_global_quorums = 0;
/// }
/// ```
#[derive(Clone, Debug)]
pub struct VerifiedHierarchicalHemEvidence {
    policy_registry_root: [u8; 32],
    epoch_floor: u64,
    message_digest: [u8; 32],
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    shards: Vec<ShardHemSummary>,
}

impl VerifiedHierarchicalHemEvidence {
    /// Registry root the children were verified under.
    pub fn policy_registry_root(&self) -> &[u8; 32] {
        &self.policy_registry_root
    }

    /// Epoch floor the children were verified at.
    pub fn epoch_floor(&self) -> u64 {
        self.epoch_floor
    }

    /// Framed digest of the verified message.
    pub fn message_digest(&self) -> &[u8; 32] {
        &self.message_digest
    }

    /// Global threshold the verification enforced.
    pub fn minimum_global_quorums(&self) -> usize {
        self.minimum_global_quorums
    }

    /// Security regime every child proof was verified under.
    pub fn regime(&self) -> WhirSecurityRegime {
        self.regime
    }

    /// Verified shard summaries, in registry order.
    pub fn summaries(&self) -> &[ShardHemSummary] {
        &self.shards
    }

    /// Verified signer total (`None` on overflow).
    pub fn checked_total_quorums(&self) -> Option<usize> {
        checked_sum_usize(self.shards.iter().map(ShardHemSummary::num_signers))
    }

    /// Whether `commitment` names exactly the verified registry, summaries and chain digest.
    /// Context (epoch, message, threshold, regime) and the outer proof are not examined;
    /// authorization goes through [`verify_succinct_hierarchical_hem_with_regime`].
    pub fn names_same_children(&self, commitment: &SuccinctHierarchicalHemAggregate) -> bool {
        self.policy_registry_root == commitment.policy_registry_root
            && self.shards == commitment.shards
            && compact_summary_chain_digest(&self.shards) == commitment.terminal_chain_digest
    }
}

fn hierarchy_summaries(aggregate: &HierarchicalHemAggregate) -> Vec<ShardHemSummary> {
    aggregate
        .shards
        .iter()
        .zip(shard_commitment_digests_seq(&aggregate.shards))
        .map(|(s, child_proof_digest)| ShardHemSummary {
            shard_id: s.shard_id,
            custodian_cluster: s.custodian_cluster,
            shard_quorum_set_root: s.shard_quorum_set_root,
            minimum_quorums: s.minimum_quorums,
            epoch_floor: s.epoch_floor,
            message_digest: s.message_digest,
            bitmap: s.proof.bitmap().clone(),
            child_proof_digest,
        })
        .collect()
}

/// Verify all child proofs and retain immutable evidence for subsequent compact-commitment checks.
///
/// The cost and bandwidth of obtaining the full hierarchy remain part of first-time signature
/// verification. Cached evidence can be reused only for the same registry, epoch, message,
/// global threshold, security regime, and exact child summaries/proof digests.
pub fn verify_hierarchical_hem_evidence(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &HierarchicalHemAggregate,
) -> Option<VerifiedHierarchicalHemEvidence> {
    let message = message.as_ref();
    if !regime.meets_qrom_128_floor()
        || !verify_hierarchical_hem_inner(
            policies,
            epoch_floor,
            message,
            minimum_global_quorums,
            regime,
            aggregate,
        )
    {
        return None;
    }
    Some(VerifiedHierarchicalHemEvidence {
        policy_registry_root: aggregate.policy_registry_root,
        epoch_floor,
        message_digest: compute_framed_message_digest(message),
        minimum_global_quorums,
        regime,
        shards: hierarchy_summaries(aggregate),
    })
}

/// [`verify_hierarchical_hem_evidence`] against a [`PreparedPolicyRegistry`]: one pass over
/// the children both verifies them and yields the evidence, without rebuilding committee roots.
pub fn verify_hierarchical_hem_evidence_prepared(
    registry: &PreparedPolicyRegistry,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &HierarchicalHemAggregate,
) -> Option<VerifiedHierarchicalHemEvidence> {
    let message = message.as_ref();
    if !regime.meets_qrom_128_floor()
        || !verify_hierarchical_hem_with_roots(
            &registry.policies,
            &registry.committee_roots,
            registry.policy_registry_root,
            epoch_floor,
            message,
            minimum_global_quorums,
            regime,
            aggregate,
        )
    {
        return None;
    }
    Some(VerifiedHierarchicalHemEvidence {
        policy_registry_root: aggregate.policy_registry_root,
        epoch_floor,
        message_digest: compute_framed_message_digest(message),
        minimum_global_quorums,
        regime,
        shards: hierarchy_summaries(aggregate),
    })
}

#[inline]
fn outer_chain_num_rows(num_shards: usize) -> Option<(usize, usize)> {
    if num_shards == 0 || num_shards > MAX_HIERARCHY_SHARDS {
        return None;
    }
    let active_rows = num_shards.checked_mul(2)?;
    let num_rows = active_rows.next_power_of_two().max(2);
    let log_rows = num_rows.trailing_zeros() as usize;
    Some((num_rows, log_rows))
}

#[inline]
fn digest32_to_u32_limbs(digest: &[u8; 32]) -> [Goldilocks; 8] {
    let mut limbs = [Goldilocks::ZERO; 8];
    for (k, dst) in limbs.iter_mut().enumerate() {
        let off = 4 * k;
        let word = u32::from_le_bytes([
            digest[off],
            digest[off + 1],
            digest[off + 2],
            digest[off + 3],
        ]);
        *dst = Goldilocks::from_u64_reduced(word as u64);
    }
    limbs
}

fn shard_summary_header_digest(summary: &ShardHemSummary) -> [u8; 32] {
    let shard_id_le = summary.shard_id.to_le_bytes();
    let min_q_le = summary.minimum_quorums.to_le_bytes();
    let epoch_le = summary.epoch_floor.to_le_bytes();
    let bm_bytes = summary.bitmap.to_bytes();
    poseidon2_hash32(&encode_multi_frame(&[
        b"QSAG.SHM.SUMMARY.HDR/v1",
        &shard_id_le,
        &summary.custodian_cluster,
        &summary.shard_quorum_set_root,
        &min_q_le,
        &epoch_le,
        &summary.message_digest,
        &bm_bytes,
    ]))
}

#[inline]
fn jive_weighted_ff_step(
    prev_chain: [Goldilocks; 4],
    row_in: [Goldilocks; 8],
) -> ([Goldilocks; 12], [Goldilocks; 118], [Goldilocks; 4]) {
    let mut st_in = [Goldilocks::ZERO; 12];
    st_in[0..4].copy_from_slice(&prev_chain);
    st_in[4..8].copy_from_slice(&row_in[0..4]);
    st_in[8..12].copy_from_slice(&row_in[4..8]);
    let mut sbox = [Goldilocks::ZERO; 118];
    let perm_out = record_poseidon2_perm12(st_in, &mut sbox);
    // Weighted 3-block Jive feed-forward (`perm_out.b0 + st_in.b0 + 2*st_in.b1 + 3*st_in.b2`),
    // matching `Qsag.jiveWeightedFeedForward` (`ePrint 2026/306` §6).
    let mut next_chain = [Goldilocks::ZERO; 4];
    for j in 0..4 {
        let b0 = st_in[j];
        let b1 = st_in[4 + j];
        let b2 = st_in[8 + j];
        next_chain[j] = perm_out[j] + b0 + (b1 + b1) + (b2 + b2 + b2);
    }
    (st_in, sbox, next_chain)
}

/// Recompute the terminal Poseidon2 chain digest of `shards` directly.
///
/// This is the value the outer proof of a [`SuccinctHierarchicalHemAggregate`] certifies: a
/// deterministic function of the public summaries, costing two permutations per shard. A
/// verifier holding the summaries can therefore obtain it without the outer proof.
pub fn compact_summary_chain_digest(shards: &[ShardHemSummary]) -> [Goldilocks; 4] {
    let mut chain = [Goldilocks::ZERO; 4];
    for summary in shards {
        let hdr = digest32_to_u32_limbs(&shard_summary_header_digest(summary));
        let prf = digest32_to_u32_limbs(&summary.child_proof_digest);
        for limbs in [hdr, prf] {
            chain = jive_weighted_ff_step(chain, limbs).2;
        }
    }
    chain
}

#[inline]
fn pack_outer_deg8_wire(
    full: &[GoldilocksExt4; ROW_SUMCHECK_COEFFS],
) -> [GoldilocksExt4; ROW_SUMCHECK_WIRE_COEFFS] {
    [
        full[0], full[2], full[3], full[4], full[5], full[6], full[7], full[8],
    ]
}

#[inline]
fn unpack_outer_deg8_wire(
    wire: &[GoldilocksExt4; ROW_SUMCHECK_WIRE_COEFFS],
    sum_claim: GoldilocksExt4,
) -> [GoldilocksExt4; ROW_SUMCHECK_COEFFS] {
    let mut hi_sum = GoldilocksExt4::ZERO;
    for &c in &wire[1..] {
        hi_sum += c;
    }
    let c0 = wire[0];
    let c1 = sum_claim - c0 - c0 - hi_sum;
    [
        c0, c1, wire[1], wire[2], wire[3], wire[4], wire[5], wire[6], wire[7],
    ]
}

fn encode_summaries_instance_frame(shards: &[ShardHemSummary]) -> Vec<u8> {
    let per_shard: Vec<Vec<u8>> = shards
        .iter()
        .map(|s| {
            let sid = s.shard_id.to_le_bytes();
            let min_q = s.minimum_quorums.to_le_bytes();
            let ep = s.epoch_floor.to_le_bytes();
            let bm = s.bitmap.to_bytes();
            encode_multi_frame(&[
                &sid,
                &s.custodian_cluster,
                &s.shard_quorum_set_root,
                &min_q,
                &ep,
                &s.message_digest,
                &bm,
                &s.child_proof_digest,
            ])
        })
        .collect();
    let slices: Vec<&[u8]> = per_shard.iter().map(Vec::as_slice).collect();
    encode_multi_frame(&slices)
}

fn init_outer_chain_transcript(
    policy_registry_root: &[u8; 32],
    epoch_floor: u64,
    message_digest: &[u8; 32],
    minimum_global_quorums: u64,
    shards: &[ShardHemSummary],
    terminal_chain_digest: &[Goldilocks; 4],
    schedule: &WhirSchedule,
) -> FiatShamirTranscript<InstanceBound> {
    let num_shards_le = (shards.len() as u64).to_le_bytes();
    let epoch_le = epoch_floor.to_le_bytes();
    let min_global_le = minimum_global_quorums.to_le_bytes();
    let mut term_bytes = [0u8; 32];
    for (j, limb) in terminal_chain_digest.iter().enumerate() {
        term_bytes[8 * j..8 * (j + 1)].copy_from_slice(&limb.to_le_bytes());
    }
    let summaries_frame = encode_summaries_instance_frame(shards);
    FiatShamirTranscript::new()
        .bind_relation(b"QSAG.SUCCINCT.OUTER.HEM/v1", &num_shards_le, schedule)
        .bind_instance(&[
            policy_registry_root,
            &epoch_le,
            message_digest,
            &min_global_le,
            &term_bytes,
            &summaries_frame,
        ])
}

#[allow(clippy::too_many_arguments)]
fn eval_outer_chain_row_constraints_ext4(
    cols: &[GoldilocksExt4; NUM_TRACE_COLS],
    pub_row_in: &[GoldilocksExt4; 8],
    terminal_chain_ext4: &[GoldilocksExt4; 4],
    is_active: GoldilocksExt4,
    is_row_first: GoldilocksExt4,
    is_row_last: GoldilocksExt4,
    eq_tau: GoldilocksExt4,
    eq_not_last: GoldilocksExt4,
    shift_tau: GoldilocksExt4,
    gamma: GoldilocksExt4,
) -> GoldilocksExt4 {
    let mut eq_acc = GoldilocksExt4::ZERO;
    let mut g_pow = GoldilocksExt4::ONE;
    let mut push_eq = |res: GoldilocksExt4| {
        if !res.is_zero() {
            eq_acc += g_pow * res;
        }
        g_pow *= gamma;
    };

    // 1. All 118 degree-7 width-12 `Poseidon2` S-box round equations (`4` full + `22` partial + `4` full).
    let mut st = [GoldilocksExt4::ZERO; 12];
    st.copy_from_slice(&cols[COL_ST_IN..COL_ST_IN + 12]);
    poseidon2_apply_me_ext4(&mut st);
    let mut cursor = 0usize;
    for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
        for (lane, lane_val) in st.iter_mut().enumerate() {
            let rc = GoldilocksExt4::from_base(poseidon2_const_at(0, r as u64, lane as u64));
            let expected = poseidon2_sbox7_ext4(*lane_val + rc);
            let sbox_col = cols[COL_SBOX_OUT + cursor];
            push_eq(sbox_col - expected);
            *lane_val = sbox_col;
            cursor += 1;
        }
        poseidon2_apply_me_ext4(&mut st);
    }
    for r in 0..POSEIDON2_INT_ROUNDS {
        let rc = GoldilocksExt4::from_base(poseidon2_const_at(1, r as u64, 0));
        let expected = poseidon2_sbox7_ext4(st[0] + rc);
        let sbox_col = cols[COL_SBOX_OUT + cursor];
        push_eq(sbox_col - expected);
        st[0] = sbox_col;
        cursor += 1;
        poseidon2_apply_mi_ext4(&mut st);
    }
    for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
        for (lane, lane_val) in st.iter_mut().enumerate() {
            let rc = GoldilocksExt4::from_base(poseidon2_const_at(2, r as u64, lane as u64));
            let expected = poseidon2_sbox7_ext4(*lane_val + rc);
            let sbox_col = cols[COL_SBOX_OUT + cursor];
            push_eq(sbox_col - expected);
            *lane_val = sbox_col;
            cursor += 1;
        }
        poseidon2_apply_me_ext4(&mut st);
    }
    debug_assert_eq!(cursor, 118);

    // 2. Bind committed `row_in[0..8]` to the public header/child-proof limb MLE.
    for (k, &pub_limb) in pub_row_in.iter().enumerate() {
        push_eq(cols[OUTER_COL_ROW_IN + k] - pub_limb);
    }

    // 3. Genesis row (`t == 0`) starts from `prev_chain == [0; 4]`.
    for j in 0..4 {
        push_eq(is_row_first * cols[OUTER_COL_PREV_CHAIN + j]);
    }

    // 4. Active absorption rows (`t < 2*M`): `st_in = [prev_chain, row_in[0..4], row_in[4..8]]`
    //    and weighted 3-block Jive feed-forward `next_chain = perm_out.b0 + b0 + 2*b1 + 3*b2`.
    for j in 0..4 {
        push_eq(is_active * (cols[COL_ST_IN + j] - cols[OUTER_COL_PREV_CHAIN + j]));
    }
    for j in 0..4 {
        push_eq(is_active * (cols[COL_ST_IN + 4 + j] - cols[OUTER_COL_ROW_IN + j]));
    }
    for j in 0..4 {
        push_eq(is_active * (cols[COL_ST_IN + 8 + j] - cols[OUTER_COL_ROW_IN + 4 + j]));
    }
    for j in 0..4 {
        let b0 = cols[COL_ST_IN + j];
        let b1 = cols[COL_ST_IN + 4 + j];
        let b2 = cols[COL_ST_IN + 8 + j];
        let jive_ff = st[j] + b0 + (b1 + b1) + (b2 + b2 + b2);
        push_eq(is_active * (cols[OUTER_COL_NEXT_CHAIN + j] - jive_ff));
    }

    // 5. Idle padding rows (`t >= 2*M`) carry `next_chain == prev_chain` forward unchanged.
    let idle_sel = GoldilocksExt4::ONE - is_active;
    for j in 0..4 {
        push_eq(idle_sel * (cols[OUTER_COL_NEXT_CHAIN + j] - cols[OUTER_COL_PREV_CHAIN + j]));
    }

    // 6. Terminal row (`t == R - 1`) matches `terminal_chain_digest`.
    for (j, &term_limb) in terminal_chain_ext4.iter().enumerate() {
        push_eq(is_row_last * (cols[OUTER_COL_NEXT_CHAIN + j] - term_limb));
    }

    // 7. Multilinear inter-row shift bus (`next_chain[t] == prev_chain[t + 1]` for `0 <= t < R - 1`).
    let mut total = eq_tau * eq_acc;
    for j in 0..4 {
        let shift_res = eq_not_last * cols[OUTER_COL_NEXT_CHAIN + j]
            - shift_tau * cols[OUTER_COL_PREV_CHAIN + j];
        total += g_pow * shift_res;
        g_pow *= gamma;
    }
    total
}

impl SuccinctHierarchicalHemAggregate {
    /// Total quorum signers claimed across all regional shard summaries (`None` on overflow).
    pub fn checked_total_quorums(&self) -> Option<usize> {
        checked_sum_usize(self.shards.iter().map(ShardHemSummary::num_signers))
    }

    /// WHIR schedule of the outer chain proof under `regime` (`None` for an invalid shard count).
    pub fn outer_schedule(&self, regime: WhirSecurityRegime) -> Option<WhirSchedule> {
        let (_, log_rows) = outer_chain_num_rows(self.shards.len())?;
        Some(regime.schedule(LOG_TRACE_COLS + log_rows))
    }

    /// Merkle hash work of verifying the outer chain proof under `regime`.
    pub fn outer_merkle_census(
        &self,
        regime: WhirSecurityRegime,
    ) -> Option<crate::recursion_census::MerkleHashCensus> {
        crate::recursion_census::whir_opening_merkle_census(
            &self.outer_schedule(regime)?,
            &self.outer_proof.witness_comm,
            &self.outer_proof.pcs_opening,
        )
    }

    /// Serialize to canonical self-delimiting wire bytes (`SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC`).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(112 + self.shards.len().saturating_mul(192) + 16_384);
        out.extend_from_slice(SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC);
        out.extend_from_slice(&self.policy_registry_root);
        for limb in &self.terminal_chain_digest {
            out.extend_from_slice(&limb.to_le_bytes());
        }
        out.extend_from_slice(&(self.shards.len() as u32).to_le_bytes());
        for s in &self.shards {
            out.extend_from_slice(&s.shard_id.to_le_bytes());
            out.extend_from_slice(&s.custodian_cluster);
            out.extend_from_slice(&s.shard_quorum_set_root);
            out.extend_from_slice(&s.minimum_quorums.to_le_bytes());
            out.extend_from_slice(&s.epoch_floor.to_le_bytes());
            out.extend_from_slice(&s.message_digest);
            out.extend_from_slice(&s.bitmap.to_bytes());
            out.extend_from_slice(&s.child_proof_digest);
        }
        out.extend_from_slice(&self.outer_proof.witness_comm.to_bytes());
        for poly in &self.outer_proof.row_sumcheck_polys {
            for c in poly {
                out.extend_from_slice(&c.to_le_bytes());
            }
        }
        for col in &self.outer_proof.col_evals {
            out.extend_from_slice(&col.to_le_bytes());
        }
        self.outer_proof.pcs_opening.push_bytes(&mut out);
        out
    }

    /// Strictly canonical wire decoder rejecting trailing bytes, non-canonical field limbs,
    /// truncated frames, or malformed `CanopyCommitment` / `HemWhirOpeningProof` payloads.
    pub fn from_bytes_canonical(bytes: &[u8]) -> Result<Self, HemAggError> {
        if bytes.len() < 76 || &bytes[0..8] != SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC {
            return Err(HemAggError::MalformedWireBytes);
        }
        let mut policy_registry_root = [0u8; 32];
        policy_registry_root.copy_from_slice(&bytes[8..40]);
        let mut terminal_chain_digest = [Goldilocks::ZERO; 4];
        for (j, dst) in terminal_chain_digest.iter_mut().enumerate() {
            let off = 40 + 8 * j;
            let mut lb = [0u8; 8];
            lb.copy_from_slice(&bytes[off..off + 8]);
            *dst =
                Goldilocks::from_le_bytes_canonical(lb).ok_or(HemAggError::MalformedWireBytes)?;
        }
        let num_shards = u32::from_le_bytes(bytes[72..76].try_into().unwrap()) as usize;
        let (_, log_rows) =
            outer_chain_num_rows(num_shards).ok_or(HemAggError::MalformedWireBytes)?;

        let mut pos = 76usize;
        let mut shards = Vec::with_capacity(num_shards);
        for _ in 0..num_shards {
            let meta_end = pos
                .checked_add(120)
                .ok_or(HemAggError::MalformedWireBytes)?;
            let meta = bytes
                .get(pos..meta_end)
                .ok_or(HemAggError::MalformedWireBytes)?;
            let shard_id = u64::from_le_bytes(meta[0..8].try_into().unwrap());
            let mut custodian_cluster = [0u8; 32];
            custodian_cluster.copy_from_slice(&meta[8..40]);
            let mut shard_quorum_set_root = [0u8; 32];
            shard_quorum_set_root.copy_from_slice(&meta[40..72]);
            let minimum_quorums = u64::from_le_bytes(meta[72..80].try_into().unwrap());
            let epoch_floor = u64::from_le_bytes(meta[80..88].try_into().unwrap());
            let mut message_digest = [0u8; 32];
            message_digest.copy_from_slice(&meta[88..120]);
            pos = meta_end;

            let (bitmap, used_bm) = SignerBitmap::from_bytes_canonical(
                bytes.get(pos..).ok_or(HemAggError::MalformedWireBytes)?,
            )
            .ok_or(HemAggError::MalformedWireBytes)?;
            pos = pos
                .checked_add(used_bm)
                .ok_or(HemAggError::MalformedWireBytes)?;

            let dig_end = pos.checked_add(32).ok_or(HemAggError::MalformedWireBytes)?;
            let dig_slice = bytes
                .get(pos..dig_end)
                .ok_or(HemAggError::MalformedWireBytes)?;
            let mut child_proof_digest = [0u8; 32];
            child_proof_digest.copy_from_slice(dig_slice);
            pos = dig_end;

            shards.push(ShardHemSummary {
                shard_id,
                custodian_cluster,
                shard_quorum_set_root,
                minimum_quorums,
                epoch_floor,
                message_digest,
                bitmap,
                child_proof_digest,
            });
        }

        let (witness_comm, used_wc) = CanopyCommitment::from_bytes_canonical(
            bytes.get(pos..).ok_or(HemAggError::MalformedWireBytes)?,
        )
        .ok_or(HemAggError::MalformedWireBytes)?;
        pos = pos
            .checked_add(used_wc)
            .ok_or(HemAggError::MalformedWireBytes)?;

        let read_ext4 = |pos: &mut usize| -> Result<GoldilocksExt4, HemAggError> {
            let end = pos.checked_add(32).ok_or(HemAggError::MalformedWireBytes)?;
            let chunk = bytes
                .get(*pos..end)
                .ok_or(HemAggError::MalformedWireBytes)?;
            let mut cb = [0u8; 32];
            cb.copy_from_slice(chunk);
            *pos = end;
            GoldilocksExt4::from_le_bytes_canonical(cb).ok_or(HemAggError::MalformedWireBytes)
        };

        let mut row_sumcheck_polys = Vec::with_capacity(log_rows);
        for _ in 0..log_rows {
            let mut poly = [GoldilocksExt4::ZERO; ROW_SUMCHECK_WIRE_COEFFS];
            for coeff in &mut poly {
                *coeff = read_ext4(&mut pos)?;
            }
            row_sumcheck_polys.push(poly);
        }

        let mut col_evals = Vec::with_capacity(NUM_TRACE_COLS);
        for _ in 0..NUM_TRACE_COLS {
            col_evals.push(read_ext4(&mut pos)?);
        }

        let (pcs_opening, used_pcs) = HemWhirOpeningProof::from_bytes_canonical(
            bytes.get(pos..).ok_or(HemAggError::MalformedWireBytes)?,
        )
        .ok_or(HemAggError::MalformedWireBytes)?;
        pos = pos
            .checked_add(used_pcs)
            .ok_or(HemAggError::MalformedWireBytes)?;

        if pos != bytes.len() {
            return Err(HemAggError::MalformedWireBytes);
        }

        Ok(Self {
            policy_registry_root,
            shards,
            terminal_chain_digest,
            outer_proof: OuterHemChainProof {
                witness_comm,
                row_sumcheck_polys,
                col_evals,
                pcs_opening,
            },
        })
    }
}

fn absorb_outer_col_evals(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    col_evals: &[GoldilocksExt4],
) {
    let mut buf = Vec::with_capacity(32 * col_evals.len());
    for c in col_evals {
        buf.extend_from_slice(&c.to_le_bytes());
    }
    transcript.absorb(b"OUTER_COL_EVALS", &buf);
}

/// Verify a hierarchy under `BciksJohnsonQrom128` and build its compact commitment.
/// The resulting wire object does not replace child-proof evidence at a new verifier.
pub fn compress_verified_hierarchical_hem(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    aggregate: &HierarchicalHemAggregate,
    blinding_seed: [u8; 32],
) -> Result<SuccinctHierarchicalHemAggregate, HemAggError> {
    let evidence = verify_hierarchical_hem_evidence(
        policies, epoch_floor, message, minimum_global_quorums,
        WhirSecurityRegime::BciksJohnsonQrom128, aggregate,
    ).ok_or(HemAggError::InvalidShardConfig)?;
    compress_hierarchical_hem_evidence(&evidence, blinding_seed)
}

/// Build the compact commitment directly from an immutable, fully verified child snapshot.
/// No child proof is reverified or rehashed. Every context field and exact child digest comes
/// from `evidence`; callers cannot substitute an unchecked hierarchy or relabel its context.
/// This avoids a second child verification after evidence creation. Recipients still need
/// their own evidence. The outer format currently supports only the default Johnson regime.
pub fn compress_hierarchical_hem_evidence(
    evidence: &VerifiedHierarchicalHemEvidence,
    blinding_seed: [u8; 32],
) -> Result<SuccinctHierarchicalHemAggregate, HemAggError> {
    if evidence.regime != WhirSecurityRegime::BciksJohnsonQrom128 {
        return Err(HemAggError::InvalidShardConfig);
    }
    let minimum = u64::try_from(evidence.minimum_global_quorums)
        .map_err(|_| HemAggError::InvalidShardConfig)?;
    prove_outer_summary_chain(
        evidence.policy_registry_root, evidence.shards.clone(), evidence.epoch_floor,
        evidence.message_digest, minimum, blinding_seed,
    )
}

/// Outer chain prover over public summaries. It takes no child proof: the relation it proves
/// is the summary hash chain alone, which is why callers must gate it on child verification.
fn prove_outer_summary_chain(
    policy_registry_root: [u8; 32],
    shards: Vec<ShardHemSummary>,
    epoch_floor: u64,
    expected_msg_digest: [u8; 32],
    min_global_u64: u64,
    blinding_seed: [u8; 32],
) -> Result<SuccinctHierarchicalHemAggregate, HemAggError> {
    let (num_rows, log_rows) =
        outer_chain_num_rows(shards.len()).ok_or(HemAggError::InvalidShardConfig)?;
    let num_vars = LOG_TRACE_COLS + log_rows;
    let schedule = WhirSecurityRegime::BciksJohnsonQrom128.schedule(num_vars);

    // Build the `num_rows x 256` outer commitment-chain trace.
    let active_rows = 2 * shards.len();
    let mut trace_rows = vec![[Goldilocks::ZERO; NUM_TRACE_COLS]; num_rows];
    let mut pub_row_in_base = vec![[Goldilocks::ZERO; 8]; num_rows];
    let mut cur_chain = [Goldilocks::ZERO; 4];

    for (i, summary) in shards.iter().enumerate() {
        let hdr_limbs = digest32_to_u32_limbs(&shard_summary_header_digest(summary));
        let prf_limbs = digest32_to_u32_limbs(&summary.child_proof_digest);
        for (sub, limbs) in [(0usize, hdr_limbs), (1usize, prf_limbs)] {
            let t = 2 * i + sub;
            pub_row_in_base[t] = limbs;
            let row = &mut trace_rows[t];
            let (st_in, sbox, next_chain) = jive_weighted_ff_step(cur_chain, limbs);
            row[COL_ST_IN..COL_ST_IN + 12].copy_from_slice(&st_in);
            row[COL_SBOX_OUT..COL_SBOX_OUT + 118].copy_from_slice(&sbox);
            row[OUTER_COL_PREV_CHAIN..OUTER_COL_PREV_CHAIN + 4].copy_from_slice(&cur_chain);
            row[OUTER_COL_NEXT_CHAIN..OUTER_COL_NEXT_CHAIN + 4].copy_from_slice(&next_chain);
            row[OUTER_COL_ROW_IN..OUTER_COL_ROW_IN + 8].copy_from_slice(&limbs);
            cur_chain = next_chain;
        }
    }

    // Blind idle padding rows (`t in active_rows..num_rows`) while preserving `next == prev`.
    let mut stream = [0u8; 128];
    for (t, row) in trace_rows
        .iter_mut()
        .enumerate()
        .skip(active_rows)
        .take(num_rows - active_rows)
    {
        let t_bytes = (t as u64).to_le_bytes();
        let row_seed = encode_multi_frame(&[
            b"QSAG.SHM.OUTER.IDLE.BLIND/v1",
            &blinding_seed,
            &policy_registry_root,
            &t_bytes,
        ]);
        shake256_into(&row_seed, &mut stream);
        let mut st_in = [Goldilocks::ZERO; 12];
        for i in 0..12 {
            let mut b = [0u8; 8];
            b.copy_from_slice(&stream[8 * i..8 * (i + 1)]);
            st_in[i] = Goldilocks::from_u64_reduced(u64::from_le_bytes(b));
        }
        let mut sbox = [Goldilocks::ZERO; 118];
        let _ = record_poseidon2_perm12(st_in, &mut sbox);
        row[COL_ST_IN..COL_ST_IN + 12].copy_from_slice(&st_in);
        row[COL_SBOX_OUT..COL_SBOX_OUT + 118].copy_from_slice(&sbox);
        row[OUTER_COL_PREV_CHAIN..OUTER_COL_PREV_CHAIN + 4].copy_from_slice(&cur_chain);
        row[OUTER_COL_NEXT_CHAIN..OUTER_COL_NEXT_CHAIN + 4].copy_from_slice(&cur_chain);
        for i in 0..4 {
            let off = 96 + 8 * i;
            let mut b = [0u8; 8];
            b.copy_from_slice(&stream[off..off + 8]);
            row[OUTER_COL_BLIND + i] = Goldilocks::from_u64_reduced(u64::from_le_bytes(b));
        }
    }

    let terminal_chain_digest = cur_chain;
    let terminal_chain_ext4 = terminal_chain_digest.map(GoldilocksExt4::from_base);

    // Flatten `trace_rows` to hypercube table `flat[row * 256 + col]` and commit via WHIR.
    let mut flat = Vec::with_capacity(num_rows * NUM_TRACE_COLS);
    for row in &trace_rows {
        flat.extend_from_slice(row);
    }
    let salt_seed = poseidon2_hash32(&encode_multi_frame(&[
        b"QSAG.SHM.OUTER.SALT/v1",
        &blinding_seed,
        &policy_registry_root,
    ]));
    let (witness_comm, prover_state) = whir_commit_owned_with_schedule(flat, &salt_seed, &schedule);

    let mut transcript = init_outer_chain_transcript(
        &policy_registry_root,
        epoch_floor,
        &expected_msg_digest,
        min_global_u64,
        &shards,
        &terminal_chain_digest,
        &schedule,
    );
    transcript.absorb(b"OUTER_WITNESS_COMM", &witness_comm.to_bytes());

    let tau = transcript.squeeze_ext4_vec(b"OUTER_TAU", log_rows);
    let gamma = transcript.squeeze_ext4(b"OUTER_GAMMA");

    // Promote trace and public row tables to `GoldilocksExt4` for degree-8 row sumcheck.
    let mut cols_tbl: Vec<[GoldilocksExt4; NUM_TRACE_COLS]> = trace_rows
        .iter()
        .map(|row| row.map(GoldilocksExt4::from_base))
        .collect();
    let mut pub_in_tbl: Vec<[GoldilocksExt4; 8]> = pub_row_in_base
        .iter()
        .map(|r| r.map(GoldilocksExt4::from_base))
        .collect();
    let mut is_active_tbl = vec![GoldilocksExt4::ZERO; num_rows];
    for v in is_active_tbl.iter_mut().take(active_rows) {
        *v = GoldilocksExt4::ONE;
    }
    let mut is_first_tbl = vec![GoldilocksExt4::ZERO; num_rows];
    let mut is_last_tbl = vec![GoldilocksExt4::ZERO; num_rows];
    is_first_tbl[0] = GoldilocksExt4::ONE;
    is_last_tbl[num_rows - 1] = GoldilocksExt4::ONE;
    let (mut eq_tbl, mut not_last_tbl, mut shift_tbl) = build_shift_tables_ext4(&tau);

    let mut row_sumcheck_polys = Vec::with_capacity(log_rows);
    let mut challenges_msb_to_lsb = Vec::with_capacity(log_rows);
    let mut cur_sum_claim = GoldilocksExt4::ZERO;
    let mut cur_m = num_rows;

    for _round in 0..log_rows {
        let half = cur_m / 2;
        let mut sum_evals = [GoldilocksExt4::ZERO; ROW_SUMCHECK_COEFFS];

        for idx in 0..half {
            let c0 = &cols_tbl[idx];
            let c1 = &cols_tbl[idx + half];
            let mut dc = [GoldilocksExt4::ZERO; NUM_TRACE_COLS];
            let mut ck = *c1;
            for col in 0..NUM_TRACE_COLS {
                dc[col] = c1[col] - c0[col];
            }

            let p0 = &pub_in_tbl[idx];
            let p1 = &pub_in_tbl[idx + half];
            let mut dp = [GoldilocksExt4::ZERO; 8];
            let mut pk = *p1;
            for k in 0..8 {
                dp[k] = p1[k] - p0[k];
            }

            let act0 = is_active_tbl[idx];
            let act1 = is_active_tbl[idx + half];
            let d_act = act1 - act0;
            let fst0 = is_first_tbl[idx];
            let fst1 = is_first_tbl[idx + half];
            let d_fst = fst1 - fst0;
            let lst0 = is_last_tbl[idx];
            let lst1 = is_last_tbl[idx + half];
            let d_lst = lst1 - lst0;
            let eq0 = eq_tbl[idx];
            let eq1 = eq_tbl[idx + half];
            let d_eq = eq1 - eq0;
            let nl0 = not_last_tbl[idx];
            let nl1 = not_last_tbl[idx + half];
            let d_nl = nl1 - nl0;
            let sh0 = shift_tbl[idx];
            let sh1 = shift_tbl[idx + half];
            let d_sh = sh1 - sh0;

            sum_evals[0] += eval_outer_chain_row_constraints_ext4(
                c0,
                p0,
                &terminal_chain_ext4,
                act0,
                fst0,
                lst0,
                eq0,
                nl0,
                sh0,
                gamma,
            );

            let mut act_k = act1;
            let mut fst_k = fst1;
            let mut lst_k = lst1;
            let mut eq_k = eq1;
            let mut nl_k = nl1;
            let mut sh_k = sh1;
            for dst_eval in sum_evals.iter_mut().take(ROW_SUMCHECK_COEFFS).skip(2) {
                for col in 0..NUM_TRACE_COLS {
                    ck[col] += dc[col];
                }
                for j in 0..8 {
                    pk[j] += dp[j];
                }
                act_k += d_act;
                fst_k += d_fst;
                lst_k += d_lst;
                eq_k += d_eq;
                nl_k += d_nl;
                sh_k += d_sh;
                *dst_eval += eval_outer_chain_row_constraints_ext4(
                    &ck,
                    &pk,
                    &terminal_chain_ext4,
                    act_k,
                    fst_k,
                    lst_k,
                    eq_k,
                    nl_k,
                    sh_k,
                    gamma,
                );
            }
        }
        sum_evals[1] = cur_sum_claim - sum_evals[0];

        let poly_coeffs = interpolate_deg8_from_evals_ext4(&sum_evals);
        let wire_poly = pack_outer_deg8_wire(&poly_coeffs);
        let mut sc_bytes = [0u8; ROW_SUMCHECK_WIRE_COEFFS * 32];
        for (i, c) in wire_poly.iter().enumerate() {
            sc_bytes[32 * i..32 * (i + 1)].copy_from_slice(&c.to_le_bytes());
        }
        transcript.absorb(b"OUTER_SC_POLY", &sc_bytes);
        let chal = transcript.squeeze_ext4(b"OUTER_SC_CHAL");
        cur_sum_claim = eval_univariate_ext4(&poly_coeffs, chal);
        challenges_msb_to_lsb.push(chal);
        row_sumcheck_polys.push(wire_poly);

        // Fold all multilinear tables at MSB = `chal`.
        for idx in 0..half {
            let c1 = cols_tbl[idx + half];
            for (v0, v1) in cols_tbl[idx].iter_mut().zip(c1.iter()) {
                *v0 += chal * (*v1 - *v0);
            }
            let p1 = pub_in_tbl[idx + half];
            for (v0, v1) in pub_in_tbl[idx].iter_mut().zip(p1.iter()) {
                *v0 += chal * (*v1 - *v0);
            }
            let d_act = is_active_tbl[idx + half] - is_active_tbl[idx];
            is_active_tbl[idx] += chal * d_act;
            let d_first = is_first_tbl[idx + half] - is_first_tbl[idx];
            is_first_tbl[idx] += chal * d_first;
            let d_last = is_last_tbl[idx + half] - is_last_tbl[idx];
            is_last_tbl[idx] += chal * d_last;
            let d_eq = eq_tbl[idx + half] - eq_tbl[idx];
            eq_tbl[idx] += chal * d_eq;
            let d_not_last = not_last_tbl[idx + half] - not_last_tbl[idx];
            not_last_tbl[idx] += chal * d_not_last;
            let d_shift = shift_tbl[idx + half] - shift_tbl[idx];
            shift_tbl[idx] += chal * d_shift;
        }
        cur_m = half;
    }
    debug_assert_eq!(cur_m, 1);

    let col_evals = cols_tbl[0].to_vec();
    absorb_outer_col_evals(&mut transcript, &col_evals);

    let mut rx = challenges_msb_to_lsb;
    rx.reverse();
    let mut point = Vec::with_capacity(num_vars);
    for _ in 0..LOG_TRACE_COLS {
        point.push(transcript.squeeze_ext4(b"OUTER_RZ"));
    }
    let v_star = mle_eval_ext4(&col_evals, &point);
    point.extend_from_slice(&rx);

    let pcs_opening = whir_open(&prover_state, &point, v_star, &mut transcript);

    Ok(SuccinctHierarchicalHemAggregate {
        policy_registry_root,
        shards,
        terminal_chain_digest,
        outer_proof: OuterHemChainProof {
            witness_comm,
            row_sumcheck_polys,
            col_evals,
            pcs_opening,
        },
    })
}

/// Prove a regional hierarchy and build its compact commitment.
/// Recipients still need independently checked child evidence for quorum verification.
pub fn prove_succinct_hierarchical_hem(
    policies: &[ShardHemPolicy],
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    config: &HemAggConfig,
) -> Result<SuccinctHierarchicalHemAggregate, HemAggError> {
    if !config.regime.meets_qrom_128_floor() {
        return Err(HemAggError::InvalidShardConfig);
    }
    let msg_ref = message.as_ref();
    let full = prove_hierarchical_hem_inner(
        policies,
        witnesses,
        epoch_floor,
        msg_ref,
        minimum_global_quorums,
        config,
    )?;
    compress_verified_hierarchical_hem(
        policies,
        epoch_floor,
        msg_ref,
        minimum_global_quorums,
        &full,
        config.blinding_seed,
    )
}

/// Check the public summary commitment relation under `expected_regime`.
///
/// A successful result does **not** certify any child proof or signature. It only checks
/// summary structure and their outer hash-chain proof. For quorum authorization use
/// [`verify_succinct_hierarchical_hem_with_regime`] with verified child evidence.
pub fn check_hierarchical_hem_commitment_with_regime(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    expected_regime: WhirSecurityRegime,
    aggregate: &SuccinctHierarchicalHemAggregate,
) -> bool {
    if !valid_policies(policies) {
        return false;
    }
    let committee_roots = compute_committee_roots(policies);
    let expected_registry_root =
        compute_policy_registry_root_with_roots(policies, &committee_roots);
    check_hierarchical_hem_commitment_with_roots(
        policies,
        &committee_roots,
        expected_registry_root,
        epoch_floor,
        message.as_ref(),
        minimum_global_quorums,
        expected_regime,
        aggregate,
    )
}

/// Commitment check against an already validated registry and its committee roots.
#[allow(clippy::too_many_arguments)]
fn check_hierarchical_hem_commitment_with_roots(
    policies: &[ShardHemPolicy],
    committee_roots: &[[u8; 32]],
    expected_registry_root: [u8; 32],
    epoch_floor: u64,
    msg_bytes: &[u8],
    minimum_global_quorums: usize,
    expected_regime: WhirSecurityRegime,
    aggregate: &SuccinctHierarchicalHemAggregate,
) -> bool {
    if !expected_regime.meets_qrom_128_floor()
        || aggregate.shards.len() != policies.len()
        || committee_roots.len() != policies.len()
        || minimum_global_quorums == 0
    {
        return false;
    }
    let Ok(min_global_u64) = u64::try_from(minimum_global_quorums) else {
        return false;
    };
    let Some((num_rows, log_rows)) = outer_chain_num_rows(aggregate.shards.len()) else {
        return false;
    };
    if aggregate.outer_proof.row_sumcheck_polys.len() != log_rows
        || aggregate.outer_proof.col_evals.len() != NUM_TRACE_COLS
    {
        return false;
    }

    if aggregate.policy_registry_root != expected_registry_root {
        return false;
    }
    let expected_msg_digest = compute_framed_message_digest(msg_bytes);

    let mut counts_u64 = Vec::with_capacity(policies.len());
    let mut minimums_u64 = Vec::with_capacity(policies.len());
    for ((p, s), c_root) in policies
        .iter()
        .zip(&aggregate.shards)
        .zip(committee_roots.iter())
    {
        if p.profile().is_none() {
            return false;
        }
        let Ok(expected_min_u64) = u64::try_from(p.minimum_quorums) else {
            return false;
        };
        let Ok(claimed_signers_u64) = u64::try_from(s.num_signers()) else {
            return false;
        };
        if s.shard_id != p.shard_id
            || s.custodian_cluster != p.custodian_cluster
            || s.shard_quorum_set_root != *c_root
            || s.minimum_quorums != expected_min_u64
            || s.epoch_floor != epoch_floor
            || s.message_digest != expected_msg_digest
            || s.bitmap.num_validators() as usize != p.quorum_keys.len()
            || s.num_signers() < p.minimum_quorums
        {
            return false;
        }
        counts_u64.push(claimed_signers_u64);
        minimums_u64.push(expected_min_u64);
    }

    let Some(total_u64) =
        qsag_whir_verified::checked_quorum_sum(&counts_u64, &minimums_u64, min_global_u64)
    else {
        return false;
    };
    if usize::try_from(total_u64).is_err() {
        return false;
    }

    let num_vars = LOG_TRACE_COLS + log_rows;
    let schedule = expected_regime.schedule(num_vars);
    let mut transcript = init_outer_chain_transcript(
        &expected_registry_root,
        epoch_floor,
        &expected_msg_digest,
        min_global_u64,
        &aggregate.shards,
        &aggregate.terminal_chain_digest,
        &schedule,
    );
    transcript.absorb(
        b"OUTER_WITNESS_COMM",
        &aggregate.outer_proof.witness_comm.to_bytes(),
    );

    let tau = transcript.squeeze_ext4_vec(b"OUTER_TAU", log_rows);
    let gamma = transcript.squeeze_ext4(b"OUTER_GAMMA");

    let mut cur_sum_claim = GoldilocksExt4::ZERO;
    let mut challenges_msb_to_lsb = Vec::with_capacity(log_rows);
    for wire_poly in &aggregate.outer_proof.row_sumcheck_polys {
        let mut sc_bytes = [0u8; ROW_SUMCHECK_WIRE_COEFFS * 32];
        for (i, c) in wire_poly.iter().enumerate() {
            sc_bytes[32 * i..32 * (i + 1)].copy_from_slice(&c.to_le_bytes());
        }
        transcript.absorb(b"OUTER_SC_POLY", &sc_bytes);
        let poly_coeffs = unpack_outer_deg8_wire(wire_poly, cur_sum_claim);
        let chal = transcript.squeeze_ext4(b"OUTER_SC_CHAL");
        cur_sum_claim = eval_univariate_ext4(&poly_coeffs, chal);
        challenges_msb_to_lsb.push(chal);
    }

    absorb_outer_col_evals(&mut transcript, &aggregate.outer_proof.col_evals);

    let mut rx = challenges_msb_to_lsb;
    rx.reverse();

    // Evaluate public header/child-digest limb MLEs and boundary selectors at `r_x`.
    let eq_rx = build_eq_table_ext4(&rx);
    let is_row_first = eq_rx[0];
    let is_row_last = eq_rx[num_rows - 1];
    let mut is_active = GoldilocksExt4::ZERO;
    let mut pub_row_in = [GoldilocksExt4::ZERO; 8];

    for (i, summary) in aggregate.shards.iter().enumerate() {
        let hdr_limbs = digest32_to_u32_limbs(&shard_summary_header_digest(summary));
        let prf_limbs = digest32_to_u32_limbs(&summary.child_proof_digest);
        for (sub, limbs) in [(0usize, hdr_limbs), (1usize, prf_limbs)] {
            let w = eq_rx[2 * i + sub];
            is_active += w;
            for (dst, &limb) in pub_row_in.iter_mut().zip(limbs.iter()) {
                *dst += w.mul_base(limb);
            }
        }
    }

    let mut cols_arr = [GoldilocksExt4::ZERO; NUM_TRACE_COLS];
    cols_arr.copy_from_slice(&aggregate.outer_proof.col_evals);
    let terminal_chain_ext4 = aggregate
        .terminal_chain_digest
        .map(GoldilocksExt4::from_base);

    let expected_terminal_val = eval_outer_chain_row_constraints_ext4(
        &cols_arr,
        &pub_row_in,
        &terminal_chain_ext4,
        is_active,
        is_row_first,
        is_row_last,
        eq_poly_ext4(&tau, &rx),
        eval_eq_not_last_ext4(&tau, &rx),
        eval_shift_kernel_ext4(&tau, &rx),
        gamma,
    );
    if !qsag_whir_verified::verify_ood_pin_eq(
        &expected_terminal_val
            .to_limbs()
            .map(Goldilocks::to_canonical_u64),
        &cur_sum_claim.to_limbs().map(Goldilocks::to_canonical_u64),
    ) {
        return false;
    }

    let mut point = Vec::with_capacity(num_vars);
    for _ in 0..LOG_TRACE_COLS {
        point.push(transcript.squeeze_ext4(b"OUTER_RZ"));
    }
    let v_star = mle_eval_ext4(&aggregate.outer_proof.col_evals, &point);
    point.extend_from_slice(&rx);

    whir_verify_with_schedule(
        &aggregate.outer_proof.witness_comm,
        num_vars,
        &point,
        v_star,
        &aggregate.outer_proof.pcs_opening,
        &mut transcript,
        &schedule,
    )
}

/// Check only the public commitment relation, pinned to `BciksJohnsonQrom128`.
/// This result must not be used as signature or quorum authorization.
pub fn check_hierarchical_hem_commitment(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    aggregate: &SuccinctHierarchicalHemAggregate,
) -> bool {
    check_hierarchical_hem_commitment_with_regime(
        policies,
        epoch_floor,
        message,
        minimum_global_quorums,
        WhirSecurityRegime::BciksJohnsonQrom128,
        aggregate,
    )
}

/// Verify a compact hierarchy against independently validated child evidence.
///
/// Matching includes every summary field and the digest of canonical child-proof bytes.
/// The terminal chain digest is also recomputed from the evidence's own summaries, so the
/// authorization decision does not rest on the outer proof alone.
/// The evidence is tied to the exact security regime and requested authorization context;
/// a commitment proof alone can never satisfy this API.
#[allow(clippy::too_many_arguments)]
pub fn verify_succinct_hierarchical_hem_with_regime(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    expected_regime: WhirSecurityRegime,
    aggregate: &SuccinctHierarchicalHemAggregate,
    evidence: &VerifiedHierarchicalHemEvidence,
) -> bool {
    let message = message.as_ref();
    evidence_authorizes(
        evidence,
        epoch_floor,
        message,
        minimum_global_quorums,
        expected_regime,
        aggregate,
    ) && check_hierarchical_hem_commitment_with_regime(
        policies,
        epoch_floor,
        message,
        minimum_global_quorums,
        expected_regime,
        aggregate,
    )
}

fn evidence_authorizes(
    evidence: &VerifiedHierarchicalHemEvidence,
    epoch_floor: u64,
    message: &[u8],
    minimum_global_quorums: usize,
    expected_regime: WhirSecurityRegime,
    aggregate: &SuccinctHierarchicalHemAggregate,
) -> bool {
    evidence.epoch_floor == epoch_floor
        && evidence.message_digest == compute_framed_message_digest(message)
        && evidence.minimum_global_quorums == minimum_global_quorums
        && evidence.regime == expected_regime
        && evidence.names_same_children(aggregate)
}

/// [`verify_succinct_hierarchical_hem_with_regime`] against a [`PreparedPolicyRegistry`].
pub fn verify_succinct_hierarchical_hem_prepared(
    registry: &PreparedPolicyRegistry,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    expected_regime: WhirSecurityRegime,
    aggregate: &SuccinctHierarchicalHemAggregate,
    evidence: &VerifiedHierarchicalHemEvidence,
) -> bool {
    let message = message.as_ref();
    evidence_authorizes(
        evidence,
        epoch_floor,
        message,
        minimum_global_quorums,
        expected_regime,
        aggregate,
    ) && check_hierarchical_hem_commitment_with_roots(
        &registry.policies,
        &registry.committee_roots,
        registry.policy_registry_root,
        epoch_floor,
        message,
        minimum_global_quorums,
        expected_regime,
        aggregate,
    )
}

/// Verify a compact hierarchy with checked child evidence under `BciksJohnsonQrom128`.
pub fn verify_succinct_hierarchical_hem(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    aggregate: &SuccinctHierarchicalHemAggregate,
    evidence: &VerifiedHierarchicalHemEvidence,
) -> bool {
    verify_succinct_hierarchical_hem_with_regime(
        policies,
        epoch_floor,
        message,
        minimum_global_quorums,
        WhirSecurityRegime::BciksJohnsonQrom128,
        aggregate,
        evidence,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ValidatorKeypair, aggregate_signatures_with_config};

    fn root_commitment(policy_registry_root: &[u8; 32], shards: &[ShardHemBatch]) -> [u8; 32] {
        let digests: Vec<_> = shards.iter().map(shard_commitment_digest).collect();
        root_commitment_from_digests(policy_registry_root, &digests)
    }

    #[test]
    fn hierarchical_three_regions_twelve_quorums() {
        let mut policies = Vec::new();
        let mut region_keys = Vec::new();
        let epoch = 17;
        let digest = [42u8; 32];
        for region in 0..3u64 {
            let keys: Vec<_> = (0..4)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[region as u8 + 1; 32],
                        i,
                    )
                })
                .collect();
            policies.push(ShardHemPolicy {
                shard_id: region,
                custodian_cluster: [region as u8; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 4,
            });
            region_keys.push(keys);
        }
        let registry_root = compute_policy_registry_root(&policies);
        let signatures: Vec<Vec<_>> = policies
            .iter()
            .zip(region_keys.iter_mut())
            .map(|(policy, keys)| {
                let message = hierarchical_hem_message(&registry_root, policy, epoch, digest);
                keys.iter_mut()
                    .map(|k| k.sign_stateful_for_unit_test(&message, 0).unwrap())
                    .collect()
            })
            .collect();
        let bitmap = SignerBitmap::from_active_indices(4, &[0, 1, 2, 3]).unwrap();
        let witnesses: Vec<_> = signatures
            .iter()
            .map(|s| ShardHemWitness {
                bitmap: &bitmap,
                signatures: s,
            })
            .collect();
        let config = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [7; 32]);
        let proof =
            prove_hierarchical_hem(&policies, &witnesses, epoch, digest, 12, &config).unwrap();
        let verify = |p: &HierarchicalHemAggregate| {
            verify_hierarchical_hem(&policies, epoch, digest, 12, config.regime, p)
        };
        assert!(verify(&proof));
        assert_eq!(proof.checked_total_quorums(), Some(12));

        // Canonical wire serialization roundtrip + trailing/truncated byte rejection.
        let wire = proof.to_bytes();
        let decoded = HierarchicalHemAggregate::from_bytes_canonical(&wire).unwrap();
        assert_eq!(decoded, proof);
        assert!(verify(&decoded));
        let mut obsolete = wire.clone();
        obsolete[7] = 2;
        assert_eq!(
            HierarchicalHemAggregate::from_bytes_canonical(&obsolete),
            Err(HemAggError::MalformedWireBytes)
        );
        let mut trailing = wire.clone();
        trailing.push(0);
        assert_eq!(
            HierarchicalHemAggregate::from_bytes_canonical(&trailing),
            Err(HemAggError::MalformedWireBytes)
        );
        assert_eq!(
            HierarchicalHemAggregate::from_bytes_canonical(&wire[..wire.len() - 1]),
            Err(HemAggError::MalformedWireBytes)
        );
        // `[AGG-04]`: Truncated 76-byte wire headers claiming huge `num_shards` must fail closed
        // BEFORE `Vec::with_capacity(num_shards)` over-allocation, and frame helpers must match
        // reference `encode_multi_frame` byte-for-byte.
        for claimed_shards in [1u32, 64, MAX_HIERARCHY_SHARDS as u32, u32::MAX] {
            let mut trunc_hdr = wire[..76].to_vec();
            trunc_hdr[72..76].copy_from_slice(&claimed_shards.to_le_bytes());
            assert_eq!(
                HierarchicalHemAggregate::from_bytes_canonical(&trunc_hdr),
                Err(HemAggError::MalformedWireBytes)
            );
        }
        let s0 = &proof.shards[0];
        let ref_shard_frame = encode_multi_frame(&[
            b"QSAG.HEM.HIERARCHY.SHARD/v3",
            &s0.shard_id.to_le_bytes(),
            &s0.custodian_cluster,
            &s0.shard_quorum_set_root,
            &s0.minimum_quorums.to_le_bytes(),
            &s0.epoch_floor.to_le_bytes(),
            &s0.message_digest,
            &s0.proof.to_bytes(),
        ]);
        assert_eq!(
            build_shard_commitment_frame(s0).as_slice(),
            ref_shard_frame.as_slice()
        );
        let p0 = &policies[0];
        let c0 = compute_committee_root(&p0.quorum_keys);
        let ref_key_frames: Vec<Vec<u8>> = p0
            .quorum_keys
            .iter()
            .map(|pk| {
                let raw = pk.to_bytes();
                encode_multi_frame(&[&raw[0..1], &raw[1..33], &raw[33..65]])
            })
            .collect();
        let ref_key_slices: Vec<&[u8]> = ref_key_frames.iter().map(Vec::as_slice).collect();
        let ref_committee_frame = encode_multi_frame(&ref_key_slices);
        let ref_row = encode_multi_frame(&[
            b"QSAG.HEM.POLICY.ROW/v2",
            &p0.shard_id.to_le_bytes(),
            &p0.custodian_cluster,
            &[p0.profile().unwrap() as u8],
            &(p0.minimum_quorums as u64).to_le_bytes(),
            &c0,
            &ref_committee_frame,
        ]);
        assert_eq!(encode_policy_registration_with_root(p0, &c0), ref_row);

        assert!(!verify_hierarchical_hem(
            &policies,
            epoch + 1,
            digest,
            12,
            config.regime,
            &proof
        ));
        assert!(!verify_hierarchical_hem(
            &policies,
            epoch,
            [43u8; 32],
            12,
            config.regime,
            &proof
        ));
        assert!(!verify_hierarchical_hem(
            &policies,
            epoch,
            digest,
            13,
            config.regime,
            &proof
        ));
        let mut tampered = proof.clone();
        tampered.root_commitment[0] ^= 1;
        assert!(!verify(&tampered));
        let mut tampered = proof.clone();
        tampered.policy_registry_root[0] ^= 1;
        assert!(!verify(&tampered));
        let mut tampered = proof.clone();
        tampered.shards[1] = tampered.shards[0].clone();
        tampered.root_commitment =
            root_commitment(&tampered.policy_registry_root, &tampered.shards);
        assert!(!verify(&tampered));
        let mut tampered = proof.clone();
        tampered.shards[0].shard_quorum_set_root[0] ^= 1;
        tampered.root_commitment =
            root_commitment(&tampered.policy_registry_root, &tampered.shards);
        assert!(!verify(&tampered));
        let mut tampered = proof.clone();
        tampered.shards[0].proof.committee_root[0] ^= 1;
        tampered.root_commitment =
            root_commitment(&tampered.policy_registry_root, &tampered.shards);
        assert!(!verify(&tampered));

        // Recomputing public summaries after relabeling epoch or shard_id still fails verification.
        let mut relabeled = proof.clone();
        for shard in &mut relabeled.shards {
            shard.epoch_floor += 1;
        }
        relabeled.root_commitment =
            root_commitment(&relabeled.policy_registry_root, &relabeled.shards);
        assert!(!verify_hierarchical_hem(
            &policies,
            epoch + 1,
            digest,
            12,
            config.regime,
            &relabeled
        ));
        let mut registry = policies.clone();
        registry[2].shard_id = 100;
        let mut relabeled = proof.clone();
        relabeled.shards[2].shard_id = 100;
        relabeled.policy_registry_root = compute_policy_registry_root(&registry);
        relabeled.root_commitment =
            root_commitment(&relabeled.policy_registry_root, &relabeled.shards);
        assert!(!verify_hierarchical_hem(
            &registry,
            epoch,
            digest,
            12,
            config.regime,
            &relabeled
        ));
        let mut registry = policies.clone();
        registry[1].custodian_cluster = registry[0].custodian_cluster;
        assert!(!verify_hierarchical_hem(
            &registry,
            epoch,
            digest,
            12,
            config.regime,
            &proof
        ));
        registry = policies.clone();
        registry[1].shard_id = registry[0].shard_id;
        assert!(!valid_policies(&registry));
        registry = policies.clone();
        registry[1].quorum_keys[0] = registry[0].quorum_keys[0];
        assert!(!valid_policies(&registry));
        assert!(!valid_policies(&[]));
    }

    #[test]
    fn hierarchical_stateless_corduroy_and_mixed_profile_registry_binding() {
        // 1. Pure stateless `CorduroyPoseidon2` 2-region x 2-quorum hierarchy:
        let epoch = 91u64;
        let payload = b"consensus-checkpoint:height=9100:variable-length-payload";
        let mut corduroy_policies = Vec::new();
        let mut corduroy_keys = Vec::new();
        for region in 0..2u64 {
            let keys: Vec<_> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::CorduroyPoseidon2,
                        &[0xA0 + region as u8; 32],
                        i,
                    )
                })
                .collect();
            corduroy_policies.push(ShardHemPolicy {
                shard_id: 10 + region,
                custodian_cluster: [0xC0 + region as u8; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 2,
            });
            corduroy_keys.push(keys);
        }
        let corduroy_root = compute_policy_registry_root(&corduroy_policies);
        let corduroy_sigs: Vec<Vec<_>> = corduroy_policies
            .iter()
            .zip(corduroy_keys.iter_mut())
            .map(|(policy, keys)| {
                let msg = hierarchical_hem_message(&corduroy_root, policy, epoch, payload);
                keys.iter_mut()
                    .map(|k| k.sign_stateless_for_unit_test(&msg).unwrap())
                    .collect()
            })
            .collect();
        let bm2 = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
        let corduroy_witnesses: Vec<_> = corduroy_sigs
            .iter()
            .map(|s| ShardHemWitness {
                bitmap: &bm2,
                signatures: s,
            })
            .collect();
        let cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [0x55; 32]);
        let corduroy_agg = prove_hierarchical_hem(
            &corduroy_policies,
            &corduroy_witnesses,
            epoch,
            payload,
            4,
            &cfg,
        )
        .unwrap();
        assert!(verify_hierarchical_hem(
            &corduroy_policies,
            epoch,
            payload,
            4,
            cfg.regime,
            &corduroy_agg
        ));
        assert_eq!(corduroy_agg.checked_total_quorums(), Some(4));
        let roundtrip =
            HierarchicalHemAggregate::from_bytes_canonical(&corduroy_agg.to_bytes()).unwrap();
        assert_eq!(roundtrip, corduroy_agg);

        // 2. Mixed `JortsPoseidon2` (Shard 0, 4 quorums) + `CorduroyPoseidon2` (Shard 1, 2 quorums)
        //    with strict registry-bound quorum signatures, plus cross-registry shard-splicing rejection!
        let mut jorts_keys: Vec<_> = (0..4)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(
                    AggSigProfile::JortsPoseidon2,
                    &[0x11; 32],
                    i,
                )
            })
            .collect();
        let mut cord_keys_a: Vec<_> = (0..2)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(
                    AggSigProfile::CorduroyPoseidon2,
                    &[0x22; 32],
                    i,
                )
            })
            .collect();
        let mut cord_keys_b: Vec<_> = (0..2)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(
                    AggSigProfile::CorduroyPoseidon2,
                    &[0x33; 32],
                    i,
                )
            })
            .collect();

        let p_jorts = ShardHemPolicy {
            shard_id: 0,
            custodian_cluster: [0x01; 32],
            quorum_keys: jorts_keys.iter().map(|k| k.pk).collect(),
            minimum_quorums: 3,
        };
        let p_cord_a = ShardHemPolicy {
            shard_id: 1,
            custodian_cluster: [0x02; 32],
            quorum_keys: cord_keys_a.iter().map(|k| k.pk).collect(),
            minimum_quorums: 2,
        };
        let p_cord_b = ShardHemPolicy {
            shard_id: 2,
            custodian_cluster: [0x03; 32],
            quorum_keys: cord_keys_b.iter().map(|k| k.pk).collect(),
            minimum_quorums: 2,
        };

        let registry_ab = alloc::vec![p_jorts.clone(), p_cord_a.clone()];
        let root_ab = compute_policy_registry_root(&registry_ab);
        let msg_jorts_ab = hierarchical_hem_message(&root_ab, &p_jorts, epoch, payload);
        let msg_cord_a = hierarchical_hem_message(&root_ab, &p_cord_a, epoch, payload);
        let bm_jorts = SignerBitmap::from_active_indices(4, &[0, 2, 3]).unwrap();
        let sigs_jorts_ab: Vec<_> = [0usize, 2, 3]
            .into_iter()
            .map(|idx| {
                jorts_keys[idx]
                    .sign_stateful_for_unit_test(&msg_jorts_ab, 3)
                    .unwrap()
            })
            .collect();
        let sigs_cord_a: Vec<_> = cord_keys_a
            .iter_mut()
            .map(|k| k.sign_stateless_for_unit_test(&msg_cord_a).unwrap())
            .collect();

        let mixed_agg = prove_hierarchical_hem(
            &registry_ab,
            &[
                ShardHemWitness {
                    bitmap: &bm_jorts,
                    signatures: &sigs_jorts_ab,
                },
                ShardHemWitness {
                    bitmap: &bm2,
                    signatures: &sigs_cord_a,
                },
            ],
            epoch,
            payload,
            5,
            &cfg,
        )
        .unwrap();
        assert!(verify_hierarchical_hem(
            &registry_ab,
            epoch,
            payload,
            5,
            cfg.regime,
            &mixed_agg
        ));

        // Splicing Shard 0 from `registry_ab` into `registry_ac = [p_jorts, p_cord_b]` must fail
        // even when Shard 2 (`p_cord_b`) genuinely signed for `registry_ac`!
        let registry_ac = alloc::vec![p_jorts.clone(), p_cord_b.clone()];
        let root_ac = compute_policy_registry_root(&registry_ac);
        let msg_cord_b = hierarchical_hem_message(&root_ac, &p_cord_b, epoch, payload);
        let sigs_cord_b: Vec<_> = cord_keys_b
            .iter_mut()
            .map(|k| k.sign_stateless_for_unit_test(&msg_cord_b).unwrap())
            .collect();
        let batch_cord_b = aggregate_signatures_with_config(
            &p_cord_b.quorum_keys,
            &bm2,
            &SigningMode::SharedMessage(&msg_cord_b),
            &sigs_cord_b,
            &HemAggConfig::default_for(AggSigProfile::CorduroyPoseidon2, [0x99; 32]),
        )
        .unwrap();

        let mut spliced_shards = alloc::vec![
            mixed_agg.shards[0].clone(),
            ShardHemBatch {
                shard_id: p_cord_b.shard_id,
                custodian_cluster: p_cord_b.custodian_cluster,
                shard_quorum_set_root: compute_committee_root(&p_cord_b.quorum_keys),
                minimum_quorums: p_cord_b.minimum_quorums as u64,
                epoch_floor: epoch,
                message_digest: compute_framed_message_digest(payload),
                proof: batch_cord_b,
            },
        ];
        let spliced_agg = HierarchicalHemAggregate {
            policy_registry_root: root_ac,
            root_commitment: root_commitment(&root_ac, &spliced_shards),
            shards: core::mem::take(&mut spliced_shards),
        };
        assert!(!verify_hierarchical_hem(
            &registry_ac,
            epoch,
            payload,
            5,
            cfg.regime,
            &spliced_agg
        ));
    }

    #[test]
    fn framing_injectivity_and_quorum_sum_overflow_rejection() {
        let k0 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[0x41; 32], 0)
                .pk;
        let k1 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[0x41; 32], 1)
                .pk;
        let k2 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[0x41; 32], 2)
                .pk;

        // Moving `k1` across the shard boundary `[k0, k1] | [k2]` vs `[k0] | [k1, k2]` must change
        // both `encode_policy_registry` and `compute_policy_registry_root`.
        let reg_left = [
            ShardHemPolicy {
                shard_id: 0,
                custodian_cluster: [1; 32],
                quorum_keys: alloc::vec![k0, k1],
                minimum_quorums: 1,
            },
            ShardHemPolicy {
                shard_id: 1,
                custodian_cluster: [2; 32],
                quorum_keys: alloc::vec![k2],
                minimum_quorums: 1,
            },
        ];
        let reg_right = [
            ShardHemPolicy {
                shard_id: 0,
                custodian_cluster: [1; 32],
                quorum_keys: alloc::vec![k0],
                minimum_quorums: 1,
            },
            ShardHemPolicy {
                shard_id: 1,
                custodian_cluster: [2; 32],
                quorum_keys: alloc::vec![k1, k2],
                minimum_quorums: 1,
            },
        ];
        assert_ne!(
            encode_policy_registry(&reg_left),
            encode_policy_registry(&reg_right)
        );
        assert_ne!(
            compute_policy_registry_root(&reg_left),
            compute_policy_registry_root(&reg_right)
        );

        // Changing `minimum_quorums` changes both the registry root and the signed regional frame.
        let mut p_min2 = reg_left[0].clone();
        p_min2.minimum_quorums = 2;
        let root_left = compute_policy_registry_root(&reg_left);
        assert_ne!(
            hierarchical_hem_message(&root_left, &reg_left[0], 7, b"abc"),
            hierarchical_hem_message(&root_left, &p_min2, 7, b"abc")
        );
        assert_ne!(
            hierarchical_hem_message(&root_left, &reg_left[0], 7, b""),
            hierarchical_hem_message(&root_left, &reg_left[0], 7, b"\x00")
        );
        // The same policy under a different registry signs a different statement.
        assert_ne!(
            hierarchical_hem_message(&root_left, &reg_left[0], 7, b"abc"),
            hierarchical_hem_message(
                &compute_policy_registry_root(&reg_right),
                &reg_left[0],
                7,
                b"abc"
            )
        );

        // Cross-profile reuse of the same `(pk_seed, pk_root)` across shards must be rejected.
        let k0_alias = ValidatorPublicKey {
            profile: AggSigProfile::CorduroyPoseidon2,
            pk_seed: k0.pk_seed,
            pk_root: k0.pk_root,
        };
        let cross_profile_dup = [
            ShardHemPolicy {
                shard_id: 0,
                custodian_cluster: [1; 32],
                quorum_keys: alloc::vec![k0],
                minimum_quorums: 1,
            },
            ShardHemPolicy {
                shard_id: 1,
                custodian_cluster: [2; 32],
                quorum_keys: alloc::vec![k0_alias],
                minimum_quorums: 1,
            },
        ];
        assert!(!valid_policies(&cross_profile_dup));

        // Zero integer overflow on summed quorum weights (`usize::MAX` / `u64::MAX` boundaries).
        assert_eq!(checked_sum_usize([usize::MAX, 1]), None);
        assert_eq!(checked_sum_usize([usize::MAX - 5, 5]), Some(usize::MAX));
        assert_eq!(
            qsag_whir_verified::checked_quorum_sum(&[u64::MAX - 3, 4], &[1, 1], 1),
            None
        );
        assert_eq!(
            qsag_whir_verified::checked_quorum_sum(&[u64::MAX - 4, 4], &[1, 1], u64::MAX),
            Some(u64::MAX)
        );

        // Up-front rejection of impossible `minimum_global_quorums = usize::MAX` without overflow.
        let bm1 = SignerBitmap::from_active_indices(2, &[0]).unwrap();
        let cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [9; 32]);
        assert_eq!(
            prove_hierarchical_hem(
                &reg_left,
                &[
                    ShardHemWitness {
                        bitmap: &bm1,
                        signatures: &[],
                    },
                    ShardHemWitness {
                        bitmap: &bm1,
                        signatures: &[],
                    },
                ],
                1,
                b"msg",
                usize::MAX,
                &cfg,
            ),
            Err(HemAggError::EmptySigners)
        );
    }

    #[test]
    fn succinct_outer_hem_three_shards_roundtrip_and_tamper_rejection() {
        let mut policies = Vec::new();
        let mut region_keys = Vec::new();
        let epoch = 29;
        let msg = b"succinct-outer-hem-binding";
        for region in 0..3u64 {
            let keys: Vec<_> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[region as u8 + 0x51; 32],
                        i,
                    )
                })
                .collect();
            policies.push(ShardHemPolicy {
                shard_id: region,
                custodian_cluster: [region as u8 + 0x10; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 2,
            });
            region_keys.push(keys);
        }

        let reg_root = compute_policy_registry_root(&policies);
        let bitmaps: Vec<_> = (0..3)
            .map(|_| SignerBitmap::from_active_indices(2, &[0, 1]).unwrap())
            .collect();
        let mut region_sigs = Vec::new();
        for (p, keys) in policies.iter().zip(region_keys.iter_mut()) {
            let region_msg = hierarchical_hem_message(&reg_root, p, epoch, msg);
            let sigs: Vec<_> = keys
                .iter_mut()
                .map(|kp| kp.sign_stateful_for_unit_test(&region_msg, 0).unwrap())
                .collect();
            region_sigs.push(sigs);
        }
        let witnesses: Vec<_> = bitmaps
            .iter()
            .zip(&region_sigs)
            .map(|(bitmap, sigs)| ShardHemWitness {
                bitmap,
                signatures: sigs,
            })
            .collect();

        let cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [0x77; 32]);
        let mut full = prove_hierarchical_hem(&policies, &witnesses, epoch, msg, 6, &cfg).unwrap();
        let succinct =
            compress_verified_hierarchical_hem(&policies, epoch, msg, 6, &full, cfg.blinding_seed)
                .unwrap();

        let evidence =
            verify_hierarchical_hem_evidence(&policies, epoch, msg, 6, cfg.regime, &full)
                .expect("full child proofs establish local evidence");
        {
            let registry = PreparedPolicyRegistry::new(policies.clone()).unwrap();
            let prepared = verify_hierarchical_hem_evidence_prepared(
                &registry, epoch, msg, 6, cfg.regime, &full,
            )
            .expect("prepared registry yields the same evidence");
            assert_eq!(prepared.summaries(), evidence.summaries());
            assert_eq!(prepared.policy_registry_root(), evidence.policy_registry_root());
            assert_eq!(prepared.message_digest(), evidence.message_digest());
            assert_eq!(
                (prepared.epoch_floor(), prepared.minimum_global_quorums(), prepared.regime()),
                (epoch, 6, cfg.regime)
            );
        }
        assert!(check_hierarchical_hem_commitment(
            &policies, epoch, msg, 6, &succinct,
        ));

        // The outer proof certifies a value any holder of the summaries can recompute.
        assert_eq!(
            compact_summary_chain_digest(&succinct.shards),
            succinct.terminal_chain_digest
        );

        // Merkle hash work of the real child verifiers against that of the outer proof.
        let child = crate::recursion_census::hierarchy_merkle_census(&full).unwrap();
        let outer = succinct.outer_merkle_census(cfg.regime).unwrap();
        assert_eq!(child.whir_openings, 3);
        assert_eq!(outer.whir_openings, 1);
        let child_perms = child.keccak_permutations().unwrap();
        std::eprintln!(
            "recursion census: child {child:?} keccak={child_perms} num_vars>={:?} rate8={:?}",
            child.bitwise_keccak_num_vars(),
            child.algebraic_rate8_permutations(),
        );
        std::eprintln!(
            "recursion census: outer {outer:?} keccak={:?} num_vars>={:?}",
            outer.keccak_permutations(),
            outer.bitwise_keccak_num_vars(),
        );
        assert!(child_perms > outer.keccak_permutations().unwrap());

        // Even a correctly committed full hierarchy cannot mint evidence when a child
        // fails verification. Keep the outer digest internally consistent in this case.
        full.shards[0].proof.committee_root[0] ^= 1;
        full.root_commitment = root_commitment(&full.policy_registry_root, &full.shards);
        assert!(
            verify_hierarchical_hem_evidence(&policies, epoch, msg, 6, cfg.regime, &full).is_none()
        );
        // Evidence owns its snapshot: mutating the source after validation cannot change it.
        assert_eq!(evidence.checked_total_quorums(), Some(6));
        assert_eq!(evidence.summaries(), succinct.shards.as_slice());
        assert!(evidence.names_same_children(&succinct));
        let registry = PreparedPolicyRegistry::new(policies.clone()).unwrap();
        // The source hierarchy is now invalid: the prepared path refuses it as well.
        assert!(
            verify_hierarchical_hem_evidence_prepared(&registry, epoch, msg, 6, cfg.regime, &full)
                .is_none()
        );
        assert!(verify_succinct_hierarchical_hem_prepared(
            &registry, epoch, msg, 6, cfg.regime, &succinct, &evidence,
        ));
        assert!(!verify_succinct_hierarchical_hem_prepared(
            &registry, epoch, msg, 5, cfg.regime, &succinct, &evidence,
        ));
        assert_eq!(succinct.checked_total_quorums(), Some(6));
        assert!(verify_succinct_hierarchical_hem(
            &policies, epoch, msg, 6, &succinct, &evidence
        ));

        for (other_epoch, other_msg, other_min) in [
            (epoch + 1, msg.as_slice(), 6),
            (epoch, b"another message".as_slice(), 6),
            (epoch, msg.as_slice(), 5),
        ] {
            assert!(!verify_succinct_hierarchical_hem(
                &policies, other_epoch, other_msg, other_min, &succinct, &evidence,
            ));
        }
        let mut other_registry = policies.clone();
        other_registry[0].custodian_cluster[0] ^= 1;
        assert!(!verify_succinct_hierarchical_hem(
            &other_registry, epoch, msg, 6, &succinct, &evidence,
        ));

        // This compact commitment needs the separately verified child evidence above.
        // Its byte size alone is not the cost of first-time signature verification.
        let full_wire = full.to_bytes();
        let succinct_wire = succinct.to_bytes();
        assert!(
            succinct_wire.len() < full_wire.len(),
            "succinct wire ({}) must compress full 3-shard wire ({})",
            succinct_wire.len(),
            full_wire.len()
        );
        let decoded = SuccinctHierarchicalHemAggregate::from_bytes_canonical(&succinct_wire)
            .expect("canonical succinct wire roundtrip");
        assert_eq!(decoded, succinct);
        assert!(verify_succinct_hierarchical_hem(
            &policies, epoch, msg, 6, &decoded, &evidence
        ));

        // Trailing byte must be rejected by canonical decoder.
        let mut trailing = succinct_wire.clone();
        trailing.push(0);
        assert_eq!(
            SuccinctHierarchicalHemAggregate::from_bytes_canonical(&trailing),
            Err(HemAggError::MalformedWireBytes)
        );

        // Classical regime downgrade must be rejected by both prover and verifier.
        assert!(!verify_succinct_hierarchical_hem_with_regime(
            &policies,
            epoch,
            msg,
            6,
            WhirSecurityRegime::BciksJohnsonClassical128,
            &succinct,
            &evidence,
        ));
        let mut classical_cfg = cfg.clone();
        classical_cfg.regime = WhirSecurityRegime::BciksJohnsonClassical128;
        assert_eq!(
            prove_succinct_hierarchical_hem(&policies, &witnesses, epoch, msg, 6, &classical_cfg),
            Err(HemAggError::InvalidShardConfig)
        );

        // Tampering child_proof_digest, terminal_chain_digest, sumcheck poly, or col_evals must fail.
        let mut bad_child = succinct.clone();
        bad_child.shards[1].child_proof_digest[0] ^= 0x01;
        assert!(!verify_succinct_hierarchical_hem(
            &policies, epoch, msg, 6, &bad_child, &evidence
        ));

        let mut bad_term = succinct.clone();
        bad_term.terminal_chain_digest[0] += Goldilocks::ONE;
        assert!(!verify_succinct_hierarchical_hem(
            &policies, epoch, msg, 6, &bad_term, &evidence
        ));

        let mut bad_sc = succinct.clone();
        bad_sc.outer_proof.row_sumcheck_polys[0][0] += GoldilocksExt4::ONE;
        assert!(!verify_succinct_hierarchical_hem(
            &policies, epoch, msg, 6, &bad_sc, &evidence
        ));

        let mut bad_col = succinct.clone();
        bad_col.outer_proof.col_evals[OUTER_COL_NEXT_CHAIN] += GoldilocksExt4::ONE;
        assert!(!verify_succinct_hierarchical_hem(
            &policies, epoch, msg, 6, &bad_col, &evidence
        ));
    }

    /// The outer relation is satisfiable for summaries that no child proof backs: the
    /// commitment check accepts them, and only child-verification evidence refuses them.
    #[test]
    fn commitment_relation_accepts_unbacked_summaries_and_evidence_gate_refuses_them() {
        let epoch = 41;
        let msg = b"no child proof exists for this message";
        let mut policies = Vec::new();
        let mut region_keys = Vec::new();
        for region in 0..2u64 {
            let keys: Vec<_> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[region as u8 + 0x61; 32],
                        i,
                    )
                })
                .collect();
            policies.push(ShardHemPolicy {
                shard_id: region,
                custodian_cluster: [region as u8 + 0x20; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 2,
            });
            region_keys.push(keys);
        }
        let committee_roots = compute_committee_roots(&policies);
        let registry_root = compute_policy_registry_root(&policies);
        let message_digest = compute_framed_message_digest(msg);

        // Nobody signed. Summaries claim full participation and name arbitrary child digests.
        let unbacked: Vec<ShardHemSummary> = policies
            .iter()
            .zip(&committee_roots)
            .map(|(p, c_root)| ShardHemSummary {
                shard_id: p.shard_id,
                custodian_cluster: p.custodian_cluster,
                shard_quorum_set_root: *c_root,
                minimum_quorums: 2,
                epoch_floor: epoch,
                message_digest,
                bitmap: SignerBitmap::from_active_indices(2, &[0, 1]).unwrap(),
                child_proof_digest: [0xEE; 32],
            })
            .collect();
        let forged =
            prove_outer_summary_chain(registry_root, unbacked, epoch, message_digest, 4, [9; 32])
                .unwrap();
        assert!(check_hierarchical_hem_commitment(&policies, epoch, msg, 4, &forged));
        let wire = forged.to_bytes();
        assert_eq!(
            SuccinctHierarchicalHemAggregate::from_bytes_canonical(&wire).unwrap(),
            forged
        );

        // Evidence from a real, fully signed hierarchy over the same registry and context
        // names different children, so the authorization path refuses the forged commitment.
        let bitmaps: Vec<_> = (0..2)
            .map(|_| SignerBitmap::from_active_indices(2, &[0, 1]).unwrap())
            .collect();
        let mut region_sigs = Vec::new();
        for (p, keys) in policies.iter().zip(region_keys.iter_mut()) {
            let region_msg = hierarchical_hem_message(&registry_root, p, epoch, msg);
            let sigs: Vec<_> = keys
                .iter_mut()
                .map(|kp| kp.sign_stateful_for_unit_test(&region_msg, 0).unwrap())
                .collect();
            region_sigs.push(sigs);
        }
        let witnesses: Vec<_> = bitmaps
            .iter()
            .zip(&region_sigs)
            .map(|(bitmap, signatures)| ShardHemWitness { bitmap, signatures })
            .collect();
        let cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [0x78; 32]);
        let full = prove_hierarchical_hem(&policies, &witnesses, epoch, msg, 4, &cfg).unwrap();
        let evidence =
            verify_hierarchical_hem_evidence(&policies, epoch, msg, 4, cfg.regime, &full).unwrap();
        assert!(!evidence.names_same_children(&forged));
        assert!(!verify_succinct_hierarchical_hem(
            &policies, epoch, msg, 4, &forged, &evidence
        ));
        let honest =
            compress_verified_hierarchical_hem(&policies, epoch, msg, 4, &full, cfg.blinding_seed)
                .unwrap();
        assert!(verify_succinct_hierarchical_hem(
            &policies, epoch, msg, 4, &honest, &evidence
        ));
    }

    #[test]
    fn prepared_policy_registry_matches_cold_verification_and_rejects_tamper() {
        assert!(PreparedPolicyRegistry::new(Vec::new()).is_none());

        let mut policies = Vec::new();
        let mut region_keys = Vec::new();
        let epoch = 41;
        let msg = b"beam-epoch-prepared-registry";
        for region in 0..2u64 {
            let keys: Vec<_> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[region as u8 + 0x71; 32],
                        i,
                    )
                })
                .collect();
            policies.push(ShardHemPolicy {
                shard_id: region,
                custodian_cluster: [region as u8 + 0x22; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 2,
            });
            region_keys.push(keys);
        }

        let prepared = PreparedPolicyRegistry::new(policies.clone()).expect("valid registry");
        assert_eq!(
            prepared.policy_registry_root(),
            compute_policy_registry_root(&policies)
        );
        assert_eq!(prepared.policies(), policies.as_slice());

        let bitmaps: Vec<_> = (0..2)
            .map(|_| SignerBitmap::from_active_indices(2, &[0, 1]).unwrap())
            .collect();
        let mut region_sigs = Vec::new();
        for (p, keys) in policies.iter().zip(region_keys.iter_mut()) {
            let region_msg =
                hierarchical_hem_message(&prepared.policy_registry_root(), p, epoch, msg);
            let sigs: Vec<_> = keys
                .iter_mut()
                .map(|kp| kp.sign_stateful_for_unit_test(&region_msg, 0).unwrap())
                .collect();
            region_sigs.push(sigs);
        }
        let witnesses: Vec<_> = bitmaps
            .iter()
            .zip(&region_sigs)
            .map(|(bitmap, sigs)| ShardHemWitness {
                bitmap,
                signatures: sigs,
            })
            .collect();

        let cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [0x44; 32]);
        let agg = prove_hierarchical_hem(&policies, &witnesses, epoch, msg, 4, &cfg).unwrap();
        let regime = WhirSecurityRegime::BciksJohnsonQrom128;
        let prepared_agg = prove_hierarchical_hem_prepared(&prepared, &witnesses, epoch, msg, 4, &cfg).unwrap();
        assert!(verify_hierarchical_hem_prepared(&prepared, epoch, msg, 4, regime, &prepared_agg));
        let evidence = verify_hierarchical_hem_evidence_prepared(&prepared, epoch, msg, 4, regime, &agg).unwrap();
        let compact = compress_hierarchical_hem_evidence(&evidence, [97;32]).unwrap();
        assert!(evidence.names_same_children(&compact));
        assert!(verify_succinct_hierarchical_hem_prepared(&prepared, epoch, msg, 4, regime, &compact, &evidence));
        assert!(!verify_succinct_hierarchical_hem_prepared(&prepared, epoch+1, msg, 4, regime, &compact, &evidence));
        assert!(!verify_succinct_hierarchical_hem_prepared(&prepared, epoch, b"relabel", 4, regime, &compact, &evidence));
        assert!(!verify_succinct_hierarchical_hem_prepared(&prepared, epoch, msg, 3, regime, &compact, &evidence));
        let mut changed = compact.clone(); changed.shards[0].child_proof_digest[0] ^= 1;
        assert!(!verify_succinct_hierarchical_hem_prepared(&prepared, epoch, msg, 4, regime, &changed, &evidence));


        assert!(verify_hierarchical_hem(
            &policies, epoch, msg, 4, regime, &agg
        ));
        assert!(verify_hierarchical_hem_prepared(
            &prepared, epoch, msg, 4, regime, &agg
        ));
        assert!(!verify_hierarchical_hem_prepared(
            &prepared,
            epoch + 1,
            msg,
            4,
            regime,
            &agg
        ));
        assert!(!verify_hierarchical_hem_prepared(
            &prepared,
            epoch,
            b"wrong-msg",
            4,
            regime,
            &agg
        ));
        assert!(!verify_hierarchical_hem_prepared(
            &prepared,
            epoch,
            msg,
            4,
            WhirSecurityRegime::BciksJohnsonClassical128,
            &agg
        ));

        let mut bad_root = agg.clone();
        bad_root.root_commitment[0] ^= 1;
        assert!(!verify_hierarchical_hem_prepared(
            &prepared, epoch, msg, 4, regime, &bad_root
        ));
    }
    /// Narrow opt-in benchmark: two regional proofs, fresh evidence versus immutable reuse.
    /// Run the already-built test binary under an enforced cgroup and /usr/bin/time -v.
    #[test]
    #[ignore]
    #[cfg(feature = "std")]
    fn pipeline_evidence_reuse_benchmark() {
        use std::time::Instant;
        let count=std::env::var("QSAG_PIPELINE_SIGNERS").ok().and_then(|x|x.parse::<usize>().ok()).unwrap_or(16);
        assert!((2..=128).contains(&count));
        let epoch=101; let msg=b"qsag-pipeline-real-shards";
        let start=Instant::now();
        let mut keys:Vec<Vec<_>>=(0..2).map(|region| (0..count).map(|i|
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2,&[region+121;32],i as u32)
        ).collect()).collect();
        let policies:Vec<_>=keys.iter().enumerate().map(|(i,keys)|ShardHemPolicy{
            shard_id:i as u64,custodian_cluster:[i as u8;32],quorum_keys:keys.iter().map(|k|k.pk).collect(),minimum_quorums:count,
        }).collect();
        let registry=PreparedPolicyRegistry::new(policies.clone()).unwrap();
        let bm=SignerBitmap::from_active_indices(count as u32,&(0..count).collect::<Vec<_>>()).unwrap();
        let sigs:Vec<Vec<_>>=keys.iter_mut().zip(&policies).map(|(keys,p)| {
            let framed=hierarchical_hem_message(&registry.policy_registry_root(),p,epoch,msg);
            keys.iter_mut().map(|k|k.sign_stateful_for_unit_test(&framed,0).unwrap()).collect()
        }).collect();
        let witnesses:Vec<_>=sigs.iter().map(|s|ShardHemWitness{bitmap:&bm,signatures:s}).collect();
        let setup_ms=start.elapsed().as_secs_f64()*1000.0;
        let cfg=HemAggConfig::default_for(AggSigProfile::JortsPoseidon2,[84;32]);
        let start=Instant::now();
        let agg=prove_hierarchical_hem_prepared(&registry,&witnesses,epoch,msg,2*count,&cfg).unwrap();
        let prove_ms=start.elapsed().as_secs_f64()*1000.0;
        let wire=agg.to_bytes();
        let agg=HierarchicalHemAggregate::from_bytes_canonical(&wire).unwrap();
        let mut fresh=Vec::new();let mut reuse=Vec::new();let mut duplicate=Vec::new();let mut compact_bytes=0;
        for sample in 0..4 {
            let start=Instant::now();
            let ev=verify_hierarchical_hem_evidence_prepared(&registry,epoch,msg,2*count,cfg.regime,&agg).unwrap();
            let evidence_ms=start.elapsed().as_secs_f64()*1000.0;
            let start=Instant::now();
            let compact=compress_hierarchical_hem_evidence(&ev,[85;32]).unwrap();
            let reuse_ms=start.elapsed().as_secs_f64()*1000.0;
            compact_bytes=compact.to_bytes().len();
            assert!(verify_succinct_hierarchical_hem_prepared(&registry,epoch,msg,2*count,cfg.regime,&compact,&ev));
            let start=Instant::now();
            let legacy=compress_verified_hierarchical_hem(&policies,epoch,msg,2*count,&agg,[85;32]).unwrap();
            let duplicate_ms=evidence_ms+start.elapsed().as_secs_f64()*1000.0;
            assert!(ev.names_same_children(&legacy));
            if sample>0 {fresh.push(evidence_ms+reuse_ms);reuse.push(reuse_ms);duplicate.push(duplicate_ms);}
        }
        let median=|mut xs:Vec<f64>| {xs.sort_by(|a,b|a.partial_cmp(b).unwrap());xs[xs.len()/2]};
        std::println!("pipeline signers={} regions=2 prover_jobs={} setup_ms={:.2} prove_ms={:.2} signers_per_s={:.2} hierarchy_bytes={} compact_bytes={} fresh_evidence_plus_build_p50_ms={:.3} reused_evidence_build_p50_ms={:.3} duplicate_verify_pipeline_p50_ms={:.3}",
            2*count,crate::prover_parallel_jobs(),setup_ms,prove_ms,2000.0*count as f64/prove_ms,wire.len(),compact_bytes,median(fresh),median(reuse),median(duplicate));
    }

}
