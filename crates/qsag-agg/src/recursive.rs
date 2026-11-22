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
//! 3. Succinct shard-opening merges ([`SuccinctShardWhirAggregate`]), where one committed
//!    outer relation executes the fixed-path WHIR verifier of every shard's evaluation claim
//!    and each claim is bound to its shard summary and policy registry. The parent is
//!    smaller than the child openings it replaces (303 KB against 528 KB for two 4,096-cell
//!    children). It certifies the openings and nothing else: a shard's row sumcheck and AIR
//!    constraint check are not in the relation, and nothing ties a claimed polynomial to the
//!    shard's signature trace. [`check_succinct_shard_whir_merge`] therefore authorizes
//!    nothing, and [`verify_succinct_shard_whir_merge`] takes the same
//!    [`VerifiedHierarchicalHemEvidence`] as mode 2.
//! 4. Succinct full-shard aggregates ([`SuccinctFullShardAggregate`], `std` only), where the
//!    outer relation runs each shard's whole verifier: the Fiat-Shamir transcript, the row
//!    sumcheck, the row constraints at the public inputs, the column fold and the opening.
//!    [`verify_succinct_full_shard_aggregate`] takes the statement and the proof and nothing
//!    else. Shards are `JortsPoseidon2` only, proved in the recursion format, and sign
//!    [`full_shard_signing_message`].

pub mod split;
pub use crate::zk_hem::recursive_ivc::{
    FixedPathWhirW24, IvcPolicyRegistry, IvcRowCensus, IvcShard, IvcStepConfig,
    IvcSubtreeStatement, IvcTableCommitment, IvcTreeStepRelation, SuccinctIvcProof, SuccinctIvcStep,
    ivc_signing_message, prove_ivc_tree, verify_ivc_tree,
};

/// The `k`-child PCS-verifier relation behind [`SuccinctShardWhirAggregate`]; unlike the
/// legacy digest hierarchy, it checks the child openings in the outer relation. It does not
/// by itself certify the signature/AIR relation that produced a child opening statement.
pub use crate::zk_hem::recursive_whir::{
    ChildWhirMergeRelation, ChildWhirRelationStats, ChildWhirStatement, FixedPathWhirParams,
    FixedPathWhirProof, MAX_MERGE_CHILDREN, RecursiveWhirError, SuccinctChildWhirMerge,
    merged_child_whir_root, prove_for_recursion, prove_succinct_children_whir_merge,
    verify_fixed_path, verify_succinct_children_whir_merge,
};

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
    if !valid_policies(policies) {
        return Err(HemAggError::InvalidShardConfig);
    }
    let committee_roots = compute_committee_roots(policies);
    let policy_registry_root = compute_policy_registry_root_with_roots(policies, &committee_roots);
    prove_hierarchical_hem_with_roots(
        policies,
        &committee_roots,
        policy_registry_root,
        witnesses,
        epoch_floor,
        message,
        minimum_global_quorums,
        config,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_hierarchical_hem_with_roots(
    policies: &[ShardHemPolicy],
    committee_roots: &[[u8; 32]],
    policy_registry_root: [u8; 32],
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: &[u8],
    minimum_global_quorums: usize,
    config: &HemAggConfig,
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
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    config: &HemAggConfig,
) -> Result<HierarchicalHemAggregate, HemAggError> {
    prove_hierarchical_hem_with_roots(
        &registry.policies,
        &registry.committee_roots,
        registry.policy_registry_root,
        witnesses,
        epoch_floor,
        message.as_ref(),
        minimum_global_quorums,
        config,
    )
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
    if !regime.is_accepted_aggregate_profile()
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
    if !regime.is_accepted_aggregate_profile()
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
    // Weighted 3-block Jive feed-forward (`perm_out.b0 + st_in.b0 + 2*st_in.b1 + 4*st_in.b2`),
    // matching `Qsag.jiveWeightedFeedForward` (`ePrint 2026/306` §6).
    let mut next_chain = [Goldilocks::ZERO; 4];
    for j in 0..4 {
        let b0 = st_in[j];
        let b1 = st_in[4 + j];
        let b2 = st_in[8 + j];
        next_chain[j] = perm_out[j] + b0 + (b1 + b1) + (b2 + b2 + b2 + b2);
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
    //    and weighted 3-block Jive feed-forward `next_chain = perm_out.b0 + b0 + 2*b1 + 4*b2`.
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
        let jive_ff = st[j] + b0 + (b1 + b1) + (b2 + b2 + b2 + b2);
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
            *dst = Goldilocks::from_le_bytes_canonical(lb)
                .map_err(|_| HemAggError::MalformedWireBytes)?;
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
        policies,
        epoch_floor,
        message,
        minimum_global_quorums,
        WhirSecurityRegime::BciksJohnsonQrom128,
        aggregate,
    )
    .ok_or(HemAggError::InvalidShardConfig)?;
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
        evidence.policy_registry_root,
        evidence.shards.clone(),
        evidence.epoch_floor,
        evidence.message_digest,
        minimum,
        blinding_seed,
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
    if !config.regime.is_accepted_aggregate_profile() {
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
    if !expected_regime.is_accepted_aggregate_profile()
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

// ============================================================================
// Succinct shard-opening mode
// ============================================================================

/// One shard's evaluation claim about its fixed-path witness commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardWhirClaim {
    pub summary: ShardHemSummary,
    pub commitment: [Goldilocks; 4],
    pub point: Vec<GoldilocksExt4>,
    pub value: GoldilocksExt4,
}

/// Header binding a shard opening to its registry and its whole summary, including the
/// signer bitmap and the child-proof digest.
pub fn shard_whir_header(policy_registry_root: &[u8; 32], summary: &ShardHemSummary) -> [u8; 32] {
    poseidon2_hash32(&encode_multi_frame(&[
        b"QSAG.SHM.WHIR.HDR/v1",
        policy_registry_root,
        &shard_summary_header_digest(summary),
        &summary.child_proof_digest,
    ]))
}

impl ShardWhirClaim {
    /// Public opening statement the merge relation verifies for this shard.
    pub fn statement(&self, policy_registry_root: &[u8; 32]) -> ChildWhirStatement {
        ChildWhirStatement {
            shard_header: shard_whir_header(policy_registry_root, &self.summary),
            commitment: self.commitment,
            point: self.point.clone(),
            value: self.value,
        }
    }
}

/// Shard summaries, their evaluation claims and one parent proof that every claim's WHIR
/// opening verifies. No child opening proof is carried.
///
/// This is an opening certificate, not a signature certificate. The summaries (signer
/// bitmaps, child-proof digests) are claims; the merge relation never runs a shard's
/// signature verifier. Use [`verify_succinct_shard_whir_merge`] with locally validated
/// evidence; [`check_succinct_shard_whir_merge`] checks only the openings and their binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctShardWhirAggregate {
    pub policy_registry_root: [u8; 32],
    pub claims: Vec<ShardWhirClaim>,
    pub merge: SuccinctChildWhirMerge,
}

fn shard_whir_statements(
    policy_registry_root: &[u8; 32],
    claims: &[ShardWhirClaim],
) -> Vec<ChildWhirStatement> {
    claims
        .iter()
        .map(|c| c.statement(policy_registry_root))
        .collect()
}

/// Merge the shards' fixed-path openings into one parent proof. `openings[i]` must open
/// `claims[i]` under the header [`shard_whir_header`] derives for it.
pub fn prove_succinct_shard_whir_merge(
    relation: &ChildWhirMergeRelation,
    policy_registry_root: [u8; 32],
    claims: Vec<ShardWhirClaim>,
    openings: &[FixedPathWhirProof],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
) -> Result<SuccinctShardWhirAggregate, RecursiveWhirError> {
    let statements = shard_whir_statements(&policy_registry_root, &claims);
    if !statements
        .iter()
        .zip(openings)
        .all(|(s, p)| verify_fixed_path(relation.params(), s, p))
    {
        return Err(RecursiveWhirError::InvalidOpening);
    }
    let merge = prove_succinct_children_whir_merge(relation, &statements, openings, regime, seed)?;
    Ok(SuccinctShardWhirAggregate {
        policy_registry_root,
        claims,
        merge,
    })
}

/// Verify a succinct shard-opening merge against independently validated child evidence.
///
/// `evidence` must come from verifying every shard's full `Hem` proof (signatures, AIR and
/// opening) for this registry, epoch, message and threshold, and must name exactly the
/// summaries the claims carry, child-proof digests included. The children's own security
/// regime must equal `regime`, the parent proof's authorization regime. An opening
/// merge alone can never satisfy this function.
#[allow(clippy::too_many_arguments)]
pub fn verify_succinct_shard_whir_merge(
    relation: &ChildWhirMergeRelation,
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &SuccinctShardWhirAggregate,
    evidence: &VerifiedHierarchicalHemEvidence,
) -> bool {
    let message = message.as_ref();
    evidence.regime() == regime
        && evidence.epoch_floor == epoch_floor
        && evidence.message_digest == compute_framed_message_digest(message)
        && evidence.minimum_global_quorums == minimum_global_quorums
        && evidence.policy_registry_root == aggregate.policy_registry_root
        && evidence
            .shards
            .iter()
            .eq(aggregate.claims.iter().map(|claim| &claim.summary))
        && check_succinct_shard_whir_merge(
            relation,
            policies,
            epoch_floor,
            message,
            minimum_global_quorums,
            regime,
            aggregate,
        )
}

/// Check the parent proof against `policies` in the exact `epoch_floor` / `message`
/// context: every summary must name its policy and meet its quorum minimum, the summed
/// quorums must reach `minimum_global_quorums`, and each claim's opening must verify inside
/// the merge relation under the header of that summary.
///
/// As with [`check_hierarchical_hem_commitment`], the signer bitmaps are claims of the
/// summaries: this does not verify the shard signatures and must not authorize anything.
pub fn check_succinct_shard_whir_merge(
    relation: &ChildWhirMergeRelation,
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &SuccinctShardWhirAggregate,
) -> bool {
    if !valid_policies(policies)
        || aggregate.claims.len() != policies.len()
        || minimum_global_quorums == 0
    {
        return false;
    }
    let committee_roots = compute_committee_roots(policies);
    if aggregate.policy_registry_root
        != compute_policy_registry_root_with_roots(policies, &committee_roots)
    {
        return false;
    }
    let message_digest = compute_framed_message_digest(message.as_ref());
    let mut counts = Vec::with_capacity(policies.len());
    let mut minimums = Vec::with_capacity(policies.len());
    for ((p, claim), c_root) in policies.iter().zip(&aggregate.claims).zip(&committee_roots) {
        let s = &claim.summary;
        let (Ok(minimum), Ok(signers)) = (
            u64::try_from(p.minimum_quorums),
            u64::try_from(s.num_signers()),
        ) else {
            return false;
        };
        if s.shard_id != p.shard_id
            || s.custodian_cluster != p.custodian_cluster
            || s.shard_quorum_set_root != *c_root
            || s.minimum_quorums != minimum
            || s.epoch_floor != epoch_floor
            || s.message_digest != message_digest
            || s.bitmap.num_validators() as usize != p.quorum_keys.len()
            || s.num_signers() < p.minimum_quorums
        {
            return false;
        }
        counts.push(signers);
        minimums.push(minimum);
    }
    let Ok(minimum_global) = u64::try_from(minimum_global_quorums) else {
        return false;
    };
    if qsag_whir_verified::checked_quorum_sum(&counts, &minimums, minimum_global).is_none() {
        return false;
    }
    let statements = shard_whir_statements(&aggregate.policy_registry_root, &aggregate.claims);
    verify_succinct_children_whir_merge(relation, &statements, regime, &aggregate.merge)
}

// ============================================================================
// Succinct full-shard mode
// ============================================================================

/// The full-shard relation and its proofs: see [`crate::zk_hem::full_shard`].
pub use crate::zk_hem::full_shard::{
    FullShardError, FullShardMergeProof, FullShardMergeRelation, FullShardParams,
    FullShardRelationStats, MAX_FULL_SHARD_CHILDREN, RECURSIVE_SHARD_WIRE_MAGIC,
    RecursiveShardProof, RecursiveShardStatement, SHARD_MESSAGE_BYTES, ShardPublic,
    committee_digest, prove_full_shard_merge, prove_recursive_shard, verify_full_shard_merge,
    verify_recursive_shard,
};

/// Canonical 8-byte wire header for [`SuccinctFullShardAggregate`].
pub const SUCCINCT_FULL_SHARD_WIRE_MAGIC: &[u8; 8] = b"QSAGFSA2";

/// The 32-byte statement a quorum key of `policy` signs in full-shard mode: a digest of
/// [`hierarchical_hem_message`], so it binds the registry root, the shard's identity,
/// minimum and committee, the epoch and the message.
pub fn full_shard_signing_message(
    policy_registry_root: &[u8; 32],
    policy: &ShardHemPolicy,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
) -> [u8; 32] {
    poseidon2_hash32(&encode_multi_frame(&[
        b"QSAG.HEM.FULL.SHARD.MSG/v1",
        &hierarchical_hem_message(policy_registry_root, policy, epoch_floor, message),
    ]))
}

/// What a [`SuccinctFullShardAggregate`] is verified against. Nothing here comes from a
/// prover.
#[derive(Clone, Copy, Debug)]
pub struct FullShardAggregateStatement<'a> {
    pub policies: &'a [ShardHemPolicy],
    pub epoch_floor: u64,
    pub message: &'a [u8],
    pub minimum_global_quorums: usize,
}

/// One parent proof that, in every shard of a registry, `signer_counts[i]` distinct quorum
/// keys signed the shard's [`full_shard_signing_message`]. It carries no child proof, no
/// signer bitmap and no summary. The parent uses committed masking; signer privacy of
/// the full composition is not proved. See [`crate::zk_hem::protocol::prove`] for the
/// simulator and concrete security bounds still missing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctFullShardAggregate {
    pub signer_counts: Vec<u32>,
    pub proof: FullShardMergeProof,
}

impl SuccinctFullShardAggregate {
    /// Serialize to canonical self-delimiting wire bytes (`QSAGFSA2` header).
    pub fn to_bytes(&self) -> Vec<u8> {
        let proof_bytes = self.proof.to_bytes();
        let mut out = Vec::with_capacity(12 + 4 * self.signer_counts.len() + proof_bytes.len());
        out.extend_from_slice(SUCCINCT_FULL_SHARD_WIRE_MAGIC);
        out.extend_from_slice(&(self.signer_counts.len() as u32).to_le_bytes());
        for &count in &self.signer_counts {
            out.extend_from_slice(&count.to_le_bytes());
        }
        out.extend_from_slice(&proof_bytes);
        out
    }

    /// Decode canonical wire bytes for `(relation, regime)`, rejecting non-canonical counts and trailing bytes.
    pub fn from_bytes_canonical(
        relation: &FullShardMergeRelation,
        regime: WhirSecurityRegime,
        bytes: &[u8],
    ) -> Option<Self> {
        if bytes.get(..8)? != SUCCINCT_FULL_SHARD_WIRE_MAGIC {
            return None;
        }
        let n = u32::from_le_bytes(bytes.get(8..12)?.try_into().ok()?) as usize;
        if n != relation.num_children() {
            return None;
        }
        let counts_end = 12usize.checked_add(4usize.checked_mul(n)?)?;
        let count_bytes = bytes.get(12..counts_end)?;
        let mut signer_counts = Vec::with_capacity(n);
        for chunk in count_bytes.as_chunks::<4>().0 {
            let c = u32::from_le_bytes(*chunk);
            if c == 0 || c as usize > relation.params().slots() {
                return None;
            }
            signer_counts.push(c);
        }
        if !regime.is_accepted_aggregate_profile() {
            return None;
        }
        let profile = crate::zk_hem::v2::params::Profile::for_regime(regime);
        let proof = FullShardMergeProof::from_bytes(bytes.get(counts_end..)?, relation, profile)?;
        Some(Self {
            signer_counts,
            proof,
        })
    }
}

fn full_shard_statements(
    relation: &FullShardMergeRelation,
    statement: &FullShardAggregateStatement<'_>,
) -> Option<Vec<(Digest4Limbs, [u8; 32])>> {
    let policies = statement.policies;
    if !valid_policies(policies)
        || policies.len() != relation.num_children()
        || statement.minimum_global_quorums == 0
    {
        return None;
    }
    let committee_roots = compute_committee_roots(policies);
    let registry_root = compute_policy_registry_root_with_roots(policies, &committee_roots);
    policies
        .iter()
        .zip(&committee_roots)
        .map(|(policy, committee_root)| {
            let signed = hierarchical_hem_message_with_root(
                &registry_root,
                policy,
                committee_root,
                statement.epoch_floor,
                statement.message,
            );
            let message = poseidon2_hash32(&encode_multi_frame(&[
                b"QSAG.HEM.FULL.SHARD.MSG/v1",
                &signed,
            ]));
            Some((
                committee_digest(relation.params(), &policy.quorum_keys)?,
                message,
            ))
        })
        .collect()
}

type Digest4Limbs = [Goldilocks; 4];

/// Prove a full-shard aggregate. `witnesses[i]` holds shard `i`'s signer bitmap over its
/// policy's quorum keys and the signatures of those signers, in ascending index order, over
/// [`full_shard_signing_message`]. Both the children and the parent use the relation's
/// regime. `seed` must be uniform and secret, as required by
/// [`crate::zk_hem::protocol::prove`].
pub fn prove_succinct_full_shard_aggregate(
    relation: &FullShardMergeRelation,
    statement: &FullShardAggregateStatement<'_>,
    witnesses: &[ShardHemWitness<'_>],
    seed: &[u8; 32],
) -> Result<SuccinctFullShardAggregate, FullShardError> {
    let shards = full_shard_statements(relation, statement)
        .filter(|shards| shards.len() == witnesses.len())
        .ok_or(FullShardError::InvalidStatement)?;
    let mut statements = Vec::with_capacity(shards.len());
    let mut counts = Vec::with_capacity(shards.len());
    let mut minimums = Vec::with_capacity(shards.len());
    for ((policy, witness), (_, message)) in statement.policies.iter().zip(witnesses).zip(&shards) {
        statements.push(RecursiveShardStatement {
            keys: policy.quorum_keys.clone(),
            bitmap: witness.bitmap.clone(),
            message: *message,
        });
        counts.push(witness.bitmap.count_ones() as u64);
        minimums.push(policy.minimum_quorums as u64);
    }
    let minimum_global = u64::try_from(statement.minimum_global_quorums)
        .map_err(|_| FullShardError::InvalidStatement)?;
    if qsag_whir_verified::checked_quorum_sum(&counts, &minimums, minimum_global).is_none() {
        return Err(FullShardError::InvalidStatement);
    }
    let prove_one = |index: usize| -> Result<RecursiveShardProof, FullShardError> {
        let mut blinding = [0u8; 40];
        blinding[..32].copy_from_slice(seed);
        blinding[32..].copy_from_slice(&(index as u64).to_le_bytes());
        let blinding = crate::sponge::cshake256_32(b"QSAG.HEM.FULL.SHARD.BLIND/v1", &blinding);
        prove_recursive_shard(
            relation.params(),
            &statements[index],
            witnesses[index].signatures,
            &blinding,
        )
    };
    #[cfg(feature = "std")]
    let proofs: Vec<RecursiveShardProof> = if statements.len() > 1 && crate::parallel_workers() > 1
    {
        let results: Vec<Result<RecursiveShardProof, FullShardError>> =
            std::thread::scope(|scope| {
                let prove_ref = &prove_one;
                let tails: Vec<_> = (1..statements.len())
                    .map(|index| crate::spawn_bounded(scope, move || prove_ref(index)))
                    .collect();
                let mut out = Vec::with_capacity(statements.len());
                out.push(prove_ref(0));
                out.extend(tails.into_iter().map(crate::join_worker));
                out
            });
        results.into_iter().collect::<Result<Vec<_>, _>>()?
    } else {
        (0..statements.len())
            .map(prove_one)
            .collect::<Result<Vec<_>, _>>()?
    };
    #[cfg(not(feature = "std"))]
    let proofs: Vec<RecursiveShardProof> = (0..statements.len())
        .map(prove_one)
        .collect::<Result<Vec<_>, _>>()?;

    if !relation.params().regime().is_accepted_aggregate_profile() {
        return Err(FullShardError::InvalidParameters);
    }
    let profile = crate::zk_hem::v2::params::Profile::for_regime(relation.params().regime());
    let proof = prove_full_shard_merge(relation, &statements, &proofs, profile, seed)?;
    Ok(SuccinctFullShardAggregate {
        signer_counts: counts.iter().map(|&c| c as u32).collect(),
        proof,
    })
}

/// Verify a full-shard aggregate from the statement and the proof alone: every shard's
/// count meets its policy minimum, the counts reach `minimum_global_quorums`, and the
/// parent proof certifies each count for that shard's committee and signed statement. No
/// child proof and no locally verified evidence is needed.
pub fn verify_succinct_full_shard_aggregate(
    relation: &FullShardMergeRelation,
    statement: &FullShardAggregateStatement<'_>,
    aggregate: &SuccinctFullShardAggregate,
) -> bool {
    let Some(shards) = full_shard_statements(relation, statement) else {
        return false;
    };
    if aggregate.signer_counts.len() != shards.len() {
        return false;
    }
    let counts: Vec<u64> = aggregate
        .signer_counts
        .iter()
        .map(|&c| u64::from(c))
        .collect();
    let minimums: Vec<u64> = statement
        .policies
        .iter()
        .map(|p| p.minimum_quorums as u64)
        .collect();
    let Ok(minimum_global) = u64::try_from(statement.minimum_global_quorums) else {
        return false;
    };
    if statement
        .policies
        .iter()
        .zip(&counts)
        .any(|(p, &c)| c > p.quorum_keys.len() as u64)
        || qsag_whir_verified::checked_quorum_sum(&counts, &minimums, minimum_global).is_none()
    {
        return false;
    }
    let publics: Vec<ShardPublic> = shards
        .into_iter()
        .zip(&aggregate.signer_counts)
        .map(|((committee, message), &signers)| ShardPublic {
            committee,
            message,
            signers,
        })
        .collect();
    if !relation.params().regime().is_accepted_aggregate_profile() {
        return false;
    }
    let profile = crate::zk_hem::v2::params::Profile::for_regime(relation.params().regime());
    verify_full_shard_merge(relation, &publics, profile, &aggregate.proof)
}

// ============================================================================
// Arbitrary-Depth `Merge -> Merge` Subtree Recursion (`SubtreePublic`, `QSAGSTA1`)
// ============================================================================

/// Constant number of public Goldilocks words per subtree node (`4 + 1 + 5 + 1 + 3 = 14`),
/// invariant across arbitrary tree depth and shard count.
pub const SUBTREE_PUBLIC_WORDS: usize = 14;

/// Canonical 8-byte wire magic for [`SuccinctSubtreeAggregate`].
pub const SUCCINCT_SUBTREE_WIRE_MAGIC: &[u8; 8] = b"QSAGSTA1";

const T_SUBTREE_POLICY_LEAF: u64 = 0x5354_4C45_4146;
const T_SUBTREE_MERKLE_NODE: u64 = 0x5354_4E4F_4445;
const T_SUBTREE_SIGN_MSG: u64 = 0x5354_5349_474E;
const SUBTREE_REC_TAG: [u8; 32] = *b"QSAG.SUBTREE.RECURSIVE.NODE/v1\0\0";
const SUBTREE_ROOT_LABEL: &[u8] = b"QSAG.SUBTREE.ROOT.HOLOGRAM/v1";

/// Constant-14-word public statement of any Level-1 or Level-2+ subtree merge node.
///
/// Contains ZERO per-shard statement growth: individual shard committees, messages, and
/// quorum thresholds are authenticated inside the binary Poseidon2 `subtree_registry_root`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SubtreePublic {
    pub subtree_registry_root: [Goldilocks; 4],
    pub epoch_floor: Goldilocks,
    pub message_digest: [Goldilocks; 5],
    pub total_active_signers: Goldilocks,
    /// Inclusive ordered directory indices (the registered shard IDs), bounded to 58 bits.
    pub min_key_idx: u64,
    pub max_key_idx: u64,
    /// Sum of active signer weights, bounded to 62 bits. Legacy policies use unit weights.
    pub total_active_weight: u64,
}

impl SubtreePublic {
    #[inline]
    pub fn words(&self) -> [Goldilocks; SUBTREE_PUBLIC_WORDS] {
        let r = self.subtree_registry_root;
        let m = self.message_digest;
        [
            r[0],
            r[1],
            r[2],
            r[3],
            self.epoch_floor,
            m[0],
            m[1],
            m[2],
            m[3],
            m[4],
            self.total_active_signers,
            Goldilocks::from_u64_reduced(self.min_key_idx),
            Goldilocks::from_u64_reduced(self.max_key_idx),
            Goldilocks::from_u64_reduced(self.total_active_weight),
        ]
    }
}

/// Canonical 5-limb (`56, 56, 56, 56, 32`-bit) message digest for [`SubtreePublic`].
pub fn subtree_message_digest(message: &[u8]) -> [Goldilocks; 5] {
    let h = poseidon2_hash32(&encode_multi_frame(&[b"QSAG.HEM.SUBTREE.MSG/v1", message]));
    core::array::from_fn(|i| {
        let width = if i < 4 { 7 } else { 4 };
        let mut acc = 0u64;
        for k in 0..width {
            acc |= u64::from(h[7 * i + k]) << (8 * k);
        }
        Goldilocks::from_u64_reduced(acc)
    })
}

fn subtree_policy_leaf_gadget<B: crate::zk_hem::recursive_whir::Backend>(
    b: &mut B,
    shard_id_limbs: &[B::W; 2],
    custodian_limbs: &[B::W; 8],
    comm_digest: &[B::W; 4],
    min_quorums: &B::W,
    weight: &B::W,
) -> [B::W; 4] {
    use crate::zk_hem::recursive_whir::{Transcript, bits};
    for limb in shard_id_limbs.iter().chain(custodian_limbs) {
        bits(b, limb, 32);
    }
    bits(b, min_quorums, 32);
    bits(b, weight, 32);
    let mut msg = Vec::with_capacity(15);
    msg.extend_from_slice(shard_id_limbs);
    msg.extend_from_slice(custodian_limbs);
    msg.extend_from_slice(comm_digest);
    msg.push(min_quorums.clone());
    msg.push(weight.clone());
    let mut tr = Transcript::new();
    tr.absorb(b, T_SUBTREE_POLICY_LEAF, &msg);
    core::array::from_fn(|i| b.pin(tr.state[i].clone()))
}

fn subtree_merkle_pair_gadget<B: crate::zk_hem::recursive_whir::Backend>(
    b: &mut B,
    merkle_level: usize,
    left: &[B::W; 4],
    right: &[B::W; 4],
) -> [B::W; 4] {
    use crate::zk_hem::recursive_whir::Transcript;
    let mut msg = Vec::with_capacity(8);
    msg.extend_from_slice(left);
    msg.extend_from_slice(right);
    let mut tr = Transcript::new();
    tr.absorb(b, T_SUBTREE_MERKLE_NODE + merkle_level as u64, &msg);
    core::array::from_fn(|i| b.pin(tr.state[i].clone()))
}

fn subtree_fold_merkle_gadget<B: crate::zk_hem::recursive_whir::Backend>(
    b: &mut B,
    base_merkle_level: usize,
    roots: &[[B::W; 4]],
) -> [B::W; 4] {
    assert!(roots.len().is_power_of_two() && !roots.is_empty());
    let mut layer = roots.to_vec();
    let mut lvl = base_merkle_level;
    while layer.len() > 1 {
        layer = layer
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| subtree_merkle_pair_gadget(b, lvl, &pair[0], &pair[1]))
            .collect();
        lvl += 1;
    }
    layer[0].clone()
}

fn subtree_sign_msg_gadget<B: crate::zk_hem::recursive_whir::Backend>(
    b: &mut B,
    leaf_digest: &[B::W; 4],
    epoch_floor: &B::W,
    msg_digest: &[B::W; 5],
) -> [B::W; SHARD_MESSAGE_BYTES] {
    use crate::zk_hem::recursive_whir::{Base as _, Transcript, bits, f};
    let mut msg = Vec::with_capacity(10);
    msg.extend_from_slice(leaf_digest);
    msg.push(epoch_floor.clone());
    msg.extend_from_slice(msg_digest);
    let mut tr = Transcript::new();
    tr.absorb(b, T_SUBTREE_SIGN_MSG, &msg);
    let mut bytes = Vec::with_capacity(SHARD_MESSAGE_BYTES);
    for lane in &tr.state[..4] {
        let lane_bits = bits(b, lane, 64);
        for byte_bits in lane_bits.as_chunks::<8>().0 {
            let byte_val = byte_bits
                .iter()
                .enumerate()
                .fold(B::W::constant(Goldilocks::ZERO), |acc, (k, bit)| {
                    acc.plus(&bit.scale(f(1u64 << k)))
                });
            bytes.push(b.pin(byte_val));
        }
    }
    bytes.try_into().unwrap_or_else(|_| unreachable!())
}

/// Compute the Poseidon2 policy leaf digest of a single [`ShardHemPolicy`].
pub fn subtree_policy_leaf_digest(
    params: &FullShardParams,
    policy: &ShardHemPolicy,
) -> Option<[Goldilocks; 4]> {
    subtree_weighted_policy_leaf_digest(params, policy, 1)
}

pub fn subtree_weighted_policy_leaf_digest(
    params: &FullShardParams,
    policy: &ShardHemPolicy,
    weight_per_signer: u32,
) -> Option<[Goldilocks; 4]> {
    if weight_per_signer == 0 || policy.shard_id >= (1 << 58) {
        return None;
    }
    if policy.minimum_quorums == 0
        || policy.minimum_quorums > policy.quorum_keys.len()
        || u32::try_from(policy.minimum_quorums).is_err()
    {
        return None;
    }
    let comm = committee_digest(params, &policy.quorum_keys)?;
    let f = crate::zk_hem::recursive_whir::f;
    let id_limbs = [f(policy.shard_id & 0xFFFF_FFFF), f(policy.shard_id >> 32)];
    let cust_limbs: [Goldilocks; 8] = core::array::from_fn(|i| {
        let chunk: [u8; 4] = policy.custodian_cluster[4 * i..4 * i + 4]
            .try_into()
            .unwrap();
        f(u64::from(u32::from_le_bytes(chunk)))
    });
    let min_q = f(policy.minimum_quorums as u64);
    let mut b = crate::zk_hem::recursive_whir::Native::default();
    let out = subtree_policy_leaf_gadget(
        &mut b,
        &id_limbs,
        &cust_limbs,
        &comm,
        &min_q,
        &f(u64::from(weight_per_signer)),
    );
    (!b.failed).then_some(out)
}

/// Compute the binary Poseidon2 `subtree_registry_root` over a power-of-two slice of policies.
pub fn subtree_registry_merkle_root(
    params: &FullShardParams,
    policies: &[ShardHemPolicy],
) -> Option<[Goldilocks; 4]> {
    if !valid_policies(policies)
        || !policies.len().is_power_of_two()
        || policies.last()?.shard_id >= (1 << 58)
    {
        return None;
    }
    let leaves: Vec<[Goldilocks; 4]> = policies
        .iter()
        .map(|p| subtree_policy_leaf_digest(params, p))
        .collect::<Option<_>>()?;
    let mut b = crate::zk_hem::recursive_whir::Native::default();
    let root = subtree_fold_merkle_gadget(&mut b, 0, &leaves);
    (!b.failed).then_some(root)
}

/// Compute the exact 32-byte message signed by quorum members of `policy` in `Merge -> Merge`
/// subtree mode.
pub fn subtree_signing_message(
    params: &FullShardParams,
    policy: &ShardHemPolicy,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
) -> Option<[u8; 32]> {
    subtree_weighted_signing_message(params, policy, 1, epoch_floor, message)
}

/// Signing message for a policy with a registered uniform per-signer weight.
pub fn subtree_weighted_signing_message(
    params: &FullShardParams,
    policy: &ShardHemPolicy,
    weight_per_signer: u32,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
) -> Option<[u8; 32]> {
    if epoch_floor >= crate::field::GOLDILOCKS_PRIME {
        return None;
    }
    let leaf = subtree_weighted_policy_leaf_digest(params, policy, weight_per_signer)?;
    let msg_digest = subtree_message_digest(message.as_ref());
    let epoch_f = Goldilocks::from_u64_reduced(epoch_floor);
    let mut b = crate::zk_hem::recursive_whir::Native::default();
    let byte_wires = subtree_sign_msg_gadget(&mut b, &leaf, &epoch_f, &msg_digest);
    if b.failed {
        return None;
    }
    Some(byte_wires.map(|w| w.to_canonical_u64() as u8))
}

struct LeafChildWitness<'a> {
    shard_id: u64,
    custodian_cluster: [u8; 32],
    comm_digest: [Goldilocks; 4],
    min_quorums: u32,
    signer_count: u32,
    weight_per_signer: u32,
    roster_siblings: Vec<[Goldilocks; 4]>,
    shard_witness: crate::zk_hem::full_shard::ShardWitness<'a>,
}

fn subtree_leaf_child_gadget<B: crate::zk_hem::recursive_whir::Backend>(
    b: &mut B,
    params: &FullShardParams,
    epoch_floor: &B::W,
    msg_digest: &[B::W; 5],
    w: &LeafChildWitness<'_>,
    sparse_height: Option<u8>,
) -> ([B::W; 4], B::W, B::W, B::W) {
    use crate::zk_hem::recursive_whir::{Base as _, bits, f};
    let id_limbs = [
        b.alloc(f(w.shard_id & 0xFFFF_FFFF)),
        b.alloc(f(w.shard_id >> 32)),
    ];
    let cust_limbs: [B::W; 8] = core::array::from_fn(|i| {
        let chunk: [u8; 4] = w.custodian_cluster[4 * i..4 * i + 4].try_into().unwrap();
        b.alloc(f(u64::from(u32::from_le_bytes(chunk))))
    });
    let comm_w: [B::W; 4] = w.comm_digest.map(|x| b.alloc(x));
    let min_q_w = b.alloc(f(u64::from(w.min_quorums)));
    let signers_w = b.alloc(f(u64::from(w.signer_count)));
    let weight = b.alloc(f(u64::from(w.weight_per_signer)));
    bits(b, &weight.minus(&B::W::constant(Goldilocks::ONE)), 32);
    bits(b, &signers_w, 32);
    // Enforce `signers >= min_quorums` (`signers - min_quorums in [0, 2^32)`).
    bits(b, &signers_w.minus(&min_q_w), 32);

    let leaf_digest =
        subtree_policy_leaf_gadget(b, &id_limbs, &cust_limbs, &comm_w, &min_q_w, &weight);
    let msg_bytes = subtree_sign_msg_gadget(b, &leaf_digest, epoch_floor, msg_digest);

    let mut shard_pub = Vec::with_capacity(crate::zk_hem::full_shard::PUBLIC_WORDS);
    shard_pub.extend_from_slice(&comm_w);
    shard_pub.extend_from_slice(&msg_bytes);
    shard_pub.push(signers_w.clone());
    crate::zk_hem::full_shard::shard_gadget(b, params, &shard_pub, &w.shard_witness);

    // Bound the integer before packing: a 64-bit ID must not alias `id - p`.
    bits(b, &id_limbs[1], 26);
    let key_idx = id_limbs[0].plus(&id_limbs[1].scale(f(1 << 32)));
    bits(b, &key_idx, 58);
    let active_weight = b.mul(&signers_w, &weight);
    bits(b, &active_weight, 62);
    let mut root = leaf_digest;
    if let Some(height) = sparse_height {
        let index_bits = bits(b, &key_idx, usize::from(height));
        for (level, bit) in index_bits.iter().enumerate() {
            let sibling = w.roster_siblings[level].map(|v| b.alloc(v));
            let left = core::array::from_fn(|i| {
                crate::zk_hem::recursive_whir::select(b, bit, &sibling[i], &root[i])
            });
            let right = core::array::from_fn(|i| root[i].plus(&sibling[i]).minus(&left[i]));
            root = subtree_merkle_pair_gadget(b, level, &left, &right);
        }
    }
    (root, signers_w, key_idx, active_weight)
}

/// Level-1 subtree relation merging `fan_in` (`1`, `2`, `4`, `8`, or `16`) [`RecursiveShardProof`]s into
/// a constant-14-word [`SubtreePublic`].
#[derive(Clone)]
pub struct SubtreeLeafMergeRelation {
    sparse_roster_height: Option<u8>,
    params: FullShardParams,
    fan_in: usize,
    shape: crate::zk_hem::relation::Shape,
    hologram: crate::zk_hem::protocol::ShapeHologram,
    stats: FullShardRelationStats,
}

impl SubtreeLeafMergeRelation {
    pub fn new(params: FullShardParams, fan_in: usize) -> Result<Self, FullShardError> {
        Self::new_inner(params, fan_in, None)
    }
    pub fn with_sparse_roster(
        params: FullShardParams,
        fan_in: usize,
        height: u8,
    ) -> Result<Self, FullShardError> {
        if !(1..=40).contains(&height) {
            return Err(FullShardError::InvalidParameters);
        }
        Self::new_inner(params, fan_in, Some(height))
    }
    fn new_inner(
        params: FullShardParams,
        fan_in: usize,
        sparse_roster_height: Option<u8>,
    ) -> Result<Self, FullShardError> {
        if !matches!(fan_in, 1 | 2 | 4 | 8 | 16) {
            return Err(FullShardError::InvalidParameters);
        }
        let placeholder = RecursiveShardProof::placeholder(&params);
        let dummy_child = LeafChildWitness {
            shard_id: 0,
            custodian_cluster: [0u8; 32],
            comm_digest: [Goldilocks::ZERO; 4],
            min_quorums: 1,
            signer_count: 1,
            weight_per_signer: 1,
            roster_siblings: vec![
                [Goldilocks::ZERO; 4];
                usize::from(sparse_roster_height.unwrap_or(0))
            ],
            shard_witness: crate::zk_hem::full_shard::ShardWitness {
                keys: vec![[Goldilocks::ZERO; 8]; params.slots()],
                size: 0,
                active: vec![false; params.slots()],
                proof: &placeholder,
            },
        };
        let mut cs = crate::zk_hem::relation::ConstraintSystem::new_hologram_aligned();
        let pub_words = [Goldilocks::ZERO; SUBTREE_PUBLIC_WORDS];
        let pub_lc: Vec<crate::zk_hem::relation::Lc> = pub_words
            .iter()
            .map(|&x| cs.public_input(x).into())
            .collect();
        let children_refs: Vec<&LeafChildWitness<'_>> = (0..fan_in).map(|_| &dummy_child).collect();
        populate_subtree_leaf(
            &mut cs,
            &params,
            &pub_lc,
            &children_refs,
            sparse_roster_height,
        );
        let used = cs.num_rows();
        let (shape, mut z) = cs.finish();
        qsag_asm::volatile_fill(&mut z, Goldilocks::ZERO);
        drop(z);
        let hologram = crate::zk_hem::protocol::ShapeHologram::compile(&shape, params.regime())
            .map_err(|_| FullShardError::InvalidParameters)?;
        let stats = FullShardRelationStats {
            sbox_rows: shape.num_sbox,
            multiplication_rows: used - shape.num_sbox,
            padded_rows: shape.num_rows(),
            variables: shape.num_vars,
        };
        Ok(Self {
            sparse_roster_height,
            params,
            fan_in,
            shape,
            hologram,
            stats,
        })
    }

    pub fn params(&self) -> &FullShardParams {
        &self.params
    }
    pub fn fan_in(&self) -> usize {
        self.fan_in
    }
    pub fn shape(&self) -> &crate::zk_hem::relation::Shape {
        &self.shape
    }
    pub fn hologram(&self) -> &crate::zk_hem::protocol::ShapeHologram {
        &self.hologram
    }
    pub fn verifier_key(&self) -> &crate::zk_hem::protocol::ShapeVerifierKey {
        self.hologram.verifier_key()
    }
    pub fn stats(&self) -> FullShardRelationStats {
        self.stats
    }

    fn build_assignment(
        &self,
        policies: &[ShardHemPolicy],
        epoch_floor: u64,
        message: &[u8],
        witnesses: &[ShardHemWitness<'_>],
        seed: &[u8; 32],
    ) -> Result<(SubtreePublic, Vec<Goldilocks>), FullShardError> {
        self.build_roster_assignment(policies, epoch_floor, message, witnesses, seed, None)
    }
    fn build_roster_assignment(
        &self,
        policies: &[ShardHemPolicy],
        epoch_floor: u64,
        message: &[u8],
        witnesses: &[ShardHemWitness<'_>],
        seed: &[u8; 32],
        openings: Option<&[SubtreeRosterOpening]>,
    ) -> Result<(SubtreePublic, Vec<Goldilocks>), FullShardError> {
        if self.sparse_roster_height.is_some() != openings.is_some()
            || openings.is_some_and(|o| {
                o.len() != self.fan_in
                    || o.iter().any(|v| {
                        v.siblings.len() != usize::from(self.sparse_roster_height.unwrap())
                            || v.weight_per_signer == 0
                    })
            })
        {
            return Err(FullShardError::InvalidStatement);
        }
        if policies.len() != self.fan_in
            || witnesses.len() != self.fan_in
            || epoch_floor >= crate::field::GOLDILOCKS_PRIME
        {
            return Err(FullShardError::InvalidStatement);
        }
        // Check distinct shard_ids locally.
        if !valid_policies(policies) {
            return Err(FullShardError::InvalidStatement);
        }
        let mut statements = Vec::with_capacity(self.fan_in);
        let mut comm_digests = Vec::with_capacity(self.fan_in);
        let mut counts = Vec::with_capacity(self.fan_in);
        for (i, (p, w)) in policies.iter().zip(witnesses).enumerate() {
            let comm = committee_digest(&self.params, &p.quorum_keys)
                .ok_or(FullShardError::InvalidStatement)?;
            let sign_msg = subtree_weighted_signing_message(
                &self.params,
                p,
                openings.map_or(1, |o| o[i].weight_per_signer),
                epoch_floor,
                message,
            )
            .ok_or(FullShardError::InvalidStatement)?;
            let active = w.bitmap.count_ones();
            if active < p.minimum_quorums || u32::try_from(active).is_err() {
                return Err(FullShardError::InvalidStatement);
            }
            comm_digests.push(comm);
            counts.push(active as u32);
            statements.push(RecursiveShardStatement {
                keys: p.quorum_keys.clone(),
                bitmap: w.bitmap.clone(),
                message: sign_msg,
            });
        }

        let prove_one = |idx: usize| -> Result<RecursiveShardProof, FullShardError> {
            let mut blind_in = [0u8; 40];
            blind_in[..32].copy_from_slice(seed);
            blind_in[32..].copy_from_slice(&(idx as u64).to_le_bytes());
            let blind = crate::sponge::cshake256_32(b"QSAG.SUBTREE.SHARD.BLIND/v1", &blind_in);
            prove_recursive_shard(
                &self.params,
                &statements[idx],
                witnesses[idx].signatures,
                &blind,
            )
        };
        #[cfg(feature = "std")]
        let child_proofs: Vec<RecursiveShardProof> =
            if self.fan_in > 1 && crate::parallel_workers() > 1 {
                let res: Vec<Result<RecursiveShardProof, FullShardError>> =
                    std::thread::scope(|scope| {
                        let pr = &prove_one;
                        let tails: Vec<_> = (1..self.fan_in)
                            .map(|i| crate::spawn_bounded(scope, move || pr(i)))
                            .collect();
                        let mut out = Vec::with_capacity(self.fan_in);
                        out.push(pr(0));
                        out.extend(tails.into_iter().map(crate::join_worker));
                        out
                    });
                res.into_iter().collect::<Result<Vec<_>, _>>()?
            } else {
                (0..self.fan_in)
                    .map(prove_one)
                    .collect::<Result<Vec<_>, _>>()?
            };
        #[cfg(not(feature = "std"))]
        let child_proofs: Vec<RecursiveShardProof> = (0..self.fan_in)
            .map(prove_one)
            .collect::<Result<Vec<_>, _>>()?;

        let subtree_root = if let Some(openings) = openings {
            if openings
                .iter()
                .any(|o| o.roster_root != openings[0].roster_root)
            {
                return Err(FullShardError::InvalidStatement);
            }
            openings[0].roster_root
        } else {
            subtree_registry_merkle_root(&self.params, policies)
                .ok_or(FullShardError::InvalidStatement)?
        };
        let epoch_f = Goldilocks::from_u64_reduced(epoch_floor);
        let msg_digest = subtree_message_digest(message);
        let total_signers_u64: u64 = counts.iter().map(|&c| u64::from(c)).sum();
        if u32::try_from(total_signers_u64).is_err() {
            return Err(FullShardError::InvalidStatement);
        }
        let total_weight = counts
            .iter()
            .enumerate()
            .try_fold(0u64, |sum, (i, c)| {
                sum.checked_add(
                    u64::from(*c) * u64::from(openings.map_or(1, |o| o[i].weight_per_signer)),
                )
            })
            .filter(|&v| v < (1 << 62))
            .ok_or(FullShardError::InvalidStatement)?;
        let subtree_pub = SubtreePublic {
            subtree_registry_root: subtree_root,
            epoch_floor: epoch_f,
            message_digest: msg_digest,
            total_active_signers: Goldilocks::from_u64_reduced(total_signers_u64),
            min_key_idx: policies[0].shard_id,
            max_key_idx: policies[self.fan_in - 1].shard_id,
            total_active_weight: total_weight,
        };

        let child_witnesses: Vec<LeafChildWitness<'_>> = (0..self.fan_in)
            .map(|i| LeafChildWitness {
                shard_id: policies[i].shard_id,
                custodian_cluster: policies[i].custodian_cluster,
                comm_digest: comm_digests[i],
                min_quorums: policies[i].minimum_quorums as u32,
                signer_count: counts[i],
                weight_per_signer: openings.map_or(1, |o| o[i].weight_per_signer),
                roster_siblings: openings.map_or_else(Vec::new, |o| o[i].siblings.clone()),
                shard_witness: statements[i].witness(&self.params, &child_proofs[i]),
            })
            .collect();

        let mut all_p2 = Vec::new();
        let mut all_misc = Vec::new();
        let mut leaf_digests = Vec::with_capacity(self.fan_in);
        for cw in &child_witnesses {
            let mut a = crate::zk_hem::recursive_whir::Assignment::hologram_aligned();
            let (ld, _, _, _) = subtree_leaf_child_gadget(
                &mut a,
                &self.params,
                &epoch_f,
                &msg_digest,
                cw,
                self.sparse_roster_height,
            );
            leaf_digests.push(ld);
            all_p2.extend_from_slice(&a.p2_values);
            all_misc.extend_from_slice(&a.values);
        }
        let mut tail_a = crate::zk_hem::recursive_whir::Assignment::hologram_aligned();
        subtree_leaf_tail_gadget(
            &mut tail_a,
            &epoch_f,
            &leaf_digests,
            &counts
                .iter()
                .map(|&c| Goldilocks::from_u64_reduced(u64::from(c)))
                .collect::<Vec<_>>(),
            &subtree_pub.words(),
            &policies
                .iter()
                .map(|p| Goldilocks::from_u64_reduced(p.shard_id))
                .collect::<Vec<_>>(),
            &counts
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    Goldilocks::from_u64_reduced(
                        u64::from(*c) * u64::from(openings.map_or(1, |o| o[i].weight_per_signer)),
                    )
                })
                .collect::<Vec<_>>(),
            self.sparse_roster_height.is_some(),
        );
        all_p2.extend_from_slice(&tail_a.p2_values);
        all_misc.extend_from_slice(&tail_a.values);

        let p2_var_base = 128 * self.shape.hologram_meta().pub_var_blocks;
        let mut z = Vec::with_capacity(self.shape.num_vars);
        z.push(Goldilocks::ONE);
        z.extend_from_slice(&subtree_pub.words());
        z.resize(p2_var_base, Goldilocks::ZERO);
        z.extend_from_slice(&all_p2);
        z.extend_from_slice(&all_misc);
        if z.len() != self.shape.mask_var_base {
            return Err(FullShardError::InvalidParameters);
        }
        z.resize(self.shape.num_vars, Goldilocks::ZERO);
        Ok((subtree_pub, z))
    }
}

#[allow(clippy::too_many_arguments)]
fn subtree_leaf_tail_gadget<B: crate::zk_hem::recursive_whir::Backend>(
    b: &mut B,
    epoch_floor: &B::W,
    leaf_digests: &[[B::W; 4]],
    signer_counts: &[B::W],
    pub_words: &[B::W],
    indices: &[B::W],
    weights: &[B::W],
    sparse: bool,
) {
    use crate::zk_hem::recursive_whir::{Base as _, bits};
    bits(b, epoch_floor, 64);
    let computed_root = if sparse {
        for root in leaf_digests {
            for i in 0..4 {
                b.equal(&root[i], &pub_words[i]);
            }
        }
        leaf_digests[0].clone()
    } else {
        subtree_fold_merkle_gadget(b, 0, leaf_digests)
    };
    for i in 0..4 {
        b.equal(&computed_root[i], &pub_words[i]);
    }
    let total = signer_counts
        .iter()
        .fold(B::W::constant(Goldilocks::ZERO), |acc, c| acc.plus(c));
    bits(b, &total, 32);
    b.equal(&total, &pub_words[10]);
    let mut weight_sum = B::W::constant(Goldilocks::ZERO);
    for weight in weights {
        weight_sum = weight_sum.plus(weight);
        bits(b, &weight_sum, 62);
    }
    b.equal(&weight_sum, &pub_words[13]);
    enforce_subtree_intervals(b, indices, indices, &pub_words[11], &pub_words[12]);
}

fn populate_subtree_leaf(
    cs: &mut crate::zk_hem::relation::ConstraintSystem,
    params: &FullShardParams,
    pub_lc: &[crate::zk_hem::relation::Lc],
    children: &[&LeafChildWitness<'_>],
    sparse_height: Option<u8>,
) {
    let epoch_lc = pub_lc[4].clone();
    let msg_lc: [crate::zk_hem::relation::Lc; 5] = core::array::from_fn(|i| pub_lc[5 + i].clone());
    let mut leaf_digests = Vec::with_capacity(children.len());
    let mut signer_counts = Vec::with_capacity(children.len());
    let mut indices = Vec::with_capacity(children.len());
    let mut weights = Vec::with_capacity(children.len());
    for cw in children {
        let (ld, sc, idx, weight) =
            subtree_leaf_child_gadget(cs, params, &epoch_lc, &msg_lc, cw, sparse_height);
        leaf_digests.push(ld);
        signer_counts.push(sc);
        indices.push(idx);
        weights.push(weight);
    }
    subtree_leaf_tail_gadget(
        cs,
        &epoch_lc,
        &leaf_digests,
        &signer_counts,
        pub_lc,
        &indices,
        &weights,
        sparse_height.is_some(),
    );
}

/// Prove a Level-1 subtree leaf merge into a [`RecursivePublicHemProof`] for Level-2+ parents.
pub fn prove_subtree_leaf_merge_for_recursion(
    relation: &SubtreeLeafMergeRelation,
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: &[u8],
    witnesses: &[ShardHemWitness<'_>],
    seed: &[u8; 32],
) -> Result<
    (
        SubtreePublic,
        crate::zk_hem::protocol::RecursivePublicHemProof,
    ),
    FullShardError,
> {
    let (subtree_pub, z) =
        relation.build_assignment(policies, epoch_floor, message, witnesses, seed)?;
    let proof = crate::zk_hem::protocol::prove_public_for_recursion(
        &relation.shape,
        &relation.hologram,
        z,
        SUBTREE_REC_TAG,
    )
    .map_err(|_| FullShardError::InvalidChild)?;
    Ok((subtree_pub, proof))
}

/// Prove a Level-1 subtree leaf merge directly into a wire-compact [`SuccinctSubtreeAggregate`].
pub fn prove_subtree_leaf_aggregate(
    relation: &SubtreeLeafMergeRelation,
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: &[u8],
    witnesses: &[ShardHemWitness<'_>],
    seed: &[u8; 32],
) -> Result<SuccinctSubtreeAggregate, FullShardError> {
    let (subtree_pub, z) =
        relation.build_assignment(policies, epoch_floor, message, witnesses, seed)?;
    let proof = crate::zk_hem::protocol::prove_public_hologram(
        &relation.shape,
        &relation.hologram,
        z,
        SUBTREE_ROOT_LABEL,
        seed,
    )
    .map_err(|_| FullShardError::InvalidChild)?;
    Ok(SuccinctSubtreeAggregate {
        total_active_signers: subtree_pub.total_active_signers.to_canonical_u64(),
        min_key_idx: subtree_pub.min_key_idx,
        max_key_idx: subtree_pub.max_key_idx,
        total_active_weight: subtree_pub.total_active_weight,
        proof,
    })
}

// ----------------------------------------------------------------------------
// Level-2+ internal subtree merge
// ----------------------------------------------------------------------------

/// Level-2+ internal subtree relation merging `fan_in` (`2`, `4`, `8`, or `16`) child
/// [`crate::zk_hem::protocol::RecursivePublicHemProof`]s into one 14-word [`SubtreePublic`].
///
/// Size: verifying one child in-circuit costs about 5.0 million rows when the child's
/// hologram has `2^23` slots (`recursive_verifier_row_census`), almost all of it the
/// correlated WHIR opening, and never less than 1.7 million. A fan-in-two parent of the
/// two-shard leaf relation therefore has `2^24` rows, larger than its `2^21`-row children,
/// and its own hologram exceeds the recursion format's 28-variable limit: the relation
/// compiles and proves natively as a root, but cannot itself be a child.
#[derive(Clone)]
pub struct SubtreeInternalMergeRelation {
    shared_roster_root: bool,
    child_vk: crate::zk_hem::protocol::ShapeVerifierKey,
    fan_in: usize,
    base_merkle_level: usize,
    shape: crate::zk_hem::relation::Shape,
    hologram: crate::zk_hem::protocol::ShapeHologram,
    stats: FullShardRelationStats,
}

impl SubtreeInternalMergeRelation {
    /// Build an internal tree-merge relation for `fan_in` (`2`, `4`, `8`, or `16`) children at
    /// `base_merkle_level` (the binary Merkle height of each child's subtree,
    /// e.g. `1` when Level-1 merged pairs of shards, `2` when Level-1 merged quads of shards).
    pub fn new(
        child_vk: crate::zk_hem::protocol::ShapeVerifierKey,
        fan_in: usize,
        base_merkle_level: usize,
        parent_regime: WhirSecurityRegime,
    ) -> Result<Self, FullShardError> {
        Self::new_inner(child_vk, fan_in, base_merkle_level, parent_regime, false)
    }
    /// Merge proofs of disjoint subsets authenticated under the same sparse directory root.
    pub fn with_roster_root(
        child_vk: crate::zk_hem::protocol::ShapeVerifierKey,
        fan_in: usize,
        parent_regime: WhirSecurityRegime,
    ) -> Result<Self, FullShardError> {
        Self::new_inner(child_vk, fan_in, 0, parent_regime, true)
    }
    fn new_inner(
        child_vk: crate::zk_hem::protocol::ShapeVerifierKey,
        fan_in: usize,
        base_merkle_level: usize,
        parent_regime: WhirSecurityRegime,
        shared_roster_root: bool,
    ) -> Result<Self, FullShardError> {
        if !matches!(fan_in, 2 | 4 | 8 | 16)
            || base_merkle_level > 58usize.saturating_sub(fan_in.trailing_zeros() as usize)
            || child_vk.num_public != SUBTREE_PUBLIC_WORDS
            || !child_vk.regime.uses_poseidon2_canopy()
            || !parent_regime.is_accepted_aggregate_profile()
        {
            return Err(FullShardError::InvalidParameters);
        }
        let placeholder = crate::zk_hem::protocol::RecursivePublicHemProof::placeholder(&child_vk)
            .ok_or(FullShardError::InvalidParameters)?;
        let dummy_pub = SubtreePublic {
            subtree_registry_root: [Goldilocks::ZERO; 4],
            epoch_floor: Goldilocks::ZERO,
            message_digest: [Goldilocks::ZERO; 5],
            total_active_signers: Goldilocks::ONE,
            min_key_idx: 0,
            max_key_idx: 0,
            total_active_weight: 1,
        };
        let dummy_children: Vec<(
            SubtreePublic,
            &crate::zk_hem::protocol::RecursivePublicHemProof,
        )> = (0..fan_in).map(|_| (dummy_pub, &placeholder)).collect();

        let mut cs = crate::zk_hem::relation::ConstraintSystem::new_hologram_aligned();
        let pub_words = [Goldilocks::ZERO; SUBTREE_PUBLIC_WORDS];
        let pub_lc: Vec<crate::zk_hem::relation::Lc> = pub_words
            .iter()
            .map(|&x| cs.public_input(x).into())
            .collect();
        internal_merge_gadget(
            &mut cs,
            &child_vk,
            base_merkle_level,
            &pub_lc,
            &dummy_children,
            shared_roster_root,
        );
        let used = cs.num_rows();
        let (shape, mut z) = cs.finish();
        qsag_asm::volatile_fill(&mut z, Goldilocks::ZERO);
        drop(z);
        let hologram = crate::zk_hem::protocol::ShapeHologram::compile(&shape, parent_regime)
            .map_err(|_| FullShardError::InvalidParameters)?;
        let stats = FullShardRelationStats {
            sbox_rows: shape.num_sbox,
            multiplication_rows: used - shape.num_sbox,
            padded_rows: shape.num_rows(),
            variables: shape.num_vars,
        };
        Ok(Self {
            shared_roster_root,
            child_vk,
            fan_in,
            base_merkle_level,
            shape,
            hologram,
            stats,
        })
    }

    pub fn child_verifier_key(&self) -> &crate::zk_hem::protocol::ShapeVerifierKey {
        &self.child_vk
    }
    pub fn fan_in(&self) -> usize {
        self.fan_in
    }
    pub fn base_merkle_level(&self) -> usize {
        self.base_merkle_level
    }
    pub fn shape(&self) -> &crate::zk_hem::relation::Shape {
        &self.shape
    }
    pub fn hologram(&self) -> &crate::zk_hem::protocol::ShapeHologram {
        &self.hologram
    }
    pub fn verifier_key(&self) -> &crate::zk_hem::protocol::ShapeVerifierKey {
        self.hologram.verifier_key()
    }
    pub fn stats(&self) -> FullShardRelationStats {
        self.stats
    }

    fn build_assignment(
        &self,
        children: &[(
            SubtreePublic,
            crate::zk_hem::protocol::RecursivePublicHemProof,
        )],
    ) -> Result<(SubtreePublic, Vec<Goldilocks>), FullShardError> {
        if children.len() != self.fan_in {
            return Err(FullShardError::InvalidStatement);
        }
        let epoch_floor = children[0].0.epoch_floor;
        let message_digest = children[0].0.message_digest;
        let mut child_roots = Vec::with_capacity(self.fan_in);
        let mut total_u64 = 0u64;
        let mut total_weight = 0u64;
        if children
            .windows(2)
            .any(|c| c[0].0.max_key_idx >= c[1].0.min_key_idx)
        {
            return Err(FullShardError::InvalidStatement);
        }
        for (cpub, cproof) in children {
            if cpub.epoch_floor != epoch_floor
                || cpub.message_digest != message_digest
                || !cproof.well_formed(&self.child_vk)
            {
                return Err(FullShardError::InvalidChild);
            }
            if cpub.min_key_idx > cpub.max_key_idx
                || cpub.max_key_idx >= (1 << 58)
                || cpub.total_active_weight >= (1 << 62)
            {
                return Err(FullShardError::InvalidStatement);
            }
            total_weight = total_weight
                .checked_add(cpub.total_active_weight)
                .filter(|&w| w < (1 << 62))
                .ok_or(FullShardError::InvalidStatement)?;
            let c_signers = cpub.total_active_signers.to_canonical_u64();
            if c_signers == 0 || c_signers >= (1 << 62) {
                return Err(FullShardError::InvalidStatement);
            }
            total_u64 = total_u64
                .checked_add(c_signers)
                .ok_or(FullShardError::InvalidStatement)?;
            child_roots.push(cpub.subtree_registry_root);
        }
        if total_u64 >= (1 << 62) {
            return Err(FullShardError::InvalidStatement);
        }
        let mut nb = crate::zk_hem::recursive_whir::Native::default();
        let merged_root = if self.shared_roster_root {
            if child_roots.iter().any(|r| *r != child_roots[0]) {
                return Err(FullShardError::InvalidStatement);
            }
            child_roots[0]
        } else {
            subtree_fold_merkle_gadget(&mut nb, self.base_merkle_level, &child_roots)
        };
        let parent_pub = SubtreePublic {
            subtree_registry_root: merged_root,
            epoch_floor,
            message_digest,
            total_active_signers: Goldilocks::from_u64_reduced(total_u64),
            min_key_idx: children[0].0.min_key_idx,
            max_key_idx: children[self.fan_in - 1].0.max_key_idx,
            total_active_weight: total_weight,
        };

        let child_refs: Vec<(
            SubtreePublic,
            &crate::zk_hem::protocol::RecursivePublicHemProof,
        )> = children.iter().map(|(p, pr)| (*p, pr)).collect();
        let mut a = crate::zk_hem::recursive_whir::Assignment::hologram_aligned();
        internal_merge_gadget(
            &mut a,
            &self.child_vk,
            self.base_merkle_level,
            &parent_pub.words(),
            &child_refs,
            self.shared_roster_root,
        );

        let p2_var_base = 128 * self.shape.hologram_meta().pub_var_blocks;
        let mut z = Vec::with_capacity(self.shape.num_vars);
        z.push(Goldilocks::ONE);
        z.extend_from_slice(&parent_pub.words());
        z.resize(p2_var_base, Goldilocks::ZERO);
        z.extend_from_slice(&a.p2_values);
        z.extend_from_slice(&a.values);
        if z.len() != self.shape.mask_var_base {
            return Err(FullShardError::InvalidParameters);
        }
        z.resize(self.shape.num_vars, Goldilocks::ZERO);
        Ok((parent_pub, z))
    }
}

fn internal_merge_gadget<B: crate::zk_hem::recursive_whir::Backend>(
    b: &mut B,
    child_vk: &crate::zk_hem::protocol::ShapeVerifierKey,
    base_merkle_level: usize,
    parent_pub: &[B::W],
    children: &[(
        SubtreePublic,
        &crate::zk_hem::protocol::RecursivePublicHemProof,
    )],
    shared_roster_root: bool,
) {
    use crate::zk_hem::recursive_whir::{Base as _, bits};
    assert_eq!(parent_pub.len(), SUBTREE_PUBLIC_WORDS);
    let epoch_w = &parent_pub[4];
    bits(b, epoch_w, 64);
    let msg_w = &parent_pub[5..10];

    let mut child_roots = Vec::with_capacity(children.len());
    let mut child_signers = Vec::with_capacity(children.len());
    let mut child_weights = Vec::with_capacity(children.len());
    let mut mins = Vec::with_capacity(children.len());
    let mut maxs = Vec::with_capacity(children.len());
    for (cpub, cproof) in children {
        let c_root: [B::W; 4] = cpub.subtree_registry_root.map(|x| b.alloc(x));
        let c_sig = b.alloc(cpub.total_active_signers);
        bits(b, &c_sig, 62);
        let min = b.alloc(Goldilocks::from_u64_reduced(cpub.min_key_idx));
        let max = b.alloc(Goldilocks::from_u64_reduced(cpub.max_key_idx));
        let weight = b.alloc(Goldilocks::from_u64_reduced(cpub.total_active_weight));
        bits(b, &weight, 62);

        let mut c_pub_wires = Vec::with_capacity(SUBTREE_PUBLIC_WORDS);
        c_pub_wires.extend_from_slice(&c_root);
        c_pub_wires.push(epoch_w.clone());
        c_pub_wires.extend_from_slice(msg_w);
        c_pub_wires.push(c_sig.clone());
        c_pub_wires.extend([min.clone(), max.clone(), weight.clone()]);
        mins.push(min);
        maxs.push(max);
        child_weights.push(weight);

        crate::zk_hem::protocol::verify_public_gadget(
            b,
            child_vk,
            SUBTREE_REC_TAG,
            &c_pub_wires,
            cproof,
        );
        child_roots.push(c_root);
        child_signers.push(c_sig);
    }

    let computed_root = if shared_roster_root {
        for root in &child_roots {
            for i in 0..4 {
                b.equal(&root[i], &parent_pub[i]);
            }
        }
        child_roots[0].clone()
    } else {
        subtree_fold_merkle_gadget(b, base_merkle_level, &child_roots)
    };
    for i in 0..4 {
        b.equal(&computed_root[i], &parent_pub[i]);
    }
    for (values, want) in [
        (&child_signers, &parent_pub[10]),
        (&child_weights, &parent_pub[13]),
    ] {
        let mut sum = B::W::constant(Goldilocks::ZERO);
        for value in values {
            sum = sum.plus(value);
            // Each addend and previous sum is < 2^62, so this addition cannot wrap in F.
            bits(b, &sum, 62);
        }
        b.equal(&sum, want);
    }
    enforce_subtree_intervals(b, &mins, &maxs, &parent_pub[11], &parent_pub[12]);
}

/// Prove a Level-2+ internal subtree merge in the recursion format, for a further parent.
/// Fails with [`FullShardError::InvalidChild`] when the relation's hologram has no recursive
/// commitment (see [`SubtreeInternalMergeRelation`] on which geometries have one).
pub fn prove_subtree_internal_merge_for_recursion(
    relation: &SubtreeInternalMergeRelation,
    children: &[(
        SubtreePublic,
        crate::zk_hem::protocol::RecursivePublicHemProof,
    )],
) -> Result<
    (
        SubtreePublic,
        crate::zk_hem::protocol::RecursivePublicHemProof,
    ),
    FullShardError,
> {
    let (parent_pub, z) = relation.build_assignment(children)?;
    let proof = crate::zk_hem::protocol::prove_public_for_recursion(
        &relation.shape,
        &relation.hologram,
        z,
        SUBTREE_REC_TAG,
    )
    .map_err(|_| FullShardError::InvalidChild)?;
    Ok((parent_pub, proof))
}

/// Prove an internal subtree merge into one root proof without carrying child proofs.
/// Proof size and runtime depend on the compiled relation and security regime.
pub fn prove_subtree_internal_aggregate(
    relation: &SubtreeInternalMergeRelation,
    children: &[(
        SubtreePublic,
        crate::zk_hem::protocol::RecursivePublicHemProof,
    )],
    seed: &[u8; 32],
) -> Result<SuccinctSubtreeAggregate, FullShardError> {
    let (parent_pub, z) = relation.build_assignment(children)?;
    let proof = crate::zk_hem::protocol::prove_public_hologram(
        &relation.shape,
        &relation.hologram,
        z,
        SUBTREE_ROOT_LABEL,
        seed,
    )
    .map_err(|_| FullShardError::InvalidChild)?;
    Ok(SuccinctSubtreeAggregate {
        total_active_signers: parent_pub.total_active_signers.to_canonical_u64(),
        min_key_idx: parent_pub.min_key_idx,
        max_key_idx: parent_pub.max_key_idx,
        total_active_weight: parent_pub.total_active_weight,
        proof,
    })
}

/// Public statement against which a root [`SuccinctSubtreeAggregate`] is verified.
#[derive(Clone, Copy, Debug)]
pub struct SubtreeAggregateStatement<'a> {
    pub policies: &'a [ShardHemPolicy],
    pub epoch_floor: u64,
    pub message: &'a [u8],
    pub minimum_global_quorums: usize,
}

/// Root proof carrying one hologram proof, signer/weight totals and a directory interval.
/// No child proofs or per-shard counts are carried. A two-level tree over real signature
/// shards has a `2^24`-row root relation whose native hologram commitment alone is 16 GiB of
/// codewords, so that root has not been proved; see [`SubtreeInternalMergeRelation`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctSubtreeAggregate {
    pub total_active_signers: u64,
    pub min_key_idx: u64,
    pub max_key_idx: u64,
    pub total_active_weight: u64,
    pub proof: crate::zk_hem::protocol::HologramPublicProof,
}

impl SuccinctSubtreeAggregate {
    pub fn to_bytes(&self) -> Vec<u8> {
        let proof_bytes = self.proof.to_bytes();
        let mut out = Vec::with_capacity(40 + proof_bytes.len());
        out.extend_from_slice(SUCCINCT_SUBTREE_WIRE_MAGIC);
        out.extend_from_slice(&self.total_active_signers.to_le_bytes());
        for v in [self.min_key_idx, self.max_key_idx, self.total_active_weight] {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&proof_bytes);
        out
    }

    pub fn from_bytes_canonical(
        root_vk: &crate::zk_hem::protocol::ShapeVerifierKey,
        bytes: &[u8],
    ) -> Option<Self> {
        if bytes.get(..8)? != SUCCINCT_SUBTREE_WIRE_MAGIC
            || root_vk.num_public != SUBTREE_PUBLIC_WORDS
        {
            return None;
        }
        let total_active_signers = u64::from_le_bytes(bytes.get(8..16)?.try_into().ok()?);
        if total_active_signers == 0 || total_active_signers >= (1 << 62) {
            return None;
        }
        let min_key_idx = u64::from_le_bytes(bytes.get(16..24)?.try_into().ok()?);
        let max_key_idx = u64::from_le_bytes(bytes.get(24..32)?.try_into().ok()?);
        let total_active_weight = u64::from_le_bytes(bytes.get(32..40)?.try_into().ok()?);
        if min_key_idx > max_key_idx
            || max_key_idx >= (1 << 58)
            || total_active_weight == 0
            || total_active_weight >= (1 << 62)
        {
            return None;
        }
        let proof =
            crate::zk_hem::protocol::HologramPublicProof::from_bytes(bytes.get(40..)?, root_vk)?;
        Some(Self {
            total_active_signers,
            min_key_idx,
            max_key_idx,
            total_active_weight,
            proof,
        })
    }
}

/// A private sparse-directory membership opening for one registered shard.
#[derive(Clone, Debug)]
pub struct SubtreeRosterOpening {
    pub roster_root: [Goldilocks; 4],
    pub weight_per_signer: u32,
    pub siblings: Vec<[Goldilocks; 4]>,
}

/// Sparse roster with up to 2^40 directory slots, stored in O(registered shards * height).
/// Each shard ID is its directory index. Distinct keys and positive uniform per-shard
/// signer weights are validated at enrollment. Unoccupied slots carry the zero digest.
pub struct SparseSubtreeRegistry {
    height: u8,
    levels: Vec<alloc::collections::BTreeMap<u64, [Goldilocks; 4]>>,
    defaults: Vec<[Goldilocks; 4]>,
    weights: alloc::collections::BTreeMap<u64, u32>,
}
impl SparseSubtreeRegistry {
    pub fn new(
        params: &FullShardParams,
        policies: &[ShardHemPolicy],
        weights: &[u32],
        height: u8,
    ) -> Option<Self> {
        if !(1..=40).contains(&height)
            || !valid_policies(policies)
            || weights.len() != policies.len()
            || weights.contains(&0)
            || policies.last()?.shard_id >= (1u64 << height)
        {
            return None;
        }
        let mut leaves = alloc::collections::BTreeMap::new();
        for (p, &weight) in policies.iter().zip(weights) {
            leaves.insert(
                p.shard_id,
                subtree_weighted_policy_leaf_digest(params, p, weight)?,
            );
        }
        let mut levels = vec![leaves];
        let mut defaults = vec![[Goldilocks::ZERO; 4]];
        let mut b = crate::zk_hem::recursive_whir::Native::default();
        for level in 0..usize::from(height) {
            let previous = &levels[level];
            let parents: BTreeSet<u64> = previous.keys().map(|i| i >> 1).collect();
            let mut next = alloc::collections::BTreeMap::new();
            for index in parents {
                let left = previous.get(&(2 * index)).unwrap_or(&defaults[level]);
                let right = previous.get(&(2 * index + 1)).unwrap_or(&defaults[level]);
                next.insert(
                    index,
                    subtree_merkle_pair_gadget(&mut b, level, left, right),
                );
            }
            defaults.push(subtree_merkle_pair_gadget(
                &mut b,
                level,
                &defaults[level],
                &defaults[level],
            ));
            levels.push(next);
        }
        Some(Self {
            height,
            levels,
            defaults,
            weights: policies
                .iter()
                .zip(weights)
                .map(|(p, &w)| (p.shard_id, w))
                .collect(),
        })
    }
    pub fn roster_root(&self) -> [u8; 32] {
        crate::sponge::limbs4_to_le_bytes32(self.levels[usize::from(self.height)][&0])
    }
    pub fn opening(&self, key_idx: u64) -> Option<SubtreeRosterOpening> {
        Some(SubtreeRosterOpening {
            roster_root: self.levels[usize::from(self.height)][&0],
            weight_per_signer: *self.weights.get(&key_idx)?,
            siblings: (0..usize::from(self.height))
                .map(|level| {
                    *self.levels[level]
                        .get(&((key_idx >> level) ^ 1))
                        .unwrap_or(&self.defaults[level])
                })
                .collect(),
        })
    }
}

/// Prove selected ordered sparse roster shards. Higher merges use [`SubtreeInternalMergeRelation::with_roster_root`]
/// to preserve the shared directory root and enforce disjoint child intervals.
pub fn prove_subtree_roster_leaf_merge_for_recursion(
    relation: &SubtreeLeafMergeRelation,
    policies: &[ShardHemPolicy],
    openings: &[SubtreeRosterOpening],
    epoch_floor: u64,
    message: &[u8],
    witnesses: &[ShardHemWitness<'_>],
    seed: &[u8; 32],
) -> Result<
    (
        SubtreePublic,
        crate::zk_hem::protocol::RecursivePublicHemProof,
    ),
    FullShardError,
> {
    let (public, z) = relation.build_roster_assignment(
        policies,
        epoch_floor,
        message,
        witnesses,
        seed,
        Some(openings),
    )?;
    let proof = crate::zk_hem::protocol::prove_public_for_recursion(
        &relation.shape,
        &relation.hologram,
        z,
        SUBTREE_REC_TAG,
    )
    .map_err(|_| FullShardError::InvalidChild)?;
    Ok((public, proof))
}

/// Prepared, trusted registry commitment. Preparation validates distinct keys once;
/// subsequent root verification performs no key hashing or directory scan.
#[derive(Clone, Debug)]
pub struct PreparedSubtreeRegistry {
    pub roster_root: [u8; 32],
    pub min_key_idx: u64,
    pub max_key_idx: u64,
    pub max_signers: u64,
}
impl PreparedSubtreeRegistry {
    pub fn new(params: &FullShardParams, policies: &[ShardHemPolicy]) -> Option<Self> {
        let root = subtree_registry_merkle_root(params, policies)?;
        Some(Self {
            roster_root: crate::sponge::limbs4_to_le_bytes32(root),
            min_key_idx: policies.first()?.shard_id,
            max_key_idx: policies.last()?.shard_id,
            max_signers: policies
                .iter()
                .try_fold(0u64, |n, p| n.checked_add(p.quorum_keys.len() as u64))?,
        })
    }
}

/// Trusted roster commitment and expected scope. The root must come from the verifier's
/// registry configuration, never from the untrusted aggregate. Indices name registered
/// shards; registry enrollment must ensure keys are distinct across those shards.
#[derive(Clone, Copy, Debug)]
pub struct RosterRootStatement<'a> {
    pub roster_root: [u8; 32],
    pub epoch_floor: u64,
    pub message: &'a [u8],
    pub minimum_global_quorums: u64,
    pub minimum_active_weight: u64,
    pub min_key_idx: u64,
    pub max_key_idx: u64,
}

/// Verify against a 32-byte roster commitment without scanning directory keys.
/// The split carrier additionally verifies every edge in its deferred PCS ledger;
/// its verification work grows with the number of accumulated edges.
pub fn verify_succinct_subtree_aggregate_against_roster_root<A: SubtreeRootProof>(
    root_vk: &crate::zk_hem::protocol::ShapeVerifierKey,
    statement: &RosterRootStatement<'_>,
    aggregate: &A,
) -> bool {
    aggregate.verify_root(root_vk, statement)
}

mod subtree_root_sealed {
    pub trait Sealed {}
}

/// Accepted root carriers. The original carrier has no deferred work; the split
/// carrier additionally checks its entire ledger. Sealed to these two formats.
pub trait SubtreeRootProof: subtree_root_sealed::Sealed {
    fn active_signers(&self) -> u64;
    fn verify_root(
        &self,
        root_vk: &crate::zk_hem::protocol::ShapeVerifierKey,
        statement: &RosterRootStatement<'_>,
    ) -> bool;
}
impl subtree_root_sealed::Sealed for SuccinctSubtreeAggregate {}
impl SubtreeRootProof for SuccinctSubtreeAggregate {
    fn active_signers(&self) -> u64 {
        self.total_active_signers
    }
    fn verify_root(
        &self,
        vk: &crate::zk_hem::protocol::ShapeVerifierKey,
        statement: &RosterRootStatement<'_>,
    ) -> bool {
        verify_legacy_subtree_aggregate_against_roster_root(vk, statement, self)
    }
}
impl subtree_root_sealed::Sealed for split::SplitSubtreeAggregate {}
impl SubtreeRootProof for split::SplitSubtreeAggregate {
    fn active_signers(&self) -> u64 {
        self.public().total_active_signers.to_canonical_u64()
    }
    fn verify_root(
        &self,
        vk: &crate::zk_hem::protocol::ShapeVerifierKey,
        statement: &RosterRootStatement<'_>,
    ) -> bool {
        self.verify_against_roster_root(vk, statement)
    }
}

fn verify_legacy_subtree_aggregate_against_roster_root(
    root_vk: &crate::zk_hem::protocol::ShapeVerifierKey,
    statement: &RosterRootStatement<'_>,
    aggregate: &SuccinctSubtreeAggregate,
) -> bool {
    if root_vk.num_public != SUBTREE_PUBLIC_WORDS
        || statement.minimum_global_quorums == 0
        || statement.epoch_floor >= crate::field::GOLDILOCKS_PRIME
        || aggregate.total_active_signers < statement.minimum_global_quorums
        || aggregate.total_active_signers >= (1 << 62)
        || aggregate.total_active_weight < statement.minimum_active_weight
        || aggregate.total_active_weight == 0
        || aggregate.total_active_weight >= (1 << 62)
        || aggregate.min_key_idx != statement.min_key_idx
        || aggregate.max_key_idx != statement.max_key_idx
        || aggregate.min_key_idx > aggregate.max_key_idx
        || aggregate.max_key_idx >= (1 << 58)
    {
        return false;
    }
    let mut root = [Goldilocks::ZERO; 4];
    for (i, limb) in root.iter_mut().enumerate() {
        let raw = u64::from_le_bytes(statement.roster_root[i * 8..i * 8 + 8].try_into().unwrap());
        let Ok(value) = Goldilocks::from_canonical(raw) else {
            return false;
        };
        *limb = value;
    }
    let public = SubtreePublic {
        subtree_registry_root: root,
        epoch_floor: Goldilocks::from_u64_reduced(statement.epoch_floor),
        message_digest: subtree_message_digest(statement.message),
        total_active_signers: Goldilocks::from_u64_reduced(aggregate.total_active_signers),
        min_key_idx: aggregate.min_key_idx,
        max_key_idx: aggregate.max_key_idx,
        total_active_weight: aggregate.total_active_weight,
    };
    crate::zk_hem::protocol::verify_public_hologram(
        root_vk,
        &public.words(),
        SUBTREE_ROOT_LABEL,
        &aggregate.proof,
    )
}

fn enforce_subtree_intervals<B: crate::zk_hem::recursive_whir::Backend>(
    b: &mut B,
    mins: &[B::W],
    maxs: &[B::W],
    parent_min: &B::W,
    parent_max: &B::W,
) {
    use crate::zk_hem::recursive_whir::{Base as _, bits};
    for i in 0..mins.len() {
        bits(b, &mins[i], 58);
        bits(b, &maxs[i], 58);
        bits(b, &maxs[i].minus(&mins[i]), 58);
        if i > 0 {
            bits(
                b,
                &mins[i]
                    .minus(&maxs[i - 1])
                    .minus(&B::W::constant(Goldilocks::ONE)),
                58,
            );
        }
    }
    b.equal(parent_min, &mins[0]);
    b.equal(parent_max, &maxs[maxs.len() - 1]);
}

/// Convenience verifier that prepares a roster root by scanning the supplied policies.
/// Cache a [`PreparedSubtreeRegistry`] and use the root verifier to avoid that scan.
pub fn verify_succinct_subtree_aggregate<A: SubtreeRootProof>(
    root_vk: &crate::zk_hem::protocol::ShapeVerifierKey,
    params: &FullShardParams,
    statement: &SubtreeAggregateStatement<'_>,
    aggregate: &A,
) -> bool {
    let Some(registry) = PreparedSubtreeRegistry::new(params, statement.policies) else {
        return false;
    };
    if aggregate.active_signers() > registry.max_signers {
        return false;
    }
    verify_succinct_subtree_aggregate_against_roster_root(
        root_vk,
        &RosterRootStatement {
            roster_root: registry.roster_root,
            epoch_floor: statement.epoch_floor,
            message: statement.message,
            minimum_global_quorums: statement.minimum_global_quorums as u64,
            minimum_active_weight: statement.minimum_global_quorums as u64,
            min_key_idx: registry.min_key_idx,
            max_key_idx: registry.max_key_idx,
        },
        aggregate,
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
            assert_eq!(
                prepared.policy_registry_root(),
                evidence.policy_registry_root()
            );
            assert_eq!(prepared.message_digest(), evidence.message_digest());
            assert_eq!(
                (
                    prepared.epoch_floor(),
                    prepared.minimum_global_quorums(),
                    prepared.regime()
                ),
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
                &policies,
                other_epoch,
                other_msg,
                other_min,
                &succinct,
                &evidence,
            ));
        }
        let mut other_registry = policies.clone();
        other_registry[0].custodian_cluster[0] ^= 1;
        assert!(!verify_succinct_hierarchical_hem(
            &other_registry,
            epoch,
            msg,
            6,
            &succinct,
            &evidence,
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

    #[test]
    #[ignore = "release measurement: QSAG_MERGE_CHILDREN=2 or 4"]
    #[cfg(feature = "std")]
    fn bench_succinct_shard_whir_aggregate() {
        let arity: usize = std::env::var("QSAG_MERGE_CHILDREN")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(2);
        let nv = 12usize;
        let epoch = 77;
        let msg = b"succinct shard openings";
        let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let mut policies = Vec::new();
        for region in 0..arity as u64 {
            let keys: Vec<_> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[region as u8 + 0x31; 32],
                        i,
                    )
                })
                .collect();
            policies.push(ShardHemPolicy {
                shard_id: region,
                custodian_cluster: [region as u8 + 0x40; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 2,
            });
        }
        let committee_roots = compute_committee_roots(&policies);
        let registry_root = compute_policy_registry_root(&policies);
        let params = FixedPathWhirParams::new(regime, nv).unwrap();
        let relation = ChildWhirMergeRelation::with_children(params.clone(), arity).unwrap();
        let (claims, openings): (Vec<_>, Vec<_>) = policies
            .iter()
            .zip(&committee_roots)
            .map(|(p, root)| {
                let summary = ShardHemSummary {
                    shard_id: p.shard_id,
                    custodian_cluster: p.custodian_cluster,
                    shard_quorum_set_root: *root,
                    minimum_quorums: 2,
                    epoch_floor: epoch,
                    message_digest: compute_framed_message_digest(msg),
                    bitmap: SignerBitmap::from_active_indices(2, &[0, 1]).unwrap(),
                    child_proof_digest: [p.shard_id as u8 + 1; 32],
                };
                let table: Vec<_> = (0..1u64 << nv)
                    .map(|i| Goldilocks::from_u64_reduced(i * i + 31 * p.shard_id + 5))
                    .collect();
                let point: Vec<_> = (0..nv as u64)
                    .map(|i| GoldilocksExt4::from_u64(1000 + 17 * i + p.shard_id))
                    .collect();
                let header = shard_whir_header(&registry_root, &summary);
                let (statement, opening) =
                    prove_for_recursion(&params, header, &table, &point).unwrap();
                let claim = ShardWhirClaim {
                    summary,
                    commitment: statement.commitment,
                    point,
                    value: statement.value,
                };
                assert_eq!(claim.statement(&registry_root), statement);
                (claim, opening)
            })
            .unzip();
        let start = std::time::Instant::now();
        let aggregate = prove_succinct_shard_whir_merge(
            &relation,
            registry_root,
            claims,
            &openings,
            regime,
            &[9; 32],
        )
        .unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.;
        let start = std::time::Instant::now();
        assert!(check_succinct_shard_whir_merge(
            &relation,
            &policies,
            epoch,
            msg,
            2 * arity,
            regime,
            &aggregate
        ));
        let verify_ms = start.elapsed().as_secs_f64() * 1000.;
        let stats = relation.stats();
        std::println!(
            "SUCCINCT_SHARD_AGG arity={arity} child_nv={nv} sbox_rows={} multiplication_rows={} padded_rows={} parent_proof_bytes={} prove_ms={prove_ms:.3} verify_ms={verify_ms:.3}",
            stats.sbox_rows,
            stats.multiplication_rows,
            stats.padded_rows,
            aggregate.merge.to_bytes().len()
        );
    }

    /// The full-shard aggregate verifies from the registry, epoch, message and threshold
    /// alone, and is refused under any other registry, epoch, message, threshold or count.
    #[test]
    #[cfg(feature = "std")]
    fn succinct_full_shard_aggregate_needs_no_child_and_binds_its_statement() {
        let epoch = 41;
        let message = b"full shard aggregate";
        let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let mut policies = Vec::new();
        let mut region_keys = Vec::new();
        for region in 0..2u64 {
            let keys: Vec<_> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[region as u8 + 0x91; 32],
                        i,
                    )
                })
                .collect();
            policies.push(ShardHemPolicy {
                shard_id: region,
                custodian_cluster: [region as u8 + 0xA0; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 1,
            });
            region_keys.push(keys);
        }
        let registry_root = compute_policy_registry_root(&policies);
        // Region 0: both keys sign. Region 1: only its second key signs.
        let signers: [&[usize]; 2] = [&[0, 1], &[1]];
        let bitmaps: Vec<_> = signers
            .iter()
            .map(|s| SignerBitmap::from_active_indices(2, s).unwrap())
            .collect();
        let signatures: Vec<Vec<_>> = policies
            .iter()
            .zip(region_keys.iter_mut())
            .zip(&signers)
            .map(|((policy, keys), signing)| {
                let signed = full_shard_signing_message(&registry_root, policy, epoch, message);
                signing
                    .iter()
                    .map(|&i| keys[i].sign_stateful_for_unit_test(&signed, 0).unwrap())
                    .collect()
            })
            .collect();
        let witnesses: Vec<_> = bitmaps
            .iter()
            .zip(&signatures)
            .map(|(bitmap, signatures)| ShardHemWitness { bitmap, signatures })
            .collect();
        let relation =
            FullShardMergeRelation::new(FullShardParams::new(regime, 2).unwrap(), 2).unwrap();
        let statement = FullShardAggregateStatement {
            policies: &policies,
            epoch_floor: epoch,
            message,
            minimum_global_quorums: 3,
        };
        let aggregate =
            prove_succinct_full_shard_aggregate(&relation, &statement, &witnesses, &[3; 32])
                .unwrap();
        assert_eq!(aggregate.signer_counts, [2, 1]);
        assert!(verify_succinct_full_shard_aggregate(
            &relation, &statement, &aggregate
        ));

        // The threshold is checked against the proven counts.
        let mut higher = statement;
        higher.minimum_global_quorums = 4;
        assert!(!verify_succinct_full_shard_aggregate(
            &relation, &higher, &aggregate
        ));
        assert_eq!(
            prove_succinct_full_shard_aggregate(&relation, &higher, &witnesses, &[3; 32]),
            Err(FullShardError::InvalidStatement)
        );
        // Another epoch or message is another signed statement.
        let mut other_epoch = statement;
        other_epoch.epoch_floor += 1;
        assert!(!verify_succinct_full_shard_aggregate(
            &relation,
            &other_epoch,
            &aggregate
        ));
        let mut other_message = statement;
        other_message.message = b"full shard aggregatf";
        assert!(!verify_succinct_full_shard_aggregate(
            &relation,
            &other_message,
            &aggregate
        ));
        // Another registry: a changed key, cluster, shard id or per-shard minimum.
        let mut edits: Vec<Vec<ShardHemPolicy>> = Vec::new();
        let mut p = policies.clone();
        p[1].quorum_keys[0].pk_root[1] += Goldilocks::ONE;
        edits.push(p);
        let mut p = policies.clone();
        p[0].custodian_cluster[5] ^= 1;
        edits.push(p);
        let mut p = policies.clone();
        p[1].shard_id = 9;
        edits.push(p);
        let mut p = policies.clone();
        p[1].minimum_quorums = 2;
        edits.push(p);
        let mut p = policies.clone();
        p[0].quorum_keys.swap(0, 1);
        edits.push(p);
        for edited in &edits {
            let mut bad = statement;
            bad.policies = edited;
            assert!(!verify_succinct_full_shard_aggregate(
                &relation, &bad, &aggregate
            ));
        }
        // Claimed counts are public inputs of the parent proof.
        for counts in [[2u32, 2], [1, 2], [1, 1], [2, 0]] {
            let mut bad = aggregate.clone();
            bad.signer_counts = counts.to_vec();
            assert!(!verify_succinct_full_shard_aggregate(
                &relation, &statement, &bad
            ));
        }
        // A signature over the legacy hierarchy statement is not a full-shard signature.
        let legacy = hierarchical_hem_message(&registry_root, &policies[1], epoch, message);
        let wrong = [region_keys[1][1]
            .sign_stateful_for_unit_test(&legacy, 1)
            .unwrap()];
        let wrong_witnesses = [
            ShardHemWitness {
                bitmap: &bitmaps[0],
                signatures: &signatures[0],
            },
            ShardHemWitness {
                bitmap: &bitmaps[1],
                signatures: &wrong,
            },
        ];
        assert_eq!(
            prove_succinct_full_shard_aggregate(&relation, &statement, &wrong_witnesses, &[3; 32]),
            Err(FullShardError::InvalidSignature)
        );
    }

    /// BACKLOG-09: an honestly proved opening merge over summaries nobody verified passes the
    /// opening check and is refused authorization; only evidence from verifying the real
    /// child proofs, for exactly these summaries and this context, is accepted.
    #[test]
    fn succinct_shard_whir_merge_authorizes_only_with_matching_child_evidence() {
        let epoch = 23;
        let digest = [9u8; 32];
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
                custodian_cluster: [region as u8 + 0x70; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 2,
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
        let bitmap = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
        let witnesses: Vec<_> = signatures
            .iter()
            .map(|s| ShardHemWitness {
                bitmap: &bitmap,
                signatures: s,
            })
            .collect();
        let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let mut config = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [8; 32]);
        config.regime = regime;
        let hierarchy =
            prove_hierarchical_hem(&policies, &witnesses, epoch, digest, 4, &config).unwrap();
        let evidence = verify_hierarchical_hem_evidence(
            &policies,
            epoch,
            digest,
            4,
            config.regime,
            &hierarchy,
        )
        .unwrap();

        let params = FixedPathWhirParams::new(regime, 3).unwrap();
        let relation = ChildWhirMergeRelation::with_children(params.clone(), 2).unwrap();
        let merge = |summaries: &[ShardHemSummary]| {
            let (claims, openings): (Vec<_>, Vec<_>) = summaries
                .iter()
                .map(|summary| {
                    let table: Vec<_> = (0..8u64)
                        .map(|i| Goldilocks::from_u64_reduced(i * i + summary.shard_id + 3))
                        .collect();
                    let point: Vec<_> = (0..3u64)
                        .map(|i| GoldilocksExt4::from_u64(50 + i + summary.shard_id))
                        .collect();
                    let header = shard_whir_header(&registry_root, summary);
                    let (statement, opening) =
                        prove_for_recursion(&params, header, &table, &point).unwrap();
                    let claim = ShardWhirClaim {
                        summary: summary.clone(),
                        commitment: statement.commitment,
                        point,
                        value: statement.value,
                    };
                    (claim, opening)
                })
                .unzip();
            prove_succinct_shard_whir_merge(
                &relation,
                registry_root,
                claims,
                &openings,
                regime,
                &[4; 32],
            )
            .unwrap()
        };
        let check = |aggregate: &SuccinctShardWhirAggregate| {
            check_succinct_shard_whir_merge(
                &relation, &policies, epoch, digest, 4, regime, aggregate,
            )
        };
        let verify = |epoch, min, aggregate: &SuccinctShardWhirAggregate, evidence: &_| {
            verify_succinct_shard_whir_merge(
                &relation, &policies, epoch, digest, min, regime, aggregate, evidence,
            )
        };

        let honest = merge(evidence.summaries());
        assert!(check(&honest));
        assert!(verify(epoch, 4, &honest, &evidence));
        // The evidence is for one epoch and one threshold.
        let mut wrong_regime = evidence.clone();
        wrong_regime.regime = WhirSecurityRegime::BciksJohnsonQrom128;
        assert_ne!(wrong_regime.regime(), regime);
        assert!(!verify(epoch, 4, &honest, &wrong_regime));
        assert!(!verify(epoch + 1, 4, &honest, &evidence));
        assert!(!verify(epoch, 3, &honest, &evidence));

        // Summaries that name a child proof nobody verified. The prover derives the headers
        // from them, so every opening is valid and the merge itself is honest.
        let mut unverified = evidence.summaries().to_vec();
        unverified[1].child_proof_digest = [0xEE; 32];
        let fabricated = merge(&unverified);
        assert!(check(&fabricated));
        assert!(!verify(epoch, 4, &fabricated, &evidence));

        // Evidence for a different message does not exist for these children, and evidence
        // for other children does not transfer.
        assert!(
            verify_hierarchical_hem_evidence(
                &policies,
                epoch,
                [10u8; 32],
                4,
                config.regime,
                &hierarchy
            )
            .is_none()
        );
        let mut relabelled = honest.clone();
        relabelled.claims.swap(0, 1);
        assert!(!verify(epoch, 4, &relabelled, &evidence));
    }

    /// Four shards: the parent proof stands in for the four child openings, and every part
    /// of a shard's context is bound through its header.
    #[test]
    #[cfg(feature = "std")]
    fn succinct_shard_whir_merge_binds_summaries_claims_and_context() {
        let epoch = 77;
        let msg = b"succinct shard openings";
        let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let mut policies = Vec::new();
        for region in 0..4u64 {
            let keys: Vec<_> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[region as u8 + 0x31; 32],
                        i,
                    )
                })
                .collect();
            policies.push(ShardHemPolicy {
                shard_id: region,
                custodian_cluster: [region as u8 + 0x40; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 2,
            });
        }
        let committee_roots = compute_committee_roots(&policies);
        let registry_root = compute_policy_registry_root(&policies);
        let params = FixedPathWhirParams::new(regime, 3).unwrap();
        let relation = ChildWhirMergeRelation::with_children(params.clone(), 4).unwrap();
        let (claims, openings): (Vec<_>, Vec<_>) = policies
            .iter()
            .zip(&committee_roots)
            .map(|(p, root)| {
                let summary = ShardHemSummary {
                    shard_id: p.shard_id,
                    custodian_cluster: p.custodian_cluster,
                    shard_quorum_set_root: *root,
                    minimum_quorums: 2,
                    epoch_floor: epoch,
                    message_digest: compute_framed_message_digest(msg),
                    bitmap: SignerBitmap::from_active_indices(2, &[0, 1]).unwrap(),
                    child_proof_digest: [p.shard_id as u8 + 1; 32],
                };
                let table: Vec<_> = (0..8u64)
                    .map(|i| Goldilocks::from_u64_reduced(i * i + 31 * p.shard_id + 5))
                    .collect();
                let point: Vec<_> = (0..3u64)
                    .map(|i| GoldilocksExt4::from_u64(1000 + 17 * i + p.shard_id))
                    .collect();
                let header = shard_whir_header(&registry_root, &summary);
                let (statement, opening) =
                    prove_for_recursion(&params, header, &table, &point).unwrap();
                let claim = ShardWhirClaim {
                    summary,
                    commitment: statement.commitment,
                    point,
                    value: statement.value,
                };
                assert_eq!(claim.statement(&registry_root), statement);
                (claim, opening)
            })
            .unzip();
        let aggregate = prove_succinct_shard_whir_merge(
            &relation,
            registry_root,
            claims,
            &openings,
            regime,
            &[9; 32],
        )
        .unwrap();
        let check = |policies: &[ShardHemPolicy], epoch, msg: &[u8], min, agg: &_| {
            check_succinct_shard_whir_merge(&relation, policies, epoch, msg, min, regime, agg)
        };
        assert!(check(&policies, epoch, msg, 8, &aggregate));
        assert!(!check(&policies, epoch + 1, msg, 8, &aggregate));
        assert!(!check(&policies, epoch, b"relabel", 8, &aggregate));
        assert!(!check(&policies, epoch, msg, 9, &aggregate));
        let mut other = policies.clone();
        other[0].custodian_cluster[0] ^= 1;
        assert!(!check(&other, epoch, msg, 8, &aggregate));

        // Fields the policy checks do not see are bound by the header inside the relation.
        let mut bad = aggregate.clone();
        bad.claims[2].summary.child_proof_digest[0] ^= 1;
        assert!(!check(&policies, epoch, msg, 8, &bad));
        // Recomputing the merged digest for the altered header does not help.
        bad.merge.merged_root =
            merged_child_whir_root(&shard_whir_statements(&registry_root, &bad.claims));
        assert!(!check(&policies, epoch, msg, 8, &bad));
        let mut bad = aggregate.clone();
        bad.claims[1].value += GoldilocksExt4::ONE;
        assert!(!check(&policies, epoch, msg, 8, &bad));
        let mut bad = aggregate.clone();
        bad.claims[3].point[0] += GoldilocksExt4::ONE;
        assert!(!check(&policies, epoch, msg, 8, &bad));
        let mut bad = aggregate.clone();
        bad.claims[0].commitment[0] += Goldilocks::ONE;
        assert!(!check(&policies, epoch, msg, 8, &bad));
        // A shard cannot borrow another shard's opening.
        let mut bad = aggregate.clone();
        let (a, b) = (bad.claims[0].clone(), bad.claims[1].clone());
        (
            bad.claims[0].commitment,
            bad.claims[0].point,
            bad.claims[0].value,
        ) = (b.commitment, b.point, b.value);
        (
            bad.claims[1].commitment,
            bad.claims[1].point,
            bad.claims[1].value,
        ) = (a.commitment, a.point, a.value);
        assert!(!check(&policies, epoch, msg, 8, &bad));

        // The prover refuses an opening made under another shard's header.
        let mut swapped = openings.clone();
        swapped.swap(0, 1);
        assert_eq!(
            prove_succinct_shard_whir_merge(
                &relation,
                registry_root,
                aggregate.claims.clone(),
                &swapped,
                regime,
                &[9; 32],
            ),
            Err(RecursiveWhirError::InvalidOpening)
        );
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
        assert!(check_hierarchical_hem_commitment(
            &policies, epoch, msg, 4, &forged
        ));
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
        let prepared_agg =
            prove_hierarchical_hem_prepared(&prepared, &witnesses, epoch, msg, 4, &cfg).unwrap();
        assert!(verify_hierarchical_hem_prepared(
            &prepared,
            epoch,
            msg,
            4,
            regime,
            &prepared_agg
        ));
        let evidence =
            verify_hierarchical_hem_evidence_prepared(&prepared, epoch, msg, 4, regime, &agg)
                .unwrap();
        let compact = compress_hierarchical_hem_evidence(&evidence, [97; 32]).unwrap();
        assert!(evidence.names_same_children(&compact));
        assert!(verify_succinct_hierarchical_hem_prepared(
            &prepared, epoch, msg, 4, regime, &compact, &evidence
        ));
        assert!(!verify_succinct_hierarchical_hem_prepared(
            &prepared,
            epoch + 1,
            msg,
            4,
            regime,
            &compact,
            &evidence
        ));
        assert!(!verify_succinct_hierarchical_hem_prepared(
            &prepared, epoch, b"relabel", 4, regime, &compact, &evidence
        ));
        assert!(!verify_succinct_hierarchical_hem_prepared(
            &prepared, epoch, msg, 3, regime, &compact, &evidence
        ));
        let mut changed = compact.clone();
        changed.shards[0].child_proof_digest[0] ^= 1;
        assert!(!verify_succinct_hierarchical_hem_prepared(
            &prepared, epoch, msg, 4, regime, &changed, &evidence
        ));

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
        let count = std::env::var("QSAG_PIPELINE_SIGNERS")
            .ok()
            .and_then(|x| x.parse::<usize>().ok())
            .unwrap_or(16);
        assert!((2..=128).contains(&count));
        let epoch = 101;
        let msg = b"qsag-pipeline-real-shards";
        let start = Instant::now();
        let mut keys: Vec<Vec<_>> = (0..2)
            .map(|region| {
                (0..count)
                    .map(|i| {
                        ValidatorKeypair::keygen_deterministic(
                            AggSigProfile::JortsPoseidon2,
                            &[region + 121; 32],
                            i as u32,
                        )
                    })
                    .collect()
            })
            .collect();
        let policies: Vec<_> = keys
            .iter()
            .enumerate()
            .map(|(i, keys)| ShardHemPolicy {
                shard_id: i as u64,
                custodian_cluster: [i as u8; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: count,
            })
            .collect();
        let registry = PreparedPolicyRegistry::new(policies.clone()).unwrap();
        let bm = SignerBitmap::from_active_indices(count as u32, &(0..count).collect::<Vec<_>>())
            .unwrap();
        let sigs: Vec<Vec<_>> = keys
            .iter_mut()
            .zip(&policies)
            .map(|(keys, p)| {
                let framed =
                    hierarchical_hem_message(&registry.policy_registry_root(), p, epoch, msg);
                keys.iter_mut()
                    .map(|k| k.sign_stateful_for_unit_test(&framed, 0).unwrap())
                    .collect()
            })
            .collect();
        let witnesses: Vec<_> = sigs
            .iter()
            .map(|s| ShardHemWitness {
                bitmap: &bm,
                signatures: s,
            })
            .collect();
        let setup_ms = start.elapsed().as_secs_f64() * 1000.0;
        let cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [84; 32]);
        let start = Instant::now();
        let agg =
            prove_hierarchical_hem_prepared(&registry, &witnesses, epoch, msg, 2 * count, &cfg)
                .unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.0;
        let wire = agg.to_bytes();
        let agg = HierarchicalHemAggregate::from_bytes_canonical(&wire).unwrap();
        let mut fresh = Vec::new();
        let mut reuse = Vec::new();
        let mut duplicate = Vec::new();
        let mut compact_bytes = 0;
        for sample in 0..4 {
            let start = Instant::now();
            let ev = verify_hierarchical_hem_evidence_prepared(
                &registry,
                epoch,
                msg,
                2 * count,
                cfg.regime,
                &agg,
            )
            .unwrap();
            let evidence_ms = start.elapsed().as_secs_f64() * 1000.0;
            let start = Instant::now();
            let compact = compress_hierarchical_hem_evidence(&ev, [85; 32]).unwrap();
            let reuse_ms = start.elapsed().as_secs_f64() * 1000.0;
            compact_bytes = compact.to_bytes().len();
            assert!(verify_succinct_hierarchical_hem_prepared(
                &registry,
                epoch,
                msg,
                2 * count,
                cfg.regime,
                &compact,
                &ev
            ));
            let start = Instant::now();
            let legacy = compress_verified_hierarchical_hem(
                &policies,
                epoch,
                msg,
                2 * count,
                &agg,
                [85; 32],
            )
            .unwrap();
            let duplicate_ms = evidence_ms + start.elapsed().as_secs_f64() * 1000.0;
            assert!(ev.names_same_children(&legacy));
            if sample > 0 {
                fresh.push(evidence_ms + reuse_ms);
                reuse.push(reuse_ms);
                duplicate.push(duplicate_ms);
            }
        }
        let median = |mut xs: Vec<f64>| {
            xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
            xs[xs.len() / 2]
        };
        std::println!(
            "pipeline signers={} regions=2 prover_jobs={} setup_ms={:.2} prove_ms={:.2} signers_per_s={:.2} hierarchy_bytes={} compact_bytes={} fresh_evidence_plus_build_p50_ms={:.3} reused_evidence_build_p50_ms={:.3} duplicate_verify_pipeline_p50_ms={:.3}",
            2 * count,
            crate::prover_parallel_jobs(),
            setup_ms,
            prove_ms,
            2000.0 * count as f64 / prove_ms,
            wire.len(),
            compact_bytes,
            median(fresh),
            median(reuse),
            median(duplicate)
        );
    }

    // A small fixture checks the native merge gadget and the roster-root wire API.
    // Full signature-shard recursion has separate resource-intensive tests below.
    #[test]
    fn roster_root_verifier_and_native_merge_binding() {
        use crate::zk_hem::{
            protocol,
            relation::{ConstraintSystem, Lc},
        };
        let child_public = |index, weight| SubtreePublic {
            subtree_registry_root: [Goldilocks::from_u64_reduced(index + 20); 4],
            epoch_floor: Goldilocks::from_u64_reduced(7),
            message_digest: subtree_message_digest(b"roster fixture"),
            total_active_signers: Goldilocks::ONE,
            min_key_idx: index,
            max_key_idx: index,
            total_active_weight: weight,
        };
        let publics = [child_public(1, 2), child_public(4, 3)];
        let build = |public: SubtreePublic| {
            let mut cs = ConstraintSystem::new_hologram_aligned();
            let words: Vec<Lc> = public
                .words()
                .iter()
                .map(|&v| cs.public_input(v).into())
                .collect();
            cs.enforce_equal(&words[10], &Lc::constant(Goldilocks::ONE));
            cs.enforce_equal(&words[11], &words[12]);
            cs.finish()
        };
        let (shape, left_z) = build(publics[0]);
        let (right_shape, right_z) = build(publics[1]);
        assert_eq!(shape, right_shape);
        let hologram = protocol::ShapeHologram::compile(
            &shape,
            WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
        )
        .unwrap();
        let left = protocol::prove_public_for_recursion(&shape, &hologram, left_z, SUBTREE_REC_TAG)
            .unwrap();
        let right =
            protocol::prove_public_for_recursion(&shape, &hologram, right_z, SUBTREE_REC_TAG)
                .unwrap();
        let children = [(publics[0], left), (publics[1], right)];
        let mut native = crate::zk_hem::recursive_whir::Native::default();
        let root =
            subtree_fold_merkle_gadget(&mut native, 0, &publics.map(|p| p.subtree_registry_root));
        let parent = SubtreePublic {
            subtree_registry_root: root,
            total_active_signers: Goldilocks::from_u64_reduced(2),
            min_key_idx: 1,
            max_key_idx: 4,
            total_active_weight: 5,
            ..publics[0]
        };
        let refs: Vec<_> = children.iter().map(|(p, proof)| (*p, proof)).collect();
        internal_merge_gadget(
            &mut native,
            hologram.verifier_key(),
            0,
            &parent.words(),
            &refs,
            false,
        );
        assert!(!native.failed);
        let reversed = [refs[1], refs[0]];
        let mut bad = crate::zk_hem::recursive_whir::Native::default();
        internal_merge_gadget(
            &mut bad,
            hologram.verifier_key(),
            0,
            &parent.words(),
            &reversed,
            false,
        );
        assert!(bad.failed);

        // A deliberately small pinned-statement relation isolates root-verifier and wire
        // behavior. It is not a compiled recursive merge or a signature authorization proof.
        let mut cs = ConstraintSystem::new_hologram_aligned();
        for word in parent.words() {
            let input: Lc = cs.public_input(word).into();
            cs.enforce_equal(&input, &Lc::constant(word));
        }
        let (root_shape, root_z) = cs.finish();
        let root_hologram = protocol::ShapeHologram::compile_native(
            &root_shape,
            WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128,
        )
        .unwrap();
        let root_vk = root_hologram.verifier_key();
        let start = std::time::Instant::now();
        let proof = SuccinctSubtreeAggregate {
            total_active_signers: 2,
            min_key_idx: 1,
            max_key_idx: 4,
            total_active_weight: 5,
            proof: protocol::prove_public_hologram(
                &root_shape,
                &root_hologram,
                root_z,
                SUBTREE_ROOT_LABEL,
                &[64; 32],
            )
            .unwrap(),
        };
        let prove_ms = start.elapsed().as_secs_f64() * 1000.0;
        let statement = RosterRootStatement {
            roster_root: crate::sponge::limbs4_to_le_bytes32(root),
            epoch_floor: 7,
            message: b"roster fixture",
            minimum_global_quorums: 2,
            minimum_active_weight: 5,
            min_key_idx: 1,
            max_key_idx: 4,
        };
        let start = std::time::Instant::now();
        assert!(verify_succinct_subtree_aggregate_against_roster_root(
            root_vk, &statement, &proof
        ));
        let verify_ms = start.elapsed().as_secs_f64() * 1000.0;
        let wire = proof.to_bytes();
        assert_eq!(
            SuccinctSubtreeAggregate::from_bytes_canonical(root_vk, &wire),
            Some(proof.clone())
        );
        for offset in [8, 16, 24, 32, 40] {
            let mut bad = wire.clone();
            bad[offset] ^= 1;
            if let Some(bad) = SuccinctSubtreeAggregate::from_bytes_canonical(root_vk, &bad) {
                assert!(!verify_succinct_subtree_aggregate_against_roster_root(
                    root_vk, &statement, &bad
                ));
            }
        }
        let mut wrong = statement;
        wrong.roster_root[0] ^= 1;
        assert!(!verify_succinct_subtree_aggregate_against_roster_root(
            root_vk, &wrong, &proof
        ));
        std::println!(
            "ROSTER_ROOT_WIRE_FIXTURE rows={} proof_bytes={} prove_ms={prove_ms:.2} verify_ms={verify_ms:.2}",
            root_shape.num_rows(),
            wire.len()
        );
    }

    #[test]
    fn sparse_roster_openings_at_planetary_depths() {
        let params =
            FullShardParams::new(WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128, 2).unwrap();
        let keys: Vec<_> = (0..2)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[71; 32], i)
                    .pk
            })
            .collect();
        for height in [20, 37, 40] {
            let policies: Vec<_> = keys
                .iter()
                .enumerate()
                .map(|(i, &key)| ShardHemPolicy {
                    shard_id: if i == 0 { 7 } else { (1u64 << height) - 1 },
                    custodian_cluster: [i as u8; 32],
                    quorum_keys: vec![key],
                    minimum_quorums: 1,
                })
                .collect();
            let registry = SparseSubtreeRegistry::new(&params, &policies, &[2, 9], height).unwrap();
            for policy in &policies {
                let opening = registry.opening(policy.shard_id).unwrap();
                let mut node =
                    subtree_weighted_policy_leaf_digest(&params, policy, opening.weight_per_signer)
                        .unwrap();
                let mut native = crate::zk_hem::recursive_whir::Native::default();
                for (level, sibling) in opening.siblings.iter().enumerate() {
                    node = if (policy.shard_id >> level) & 1 == 0 {
                        subtree_merkle_pair_gadget(&mut native, level, &node, sibling)
                    } else {
                        subtree_merkle_pair_gadget(&mut native, level, sibling, &node)
                    };
                }
                assert_eq!(
                    crate::sponge::limbs4_to_le_bytes32(node),
                    registry.roster_root()
                );
                assert_ne!(
                    subtree_weighted_policy_leaf_digest(
                        &params,
                        policy,
                        opening.weight_per_signer + 1
                    )
                    .unwrap(),
                    subtree_weighted_policy_leaf_digest(&params, policy, opening.weight_per_signer)
                        .unwrap()
                );
            }
        }
    }

    #[test]
    fn sparse_roster_native_signature_leaf_and_tampering() {
        use crate::zk_hem::recursive_whir::{Native, f};
        let params =
            FullShardParams::new(WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128, 2).unwrap();
        let mut key =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[72; 32], 0);
        let policy = ShardHemPolicy {
            shard_id: (1 << 36) + 9,
            custodian_cluster: [13; 32],
            quorum_keys: vec![key.pk],
            minimum_quorums: 1,
        };
        let registry =
            SparseSubtreeRegistry::new(&params, core::slice::from_ref(&policy), &[7], 37).unwrap();
        let opening = registry.opening(policy.shard_id).unwrap();
        let epoch = 3;
        let message = b"sparse signature membership";
        let signing_message =
            subtree_weighted_signing_message(&params, &policy, 7, epoch, message).unwrap();
        let signature = key
            .sign_stateful_for_unit_test(&signing_message, 3)
            .unwrap();
        let statement = RecursiveShardStatement {
            keys: policy.quorum_keys.clone(),
            bitmap: SignerBitmap::from_active_indices(1, &[0]).unwrap(),
            message: signing_message,
        };
        let proof = prove_recursive_shard(&params, &statement, &[signature], &[73; 32]).unwrap();
        let mut witness = LeafChildWitness {
            shard_id: policy.shard_id,
            custodian_cluster: policy.custodian_cluster,
            comm_digest: committee_digest(&params, &policy.quorum_keys).unwrap(),
            min_quorums: 1,
            signer_count: 1,
            weight_per_signer: 7,
            roster_siblings: opening.siblings.clone(),
            shard_witness: statement.witness(&params, &proof),
        };
        let public = SubtreePublic {
            subtree_registry_root: opening.roster_root,
            epoch_floor: f(epoch),
            message_digest: subtree_message_digest(message),
            total_active_signers: f(1),
            min_key_idx: policy.shard_id,
            max_key_idx: policy.shard_id,
            total_active_weight: 7,
        };
        let check = |w: &LeafChildWitness<'_>| {
            let mut b = Native::default();
            let (root, count, index, weight) = subtree_leaf_child_gadget(
                &mut b,
                &params,
                &public.epoch_floor,
                &public.message_digest,
                w,
                Some(37),
            );
            subtree_leaf_tail_gadget(
                &mut b,
                &public.epoch_floor,
                &[root],
                &[count],
                &public.words(),
                &[index],
                &[weight],
                true,
            );
            !b.failed
        };
        assert!(check(&witness));
        witness.roster_siblings[10][0] += Goldilocks::ONE;
        assert!(!check(&witness));
        witness.roster_siblings[10][0] -= Goldilocks::ONE;
        witness.weight_per_signer = 8;
        assert!(!check(&witness));
        witness.weight_per_signer = 7;
        witness.shard_id += 1;
        assert!(!check(&witness));
    }

    #[test]
    fn subtree_interval_constraints_reject_overlap_and_field_wrap() {
        use crate::zk_hem::recursive_whir::{Native, f};
        for (mins, maxs, expected) in [
            ([1, 9], [3, 12], true),
            ([1, 3], [3, 12], false),
            ([9, 1], [12, 3], false),
            ([1, 2], [0, 3], false),
            ([1, 1 << 58], [3, 1 << 58], false),
        ] {
            let mut b = Native::default();
            enforce_subtree_intervals(&mut b, &mins.map(f), &maxs.map(f), &f(mins[0]), &f(maxs[1]));
            assert_eq!(!b.failed, expected);
        }
    }

    #[test]
    fn three_level_four_shard_subtree_recursion_and_tamper_suite() {
        subtree_two_level(false, 2);
    }
    #[test]
    fn sparse_roster_depth37_weighted_two_level_recursion() {
        subtree_two_level(true, 1);
    }
    #[test]
    fn two_level_two_shard_roster_root_recursion() {
        subtree_two_level(false, 1);
    }
    fn subtree_two_level(sparse: bool, leaf_fan: usize) {
        use super::split::{SplitSubtreeAggregate, SplitSubtreeProof, SplitSubtreeRelation};
        use std::time::Instant;
        let _permit = crate::prover_admission::acquire();

        let child_regime = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128;
        let root_regime = WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128;
        let params = FullShardParams::new(child_regime, 2).unwrap();

        let shard_count = 2 * leaf_fan;
        let total_signers = 3 * leaf_fan as u64;
        let total_weight = if sparse {
            if leaf_fan == 1 { 7 } else { 20 }
        } else {
            total_signers
        };
        let epoch_floor = 2026_1116u64;
        let message = b"two-level arbitrary-depth merge->merge root authorization";

        let mut policies = Vec::with_capacity(shard_count);
        let mut all_keypairs = Vec::with_capacity(shard_count);
        for s in 0..shard_count {
            let kps: Vec<ValidatorKeypair> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[(40 + s) as u8; 32],
                        i,
                    )
                })
                .collect();
            policies.push(ShardHemPolicy {
                shard_id: if sparse {
                    (1u64 << 36) + (1u64 << 30) * s as u64
                } else {
                    100 + s as u64
                },
                custodian_cluster: [(0xA0 + s) as u8; 32],
                quorum_keys: kps.iter().map(|k| k.pk).collect(),
                minimum_quorums: 1,
            });
            all_keypairs.push(kps);
        }

        let weights = if sparse { [2, 3, 4, 5] } else { [1; 4] };
        let registry = sparse.then(|| {
            SparseSubtreeRegistry::new(&params, &policies, &weights[..shard_count], 37).unwrap()
        });
        // Active signers per shard: [2, 1, 2, 1] -> total = 6 >= minimum_global_quorums (5).
        let active_sets: [&[usize]; 4] = [&[0, 1], &[1], &[0, 1], &[0]];
        let mut bitmaps = Vec::with_capacity(shard_count);
        let mut sig_vecs = Vec::with_capacity(shard_count);
        for s in 0..shard_count {
            let sign_msg = subtree_weighted_signing_message(
                &params,
                &policies[s],
                weights[s],
                epoch_floor,
                message,
            )
            .unwrap();
            let sigs: Vec<ValidatorSignature> = active_sets[s]
                .iter()
                .map(|&idx| {
                    all_keypairs[s][idx]
                        .sign_stateful_for_unit_test(&sign_msg, (s * 3 + idx) as u32)
                        .unwrap()
                })
                .collect();
            bitmaps.push(SignerBitmap::from_active_indices(2, active_sets[s]).unwrap());
            sig_vecs.push(sigs);
        }
        let witnesses: Vec<ShardHemWitness<'_>> = (0..shard_count)
            .map(|s| ShardHemWitness {
                bitmap: &bitmaps[s],
                signatures: &sig_vecs[s],
            })
            .collect();

        // Prove one shard per leaf; binary split nodes keep every internal level contractive.
        let t_setup1 = Instant::now();
        let l1_rel = if sparse {
            SubtreeLeafMergeRelation::with_sparse_roster(params.clone(), 1, 37)
        } else {
            SubtreeLeafMergeRelation::new(params.clone(), 1)
        }
        .unwrap();
        let setup1_ms = t_setup1.elapsed().as_secs_f64() * 1000.0;
        std::println!("SUBTREE_SETUP1 ms={setup1_ms:.1}");
        let l1_rows = l1_rel.stats().padded_rows;
        let l1_vk = l1_rel.verifier_key().clone();

        // Leaf proofs bind each real shard and its weighted roster opening.
        let t_l1 = Instant::now();
        let prove_leaf_node = |offset: usize, seed: &[u8; 32]| {
            if let Some(registry) = &registry {
                let openings: Vec<_> = policies[offset..offset + 1]
                    .iter()
                    .map(|p| registry.opening(p.shard_id).unwrap())
                    .collect();
                SplitSubtreeProof::prove_roster_leaf(
                    &l1_rel,
                    &policies[offset..offset + 1],
                    &openings,
                    epoch_floor,
                    message,
                    &witnesses[offset..offset + 1],
                    seed,
                )
            } else {
                SplitSubtreeProof::prove_leaf(
                    &l1_rel,
                    &policies[offset..offset + 1],
                    epoch_floor,
                    message,
                    &witnesses[offset..offset + 1],
                    seed,
                )
            }
            .unwrap()
        };
        let mut children = Vec::with_capacity(shard_count);
        for s in 0..shard_count {
            children.push(prove_leaf_node(s, &[(s + 17) as u8; 32]));
            std::println!("SUBTREE_LEAF_PROVED index={s}");
        }
        let l1_ms = t_l1.elapsed().as_secs_f64() * 1000.0;
        drop(l1_rel);
        let child_vk = if leaf_fan == 2 {
            let middle = SplitSubtreeRelation::new(l1_vk, 0, sparse, child_regime).unwrap();
            let start = Instant::now();
            children = children
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| {
                    middle
                        .prove_for_recursion(&[pair[0].clone(), pair[1].clone()])
                        .unwrap()
                })
                .collect();
            std::println!(
                "SUBTREE_MIDDLE rows={} prove_ms={:.1}",
                middle.stats().padded_rows,
                start.elapsed().as_secs_f64() * 1000.0
            );
            middle.verifier_key().clone()
        } else {
            l1_vk
        };
        let children: [SplitSubtreeProof; 2] = children.try_into().ok().unwrap();
        assert_eq!(
            children[0].public().total_active_signers.to_canonical_u64(),
            if leaf_fan == 1 { 2 } else { 3 }
        );
        assert_eq!(
            children[1].public().total_active_signers.to_canonical_u64(),
            if leaf_fan == 1 { 1 } else { 3 }
        );

        let t_setup2 = Instant::now();
        let l2_rel = SplitSubtreeRelation::new(
            child_vk,
            leaf_fan.trailing_zeros() as usize,
            sparse,
            root_regime,
        )
        .unwrap();
        let setup_ms = setup1_ms + t_setup2.elapsed().as_secs_f64() * 1000.0;
        let root_vk = l2_rel.verifier_key();
        assert!(root_vk.to_bytes().len() < 256);

        // Root proof plus every bound deferred PCS opening in the tree.
        let t_l2 = Instant::now();
        let root_agg = l2_rel.prove_root(&children, &[0x33; 32]).unwrap();
        let l2_ms = t_l2.elapsed().as_secs_f64() * 1000.0;
        assert_eq!(
            root_agg.public().total_active_signers.to_canonical_u64(),
            total_signers
        );

        let root_bytes = root_agg.to_bytes();
        let decoded = SplitSubtreeAggregate::from_bytes_canonical(root_vk, &root_bytes).unwrap();
        assert_eq!(decoded.to_bytes(), root_bytes);

        let stmt = SubtreeAggregateStatement {
            policies: &policies,
            epoch_floor,
            message,
            minimum_global_quorums: total_signers as usize,
        };
        let roster_stmt = RosterRootStatement {
            roster_root: registry.as_ref().map_or_else(
                || {
                    PreparedSubtreeRegistry::new(&params, &policies)
                        .unwrap()
                        .roster_root
                },
                |r| r.roster_root(),
            ),
            epoch_floor,
            message,
            minimum_global_quorums: total_signers,
            minimum_active_weight: total_weight,
            min_key_idx: policies[0].shard_id,
            max_key_idx: policies[shard_count - 1].shard_id,
        };
        let t_ver = Instant::now();
        assert!(verify_succinct_subtree_aggregate_against_roster_root(
            root_vk,
            &roster_stmt,
            &decoded
        ));
        let ver_ms = t_ver.elapsed().as_secs_f64() * 1000.0;
        std::println!(
            "SUBTREE_ROSTER_TREE sparse={sparse} shards={shard_count} signers={total_signers} l1_rows={} l2_rows={} vk_bytes={} root_bytes={} setup_ms={setup_ms:.1} l1_prove_ms={l1_ms:.1} l2_prove_ms={l2_ms:.1} root_verify_ms={ver_ms:.2}",
            l1_rows,
            l2_rel.stats().padded_rows,
            root_vk.to_bytes().len(),
            root_bytes.len(),
        );
        assert!(l2_rel.stats().padded_rows <= 1 << 20);

        for mutate in 0..6 {
            let mut bad = roster_stmt;
            match mutate {
                0 => bad.roster_root[0] ^= 1,
                1 => bad.min_key_idx += 1,
                2 => bad.max_key_idx -= 1,
                3 => bad.minimum_active_weight += 1,
                4 => bad.epoch_floor += 1,
                _ => bad.message = b"forged",
            }
            assert!(!verify_succinct_subtree_aggregate_against_roster_root(
                root_vk, &bad, &decoded
            ));
        }
        let mut bad = decoded.clone();
        bad.public.total_active_weight += 1;
        assert!(!verify_succinct_subtree_aggregate_against_roster_root(
            root_vk,
            &roster_stmt,
            &bad
        ));
        if sparse {
            return;
        }
        assert!(verify_succinct_subtree_aggregate(
            root_vk, &params, &stmt, &decoded
        ));
        // Tamper suite: every statement & proof mutation must reject!
        assert!(!verify_succinct_subtree_aggregate(
            root_vk,
            &params,
            &SubtreeAggregateStatement {
                message: b"forged message",
                ..stmt
            },
            &root_agg
        ));
        assert!(!verify_succinct_subtree_aggregate(
            root_vk,
            &params,
            &SubtreeAggregateStatement {
                epoch_floor: epoch_floor + 1,
                ..stmt
            },
            &root_agg
        ));
        assert!(!verify_succinct_subtree_aggregate(
            root_vk,
            &params,
            &SubtreeAggregateStatement {
                minimum_global_quorums: 7,
                ..stmt
            },
            &root_agg
        ));
        let mut swapped_policies = policies.clone();
        swapped_policies.swap(0, 1);
        assert!(!verify_succinct_subtree_aggregate(
            root_vk,
            &params,
            &SubtreeAggregateStatement {
                policies: &swapped_policies,
                ..stmt
            },
            &root_agg
        ));
        let mut bad_min_policies = policies.clone();
        bad_min_policies[0].minimum_quorums = 2;
        assert!(!verify_succinct_subtree_aggregate(
            root_vk,
            &params,
            &SubtreeAggregateStatement {
                policies: &bad_min_policies,
                ..stmt
            },
            &root_agg
        ));
        let mut bad_agg = root_agg.clone();
        bad_agg.public.total_active_signers = Goldilocks::from_u64_reduced(7);
        assert!(!verify_succinct_subtree_aggregate(
            root_vk, &params, &stmt, &bad_agg
        ));
        let mut bad_agg = root_agg;
        bad_agg.proof.m_sparse_claim += GoldilocksExt4::ONE;
        assert!(!verify_succinct_subtree_aggregate(
            root_vk, &params, &stmt, &bad_agg
        ));
    }
}
