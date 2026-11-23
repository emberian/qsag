//! Multi-shard hierarchical `Hem` composition (`QSAGHEM\x04`) and `[DKT26]` `< 2^{-128}` QROM
//! binary recursive IVC (`QSAGIVC1`, [`crate::zk_hem::recursive_ivc`]) over Quintic `Fp5`:
//!
//! 1. **Direct Regional Hierarchy ([`HierarchicalHemAggregate`])**: each regional quorum shard
//!    (`JortsPoseidon2`, `CorduroyPoseidon2`, or mixed regional profiles) carries a verified
//!    Quintic `Fp5` [`HemQuinticProof`] (`QSAGHQM2`) over the registry-pinned
//!    [`hierarchical_hem_message`], bound under a length-prefixed `cSHAKE256` root commitment.
//! 2. **Succinct Binary Recursive IVC ([`SuccinctIvcProof`])**: `O(1)`-size (`639,673 B`)
//!    recursive binary tree proof over `[DKT26]` `< 2^{-128}` QROM Quintic `Fp5` WHIR
//!    (`FixedPathWhirW24`), verifying both children's complete WHIR openings and row/column
//!    sumchecks inside every internal step circuit.

pub use crate::zk_hem::recursive_ivc::{
    FixedPathWhirW24, IvcPolicyRegistry, IvcRowCensus, IvcShard, IvcStepConfig,
    IvcSubtreeStatement, IvcTableCommitment, IvcTreeStepRelation, SuccinctIvcProof,
    SuccinctIvcStep, ivc_signing_message, prove_ivc_tree, verify_ivc_tree,
};

use alloc::{collections::BTreeSet, vec::Vec};

use crate::hem_quintic::{
    HemQuinticProfile, HemQuinticProof, prove_hem_quintic_128, verify_hem_quintic_128,
};
use crate::sponge::{
    cshake256_from_midstate_32, cshake256_from_midstate_32_x4, cshake256_static_midstate,
    encode_multi_frame, poseidon2_hash32, push_leb128,
};
use crate::trace::LOG_TRACE_COLS;
use crate::{
    AggSigProfile, HemAggError, SignerBitmap, SigningMode, ValidatorPublicKey, ValidatorSignature,
    compute_committee_root, max_shard_signers,
};

/// Canonical v4 wire magic (Quintic `Fp5` `QSAGHQM2` shard proofs + `cSHAKE256` outer commitment)
/// for [`HierarchicalHemAggregate`].
pub const HIERARCHICAL_HEM_WIRE_MAGIC: &[u8; 8] = b"QSAGHEM\x04";

/// Largest regional shard count (`2^{MAX_PCS_NUM_VARS - LOG_TRACE_COLS - 1} = 2^19`).
/// Wire decoding requires the body to hold every claimed shard header before allocating.
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
    pub proof: HemQuinticProof,
}

/// Two-layer hierarchical Quintic `Fp5` `Hem` aggregate over an ordered regional policy registry.
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
            let proof =
                HemQuinticProof::from_bytes(proof_slice).ok_or(HemAggError::MalformedWireBytes)?;
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

/// Overflow-free per-shard and global quorum threshold check delegated to the Aeneas-extracted
/// `qsag-whir-verified` kernel.
fn checked_quorum_sum(counts: &[u64], minimums: &[u64], min_global: u64) -> Option<u64> {
    qsag_whir_verified::checked_quorum_sum(counts, minimums, min_global)
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

/// Exact length-framed regional statement signed by each quorum under `policy`.
/// Binds `policy_registry_root` directly into the quorum signature so a regional batch cannot
/// be spliced into any other global policy registry.
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
    if policies.is_empty()
        || policies.len() > MAX_HIERARCHY_SHARDS
        || !policies.windows(2).all(|p| p[0].shard_id < p[1].shard_id)
    {
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
            || p.quorum_keys.len() > max_shard_signers(shard_profile)
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

    let Some(total_cap) = checked_quorum_sum(&capacities, &minimums, 1) else {
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

#[cfg(feature = "std")]
std::thread_local! {
    static SHARD_FRAME_SCRATCH: core::cell::RefCell<Vec<Vec<u8>>> =
        const { core::cell::RefCell::new(Vec::new()) };
}

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

type CommittedShard = (ShardHemBatch, [u8; 32]);

fn root_commitment_from_digests(policy_registry_root: &[u8; 32], digests: &[[u8; 32]]) -> [u8; 32] {
    let mut fields: Vec<&[u8]> = Vec::with_capacity(2 + digests.len());
    fields.push(HIERARCHY_ROOT_CUSTOM);
    fields.push(policy_registry_root);
    fields.extend(digests.iter().map(|d| d.as_slice()));
    cshake256_from_midstate_32(&HIERARCHY_ROOT_MIDSTATE, &encode_multi_frame(&fields))
}

fn map_hem_quintic_err(err: crate::hem_quintic::Error) -> HemAggError {
    match err {
        crate::hem_quintic::Error::Statement => HemAggError::DuplicateValidatorOrProfileMismatch,
        crate::hem_quintic::Error::Geometry => HemAggError::InvalidShardConfig,
        crate::hem_quintic::Error::Signature => HemAggError::InvalidIndividualSignature,
        crate::hem_quintic::Error::InconsistentTrace
        | crate::hem_quintic::Error::TranscriptLimit => HemAggError::InvalidChildProof,
    }
}

fn prove_hierarchical_hem_inner(
    policies: &[ShardHemPolicy],
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: &[u8],
    minimum_global_quorums: usize,
    profile: HemQuinticProfile,
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
        profile,
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
    profile: HemQuinticProfile,
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
        if w.bitmap.num_validators() as usize != p.quorum_keys.len() {
            return Err(HemAggError::CommitteeMismatch);
        }
        let n = w.bitmap.count_ones();
        if w.signatures.len() != n {
            return Err(HemAggError::SignatureCountMismatch);
        }
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
    let Some(total_u64) = checked_quorum_sum(&counts_u64, &minimums_u64, min_global_u64) else {
        let sum_no_global = checked_quorum_sum(&counts_u64, &minimums_u64, 1);
        return Err(if sum_no_global.is_some() {
            HemAggError::EmptySigners
        } else {
            HemAggError::InvalidShardConfig
        });
    };
    usize::try_from(total_u64).map_err(|_| HemAggError::InvalidShardConfig)?;

    let message_digest = compute_framed_message_digest(message);

    let prove_shard = |((p, w), c_root): ((&ShardHemPolicy, &ShardHemWitness<'_>), &[u8; 32])|
     -> Result<CommittedShard, HemAggError> {
        let region_msg = hierarchical_hem_message_with_root(
            &policy_registry_root,
            p,
            c_root,
            epoch_floor,
            message,
        );
        let proof = prove_hem_quintic_128(
            profile,
            &p.quorum_keys,
            w.bitmap,
            &SigningMode::SharedMessage(&region_msg),
            w.signatures,
        )
        .map_err(map_hem_quintic_err)?;
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
    expected_profile: HemQuinticProfile,
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
        if p.profile().is_none() {
            return false;
        }
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
            || s.proof.profile != expected_profile
            || s.proof.bitmap.num_validators() as usize != p.quorum_keys.len()
            || s.proof.num_signers() < p.minimum_quorums
        {
            return false;
        }
        counts_u64.push(verified_signers_u64);
        minimums_u64.push(expected_min_u64);
    }

    let Some(total_u64) = checked_quorum_sum(&counts_u64, &minimums_u64, min_global_u64) else {
        return false;
    };
    if usize::try_from(total_u64).is_err() {
        return false;
    }

    let verify_shard_only =
        |((p, s), c_root): ((&ShardHemPolicy, &ShardHemBatch), &[u8; 32])| -> bool {
            let region_msg = hierarchical_hem_message_with_root(
                &expected_registry_root,
                p,
                c_root,
                epoch_floor,
                message,
            );
            verify_hem_quintic_128(
                &p.quorum_keys,
                &SigningMode::SharedMessage(&region_msg),
                &s.proof,
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
    expected_profile: HemQuinticProfile,
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
        expected_profile,
        aggregate,
    )
}

/// Prove a two-layer hierarchical Quintic `Fp5` `Hem` aggregate across `policies`
/// (`JortsPoseidon2`, `CorduroyPoseidon2`, or mixed regional profiles).
pub fn prove_hierarchical_hem(
    policies: &[ShardHemPolicy],
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    profile: HemQuinticProfile,
) -> Result<HierarchicalHemAggregate, HemAggError> {
    prove_hierarchical_hem_inner(
        policies,
        witnesses,
        epoch_floor,
        message.as_ref(),
        minimum_global_quorums,
        profile,
    )
}

/// Prove using the registry's validated policies and cached committee roots.
pub fn prove_hierarchical_hem_prepared(
    registry: &PreparedPolicyRegistry,
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    profile: HemQuinticProfile,
) -> Result<HierarchicalHemAggregate, HemAggError> {
    prove_hierarchical_hem_with_roots(
        &registry.policies,
        &registry.committee_roots,
        registry.policy_registry_root,
        witnesses,
        epoch_floor,
        message.as_ref(),
        minimum_global_quorums,
        profile,
    )
}

/// Verify a two-layer hierarchical Quintic `Fp5` `Hem` aggregate against `policies`, exact
/// `epoch_floor` and `message`, global quorum threshold, and `expected_profile`.
pub fn verify_hierarchical_hem(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    expected_profile: HemQuinticProfile,
    aggregate: &HierarchicalHemAggregate,
) -> bool {
    verify_hierarchical_hem_inner(
        policies,
        epoch_floor,
        message.as_ref(),
        minimum_global_quorums,
        expected_profile,
        aggregate,
    )
}

/// Verify against a pre-validated [`PreparedPolicyRegistry`], skipping redundant committee root
/// and `policy_registry_root` recomputation.
pub fn verify_hierarchical_hem_prepared(
    registry: &PreparedPolicyRegistry,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
    minimum_global_quorums: usize,
    expected_profile: HemQuinticProfile,
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
        expected_profile,
        aggregate,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sig::ValidatorKeypair;
    use alloc::vec;

    #[test]
    fn hierarchical_quintic_hem_roundtrip_and_tamper_rejection() {
        let mut kp0 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[11; 32], 0);
        let mut kp1 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[12; 32], 1);
        let mut kp2 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::CorduroyPoseidon2, &[21; 32], 0);

        let policies = vec![
            ShardHemPolicy {
                shard_id: 10,
                custodian_cluster: [0xA1; 32],
                quorum_keys: vec![kp0.pk, kp1.pk],
                minimum_quorums: 2,
            },
            ShardHemPolicy {
                shard_id: 20,
                custodian_cluster: [0xB2; 32],
                quorum_keys: vec![kp2.pk],
                minimum_quorums: 1,
            },
        ];
        let prepared = PreparedPolicyRegistry::new(policies.clone()).unwrap();
        let epoch_floor = 77u64;
        let msg = b"qsag-quintic-hierarchy";

        let msg_s0 = hierarchical_hem_message(
            &prepared.policy_registry_root(),
            &policies[0],
            epoch_floor,
            msg,
        );
        let msg_s1 = hierarchical_hem_message(
            &prepared.policy_registry_root(),
            &policies[1],
            epoch_floor,
            msg,
        );
        let sig0 = kp0.sign_stateful_for_unit_test(&msg_s0, 0).unwrap();
        let sig1 = kp1.sign_stateful_for_unit_test(&msg_s0, 0).unwrap();
        let sig2 = kp2.sign_stateless_for_unit_test(&msg_s1).unwrap();

        let bm0 = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
        let bm1 = SignerBitmap::from_active_indices(1, &[0]).unwrap();
        let sigs0 = [sig0, sig1];
        let sigs1 = [sig2];
        let witnesses = [
            ShardHemWitness {
                bitmap: &bm0,
                signatures: &sigs0,
            },
            ShardHemWitness {
                bitmap: &bm1,
                signatures: &sigs1,
            },
        ];

        let agg = prove_hierarchical_hem_prepared(
            &prepared,
            &witnesses,
            epoch_floor,
            msg,
            3,
            HemQuinticProfile::TurboShake400,
        )
        .unwrap();
        assert_eq!(agg.checked_total_quorums(), Some(3));
        assert!(verify_hierarchical_hem(
            &policies,
            epoch_floor,
            msg,
            3,
            HemQuinticProfile::TurboShake400,
            &agg
        ));
        assert!(verify_hierarchical_hem_prepared(
            &prepared,
            epoch_floor,
            msg,
            3,
            HemQuinticProfile::TurboShake400,
            &agg
        ));
        assert!(!verify_hierarchical_hem_prepared(
            &prepared,
            epoch_floor,
            msg,
            4,
            HemQuinticProfile::TurboShake400,
            &agg
        ));
        assert!(!verify_hierarchical_hem_prepared(
            &prepared,
            epoch_floor + 1,
            msg,
            3,
            HemQuinticProfile::TurboShake400,
            &agg
        ));
        assert!(!verify_hierarchical_hem_prepared(
            &prepared,
            epoch_floor,
            msg,
            3,
            HemQuinticProfile::Poseidon2Gl24,
            &agg
        ));

        let wire = agg.to_bytes();
        let decoded = HierarchicalHemAggregate::from_bytes_canonical(&wire).unwrap();
        assert_eq!(decoded, agg);
        let mut trailing = wire.clone();
        trailing.push(0);
        assert!(HierarchicalHemAggregate::from_bytes_canonical(&trailing).is_err());
    }
}
