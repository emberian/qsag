//! Two-layer `Hem` composition across regional quorum shards (`JortsPoseidon2` stateful XMSS,
//! `CorduroyPoseidon2` stateless FORS + hypertree, or mixed-profile regional hierarchies).
//!
//! Every regional `Hem` proof is verified in full, and the root is a collision-bound,
//! length-prefixed (`encode_multi_frame`) commitment over the policy registry root, statement,
//! and child proofs (not a succinct recursive verifier circuit). Committee keys represent
//! application-authorized threshold quorum keys; threshold key generation and custodian
//! membership remain registry obligations.

use crate::sponge::{encode_multi_frame, poseidon2_hash32};
use crate::{
    AggSigProfile, HemAggConfig, HemAggError, HemAggregatedProof, SignerBitmap, SigningMode,
    ValidatorPublicKey, ValidatorSignature, WhirSecurityRegime, aggregate_signatures_with_config,
    compute_committee_root, max_shard_signers, verify_aggregate_with_regime,
};
use alloc::{collections::BTreeSet, vec::Vec};

/// Canonical 8-byte wire magic for [`HierarchicalHemAggregate`].
pub const HIERARCHICAL_HEM_WIRE_MAGIC: &[u8; 8] = b"QSAGHEM\x02";

/// Upper bound on regional shard count accepted during canonical wire decoding.
pub const MAX_HIERARCHY_SHARDS: usize = 4_096;

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
        let mut out = Vec::new();
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
            let proof_bytes = s.proof.to_bytes();
            out.extend_from_slice(&(proof_bytes.len() as u32).to_le_bytes());
            out.extend_from_slice(&proof_bytes);
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
        if num_shards == 0 || num_shards > MAX_HIERARCHY_SHARDS {
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

fn encode_policy_registration(policy: &ShardHemPolicy) -> Vec<u8> {
    let key_frames: Vec<Vec<u8>> = policy
        .quorum_keys
        .iter()
        .map(|pk| {
            let raw = pk.to_bytes();
            encode_multi_frame(&[&raw[0..1], &raw[1..33], &raw[33..65]])
        })
        .collect();
    let key_refs: Vec<&[u8]> = key_frames.iter().map(Vec::as_slice).collect();
    let committee_frame = encode_multi_frame(&key_refs);
    let profile_tag = [policy.profile().map_or(0u8, |p| p as u8)];
    let shard_id_bytes = policy.shard_id.to_le_bytes();
    let min_q_bytes = (policy.minimum_quorums as u64).to_le_bytes();
    let committee_root = compute_committee_root(&policy.quorum_keys);
    encode_multi_frame(&[
        b"QSAG.HEM.POLICY.ROW/v2",
        &shard_id_bytes,
        &policy.custodian_cluster,
        &profile_tag,
        &min_q_bytes,
        &committee_root,
        &committee_frame,
    ])
}

/// Self-delimiting `encode_multi_frame` serialization of the ordered shard policy registry,
/// matching `Qsag.encodeRegistry` (`encodeRegistry_injective`).
pub fn encode_policy_registry(policies: &[ShardHemPolicy]) -> Vec<u8> {
    let rows: Vec<Vec<u8>> = policies.iter().map(encode_policy_registration).collect();
    let mut fields: Vec<&[u8]> = Vec::with_capacity(1 + rows.len());
    fields.push(b"QSAG.HEM.POLICY.REGISTRY/v2");
    for row in &rows {
        fields.push(row.as_slice());
    }
    encode_multi_frame(&fields)
}

/// Collision-bound 32-byte Poseidon2 commitment over [`encode_policy_registry`].
pub fn compute_policy_registry_root(policies: &[ShardHemPolicy]) -> [u8; 32] {
    poseidon2_hash32(&encode_policy_registry(policies))
}

/// Domain-separated length-framed Poseidon2 digest of an arbitrary message slice.
pub fn compute_framed_message_digest(message: &[u8]) -> [u8; 32] {
    poseidon2_hash32(&encode_multi_frame(&[b"QSAG.HEM.MSG/v2", message]))
}

/// Exact length-framed regional statement signed by each quorum under `policy`.
/// Every variable-length and fixed-width slice is length-prefixed via [`encode_multi_frame`].
pub fn hierarchical_hem_message(
    policy: &ShardHemPolicy,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
) -> Vec<u8> {
    let profile_tag = [policy.profile().map_or(0u8, |p| p as u8)];
    let shard_id_bytes = policy.shard_id.to_le_bytes();
    let min_q_bytes = (policy.minimum_quorums as u64).to_le_bytes();
    let committee_root = compute_committee_root(&policy.quorum_keys);
    let epoch_bytes = epoch_floor.to_le_bytes();
    encode_multi_frame(&[
        b"QSAG.HEM.REGION/v2",
        &shard_id_bytes,
        &policy.custodian_cluster,
        &profile_tag,
        &min_q_bytes,
        &committee_root,
        &epoch_bytes,
        message.as_ref(),
    ])
}

/// Registry-pinned regional statement signed by each quorum: binds `policy_registry_root`
/// directly into the quorum signature so a regional batch cannot be spliced into any modified
/// global policy registry even if a verifier is handed the altered registry.
pub fn hierarchical_hem_registry_bound_message(
    policy_registry_root: &[u8; 32],
    policy: &ShardHemPolicy,
    epoch_floor: u64,
    message: impl AsRef<[u8]>,
) -> Vec<u8> {
    let profile_tag = [policy.profile().map_or(0u8, |p| p as u8)];
    let shard_id_bytes = policy.shard_id.to_le_bytes();
    let min_q_bytes = (policy.minimum_quorums as u64).to_le_bytes();
    let committee_root = compute_committee_root(&policy.quorum_keys);
    let epoch_bytes = epoch_floor.to_le_bytes();
    encode_multi_frame(&[
        b"QSAG.HEM.REGION.BOUND/v2",
        policy_registry_root,
        &shard_id_bytes,
        &policy.custodian_cluster,
        &profile_tag,
        &min_q_bytes,
        &committee_root,
        &epoch_bytes,
        message.as_ref(),
    ])
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

fn root_commitment(policy_registry_root: &[u8; 32], shards: &[ShardHemBatch]) -> [u8; 32] {
    let shard_frames: Vec<Vec<u8>> = shards
        .iter()
        .map(|s| {
            let shard_id = s.shard_id.to_le_bytes();
            let min_q = s.minimum_quorums.to_le_bytes();
            let epoch = s.epoch_floor.to_le_bytes();
            let proof_bytes = s.proof.to_bytes();
            encode_multi_frame(&[
                b"QSAG.HEM.HIERARCHY.SHARD/v2",
                &shard_id,
                &s.custodian_cluster,
                &s.shard_quorum_set_root,
                &min_q,
                &epoch,
                &s.message_digest,
                &proof_bytes,
            ])
        })
        .collect();
    let mut fields: Vec<&[u8]> = Vec::with_capacity(2 + shard_frames.len());
    fields.push(b"QSAG.HEM.HIERARCHY.ROOT/v2");
    fields.push(policy_registry_root);
    for sf in &shard_frames {
        fields.push(sf.as_slice());
    }
    poseidon2_hash32(&encode_multi_frame(&fields))
}

fn prove_hierarchical_hem_inner(
    policies: &[ShardHemPolicy],
    witnesses: &[ShardHemWitness<'_>],
    epoch_floor: u64,
    message: &[u8],
    minimum_global_quorums: usize,
    config: &HemAggConfig,
    bind_registry_in_sig: bool,
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

    let policy_registry_root = compute_policy_registry_root(policies);
    let message_digest = compute_framed_message_digest(message);
    if config.max_signers_per_shard == 0 {
        return Err(HemAggError::InvalidShardConfig);
    }

    let prove_shard =
        |(p, w): (&ShardHemPolicy, &ShardHemWitness<'_>)| -> Result<ShardHemBatch, HemAggError> {
            let shard_profile = p.profile().ok_or(HemAggError::InvalidShardConfig)?;
            let region_msg = if bind_registry_in_sig {
                hierarchical_hem_registry_bound_message(
                    &policy_registry_root,
                    p,
                    epoch_floor,
                    message,
                )
            } else {
                hierarchical_hem_message(p, epoch_floor, message)
            };
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
            let proof = aggregate_signatures_with_config(
                &p.quorum_keys,
                w.bitmap,
                &SigningMode::SharedMessage(&region_msg),
                w.signatures,
                &cfg,
            )?;
            Ok(ShardHemBatch {
                shard_id: p.shard_id,
                custodian_cluster: p.custodian_cluster,
                shard_quorum_set_root: compute_committee_root(&p.quorum_keys),
                minimum_quorums: p.minimum_quorums as u64,
                epoch_floor,
                message_digest,
                proof,
            })
        };

    #[cfg(feature = "std")]
    let shards: Vec<ShardHemBatch> = if policies.len() > 1 && crate::parallel_workers() > 1 {
        let pairs: Vec<_> = policies.iter().zip(witnesses).collect();
        let groups: Vec<Result<Vec<ShardHemBatch>, HemAggError>> =
            crate::map_chunks_bounded(&pairs, |sub| {
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
            .map(prove_shard)
            .collect::<Result<Vec<_>, _>>()?
    };

    #[cfg(not(feature = "std"))]
    let shards: Vec<ShardHemBatch> = policies
        .iter()
        .zip(witnesses)
        .map(prove_shard)
        .collect::<Result<Vec<_>, _>>()?;

    Ok(HierarchicalHemAggregate {
        policy_registry_root,
        root_commitment: root_commitment(&policy_registry_root, &shards),
        shards,
    })
}

fn verify_hierarchical_hem_inner(
    policies: &[ShardHemPolicy],
    epoch_floor: u64,
    message: &[u8],
    minimum_global_quorums: usize,
    regime: WhirSecurityRegime,
    aggregate: &HierarchicalHemAggregate,
    bind_registry_in_sig: bool,
) -> bool {
    if !valid_policies(policies)
        || aggregate.shards.len() != policies.len()
        || minimum_global_quorums == 0
    {
        return false;
    }
    let Ok(min_global_u64) = u64::try_from(minimum_global_quorums) else {
        return false;
    };
    let expected_registry_root = compute_policy_registry_root(policies);
    if aggregate.policy_registry_root != expected_registry_root {
        return false;
    }
    let expected_msg_digest = compute_framed_message_digest(message);

    let mut counts_u64 = Vec::with_capacity(policies.len());
    let mut minimums_u64 = Vec::with_capacity(policies.len());
    for (p, s) in policies.iter().zip(&aggregate.shards) {
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
            || s.shard_quorum_set_root != compute_committee_root(&p.quorum_keys)
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

    let verify_shard = |(p, s): (&ShardHemPolicy, &ShardHemBatch)| -> bool {
        let region_msg = if bind_registry_in_sig {
            hierarchical_hem_registry_bound_message(
                &expected_registry_root,
                p,
                epoch_floor,
                message,
            )
        } else {
            hierarchical_hem_message(p, epoch_floor, message)
        };
        verify_aggregate_with_regime(
            &p.quorum_keys,
            &SigningMode::SharedMessage(&region_msg),
            &s.proof,
            regime,
        )
    };

    #[cfg(feature = "std")]
    let all_shards_valid = if policies.len() > 1 && crate::parallel_workers() > 1 {
        let pairs: Vec<_> = policies.iter().zip(&aggregate.shards).collect();
        let verdicts =
            crate::map_chunks_bounded(&pairs, |sub| sub.iter().copied().all(&verify_shard));
        verdicts.into_iter().all(|v| v)
    } else {
        policies.iter().zip(&aggregate.shards).all(verify_shard)
    };

    #[cfg(not(feature = "std"))]
    let all_shards_valid = policies.iter().zip(&aggregate.shards).all(verify_shard);

    if !all_shards_valid {
        return false;
    }

    root_commitment(&expected_registry_root, &aggregate.shards) == aggregate.root_commitment
}

/// Prove a two-layer hierarchical `Hem` aggregate across `policies` (`JortsPoseidon2`,
/// `CorduroyPoseidon2`, or mixed regional profiles).
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
        false,
    )
}

/// Verify a two-layer hierarchical `Hem` aggregate against `policies`, exact `epoch_floor` and
/// `message`, global quorum threshold, and `regime`.
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
        false,
    )
}

/// Prove a registry-pinned two-layer hierarchical `Hem` aggregate whose individual quorum
/// signatures sign [`hierarchical_hem_registry_bound_message`].
pub fn prove_hierarchical_hem_registry_bound(
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
        true,
    )
}

/// Verify a registry-pinned two-layer hierarchical `Hem` aggregate produced by
/// [`prove_hierarchical_hem_registry_bound`].
pub fn verify_hierarchical_hem_registry_bound(
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
        true,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ValidatorKeypair;

    #[test]
    fn hierarchical_three_regions_twelve_quorums() {
        let mut policies = Vec::new();
        let mut signatures = Vec::new();
        let epoch = 17;
        let digest = [42u8; 32];
        for region in 0..3u64 {
            let mut keys: Vec<_> = (0..4)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::JortsPoseidon2,
                        &[region as u8 + 1; 32],
                        i,
                    )
                })
                .collect();
            let policy = ShardHemPolicy {
                shard_id: region,
                custodian_cluster: [region as u8; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 4,
            };
            let message = hierarchical_hem_message(&policy, epoch, digest);
            signatures.push(
                keys.iter_mut()
                    .map(|k| k.sign_stateful_for_unit_test(&message, 0).unwrap())
                    .collect::<Vec<_>>(),
            );
            policies.push(policy);
        }
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
        let mut corduroy_sigs = Vec::new();
        for region in 0..2u64 {
            let mut keys: Vec<_> = (0..2)
                .map(|i| {
                    ValidatorKeypair::keygen_deterministic(
                        AggSigProfile::CorduroyPoseidon2,
                        &[0xA0 + region as u8; 32],
                        i,
                    )
                })
                .collect();
            let policy = ShardHemPolicy {
                shard_id: 10 + region,
                custodian_cluster: [0xC0 + region as u8; 32],
                quorum_keys: keys.iter().map(|k| k.pk).collect(),
                minimum_quorums: 2,
            };
            let msg = hierarchical_hem_message(&policy, epoch, payload);
            corduroy_sigs.push(
                keys.iter_mut()
                    .map(|k| k.sign_stateless_for_unit_test(&msg).unwrap())
                    .collect::<Vec<_>>(),
            );
            corduroy_policies.push(policy);
        }
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
        let msg_jorts_ab =
            hierarchical_hem_registry_bound_message(&root_ab, &p_jorts, epoch, payload);
        let msg_cord_a =
            hierarchical_hem_registry_bound_message(&root_ab, &p_cord_a, epoch, payload);
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

        let mixed_agg = prove_hierarchical_hem_registry_bound(
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
        assert!(verify_hierarchical_hem_registry_bound(
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
        let msg_cord_b =
            hierarchical_hem_registry_bound_message(&root_ac, &p_cord_b, epoch, payload);
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
        assert!(!verify_hierarchical_hem_registry_bound(
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
        assert_ne!(
            hierarchical_hem_message(&reg_left[0], 7, b"abc"),
            hierarchical_hem_message(&p_min2, 7, b"abc")
        );
        assert_ne!(
            hierarchical_hem_message(&reg_left[0], 7, b""),
            hierarchical_hem_message(&reg_left[0], 7, b"\x00")
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
}
