//! Ethereum Beam Chain Slot Aggregation Benchmark (`qsag-agg` 2-Layer Hierarchical `Hem`).
//!
//! Models a 4-second Ethereum Beam Chain slot with regional attestation subnets:
//! - **Subnet Validators (`JortsPoseidon2` stateful + `CorduroyPoseidon2` stateless hypertree)**:
//!   Validators sign the registry-pinned regional attestation statement
//!   `hierarchical_hem_registry_bound_message`.
//! - **Layer-1 Subnet Aggregators + Layer-2 Block Proposer (`recursive.rs`)**:
//!   Aggregates regional subnets concurrently via `std::thread::scope`, binds the collision-free
//!   `encode_multi_frame` policy registry root and `checked_quorum_sum` quorum weights, round-trips
//!   canonical wire bytes (`HIERARCHICAL_HEM_WIRE_MAGIC`), and benchmarks block verification against
//!   the `< 8.0 ms` Beam Chain verifier target.

use std::time::Instant;

use qsag_agg::{
    AggSigProfile, EpochWalSink, HemAggConfig, HierarchicalHemAggregate, ShardHemPolicy,
    ShardHemWitness, SigError, SignerBitmap, StatelessBudgetWalSink, ValidatorKeypair,
    ValidatorSignature, WhirSecurityRegime, compute_policy_registry_root,
    hierarchical_hem_registry_bound_message, prove_hierarchical_hem_registry_bound,
    verify_hierarchical_hem_registry_bound,
};

type EpochReceipt = (u32, u32, [u8; 32]);

#[derive(Default)]
struct MemEpochWal {
    state: Option<([u8; 32], EpochReceipt)>,
}

impl EpochWalSink for MemEpochWal {
    fn recovered_state(
        &self,
        pk_root: &[u8; 32],
    ) -> Result<Option<(u32, u32, [u8; 32])>, SigError> {
        match &self.state {
            None => Ok(None),
            Some((root, st)) if root == pk_root => Ok(Some(*st)),
            Some(_) => Err(SigError::WalPersistenceFailed),
        }
    }

    fn persist_latched_epoch(
        &mut self,
        pk_root: &[u8; 32],
        next_unused_epoch: u32,
        latched_epoch: u32,
        mu_bytes: &[u8; 32],
    ) -> Result<(), SigError> {
        if let Some((root, _)) = &self.state
            && root != pk_root
        {
            return Err(SigError::WalPersistenceFailed);
        }
        self.state = Some((*pk_root, (next_unused_epoch, latched_epoch, *mu_bytes)));
        Ok(())
    }
}

#[derive(Default)]
struct MemStatelessWal {
    used: u64,
}

impl StatelessBudgetWalSink for MemStatelessWal {
    fn reserve(&mut self, _pk_root: &[u8; 32], limit: u64) -> Result<u64, SigError> {
        if self.used >= limit {
            return Err(SigError::StatelessBudgetExhausted);
        }
        self.used += 1;
        Ok(self.used)
    }
}

fn seed32(tag: u8, id: u64) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[0] = tag;
    s[1..9].copy_from_slice(&id.to_le_bytes());
    for (i, b) in s[9..].iter_mut().enumerate() {
        *b = tag
            .wrapping_mul(53)
            .wrapping_add(id as u8)
            .wrapping_add(i as u8);
    }
    s
}

fn run_beam_hierarchy_bench(
    label: &str,
    subnet_specs: &[(u64, AggSigProfile, usize, usize)],
    regime: WhirSecurityRegime,
) {
    // This floor is a key-local leaf index; the beacon slot is bound in the message.
    let epoch_floor = 0u64;
    let beacon_root_msg = b"ethereum.beam.slot.128000.head_root.0x4a7b8c9d0e1f2a3b4c5d6e7f8091a2b3";

    let t_setup = Instant::now();
    let built: Vec<(ShardHemPolicy, ValidatorKeypairVec)> = std::thread::scope(|scope| {
        let handles: Vec<_> = subnet_specs
            .iter()
            .map(|&(shard_id, profile, committee_len, min_quorum)| {
                scope.spawn(move || {
                    let master = seed32(0x31, shard_id);
                    let mut keypairs = Vec::with_capacity(committee_len);
                    let mut pks = Vec::with_capacity(committee_len);
                    for idx in 0..committee_len {
                        let kp =
                            ValidatorKeypair::keygen_deterministic(profile, &master, idx as u32);
                        pks.push(kp.pk);
                        keypairs.push(kp);
                    }
                    let policy = ShardHemPolicy {
                        shard_id,
                        custodian_cluster: seed32(0x52, shard_id),
                        quorum_keys: pks,
                        minimum_quorums: min_quorum,
                    };
                    (policy, keypairs)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("subnet keygen panicked"))
            .collect()
    });

    let mut policies = Vec::with_capacity(built.len());
    let mut subnet_keypairs = Vec::with_capacity(built.len());
    for (policy, kps) in built {
        policies.push(policy);
        subnet_keypairs.push(kps);
    }
    let registry_root = compute_policy_registry_root(&policies);

    let signed_subnets: Vec<(SignerBitmap, Vec<ValidatorSignature>)> =
        std::thread::scope(|scope| {
            let policies_ref = &policies;
            let handles: Vec<_> = subnet_keypairs
                .into_iter()
                .enumerate()
                .map(|(s_idx, mut kps)| {
                    scope.spawn(move || {
                        let policy = &policies_ref[s_idx];
                        let region_msg = hierarchical_hem_registry_bound_message(
                            &registry_root,
                            policy,
                            epoch_floor,
                            beacon_root_msg,
                        );
                        let indices: Vec<usize> = (0..kps.len()).collect();
                        let bitmap = SignerBitmap::from_active_indices(kps.len() as u32, &indices)
                            .expect("bitmap");
                        let mut sigs = Vec::with_capacity(kps.len());
                        for kp in &mut kps {
                            let sig = match kp.pk.profile {
                                AggSigProfile::JortsPoseidon2 => {
                                    let mut wal = MemEpochWal::default();
                                    kp.sign_stateful(&region_msg, epoch_floor as u32, &mut wal)
                                        .expect("Jorts subnet sign")
                                }
                                AggSigProfile::CorduroyPoseidon2 => {
                                    let mut wal = MemStatelessWal::default();
                                    kp.sign_stateless(&region_msg, &mut wal)
                                        .expect("Corduroy subnet sign")
                                }
                            };
                            sigs.push(sig);
                        }
                        (bitmap, sigs)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().expect("subnet sign panicked"))
                .collect()
        });
    let setup_ms = t_setup.elapsed().as_secs_f64() * 1_000.0;

    let witnesses: Vec<ShardHemWitness<'_>> = signed_subnets
        .iter()
        .map(|(bitmap, sigs)| ShardHemWitness {
            bitmap,
            signatures: sigs.as_slice(),
        })
        .collect();
    let min_global: usize = policies.iter().map(|p| p.minimum_quorums).sum();

    let mut cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, seed32(0x73, 99));
    cfg.regime = regime;

    let t_prove = Instant::now();
    let agg = prove_hierarchical_hem_registry_bound(
        &policies,
        &witnesses,
        epoch_floor,
        beacon_root_msg,
        min_global,
        &cfg,
    )
    .expect("2-layer Beam Chain hierarchical Hem aggregation");
    let prove_ms = t_prove.elapsed().as_secs_f64() * 1_000.0;

    let wire = agg.to_bytes();
    let decoded =
        HierarchicalHemAggregate::from_bytes_canonical(&wire).expect("canonical wire roundtrip");
    assert_eq!(decoded, agg);

    // Warm + 9-iteration median verification timing.
    assert!(verify_hierarchical_hem_registry_bound(
        &policies,
        epoch_floor,
        beacon_root_msg,
        min_global,
        regime,
        &decoded,
    ));
    let mut samples_ms = Vec::with_capacity(9);
    for _ in 0..9 {
        let t_v = Instant::now();
        let ok = verify_hierarchical_hem_registry_bound(
            &policies,
            epoch_floor,
            beacon_root_msg,
            min_global,
            regime,
            &decoded,
        );
        assert!(ok);
        samples_ms.push(t_v.elapsed().as_secs_f64() * 1_000.0);
    }
    samples_ms.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median_verify_ms = samples_ms[samples_ms.len() / 2];
    let total_signers = decoded
        .checked_total_quorums()
        .expect("checked_total_quorums");

    println!(
        "[{label}] subnets={} | total_validators={total_signers} | regime={regime:?}",
        policies.len()
    );
    println!(
        "      prove_2layer = {prove_ms:.2} ms (4000 ms slot budget) | verify_median = {median_verify_ms:.2} ms (8.00 ms target) | wire = {} B ({:.1} KiB) | keygen+sign = {setup_ms:.1} ms",
        wire.len(),
        wire.len() as f64 / 1024.0
    );
    println!(
        "      timing_targets: prove={} | verify={} (informational; hardware/load dependent)",
        if prove_ms < 4_000.0 { "met" } else { "missed" },
        if median_verify_ms < 8.0 {
            "met"
        } else {
            "missed"
        },
    );
}

type ValidatorKeypairVec = Vec<ValidatorKeypair>;

fn main() {
    let workers = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    println!("========================================================================");
    println!(" QSAG x Ethereum Beam Chain (2-Layer Hierarchical `Hem`, threads={workers})");
    println!("========================================================================");

    // Scenario A: 4 JortsPoseidon2 attestation subnets x 32 validators = 128 validators
    let jorts_subnets = [
        (10, AggSigProfile::JortsPoseidon2, 32, 24),
        (20, AggSigProfile::JortsPoseidon2, 32, 24),
        (30, AggSigProfile::JortsPoseidon2, 32, 24),
        (40, AggSigProfile::JortsPoseidon2, 32, 24),
    ];
    run_beam_hierarchy_bench(
        "Beam-Jorts-4x32-Classical128",
        &jorts_subnets,
        WhirSecurityRegime::Habr24Classical128,
    );
    run_beam_hierarchy_bench(
        "Beam-Jorts-4x32-Qrom128",
        &jorts_subnets,
        WhirSecurityRegime::Habr24Qrom128,
    );

    // Scenario B: Mixed Stateful (`JortsPoseidon2`) + Stateless Hypertree (`CorduroyPoseidon2`) subnets
    let mixed_subnets = [
        (100, AggSigProfile::JortsPoseidon2, 32, 22),
        (200, AggSigProfile::JortsPoseidon2, 32, 22),
        (300, AggSigProfile::CorduroyPoseidon2, 4, 3),
        (400, AggSigProfile::CorduroyPoseidon2, 4, 3),
    ];
    run_beam_hierarchy_bench(
        "Beam-Mixed-Jorts+Corduroy-Qrom128",
        &mixed_subnets,
        WhirSecurityRegime::Habr24Qrom128,
    );
}
