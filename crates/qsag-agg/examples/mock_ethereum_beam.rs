//! Ethereum Beam Chain (`4.0 s` Slot) Consensus Aggregation & Optional `3f + 1` DVT Benchmark
//! over `[DKT26]` `< 2^{-128}` QROM Quintic `Fp5` (`QSAGHQM2` / `QSAGHEM\x04`).

use std::time::Instant;

use qsag_agg::{
    AggSigProfile, EpochWalSink, HemQuinticProfile, HierarchicalHemAggregate,
    PreparedPolicyRegistry, ShardHemPolicy, ShardHemWitness, SigError, SignerBitmap,
    StatelessBudgetWalSink, ValidatorKeypair, ValidatorSignature, hierarchical_hem_message,
    prove_hem_quintic_128, prove_hierarchical_hem_prepared, verify_hem_quintic_128,
    verify_hierarchical_hem_prepared, with_worker_limit,
};
use qsag_core::belt_latch::{BeltLatchRecord, BeltLatchState, DurableWal, WalError};
use qsag_quorum::party_node::IsolatedQuorumParty;
use qsag_quorum::quorum_jorts::{
    QuorumConfig, ShamirCustodian, quorum_jorts_verify, stage_bft_shamir,
};
use qsag_quorum::wire_channel::InMemoryWireMesh;

const BEAM_SLOT_BUDGET_MS: f64 = 4_000.0;
const BEAM_VERIFY_TARGET_MS: f64 = 8.0;
const ML_DSA_44_SIG_BYTES: usize = 2_420;

type EpochReceipt = (u32, u32, [u8; 32]);

#[derive(Default)]
struct MemEpochWal {
    state: Option<([u8; 32], EpochReceipt)>,
}

impl EpochWalSink for MemEpochWal {
    fn recovered_state(&self, pk_root: &[u8; 32]) -> Result<Option<EpochReceipt>, SigError> {
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

#[derive(Clone, Debug, Default)]
struct MemBeltWal {
    stored: Option<Vec<u8>>,
}

impl DurableWal for MemBeltWal {
    fn authorize_open(&self, _record: &BeltLatchRecord) -> Result<(), WalError> {
        Ok(())
    }
    fn sync_persist(&mut self, state: &BeltLatchState) -> Result<(), WalError> {
        self.stored = Some(state.to_bytes());
        Ok(())
    }
    fn load(&self) -> Result<Option<BeltLatchState>, WalError> {
        match &self.stored {
            None => Ok(None),
            Some(raw) => BeltLatchState::from_bytes(raw)
                .map(Some)
                .ok_or(WalError::Corrupt),
        }
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

fn evm_calldata_gas(bytes: &[u8]) -> (u64, u64) {
    let zero_bytes = bytes.iter().filter(|&&b| b == 0).count() as u64;
    let nonzero_bytes = (bytes.len() as u64) - zero_bytes;
    (
        nonzero_bytes * 16 + zero_bytes * 4,
        nonzero_bytes * 40 + zero_bytes * 10,
    )
}

fn run_beam_hierarchy_bench(label: &str, subnet_specs: &[(u64, AggSigProfile, usize, usize)]) {
    let epoch_floor = 128_001u64;
    let block_msg = b"ethereum.beam.slot.128001.attestation_root";
    let mut key_groups: Vec<Vec<ValidatorKeypair>> = Vec::with_capacity(subnet_specs.len());
    let mut policies = Vec::with_capacity(subnet_specs.len());

    for &(shard_id, profile, n_vals, min_q) in subnet_specs {
        let kps: Vec<ValidatorKeypair> = (0..n_vals as u32)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(
                    profile,
                    &seed32(0x20 + shard_id as u8, shard_id),
                    i,
                )
            })
            .collect();
        policies.push(ShardHemPolicy {
            shard_id,
            custodian_cluster: seed32(0x70, shard_id),
            quorum_keys: kps.iter().map(|kp| kp.pk).collect(),
            minimum_quorums: min_q,
        });
        key_groups.push(kps);
    }

    let prepared = PreparedPolicyRegistry::new(policies.clone()).expect("valid Beam policies");
    let reg_root = prepared.policy_registry_root();
    let mut bitmaps = Vec::with_capacity(subnet_specs.len());
    let mut sig_groups: Vec<Vec<ValidatorSignature>> = Vec::with_capacity(subnet_specs.len());

    for (idx, ((_, profile, n_vals, _), kps)) in
        subnet_specs.iter().zip(key_groups.iter_mut()).enumerate()
    {
        let region_msg =
            hierarchical_hem_message(&reg_root, &policies[idx], epoch_floor, block_msg);
        let active: Vec<usize> = (0..*n_vals).collect();
        bitmaps.push(SignerBitmap::from_active_indices(*n_vals as u32, &active).unwrap());
        let mut sigs = Vec::with_capacity(*n_vals);
        for kp in kps.iter_mut() {
            let sig = if *profile == AggSigProfile::CorduroyPoseidon2 {
                let mut wal = MemStatelessWal::default();
                kp.sign_stateless(&region_msg, &mut wal).unwrap()
            } else {
                let mut wal = MemEpochWal::default();
                kp.sign_stateful(&region_msg, 0, &mut wal).unwrap()
            };
            sigs.push(sig);
        }
        sig_groups.push(sigs);
    }

    // Measure single-subnet `QSAGHQM2` (`TurboShake400`) prove + verify latency.
    let sub0_msg = hierarchical_hem_message(&reg_root, &policies[0], epoch_floor, block_msg);
    let sub0_mode = qsag_agg::SigningMode::SharedMessage(&sub0_msg);
    let t_sub = Instant::now();
    let sub0_proof = prove_hem_quintic_128(
        HemQuinticProfile::TurboShake400,
        &policies[0].quorum_keys,
        &bitmaps[0],
        &sub0_mode,
        &sig_groups[0],
    )
    .expect("quintic subnet proof");
    let sub_prove_ms = t_sub.elapsed().as_secs_f64() * 1_000.0;
    assert!(verify_hem_quintic_128(
        &policies[0].quorum_keys,
        &sub0_mode,
        &sub0_proof
    ));

    let witnesses: Vec<ShardHemWitness<'_>> = bitmaps
        .iter()
        .zip(sig_groups.iter())
        .map(|(bm, sigs)| ShardHemWitness {
            bitmap: bm,
            signatures: sigs,
        })
        .collect();
    let total_signers: usize = subnet_specs.iter().map(|s| s.2).sum();
    let min_global: usize = subnet_specs.iter().map(|s| s.3).sum();

    let t_prove = Instant::now();
    let hierarchy = prove_hierarchical_hem_prepared(
        &prepared,
        &witnesses,
        epoch_floor,
        block_msg,
        min_global,
        HemQuinticProfile::TurboShake400,
    )
    .expect("hierarchical quintic proof");
    let joint_prove_ms = t_prove.elapsed().as_secs_f64() * 1_000.0;

    let wire = hierarchy.to_bytes();
    let decoded = HierarchicalHemAggregate::from_bytes_canonical(&wire).unwrap();
    let t_ver_mc = Instant::now();
    assert!(verify_hierarchical_hem_prepared(
        &prepared,
        epoch_floor,
        block_msg,
        min_global,
        HemQuinticProfile::TurboShake400,
        &decoded,
    ));
    let verify_mc_ms = t_ver_mc.elapsed().as_secs_f64() * 1_000.0;

    let verify_1c_ms = with_worker_limit(1, || {
        let t = Instant::now();
        assert!(verify_hierarchical_hem_prepared(
            &prepared,
            epoch_floor,
            block_msg,
            min_global,
            HemQuinticProfile::TurboShake400,
            &decoded,
        ));
        t.elapsed().as_secs_f64() * 1_000.0
    });

    let (gas_2028, gas_7623) = evm_calldata_gas(&wire);
    let mldsa_raw = total_signers * ML_DSA_44_SIG_BYTES;
    println!(
        "[{label}] signers={total_signers} wire={} B ({:.2}x vs ML-DSA-44) gas_2028={gas_2028} gas_7623={gas_7623} \
         sub0_prove={sub_prove_ms:.1} ms joint_prove={joint_prove_ms:.1} ms (slot={BEAM_SLOT_BUDGET_MS:.0} ms) \
         verify_mc={verify_mc_ms:.2} ms verify_1c={verify_1c_ms:.2} ms (target={BEAM_VERIFY_TARGET_MS:.1} ms)",
        wire.len(),
        mldsa_raw as f64 / wire.len() as f64,
    );
}

fn run_dvt_cluster_bench() {
    let cfg = QuorumConfig::tight(2).expect("3-of-4 BFT Shamir config (t=2, n=4, f=1, q=3)");
    let staged = stage_bft_shamir(cfg, 2, &seed32(0xD1, 1)).expect("stage BFT Shamir");
    let pk = *staged.tree.public_key();
    let deployment = [0xDA; 32];
    let session = [0x5E; 32];
    let (endpoints, _) = InMemoryWireMesh::connect(4, session);
    let nodes: Vec<_> = endpoints
        .into_iter()
        .zip(staged.parties)
        .map(|(endpoint, material)| {
            let custodian =
                ShamirCustodian::new(cfg, staged.tree.clone(), material, MemBeltWal::default())
                    .unwrap();
            IsolatedQuorumParty::new_deployed(deployment, session, custodian, endpoint).unwrap()
        })
        .collect();
    let msg = b"ethereum.beam.dvt.validator_attestation";
    let online = [0usize, 1, 2, 3];
    let openers = [0usize, 1];
    let t0 = Instant::now();
    let outcomes = std::thread::scope(|scope| {
        let handles: Vec<_> = nodes
            .into_iter()
            .map(|mut node| scope.spawn(move || node.sign(&online, &openers, 0, msg)))
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap().unwrap())
            .collect::<Vec<_>>()
    });
    let elapsed_ms = t0.elapsed().as_secs_f64() * 1_000.0;
    let sig = &outcomes[0].signature;
    assert!(quorum_jorts_verify(&pk, msg, sig));
    let sig_bytes = 12 + 32 * (sig.nodes.len() + sig.auth_path.len());
    println!("[DVT 3-of-4 BftShamirJorts] sign_ms={elapsed_ms:.2} sig_bytes={sig_bytes}");
}

fn main() {
    println!("=== Ethereum Beam Chain Quintic Fp5 (`QSAGHQM2` / `QSAGHEM\\x04`, DKT26 < 2^-128 QROM) ===");
    run_beam_hierarchy_bench(
        "4x32 JortsPoseidon2",
        &[
            (1, AggSigProfile::JortsPoseidon2, 32, 22),
            (2, AggSigProfile::JortsPoseidon2, 32, 22),
            (3, AggSigProfile::JortsPoseidon2, 32, 22),
            (4, AggSigProfile::JortsPoseidon2, 32, 22),
        ],
    );
    run_beam_hierarchy_bench(
        "Mixed Jorts+Corduroy",
        &[
            (10, AggSigProfile::JortsPoseidon2, 16, 11),
            (20, AggSigProfile::CorduroyPoseidon2, 2, 2),
        ],
    );
    run_dvt_cluster_bench();
}
