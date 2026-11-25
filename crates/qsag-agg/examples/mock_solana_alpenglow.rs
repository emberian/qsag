//! Solana Alpenglow (`Rotor` + `Votor`) Consensus Benchmark over `[DKT26]` `< 2^{-128}` QROM
//! Quintic `Fp5` (`QSAGHQM2` / `QSAGHEM\x04`) and `Compact1122` / `Full256Bit` Frontier FTS.

use std::time::Instant;

use qsag_accel::CpuReferenceBackend;
use qsag_agg::{
    AggSigProfile, EpochWalSink, HemQuinticProfile, HierarchicalHemAggregate,
    PreparedPolicyRegistry, ShardHemPolicy, ShardHemWitness, SigError, SignerBitmap, SigningMode,
    ValidatorKeypair, ValidatorSignature, hierarchical_hem_message, prove_hem_quintic_128,
    prove_hierarchical_hem_prepared, verify_hem_quintic_128, verify_hierarchical_hem_prepared,
    with_worker_limit,
};
use qsag_fts::{
    FrontierDpTable, FrontierFtsError, FrontierFtsProfile, FrontierFtsSigningKey,
    FrontierVerifyInput, FtsEpochWal, verify_frontier_fts_batch,
};

type EpochReceipt = (u32, u32, [u8; 32]);

#[derive(Default)]
struct MemFtsWal {
    key: Option<[u8; 32]>,
    uses: u8,
}

impl FtsEpochWal for MemFtsWal {
    fn uses_completed(&self, wal_key: &[u8; 32]) -> Result<u8, FrontierFtsError> {
        match &self.key {
            None => Ok(0),
            Some(k) if k == wal_key => Ok(self.uses),
            Some(_) => Err(FrontierFtsError::PersistenceFailed),
        }
    }

    fn reserve_use(&mut self, wal_key: &[u8; 32], next: u8) -> Result<(), FrontierFtsError> {
        if let Some(k) = &self.key
            && k != wal_key
        {
            return Err(FrontierFtsError::PersistenceFailed);
        }
        if next <= self.uses {
            return Err(FrontierFtsError::UseBudgetExhausted);
        }
        self.key = Some(*wal_key);
        self.uses = next;
        Ok(())
    }
}

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

fn seed32(tag: u8, idx: u32) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0] = tag;
    out[1..5].copy_from_slice(&idx.to_le_bytes());
    for (i, b) in out[5..].iter_mut().enumerate() {
        *out_b(b) = tag
            .wrapping_mul(37)
            .wrapping_add((idx as u8).wrapping_mul(13))
            .wrapping_add(i as u8);
    }
    out
}

#[inline]
fn out_b(b: &mut u8) -> &mut u8 {
    b
}

fn run_votor_fts_section(votes: usize) {
    let profile = FrontierFtsProfile::Compact1122;
    let dp = FrontierDpTable::build(profile);
    let backend = CpuReferenceBackend;
    let mut sks: Vec<FrontierFtsSigningKey> = (0..votes as u32)
        .map(|i| {
            FrontierFtsSigningKey::keygen(
                profile,
                seed32(0x11, i),
                seed32(0x12, i),
                seed32(0x13, i),
                true,
                &backend,
            )
            .attach_wal(Box::new(MemFtsWal::default()))
            .unwrap()
        })
        .collect();
    let pks: Vec<_> = sks.iter().map(|sk| sk.pk.clone()).collect();
    let msgs: Vec<[u8; 64]> = (0..votes)
        .map(|i| {
            let mut m = [0u8; 64];
            m[..8].copy_from_slice(&(i as u64).to_le_bytes());
            m[8..40].copy_from_slice(b"solana.alpenglow.votor.notarize.");
            m
        })
        .collect();

    let t_sign = Instant::now();
    let sigs: Vec<_> = sks
        .iter_mut()
        .zip(msgs.iter())
        .enumerate()
        .map(|(i, (sk, m))| sk.sign(&dp, m, &seed32(0x14, i as u32)).unwrap())
        .collect();
    let sign_ms = t_sign.elapsed().as_secs_f64() * 1_000.0;

    let inputs: Vec<FrontierVerifyInput<'_>> = pks
        .iter()
        .zip(msgs.iter())
        .zip(sigs.iter())
        .map(|((pk, msg), sig)| FrontierVerifyInput {
            pk,
            dp: &dp,
            message: msg,
            signature: sig,
        })
        .collect();
    let t_ver = Instant::now();
    let verdicts = verify_frontier_fts_batch(&inputs);
    let ver_ms = t_ver.elapsed().as_secs_f64() * 1_000.0;
    assert!(verdicts.iter().all(Result::is_ok));
    let sig_bytes = 2 + sigs[0].randomizer.len() + sigs[0].chain_values.len();
    println!(
        "[Votor Compact1122] votes={votes} sig_bytes={sig_bytes} sign_total_ms={sign_ms:.2} batch_verify_ms={ver_ms:.2}"
    );
}

fn run_hem_finality_section(shards: usize, per_shard: usize) {
    let epoch_floor = 42_000_000u64;
    let checkpoint_msg = b"solana.alpenglow.finality.slot.42000000";
    let mut key_groups: Vec<Vec<ValidatorKeypair>> = Vec::with_capacity(shards);
    let mut policies = Vec::with_capacity(shards);
    for s in 0..shards {
        let kps: Vec<ValidatorKeypair> = (0..per_shard as u32)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(
                    AggSigProfile::JortsPoseidon2,
                    &seed32(0x50 + s as u8, i),
                    i,
                )
            })
            .collect();
        policies.push(ShardHemPolicy {
            shard_id: (s + 1) as u64,
            custodian_cluster: seed32(0x88, s as u32),
            quorum_keys: kps.iter().map(|kp| kp.pk).collect(),
            minimum_quorums: (per_shard * 2).div_ceil(3),
        });
        key_groups.push(kps);
    }

    let prepared = PreparedPolicyRegistry::new(policies.clone()).unwrap();
    let reg_root = prepared.policy_registry_root();
    let mut bitmaps = Vec::with_capacity(shards);
    let mut sig_groups: Vec<Vec<ValidatorSignature>> = Vec::with_capacity(shards);
    for (s, kps) in key_groups.iter_mut().enumerate() {
        let region_msg =
            hierarchical_hem_message(&reg_root, &policies[s], epoch_floor, checkpoint_msg);
        let active: Vec<usize> = (0..per_shard).collect();
        bitmaps.push(SignerBitmap::from_active_indices(per_shard as u32, &active).unwrap());
        let sigs: Vec<_> = kps
            .iter_mut()
            .map(|kp| {
                let mut wal = MemEpochWal::default();
                kp.sign_stateful(&region_msg, 0, &mut wal).unwrap()
            })
            .collect();
        sig_groups.push(sigs);
    }

    let s0_msg = hierarchical_hem_message(&reg_root, &policies[0], epoch_floor, checkpoint_msg);
    let s0_mode = SigningMode::SharedMessage(&s0_msg);
    let t_s0 = Instant::now();
    let s0_proof = prove_hem_quintic_128(
        HemQuinticProfile::TurboShake400,
        &policies[0].quorum_keys,
        &bitmaps[0],
        &s0_mode,
        &sig_groups[0],
    )
    .unwrap();
    let s0_prove_ms = t_s0.elapsed().as_secs_f64() * 1_000.0;
    assert!(verify_hem_quintic_128(
        HemQuinticProfile::TurboShake400,
        &policies[0].quorum_keys,
        &s0_mode,
        &s0_proof
    ));

    let witnesses: Vec<ShardHemWitness<'_>> = bitmaps
        .iter()
        .zip(sig_groups.iter())
        .map(|(bm, sigs)| ShardHemWitness {
            bitmap: bm,
            signatures: sigs,
        })
        .collect();
    let min_global: usize = policies.iter().map(|p| p.minimum_quorums).sum();
    let t_joint = Instant::now();
    let cert = prove_hierarchical_hem_prepared(
        &prepared,
        &witnesses,
        epoch_floor,
        checkpoint_msg,
        min_global,
        HemQuinticProfile::TurboShake400,
    )
    .unwrap();
    let joint_ms = t_joint.elapsed().as_secs_f64() * 1_000.0;
    let wire = cert.to_bytes();
    let decoded = HierarchicalHemAggregate::from_bytes_canonical(&wire).unwrap();

    let ver_mc_ms = {
        let t = Instant::now();
        assert!(verify_hierarchical_hem_prepared(
            &prepared,
            epoch_floor,
            checkpoint_msg,
            min_global,
            HemQuinticProfile::TurboShake400,
            &decoded,
        ));
        t.elapsed().as_secs_f64() * 1_000.0
    };
    let ver_1c_ms = with_worker_limit(1, || {
        let t = Instant::now();
        assert!(verify_hierarchical_hem_prepared(
            &prepared,
            epoch_floor,
            checkpoint_msg,
            min_global,
            HemQuinticProfile::TurboShake400,
            &decoded,
        ));
        t.elapsed().as_secs_f64() * 1_000.0
    });

    println!(
        "[Alpenglow HemQuintic128] shards={shards}x{per_shard} wire={} B s0_prove_ms={s0_prove_ms:.1} \
         joint_prove_ms={joint_ms:.1} verify_mc_ms={ver_mc_ms:.2} verify_1c_ms={ver_1c_ms:.2}",
        wire.len()
    );
}

fn main() {
    println!(
        "=== Solana Alpenglow Quintic Fp5 (`QSAGHQM2` / `QSAGHEM\\x04`, DKT26 < 2^-128 QROM) ==="
    );
    run_votor_fts_section(64);
    run_hem_finality_section(2, 32);
}
