//! Solana Alpenglow `400 ms` Rotor & Notarization Slot Benchmark (`qsag`).
//!
//! Benchmarks the three post-quantum primitives relevant to a 1,000-validator Alpenglow slot:
//! 1. **Sub-MTU `FrontierSumFts` (`Compact514` = `514 B`, `Compact770` = `770 B`) Rotor Votes**:
//!    Fits a complete 128-bit PQ notarization vote inside a single 1,280-byte QUIC/UDP MTU packet
//!    and compares parallel verification of 1,000 validator votes with the `400 ms` slot budget.
//! 2. **`QS-A` 3-of-5 Distributed Validator (`IsolatedJortsParty`) Hot-Path**:
//!    Runs 3 isolated custodian nodes over framed `InMemoryWireMesh` channels (`MemoryWal` latch +
//!    pairwise MAC echo barrier + zero-secret-hash additive WOTS+C share opening).
//! 3. **`Hem` Succinct Finality Checkpoint Proof (`JortsPoseidon2`)**:
//!    Compresses stateful validator checkpoint signatures into a succinct `GoldilocksExt4` WHIR
//!    proof (`Habr24Classical128` + `Habr24Qrom128` comparison) with millisecond verification.

use std::time::Instant;

use qsag_accel::CpuReferenceBackend;
use qsag_agg::{
    AggSigProfile, EpochWalSink, HemAggConfig, SigError, SignerBitmap, SigningMode,
    ValidatorKeypair, ValidatorPublicKey, ValidatorSignature, WhirSecurityRegime,
    aggregate_signatures_with_config, verify_aggregate_with_regime,
};
use qsag_core::belt_latch::{BeltLatchRecord, BeltLatchState, DurableWal, WalError};
use qsag_fts::{
    FrontierDpTable, FrontierFtsProfile, FrontierFtsPublicKey, FrontierFtsSignature,
    FrontierFtsSigningKey, FsWalFtsEpochLatch, verify_frontier_fts,
};
use qsag_quorum::party_node::IsolatedJortsParty;
use qsag_quorum::quorum_jorts::{
    CommitteeCustodian, quorum_jorts_verify, stage_committee_partitioned,
};
use qsag_quorum::wire_channel::InMemoryWireMesh;

#[derive(Clone, Debug, Default)]
struct BenchBeltWal {
    stored: Option<Vec<u8>>,
}

impl DurableWal for BenchBeltWal {
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

type EpochReceipt = (u32, u32, [u8; 32]);

#[derive(Default)]
struct BenchEpochWal {
    state: Option<([u8; 32], EpochReceipt)>,
}

impl EpochWalSink for BenchEpochWal {
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

fn seed32(tag: u8, idx: u32) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0] = tag;
    out[1..5].copy_from_slice(&idx.to_le_bytes());
    for (i, b) in out[5..].iter_mut().enumerate() {
        *b = tag
            .wrapping_mul(37)
            .wrapping_add((idx as u8).wrapping_mul(13))
            .wrapping_add(i as u8);
    }
    out
}

fn bench_alpenglow_sub_mtu_rotor_votes(num_validators: usize, workers: usize) {
    let profile = FrontierFtsProfile::Compact514;
    let dp = FrontierDpTable::build(profile);
    let slot_msg = b"solana.alpenglow.notarize.slot.42000000.blockhash.9f8e7d6c5b4a3210";

    // These deterministic benchmark keys are disposable fixtures. Exercise the
    // production reservation path with fresh, exclusively created journals.
    let run_id = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock")
        .as_nanos();
    let wal_dir =
        std::env::temp_dir().join(format!("qsag-alpenglow-{}-{run_id}", std::process::id()));
    std::fs::create_dir(&wal_dir).expect("create fresh benchmark journal directory");
    let t_keygen = Instant::now();
    let chunk = num_validators.div_ceil(workers);
    let key_batches: Vec<Vec<(FrontierFtsPublicKey, FrontierFtsSignature)>> =
        std::thread::scope(|scope| {
            let dp_ref = &dp;
            let wal_dir_ref = &wal_dir;
            let handles: Vec<_> = (0..workers)
                .filter_map(|w_idx| {
                    let start = w_idx * chunk;
                    (start < num_validators).then(|| {
                        let end = (start + chunk).min(num_validators);
                        scope.spawn(move || {
                            let accel = CpuReferenceBackend::new();
                            let mut out = Vec::with_capacity(end - start);
                            for idx in start..end {
                                let u = idx as u32;
                                let sk = FrontierFtsSigningKey::keygen(
                                    profile,
                                    seed32(0xA1, u),
                                    seed32(0xB2, u),
                                    seed32(0xC3, u),
                                    true,
                                    &accel,
                                );
                                let wal = FsWalFtsEpochLatch::create(
                                    wal_dir_ref.join(format!("validator-{idx}.wal")),
                                    sk.wal_key(),
                                    seed32(0xE5, u),
                                )
                                .expect("create validator use journal");
                                let mut sk = sk
                                    .attach_wal(Box::new(wal))
                                    .expect("attach validator use journal");
                                let hedge = seed32(0xD4, u);
                                let sig = sk
                                    .sign(dp_ref, slot_msg, &hedge)
                                    .expect("fresh Compact514 key signs slot vote");
                                out.push((sk.pk.clone(), sig));
                            }
                            out
                        })
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().expect("rotor worker panicked"))
                .collect()
        });
    let setup_ms = t_keygen.elapsed().as_secs_f64() * 1_000.0;

    let votes: Vec<(FrontierFtsPublicKey, FrontierFtsSignature)> =
        key_batches.into_iter().flatten().collect();
    assert_eq!(votes.len(), num_validators);
    let wire_bytes = votes[0].1.to_bytes(profile).len();
    assert_eq!(wire_bytes, 514);

    // Measure single-validator sign latency on a warm cached key.
    let accel = CpuReferenceBackend::new();
    let warm_sk = FrontierFtsSigningKey::keygen(
        profile,
        seed32(0xE1, 9_999),
        seed32(0xE2, 9_999),
        seed32(0xE3, 9_999),
        true,
        &accel,
    );
    let warm_wal = FsWalFtsEpochLatch::create(
        wal_dir.join("warm-validator.wal"),
        warm_sk.wal_key(),
        seed32(0xE5, 9_999),
    )
    .expect("create warm validator use journal");
    let mut warm_sk = warm_sk
        .attach_wal(Box::new(warm_wal))
        .expect("attach warm validator use journal");
    let t_sign = Instant::now();
    let warm_sig = warm_sk
        .sign(&dp, slot_msg, &seed32(0xE4, 9_999))
        .expect("warm sign");
    let single_sign_us = t_sign.elapsed().as_secs_f64() * 1_000_000.0;
    verify_frontier_fts(&warm_sk.pk, &dp, slot_msg, &warm_sig).expect("warm vote verifies");
    drop(warm_sk);
    std::fs::remove_dir_all(&wal_dir).expect("remove completed benchmark journals");

    // Measure parallel verification of all 1,000 Alpenglow rotor notarization votes!
    let t_verify = Instant::now();
    std::thread::scope(|scope| {
        let dp_ref = &dp;
        for batch in votes.chunks(chunk) {
            scope.spawn(move || {
                for (pk, sig) in batch {
                    verify_frontier_fts(pk, dp_ref, slot_msg, sig)
                        .expect("Alpenglow notarization vote must verify");
                }
            });
        }
    });
    let batch_verify_ms = t_verify.elapsed().as_secs_f64() * 1_000.0;

    println!(
        "[1/3] Rotor Notarization Votes (`FrontierSumFts::Compact514`, N={num_validators} validators):"
    );
    println!(
        "      vote_wire = {wire_bytes} B (< 1280 B QUIC MTU; Compact770 2-use = {} B) | warm_sign = {single_sign_us:.1} us",
        FrontierFtsProfile::Compact770.signature_bytes()
    );
    println!(
        "      verify_{num_validators}_votes_parallel = {batch_verify_ms:.2} ms (budget: 400.00 ms, {:.1}x headroom) | setup = {setup_ms:.1} ms",
        400.0 / batch_verify_ms.max(0.001)
    );
    // Timing is informational: shared-host load and core count affect the slot budget.
    // Every signature above is still required to verify.
}

fn bench_alpenglow_qsa_dvt_hot_path() {
    let seed = seed32(0x77, 0);
    let staged =
        stage_committee_partitioned(3, 5, 7, &seed).expect("stage 3-of-5 QS-A DVT committee");
    let pk = *staged.tree.public_key();
    let layout = staged.layout.clone();
    let tree = staged.tree.clone();

    let (endpoints, stats) = InMemoryWireMesh::connect(5, seed32(0x88, 1));
    let mut custodians: Vec<Option<IsolatedJortsParty<_, BenchBeltWal>>> = staged
        .parties
        .into_iter()
        .zip(endpoints)
        .map(|(mat, ep)| {
            let wals = (0..mat.stores.len())
                .map(|_| BenchBeltWal::default())
                .collect();
            let cust = CommitteeCustodian::new(layout.clone(), tree.clone(), mat, wals)
                .expect("build CommitteeCustodian");
            Some(IsolatedJortsParty::new(cust, ep).expect("build IsolatedJortsParty"))
        })
        .collect();

    // Committee 0 is `{0, 1, 2}`: run 8 consecutive slot votes to measure steady-state DVT latency.
    let p2 = custodians[2].take().expect("party 2");
    let p1 = custodians[1].take().expect("party 1");
    let p0 = custodians[0].take().expect("party 0");
    let mut active = [p0, p1, p2];

    let rounds = 8u64;
    assert!(rounds <= layout.leaves_per_committee());
    let mut last_sig = None;
    let t_dvt = Instant::now();
    for epoch in 0..rounds {
        let mut msg = Vec::from(&b"solana.alpenglow.dvt.vote.epoch."[..]);
        msg.extend_from_slice(&epoch.to_le_bytes());
        let msg_ref = msg.as_slice();
        let sigs: Vec<_> = std::thread::scope(|scope| {
            let handles: Vec<_> = active
                .iter_mut()
                .map(|party| {
                    scope.spawn(move || {
                        party
                            .sign(0, epoch, msg_ref)
                            .expect("QS-A 3-of-5 isolated signing")
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().expect("DVT party thread panicked"))
                .collect()
        });
        assert_eq!(sigs[0], sigs[1]);
        assert_eq!(sigs[1], sigs[2]);
        assert!(quorum_jorts_verify(&pk, msg_ref, &sigs[0]));
        last_sig = Some(sigs.into_iter().next().unwrap());
    }
    let avg_dvt_sign_us = (t_dvt.elapsed().as_secs_f64() * 1_000_000.0) / (rounds as f64);
    let sig = last_sig.expect("at least one DVT signature");

    let mut verify_msg = Vec::from(&b"solana.alpenglow.dvt.vote.epoch."[..]);
    verify_msg.extend_from_slice(&(rounds - 1).to_le_bytes());
    let t_ver = Instant::now();
    for _ in 0..100 {
        assert!(quorum_jorts_verify(&pk, &verify_msg, &sig));
    }
    let avg_verify_us = (t_ver.elapsed().as_secs_f64() * 1_000_000.0) / 100.0;
    let wire_per_sign = stats.total_bytes() / rounds;

    println!("[2/3] DVT Validator Hot-Path (`QS-A` 3-of-5 `IsolatedJortsParty` over framed mesh):");
    println!(
        "      3_of_5_sign = {avg_dvt_sign_us:.1} us | verify = {avg_verify_us:.1} us | sig_wire = {} B | mesh_traffic/slot = {wire_per_sign} B",
        sig.wire_bytes()
    );
}

fn bench_alpenglow_hem_checkpoint(num_signers: usize, workers: usize) {
    let master_seed = seed32(0x99, 42);
    let msg = b"solana.alpenglow.finality.checkpoint.slot.42000000";
    let chunk = num_signers.div_ceil(workers);
    let signer_batches: Vec<Vec<(ValidatorPublicKey, ValidatorSignature)>> =
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers)
                .filter_map(|w_idx| {
                    let start = w_idx * chunk;
                    (start < num_signers).then(|| {
                        let end = (start + chunk).min(num_signers);
                        scope.spawn(move || {
                            let mut out = Vec::with_capacity(end - start);
                            for idx in start..end {
                                let mut kp = ValidatorKeypair::keygen_deterministic(
                                    AggSigProfile::JortsPoseidon2,
                                    &master_seed,
                                    idx as u32,
                                );
                                let mut wal = BenchEpochWal::default();
                                let sig = kp
                                    .sign_stateful(msg, 0, &mut wal)
                                    .expect("stateful JortsPoseidon2 checkpoint sign");
                                out.push((kp.pk, sig));
                            }
                            out
                        })
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().expect("checkpoint keygen worker panicked"))
                .collect()
        });

    let mut pks = Vec::with_capacity(num_signers);
    let mut sigs = Vec::with_capacity(num_signers);
    for (pk, sig) in signer_batches.into_iter().flatten() {
        pks.push(pk);
        sigs.push(sig);
    }
    let active_indices: Vec<usize> = (0..num_signers).collect();
    let bitmap =
        SignerBitmap::from_active_indices(num_signers as u32, &active_indices).expect("bitmap");

    for regime in [
        WhirSecurityRegime::Habr24Classical128,
        WhirSecurityRegime::Habr24Qrom128,
    ] {
        let mut cfg = HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, seed32(0xAA, 7));
        cfg.regime = regime;
        let t_prove = Instant::now();
        let proof = aggregate_signatures_with_config(
            &pks,
            &bitmap,
            &SigningMode::SharedMessage(msg),
            &sigs,
            &cfg,
        )
        .expect("Hem checkpoint aggregation");
        let prove_ms = t_prove.elapsed().as_secs_f64() * 1_000.0;
        let proof_bytes = proof.to_bytes();

        let t_ver = Instant::now();
        let ok =
            verify_aggregate_with_regime(&pks, &SigningMode::SharedMessage(msg), &proof, regime);
        let verify_ms = t_ver.elapsed().as_secs_f64() * 1_000.0;
        assert!(ok, "Hem checkpoint proof failed verification");

        println!(
            "[3/3] `Hem` Finality Checkpoint (`JortsPoseidon2`, K={num_signers}, regime={regime:?}):"
        );
        println!(
            "      prove = {prove_ms:.2} ms | verify = {verify_ms:.2} ms | proof_wire = {} B ({:.1} KiB)",
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0
        );
    }
}

fn main() {
    let workers = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    println!("========================================================================");
    println!(" QSAG x Solana Alpenglow (400 ms Slot Budget) Benchmark (threads={workers})");
    println!("========================================================================");
    bench_alpenglow_sub_mtu_rotor_votes(1_000, workers);
    bench_alpenglow_qsa_dvt_hot_path();
    bench_alpenglow_hem_checkpoint(64, workers);
}
