//! Compact few-time signatures, single-signer and threshold (`qsag-fts`).
//!
//! ```bash
//! cargo run --release -p qsag-cli --example few_time_signatures
//! ```
//!
//! 1. `FrontierSumFts`: a 1,058-byte signature, the two-use budget, and a wire round trip.
//! 2. `ParallelSeededFts`: three parties sign under one public key without reconstructing it,
//!    with a durable burn journal that refuses to spend an epoch twice, even after a restart.

#[allow(dead_code)]
#[path = "../src/dealerless_ceremony.rs"]
mod dealerless_ceremony;

use qsag_accel::CpuReferenceBackend;
use qsag_fts::{
    FrontierDpTable, FrontierFtsError, FrontierFtsProfile, FrontierFtsSignature,
    FrontierFtsSigningKey, FsWalFtsEpochLatch, ParallelSeededError, ParallelSeededParams,
    ParallelSeededSignature, verify_frontier_fts, verify_parallel_seeded_fts,
};

fn main() {
    println!("=== 1. FrontierSumFts (single signer, one signature per key) ===");
    let profile = FrontierFtsProfile::Full256Bit;
    let table = FrontierDpTable::build(profile);
    let mut key = FrontierFtsSigningKey::keygen(
        profile,
        [1; 32],
        [2; 32],
        [3; 32],
        true,
        &CpuReferenceBackend,
    );
    let journal_path = std::env::temp_dir().join(format!(
        "qsag-frontier-check-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let wal = qsag_fts::FsWalFtsEpochLatch::create(&journal_path, key.wal_key(), [0x91; 32])
        .expect("create fresh test journal");
    key = key.attach_wal(Box::new(wal)).expect("attach test journal");
    let first = key
        .sign(&table, b"first message", &[0x10; 32])
        .expect("first use");
    let wire = first.to_bytes(profile);
    assert_eq!(wire.len(), profile.signature_bytes());
    let decoded = FrontierFtsSignature::from_bytes(profile, &wire).expect("exact-length signature");
    assert_eq!(
        verify_frontier_fts(&key.pk, &table, b"first message", &decoded),
        Ok(())
    );
    assert!(verify_frontier_fts(&key.pk, &table, b"another message", &decoded).is_err());
    assert!(key.sign(&table, b"second message", &[0x11; 32]).is_err());
    assert_eq!(
        key.sign(&table, b"third message", &[0x12; 32]).err(),
        Some(FrontierFtsError::UseBudgetExhausted)
    );
    println!(
        "  [ok] {}-byte signature verified; third signature refused",
        wire.len()
    );

    drop(key);
    std::fs::remove_file(journal_path).expect("remove own test journal");

    println!("\n=== 2. ParallelSeededFts (three-party threshold, one signature per epoch) ===");
    let params = ParallelSeededParams {
        tree_height: 2,
        winternitz_w: 5,
        num_chains: 68,
        target_sum: 136,
    };
    let mut setup =
        dealerless_ceremony::DealerlessThresholdFtsSetup::run_ceremony(params, 3, [0x21; 32], None)
            .expect("valid parameters");
    let public_key = setup.pk.clone();
    let cached_layers = setup.public_tree_layers.clone();

    let journal_path =
        std::env::temp_dir().join(format!("qsag-example-burn-{}", std::process::id()));
    let journal_key = [0x23; 32];
    let mut journal =
        FsWalFtsEpochLatch::create(&journal_path, public_key.pk_seed_bytes, journal_key)
            .expect("fresh burn journal");
    let signature = setup
        .threshold_sign(1, b"settle batch 41", [0x24; 32], &mut journal)
        .expect("three parties sign at epoch 1");
    let wire = signature.to_bytes();
    let decoded =
        ParallelSeededSignature::from_bytes_canonical(&params, &wire).expect("canonical signature");
    assert_eq!(
        verify_parallel_seeded_fts(
            &public_key,
            b"settle batch 41",
            &decoded,
            &CpuReferenceBackend
        ),
        Ok(())
    );
    assert!(
        verify_parallel_seeded_fts(
            &public_key,
            b"settle batch 42",
            &decoded,
            &CpuReferenceBackend
        )
        .is_err()
    );

    // Restart: a new process rebuilds its shares and reopens the journal. Epoch 1 stays spent.
    drop(journal);
    let mut restarted = dealerless_ceremony::DealerlessThresholdFtsSetup::run_ceremony(
        params,
        3,
        [0x21; 32],
        Some((public_key.clone(), cached_layers)),
    )
    .expect("valid parameters");
    let mut journal =
        FsWalFtsEpochLatch::open(&journal_path, public_key.pk_seed_bytes, journal_key)
            .expect("authentic burn journal");
    assert_eq!(
        restarted
            .threshold_sign(1, b"settle batch 42", [0x25; 32], &mut journal)
            .err(),
        Some(ParallelSeededError::PersistenceFailed)
    );
    drop(journal);
    let _ = std::fs::remove_file(&journal_path);
    let mut lock = journal_path.into_os_string();
    lock.push(".lock");
    let _ = std::fs::remove_file(lock);
    println!(
        "  [ok] {}-byte threshold signature verified; epoch reuse refused after restart",
        wire.len()
    );
}
