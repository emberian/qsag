//! Compact few-time signatures, with a durable use counter (`qsag-fts`).
//!
//! ```bash
//! cargo run --release -p qsag-cli --example few_time_signatures
//! ```
//!
//! Sign with the 1,122-byte Compact1122 profile, enforce
//! the one-use budget, and verify a wire round trip.
use qsag_accel::CpuReferenceBackend;
use qsag_fts::{
    FrontierDpTable, FrontierFtsError, FrontierFtsProfile, FrontierFtsSignature,
    FrontierFtsSigningKey, verify_frontier_fts,
};

fn main() {
    println!("=== 1. FrontierSumFts (single signer, one signature per key) ===");
    let profile = FrontierFtsProfile::Compact1122;
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
        "  [ok] {}-byte signature verified; further signatures refused",
        wire.len()
    );

    drop(key);
    std::fs::remove_file(journal_path).expect("remove own test journal");
}
