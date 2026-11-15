//! Succinct K-to-1 signature aggregation and 2-to-1 merging (`qsag-agg`).
//!
//! ```bash
//! cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
//! ```
//!
//! 1. Eight validators enroll a durable epoch write-ahead log and sign one block header in two
//!    disjoint shards, each epoch being persisted before its signature is computed.
//! 2. Each shard's signatures are aggregated into one proof (`aggregate_signatures`).
//! 3. The two proofs are merged (`merge_aggregates`), serialized, decoded strictly, and verified
//!    without any individual signature; a forged header and overlapping signer sets are refused.

use qsag_agg::sig::digest4_to_bytes;
use qsag_agg::{
    AggSigProfile, FsWalEpochSink, HemAggregatedProof, SignerBitmap, SigningMode, ValidatorKeypair,
    ValidatorPublicKey, ValidatorSignature, aggregate_signatures, merge_aggregates,
    verify_aggregate, verify_individual_signature,
};

fn main() {
    let validators = 8u32;
    let epoch = 0u32;
    let header = b"consensus::slot=1048576::state_root=0x9f8e7d6c5b4a3928";
    let mode = SigningMode::SharedMessage(header);
    let wal_dir = std::env::temp_dir().join(format!("qsag-example-agg-{}", std::process::id()));
    std::fs::create_dir_all(&wal_dir).expect("temporary directory");

    let mut keys: Vec<ValidatorKeypair> = (0..validators)
        .map(|i| {
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[0xA5; 32], i)
        })
        .collect();
    let committee: Vec<ValidatorPublicKey> = keys.iter().map(|k| k.pk).collect();

    let mut sign_shard = |indices: &[usize]| -> (SignerBitmap, Vec<ValidatorSignature>) {
        let bitmap =
            SignerBitmap::from_active_indices(validators, indices).expect("ascending indices");
        let signatures = indices
            .iter()
            .map(|&i| {
                let root = digest4_to_bytes(&keys[i].pk.pk_root);
                let wal_path = wal_dir.join(format!("validator-{i}.wal"));
                let (mut wal, _) =
                    FsWalEpochSink::create_new_for_fresh_key(wal_path, &root, [0x40 + i as u8; 32])
                        .expect("fresh write-ahead log");
                let signature = keys[i]
                    .sign_stateful_with_wal(header, epoch, &mut wal)
                    .expect("epoch is persisted, then signed");
                assert!(verify_individual_signature(
                    &committee[i],
                    header,
                    &signature
                ));
                signature
            })
            .collect();
        (bitmap, signatures)
    };
    let (bitmap_a, signatures_a) = sign_shard(&[0, 1, 2, 5]);
    let (bitmap_b, signatures_b) = sign_shard(&[3, 4, 6, 7]);
    let raw_bytes: usize = signatures_a
        .iter()
        .chain(&signatures_b)
        .map(|s| s.to_bytes().len())
        .sum();

    let started = std::time::Instant::now();
    let proof_a = aggregate_signatures(&committee, &bitmap_a, &mode, &signatures_a, [0x31; 32])
        .expect("shard A");
    let proof_b = aggregate_signatures(&committee, &bitmap_b, &mode, &signatures_b, [0x32; 32])
        .expect("shard B");
    let prove_time = started.elapsed();
    assert!(verify_aggregate(&committee, &mode, &proof_a));
    assert!(verify_aggregate(&committee, &mode, &proof_b));
    println!(
        "  [ok] two 4-signer shards aggregated in {prove_time:.2?}: {} B and {} B",
        proof_a.to_bytes().len(),
        proof_b.to_bytes().len()
    );

    let merged =
        merge_aggregates(&committee, &mode, &proof_a, &proof_b).expect("disjoint signer sets");
    let wire = merged.to_bytes();
    let decoded = HemAggregatedProof::from_bytes_canonical(&wire).expect("canonical proof");
    assert_eq!(decoded.num_signers(), 8);
    let started = std::time::Instant::now();
    assert!(verify_aggregate(&committee, &mode, &decoded));
    let verify_time = started.elapsed();
    assert!(!verify_aggregate(
        &committee,
        &SigningMode::SharedMessage(b"forged header"),
        &decoded
    ));
    assert!(
        merge_aggregates(&committee, &mode, &proof_a, &merged).is_err(),
        "overlapping signers"
    );

    let _ = std::fs::remove_dir_all(&wal_dir);
    println!(
        "  [ok] merged proof for 8 signers: {} B on the wire, verified in {verify_time:.2?} ({raw_bytes} B of raw signatures)",
        wire.len()
    );
}
