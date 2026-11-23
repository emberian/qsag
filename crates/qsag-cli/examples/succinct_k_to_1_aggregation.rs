//! Succinct $K$-to-$1$ Quintic `Fp5` signature aggregation (`QSAGHQM2`) and regional hierarchy
//! composition (`QSAGHEM\x04`, `qsag-agg`).
//!
//! ```bash
//! cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
//! ```

use qsag_agg::sig::digest4_to_bytes;
use qsag_agg::{
    AggSigProfile, FsWalEpochSink, HemQuinticProfile, HemQuinticProof, SignerBitmap, SigningMode,
    ValidatorKeypair, ValidatorPublicKey, ValidatorSignature, prove_hem_quintic_128,
    verify_hem_quintic_128, verify_individual_signature,
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

    let indices = [0usize, 1, 2, 3, 4, 5, 6, 7];
    let bitmap = SignerBitmap::from_active_indices(validators, &indices).expect("ascending");
    let signatures: Vec<ValidatorSignature> = indices
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
    let raw_bytes: usize = signatures.iter().map(|s| s.to_bytes().len()).sum();

    let started = std::time::Instant::now();
    let proof = prove_hem_quintic_128(
        HemQuinticProfile::TurboShake400,
        &committee,
        &bitmap,
        &mode,
        &signatures,
    )
    .expect("quintic 8-signer aggregate");
    let prove_time = started.elapsed();

    let wire = proof.to_bytes();
    let decoded = HemQuinticProof::from_bytes(&wire).expect("canonical QSAGHQM2 proof");
    assert_eq!(decoded.num_signers(), 8);
    let started = std::time::Instant::now();
    assert!(verify_hem_quintic_128(&committee, &mode, &decoded));
    let verify_time = started.elapsed();
    assert!(!verify_hem_quintic_128(
        &committee,
        &SigningMode::SharedMessage(b"forged header"),
        &decoded
    ));

    let _ = std::fs::remove_dir_all(&wal_dir);
    println!(
        "  [ok] 8-signer QSAGHQM2 Quintic Fp5 proof: {} B on the wire (vs {raw_bytes} B raw), proved in {prove_time:.2?}, verified in {verify_time:.2?}",
        wire.len()
    );
}
