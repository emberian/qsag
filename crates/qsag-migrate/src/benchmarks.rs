//! Opt-in full-profile wall-clock benchmarks. No repetitions or checks are skipped.
use crate::*;
use qsag_accel::CpuReferenceBackend;
use std::time::Instant;

/// The length-framed encoding used by the existing proof parity benchmark:
/// root; then challenge, two (seed, three u64-length-prefixed vectors), hidden
/// commitment and u64-length-prefixed hidden outputs for each repetition.
pub(crate) fn proof_bytes(p: &zk_engine::MigrationZkProof) -> usize {
    32 + p
        .repetitions
        .iter()
        .map(|r| {
            1 + r
                .pair
                .iter()
                .map(|v| 32 + 24 + v.inputs.len() + v.products.len() + v.outputs.len())
                .sum::<usize>()
                + 32
                + 8
                + r.hidden_outputs.len()
        })
        .sum::<usize>()
}

#[test]
#[ignore = "full-profile four-curve local migration wall-clock benchmark"]
fn local_four_curve_benchmark() {
    let backend = CpuReferenceBackend;
    let mut key = [0; 32];
    key[31] = 1;
    let witness = LegacyOwnershipWitness::from_raw_secret(key);
    for (label, kind) in [
        ("secp256k1", witness.compute_bitcoin_hash160().unwrap()),
        ("Ed25519", witness.compute_slip0010_commitment()),
    ] {
        let start = Instant::now();
        let (statement, proof) = zk_engine::prove_migration_in_domain(
            &witness,
            zk_engine::tests::request(kind),
            [31; 32],
            &backend,
        )
        .unwrap();
        let prove = start.elapsed();
        let start = Instant::now();
        zk_engine::verify_migration_proof(
            &statement,
            &proof,
            &statement.migration_domain,
            statement.epoch_anchor,
        )
        .unwrap();
        std::eprintln!(
            "BENCH local {label} repetitions={} prove_ns={} verify_ns={} proof_bytes={}",
            proof.repetitions.len(),
            prove.as_nanos(),
            start.elapsed().as_nanos(),
            proof_bytes(&proof)
        );
    }
    let target = zk_engine::tests::request(witness.compute_slip0010_commitment()).target;
    let mut scalar = [0; 32];
    scalar[0] = 0x37;
    let witness = PallasOwnershipWitness::from_spend_auth_scalar_le(scalar).unwrap();
    let request = PallasMigrationRequest {
        commitment: witness.compute_spend_auth_key().unwrap(),
        target: target.clone(),
        epoch: 77,
        domain: [0x51; 32],
    };
    let start = Instant::now();
    let (statement, proof) =
        prove_pallas_migration_in_domain(&witness, request, [31; 32], &backend).unwrap();
    let prove = start.elapsed();
    let start = Instant::now();
    verify_pallas_migration(
        &statement,
        &proof,
        &statement.migration_domain,
        statement.epoch_anchor,
    )
    .unwrap();
    std::eprintln!(
        "BENCH local Pallas repetitions={} prove_ns={} verify_ns={} proof_bytes={}",
        proof.repetitions.len(),
        prove.as_nanos(),
        start.elapsed().as_nanos(),
        proof_bytes(&proof)
    );
    let witness = BlsOwnershipWitness::from_secret_scalar_le(scalar).unwrap();
    let mut credentials = [0x44; 32];
    credentials[..12].fill(0);
    credentials[0] = 1;
    let request = BlsMigrationRequest {
        commitment: witness.compute_beacon_commitment().unwrap(),
        validator_index: 42,
        withdrawal_credentials: credentials,
        target,
        epoch: 77,
        domain: [0x52; 32],
    };
    let start = Instant::now();
    let (statement, proof) =
        prove_bls_migration_in_domain(&witness, request, [31; 32], &backend).unwrap();
    let prove = start.elapsed();
    let start = Instant::now();
    verify_bls_migration(
        &statement,
        &proof,
        &statement.migration_domain,
        statement.epoch_anchor,
    )
    .unwrap();
    std::eprintln!(
        "BENCH local BLS12-381 repetitions={} prove_ns={} verify_ns={} proof_bytes={}",
        proof.repetitions.len(),
        prove.as_nanos(),
        start.elapsed().as_nanos(),
        proof_bytes(&proof)
    );
}
