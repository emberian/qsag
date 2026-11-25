//! Succinct $K$-to-$1$ Quintic `Fp5` signature aggregation over one block header (`QSAGHQM2` and regional composition).
//!
//! ```bash
//! cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
//! ```

use qsag_agg::sig::digest4_to_bytes;
use qsag_agg::{
    AggSigProfile, FsStatelessBudgetWal, FsWalEpochSink, HemQuinticProfile, HemQuinticProof,
    HierarchicalHemAggregate, PreparedPolicyRegistry, ShardHemPolicy, ShardHemWitness,
    SignerBitmap, SigningMode, ValidatorKeypair, ValidatorSignature, hierarchical_hem_message,
    prove_hem_quintic_128, prove_hierarchical_hem_prepared, verify_hem_quintic_128,
    verify_hierarchical_hem_prepared, verify_individual_signature,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let validators: u32 = match args.as_slice() {
        [] => 128,
        [flag] if flag == "--help" || flag == "-h" => {
            println!("Usage: succinct_k_to_1_aggregation [--signers <N>] (default 128)");
            return Ok(());
        }
        [flag, n] if flag == "--signers" => n.parse()?,
        _ => return Err("expected --signers <N>".into()),
    };
    // One Corduroy committee member per eight Jorts-sized slots in the mixed fixture.
    // Small runs retain the original single-region Jorts example.
    let corduroy = if validators > 8 { validators / 8 } else { 0 };
    let jorts = validators - corduroy;
    if validators == 0 || corduroy > 128 || jorts > 2048 {
        return Err("committee exceeds the quintic proof schedule, or has no signers".into());
    }
    let header = b"consensus::slot=1048576::state_root=0x9f8e7d6c5b4a3928";
    let wal_dir = std::env::temp_dir().join(format!("qsag-example-agg-{}", std::process::id()));
    std::fs::create_dir(&wal_dir)?;

    let groups = [
        (AggSigProfile::JortsPoseidon2, jorts),
        (AggSigProfile::CorduroyPoseidon2, corduroy),
    ];
    let mut keys: Vec<Vec<_>> = groups
        .into_iter()
        .filter(|(_, n)| *n > 0)
        .map(|(profile, n)| {
            (0..n)
                .map(|i| ValidatorKeypair::keygen_deterministic(profile, &[0xA5; 32], i))
                .collect()
        })
        .collect();
    let policies = keys
        .iter()
        .enumerate()
        .map(|(i, keys)| ShardHemPolicy {
            shard_id: i as u64,
            custodian_cluster: [i as u8 + 1; 32],
            quorum_keys: keys.iter().map(|k| k.pk).collect(),
            minimum_quorums: keys.len(),
        })
        .collect();
    let registry = PreparedPolicyRegistry::new(policies).expect("valid committees");
    let mut signatures = Vec::new();
    let mut bitmaps = Vec::new();
    for (region, (keys, policy)) in keys.iter_mut().zip(registry.policies()).enumerate() {
        let message = if corduroy == 0 {
            header.to_vec()
        } else {
            hierarchical_hem_message(&registry.policy_registry_root(), policy, 0, header).to_vec()
        };
        let active: Vec<_> = (0..keys.len()).collect();
        bitmaps.push(
            SignerBitmap::from_active_indices(keys.len() as u32, &active)
                .expect("ordered committee"),
        );
        let mut signed = Vec::with_capacity(keys.len());
        for (i, key) in keys.iter_mut().enumerate() {
            let root = digest4_to_bytes(&key.pk.pk_root);
            let path = wal_dir.join(format!("{region}-{i}.wal"));
            let mut mac_key = [0; 32];
            qsag_accel::fill_os_random(&mut mac_key)?;
            let sig = if key.pk.profile.is_jorts() {
                let (mut wal, _) = FsWalEpochSink::create_new_for_fresh_key(path, &root, mac_key)
                    .expect("fresh epoch log");
                key.sign_stateful_with_wal(&message, 0, &mut wal)
                    .expect("sign with persisted epoch")
            } else {
                let mut wal = FsStatelessBudgetWal::create_new_for_fresh_key(path, &root, mac_key)
                    .expect("fresh signature budget");
                key.sign_stateless_with_wal(&message, &mut wal)
                    .expect("sign with persisted budget")
            };
            assert!(verify_individual_signature(&key.pk, &message, &sig));
            signed.push(sig);
        }
        signatures.push(signed);
    }
    std::fs::remove_dir_all(wal_dir)?;
    let raw_bytes: usize = signatures
        .iter()
        .flatten()
        .map(ValidatorSignature::to_bytes)
        .map(|s| s.len())
        .sum();
    let profile = HemQuinticProfile::TurboShake400;
    let start = std::time::Instant::now();
    let (format, size, prove_time, verify_time) = if corduroy == 0 {
        let committee = &registry.policies()[0].quorum_keys;
        let proof = prove_hem_quintic_128(
            profile,
            committee,
            &bitmaps[0],
            &SigningMode::SharedMessage(header),
            &signatures[0],
        )
        .expect("quintic proof");
        let elapsed = start.elapsed();
        let wire = proof.to_bytes();
        let decoded = HemQuinticProof::from_bytes(&wire).expect("canonical proof");
        assert_eq!(decoded.num_signers(), validators as usize);
        let start = std::time::Instant::now();
        assert!(verify_hem_quintic_128(
            profile,
            committee,
            &SigningMode::SharedMessage(header),
            &decoded
        ));
        let verified = start.elapsed();
        assert!(!verify_hem_quintic_128(
            profile,
            committee,
            &SigningMode::SharedMessage(b"forged header"),
            &decoded
        ));
        ("QSAGHQM2", wire.len(), elapsed, verified)
    } else {
        let witnesses: Vec<_> = bitmaps
            .iter()
            .zip(&signatures)
            .map(|(bitmap, sigs)| ShardHemWitness {
                bitmap,
                signatures: sigs,
            })
            .collect();
        let proof = prove_hierarchical_hem_prepared(
            &registry,
            &witnesses,
            0,
            header,
            validators as usize,
            profile,
        )
        .expect("regional proof");
        let elapsed = start.elapsed();
        let wire = proof.to_bytes();
        let decoded =
            HierarchicalHemAggregate::from_bytes_canonical(&wire).expect("canonical aggregate");
        assert_eq!(decoded.checked_total_quorums(), Some(validators as usize));
        let verify = |msg: &[u8]| {
            verify_hierarchical_hem_prepared(
                &registry,
                0,
                msg,
                validators as usize,
                profile,
                &decoded,
            )
        };
        let start = std::time::Instant::now();
        assert!(verify(header));
        let verified = start.elapsed();
        assert!(!verify(b"forged header"));
        ("QSAGHEM v4", wire.len(), elapsed, verified)
    };
    if validators == 128 {
        assert!(
            size < raw_bytes,
            "default aggregate must compress the raw signatures"
        );
    }
    println!(
        "{validators} signers ({jorts} Jorts, {corduroy} Corduroy), {format}: {size} B on wire vs {raw_bytes} B raw, proved in {prove_time:.2?}, verified in {verify_time:.2?}"
    );
    Ok(())
}
