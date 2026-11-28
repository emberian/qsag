//! Single-trial CPU comparison using the same signed, threshold-one committees.
use super::*;
use crate::sig::{AggSigProfile, ValidatorKeypair};
use crate::zk_hem::multisig::{MultisigSigner, Policy};
use std::time::Instant;

fn measure(
    counts: &[u32],
    mut run: impl FnMut(&IvcPolicyRegistry, [u8; 32], &[IvcShard<'_>]) -> (f64, f64, usize),
) {
    for &n in counts {
        let mut keys: Vec<_> = (0..n)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[41; 32], i)
            })
            .collect();
        let entries: Vec<_> = keys
            .iter()
            .enumerate()
            .map(|(i, k)| (i as u64, Policy::new(vec![k.pk], 1, 8).unwrap()))
            .collect();
        let reg = IvcPolicyRegistry::new(&entries).unwrap();
        let digest = [145; 32];
        let signatures: Vec<_> = keys
            .iter_mut()
            .enumerate()
            .map(|(i, k)| {
                [MultisigSigner {
                    member_index: 0,
                    signature: k
                        .sign_stateful_for_unit_test(
                            &ivc_signing_message(reg.root(), i as u64, digest),
                            0,
                        )
                        .unwrap(),
                }]
            })
            .collect();
        let shards: Vec<_> = entries
            .iter()
            .zip(&signatures)
            .map(|((id, policy), s)| IvcShard {
                shard_id: *id,
                policy,
                signers: s,
            })
            .collect();
        let (p, v, bytes) = run(&reg, digest, &shards);
        std::println!("shards={n} prove_s={p:.6} verify_s={v:.6} bytes={bytes}");
    }
}

#[test]
#[ignore = "production binary comparison on 2 and 4 signed committees"]
fn high_arity_binary_timings() {
    let rel = IvcTreeStepRelation::new().unwrap();
    measure(&[2, 4], |reg, digest, shards| {
        let start = Instant::now();
        let (s, p) = rel.prove(reg, digest, shards, &[1; 32]).unwrap();
        let prove = start.elapsed();
        let start = Instant::now();
        assert!(rel.verify(&s, &p));
        (
            prove.as_secs_f64(),
            start.elapsed().as_secs_f64(),
            p.to_bytes().len(),
        )
    });
}

#[test]
#[ignore = "production high arity comparison on 2, 4, 16, 64 and 256 signed committees"]
fn high_arity_batch_timings() {
    let _ = shape();
    measure(&[2, 4, 16, 64, 256], |reg, digest, shards| {
        let start = Instant::now();
        let (s, p) =
            prove_high_arity_tree(reg, digest, shards, Profile::TurboShakeJohnson400, &[1; 32])
                .unwrap();
        let prove = start.elapsed();
        let start = Instant::now();
        assert!(verify_high_arity_tree(&s, &p));
        (
            prove.as_secs_f64(),
            start.elapsed().as_secs_f64(),
            p.to_bytes().len(),
        )
    });
}
