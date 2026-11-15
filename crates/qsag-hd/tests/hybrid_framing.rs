use qsag_addr::{HybridPinnedEnvelope, HybridRole, HybridSuiteSpec, WitnessSuiteTag};
use qsag_verified::{HybridRoleTag, derive_hybrid_transcript_digest};

#[test]
fn verified_hybrid_digest_hashes_the_exact_address_wire_transcript() {
    for suite in [
        WitnessSuiteTag::HybridSecp256k1MlDsa44,
        WitnessSuiteTag::HybridEd25519MlDsa65,
    ] {
        let spec = HybridSuiteSpec::for_suite(suite).unwrap();
        for (role, tag) in [
            (HybridRole::Classical, HybridRoleTag::Classical),
            (HybridRole::PostQuantum, HybridRoleTag::PostQuantum),
        ] {
            for length in [0, 1, 11, 135, 136, 137, 512] {
                let message = vec![42; length];
                let wire = HybridPinnedEnvelope::signing_transcript(
                    role, &spec, &[1; 32], &[2; 32], &[3; 32], &message,
                );
                assert_eq!(
                    derive_hybrid_transcript_digest(
                        tag,
                        suite as u16,
                        &[1; 32],
                        &[2; 32],
                        &[3; 32],
                        &message
                    ),
                    Some(qsag_verified::keccak::shake256_32(&wire))
                );
            }
        }
    }
}
