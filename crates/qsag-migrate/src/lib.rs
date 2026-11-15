#![no_std]
#![forbid(unsafe_code)]
//! Classical spending-key ownership with 438-repetition mixed-domain ZKBoo proofs
//! (`(2/3)^438 < 2^-256` classical soundness error; generic Grover search over the
//! challenge space costs `> 2^128` oracle iterations).
//!
//! The distributed outer prover (`co_zk_mpc`) enforces active 1-of-3 malicious
//! multiplication verification (per-flush `< 2^-186` prime-field and `< 2^-127.99`
//! Boolean `AND` soundness with two-round transcript-bound coin-flipping) and pre-open circuit
//! output-zero verification (`all_outputs_zero`) over confidential authenticated
//! pairwise channels, providing non-identifiable abort against one actively
//! corrupted physical custodian (`2`-of-`3` collusion reconstructs the witness).
//! See `SECURITY.md` for exact security bounds and assumptions.
//!
extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod bls12_381;
pub mod ed25519_ct;
pub mod legacy;
pub mod pallas;
pub mod scalar;
pub use scalar::{ScalarGroup, SpendingScalar};
pub mod secp256k1_ct;
pub mod zk_engine;

pub use bls12_381::{
    BlsG1Point, BlsMigrationRequest, BlsMigrationStatement, BlsOwnershipWitness,
    BlsValidatorCommitment, FpBls381, FrBls381, compute_bls_0x00_withdrawal_credentials,
    prove_bls_migration, prove_bls_migration_in_domain, verify_bls_migration,
    verify_bls_migration_with_backend,
};
pub use legacy::{HardenedChainStep, LegacyCommitmentKind, LegacyOwnershipWitness};
pub use pallas::{
    FpPallas, FqPallas, PallasCommitmentKind, PallasMigrationRequest, PallasMigrationStatement,
    PallasOwnershipWitness, PallasPoint, prove_pallas_migration, prove_pallas_migration_in_domain,
    verify_pallas_migration, verify_pallas_migration_with_backend,
};
mod boolean_hash;
mod circuit;
pub mod co_zk_mpc;
mod ownership;
pub use co_zk_mpc::CoZkCustodianShare;
mod batch_hash;
mod outer_mpc;
mod parallel;
mod secret;
mod tape_sponge;
pub use zk_engine::{
    MIT_PARTIES, MIT_REPETITIONS, MigrateError, MigrationRequest, MigrationStatement,
    MigrationZkProof, OpenedRepetitionView, prove_migration_in_domain, prove_migration_ownership,
    verify_migration_proof,
};

#[cfg(test)]
mod tests {
    use alloc::format;

    use super::*;

    #[test]
    fn canonical_spending_keys_match_all_four_public_encodings() {
        let mut key = [0; 32];
        key[31] = 1;
        let witness = LegacyOwnershipWitness::from_raw_secret(key);
        let domain = [23; 32];
        for kind in [
            witness.compute_bitcoin_hash160().unwrap(),
            witness.compute_taproot_tweaked_xonly().unwrap(),
            witness.compute_ethereum_keccak20().unwrap(),
            witness.compute_slip0010_commitment(),
        ] {
            let scalar = witness.normalize_spending_scalar(&kind).unwrap();
            assert_eq!(
                witness.compute_nullifier(&kind, &domain),
                Some(scalar.compute_nullifier(&domain)),
            );
            if let LegacyCommitmentKind::Slip0010Ed25519(expected) = kind {
                assert_eq!(scalar.group(), ScalarGroup::Ed25519);
                assert_eq!(
                    ed25519_ct::public_key_from_clamped_scalar(scalar.as_le_bytes()),
                    expected,
                );
                continue;
            }
            assert_eq!(scalar.group(), ScalarGroup::Secp256k1);
            let mut bytes = scalar.to_be_bytes();
            let mut point = secp256k1_ct::SecpPoint::generator_mul_ct(&bytes);
            qsag_accel::ct::ct_zeroize_bytes(&mut bytes);
            match kind {
                LegacyCommitmentKind::BitcoinHash160(expected) => {
                    assert_eq!(
                        qsag_accel::sha2::hash160(&point.to_compressed_bytes().unwrap()),
                        expected,
                    );
                }
                LegacyCommitmentKind::BitcoinTaprootXOnly(expected) => {
                    let (x, y) = point.to_affine().unwrap();
                    assert_eq!(x.to_be_bytes(), expected);
                    assert!(!y.is_odd());
                }
                LegacyCommitmentKind::EthereumKeccak20(expected) => {
                    let hash = qsag_accel::keccak::keccak256(&point.to_uncompressed_64().unwrap());
                    assert_eq!(&hash[12..], &expected);
                }
                LegacyCommitmentKind::Slip0010Ed25519(_) => unreachable!(),
            }
            point.wipe();
        }
    }

    #[test]
    fn nullifiers_identify_spending_keys_across_equivalent_witnesses() {
        let mut key = [0; 32];
        key[31] = 1;
        let domain = [19; 32];
        let witness = LegacyOwnershipWitness::from_raw_secret(key);
        let opposite =
            LegacyOwnershipWitness::from_raw_secret(secp256k1_ct::secp_scalar_neg_mod_n(&key));
        let taproot = witness.compute_taproot_tweaked_xonly().unwrap();
        assert_eq!(opposite.compute_taproot_tweaked_xonly(), Some(taproot));
        assert_eq!(
            witness.compute_nullifier(&taproot, &domain),
            opposite.compute_nullifier(&taproot, &domain),
        );
        let bitcoin = witness.compute_bitcoin_hash160().unwrap();
        let ethereum = witness.compute_ethereum_keccak20().unwrap();
        assert_eq!(
            witness.compute_nullifier(&bitcoin, &domain),
            witness.compute_nullifier(&ethereum, &domain),
        );
        assert_ne!(
            witness.compute_nullifier(&bitcoin, &domain),
            witness.compute_nullifier(&bitcoin, &[20; 32]),
        );
        let invalid = LegacyOwnershipWitness::from_raw_secret([0; 32]);
        assert!(invalid.compute_nullifier(&bitcoin, &domain).is_none());
    }

    #[test]
    fn nullifier_encoding_separates_groups_and_preserves_scalar_bytes() {
        let mut bytes = [0; 32];
        bytes[0] = 1;
        let secp = SpendingScalar::from_le_bytes(bytes, ScalarGroup::Secp256k1).unwrap();
        let ed = SpendingScalar::from_le_bytes(bytes, ScalarGroup::Ed25519).unwrap();
        let mut expected = [0; 32];
        expected[31] = 1;
        assert_eq!(secp.to_be_bytes(), expected);
        assert_ne!(
            secp.compute_nullifier(&[0; 32]),
            ed.compute_nullifier(&[0; 32])
        );
        bytes[30] = 1;
        let changed = SpendingScalar::from_le_bytes(bytes, ScalarGroup::Secp256k1).unwrap();
        assert_ne!(
            secp.compute_nullifier(&[0; 32]),
            changed.compute_nullifier(&[0; 32])
        );
    }

    #[test]
    fn test_secp256k1_generator_and_all_four_legacy_commitment_modes() {
        // Verify `1 * G` compressed pubkey == `02 79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798`
        // and Bitcoin HASH160(G) == `751e76e8199196d454941c45d1b3a323f1433bd6`!
        let mut sk_one = [0u8; 32];
        sk_one[31] = 1;
        let wit_one = LegacyOwnershipWitness::from_raw_secret(sk_one);
        assert!(format!("{:?}", wit_one).contains("<REDACTED>"));

        let h160 = wit_one.compute_bitcoin_hash160().unwrap();
        assert_eq!(
            h160,
            LegacyCommitmentKind::BitcoinHash160([
                0x75, 0x1e, 0x76, 0xe8, 0x19, 0x91, 0x96, 0xd4, 0x54, 0x94, 0x1c, 0x45, 0xd1, 0xb3,
                0xa3, 0x23, 0xf1, 0x43, 0x3b, 0xd6,
            ])
        );

        // Verify `2 * G` via complete addition == scalar_mul_ct(2):
        // x(2G) = c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5
        let mut sk_two = [0u8; 32];
        sk_two[31] = 2;
        let pt2 = secp256k1_ct::SecpPoint::GENERATOR.scalar_mul_ct(&sk_two);
        let comp2 = pt2.to_compressed_bytes().unwrap();
        assert_eq!(comp2[0], 0x02);
        assert_eq!(
            &comp2[1..9],
            &[0xc6, 0x04, 0x7f, 0x94, 0x41, 0xed, 0x7d, 0x6d]
        );

        // Hardened BIP-32 step -> Taproot tweaked x-only commitment & Ethereum Keccak256 20B commitment!
        let step = HardenedChainStep::new([0x33u8; 32], [0x44u8; 32], 0x8000_002C).unwrap();
        let bip32_wit = LegacyOwnershipWitness::from_bip32_hardened_step(step).unwrap();
        let taproot_comm = bip32_wit.compute_taproot_tweaked_xonly().unwrap();
        let eth_comm = bip32_wit.compute_ethereum_keccak20().unwrap();
        assert!(bip32_wit.matches_commitment(&taproot_comm));
        assert!(bip32_wit.matches_commitment(&eth_comm));

        // SLIP-0010 hardened Ed25519 step
        let step = HardenedChainStep::new([0x33u8; 32], [0x44u8; 32], 0x8000_002C).unwrap();
        let slip_wit = LegacyOwnershipWitness::from_slip0010_hardened_step(step);
        let slip_comm = slip_wit.compute_slip0010_commitment();
        assert!(slip_wit.matches_commitment(&slip_comm));
    }
}
