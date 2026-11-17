//! Statement-derived serialized stream lengths, without building an ownership circuit.
//!
//! These descriptors are independent of witness and public-field values: those values only
//! affect linear operations, public constants, and output equalities. Nonlinear topology is
//! fixed by the commitment kind. The regression census below checks every kind against the
//! builder, including zero/one values that exercise public constant folding. Circuit changes
//! must update these descriptors alongside the circuit; verification must never build a
//! circuit merely to discover the lengths of an unauthenticated proof.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ProofShape {
    /// V3 inputs encode each Boolean in one byte and each field in whole bytes.
    pub input_bytes: usize,
    /// CoZK inputs pack all values tightly, with only final-byte padding.
    pub input_bits: usize,
    /// V3 multiplication/output streams byte-align each non-Boolean value.
    pub product_bytes: usize,
    pub product_bits: usize,
    pub output_bytes: usize,
    pub output_bits: usize,
}

pub(crate) fn legacy(kind: &crate::LegacyCommitmentKind) -> ProofShape {
    use crate::LegacyCommitmentKind::*;
    let (input_bits, product_bytes, product_bits, output_bytes, output_bits) = match kind {
        BitcoinHash160(_) => (512, 81_424, 651_390, 85, 674),
        EthereumKeccak20(_) => (512, 80_480, 643_838, 85, 674),
        BitcoinTaprootXOnly(_) => (512, 75_680, 605_438, 98, 771),
        Slip0010Ed25519(_) => (511, 65_600, 523_126, 97, 769),
    };
    ProofShape {
        input_bytes: 288,
        input_bits,
        product_bytes,
        product_bits,
        output_bytes,
        output_bits,
    }
}

pub(crate) fn pallas(kind: &crate::pallas::PallasCommitmentKind) -> ProofShape {
    if kind.is_rerandomized() {
        ProofShape {
            input_bytes: 544,
            input_bits: 767,
            product_bytes: 75_392,
            product_bits: 601_159,
            output_bytes: 129,
            output_bits: 1_025,
        }
    } else {
        ProofShape {
            input_bytes: 288,
            input_bits: 511,
            product_bytes: 75_232,
            product_bits: 599_881,
            output_bytes: 129,
            output_bits: 1_023,
        }
    }
}

pub(crate) fn bls(kind: &crate::bls12_381::BlsValidatorCommitment) -> ProofShape {
    use crate::bls12_381::BlsValidatorCommitment::*;
    let (product_bytes, product_bits, output_bytes, output_bits) = match kind {
        OperatorSigningPubkey(_) => (106_800, 848_479, 177, 1_401),
        BlsWithdrawalCredential(_) => (110_295, 876_429, 112, 887),
    };
    ProofShape {
        input_bytes: 304,
        input_bits: 637,
        product_bytes,
        product_bits,
        output_bytes,
        output_bits,
    }
}

#[cfg(test)]
pub(crate) use tests::assert_descriptors_match_circuit_streams;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        LegacyCommitmentKind, MigrationStatement,
        bls12_381::{
            BlsG1Point, BlsMigrationStatement, BlsValidatorCommitment, FpBls381,
            build_bls_ownership_circuit,
        },
        circuit::{Circuit, Domain, Op},
        pallas::{
            FpPallas, PallasCommitmentKind, PallasMigrationStatement, PallasPoint,
            build_pallas_ownership_circuit,
        },
    };
    use qsag_addr::{KeyIdentityKind, QsagAddress, WitnessSuiteTag};

    fn v3_packed_len(domains: impl Iterator<Item = Domain>) -> usize {
        let mut bytes = 0;
        let mut bit = 0;
        for domain in domains {
            if domain == Domain::Bit {
                if bit == 0 {
                    bytes += 1;
                }
                bit = (bit + 1) % 8;
            } else {
                bit = 0;
                bytes += domain.byte_len();
            }
        }
        bytes
    }
    fn measured(c: &Circuit) -> ProofShape {
        ProofShape {
            input_bytes: c
                .nodes
                .iter()
                .filter(|n| matches!(n.op, Op::Input))
                .map(|n| n.domain.byte_len())
                .sum(),
            input_bits: c
                .nodes
                .iter()
                .filter(|n| matches!(n.op, Op::Input))
                .map(|n| n.domain.width())
                .sum(),
            product_bytes: v3_packed_len(
                c.nodes
                    .iter()
                    .filter(|n| matches!(n.op, Op::Mul(_, _)))
                    .map(|n| n.domain),
            ),
            product_bits: c
                .nodes
                .iter()
                .filter(|n| matches!(n.op, Op::Mul(_, _)))
                .map(|n| n.domain.width())
                .sum(),
            output_bytes: v3_packed_len(c.outputs.iter().map(|&w| c.nodes[w].domain)),
            output_bits: c.outputs.iter().map(|&w| c.nodes[w].domain.width()).sum(),
        }
    }
    fn target() -> QsagAddress {
        QsagAddress::from_pubkey_poseidon2(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            b"shape census",
        )
        .unwrap()
    }
    pub(crate) fn assert_descriptors_match_circuit_streams() {
        for variant in [0u8, 1, 255] {
            for kind in [
                LegacyCommitmentKind::BitcoinHash160([variant; 20]),
                LegacyCommitmentKind::EthereumKeccak20([variant; 20]),
                LegacyCommitmentKind::BitcoinTaprootXOnly([variant; 32]),
                LegacyCommitmentKind::Slip0010Ed25519([variant; 32]),
            ] {
                let statement = MigrationStatement {
                    legacy_commitment: kind,
                    target_pq_address: target(),
                    epoch_anchor: 1,
                    migration_domain: [variant; 32],
                    migration_nullifier: [variant as u64; 4],
                    witness_anchor: [0; 4],
                };
                let c = crate::ownership::build(&statement, &[variant; 32]);
                assert_eq!(legacy(&statement.legacy_commitment), measured(&c));
            }
            for kind in [
                PallasCommitmentKind::OrchardSpendAuthKey([variant; 32]),
                PallasCommitmentKind::OrchardRedPallasRk([variant; 32]),
            ] {
                let statement = PallasMigrationStatement {
                    commitment: kind,
                    target_pq_address: target(),
                    epoch_anchor: 1,
                    migration_domain: [variant; 32],
                    migration_nullifier: [variant as u64; 4],
                };
                let c = build_pallas_ownership_circuit(
                    &statement,
                    match variant {
                        0 => (FpPallas::ZERO, FpPallas::ZERO),
                        1 => (FpPallas::ONE, FpPallas::ONE),
                        _ => PallasPoint::ORCHARD_SPEND_AUTH_G.to_affine().unwrap(),
                    },
                    &[variant; 32],
                    &[variant; 32],
                );
                assert_eq!(pallas(&statement.commitment), measured(&c.0));
            }
            for (kind, affine) in [
                (
                    BlsValidatorCommitment::OperatorSigningPubkey([variant; 48]),
                    Some(match variant {
                        0 => (FpBls381::ZERO, FpBls381::ZERO),
                        1 => (FpBls381::ONE, FpBls381::ONE),
                        _ => BlsG1Point::GENERATOR.to_affine().unwrap(),
                    }),
                ),
                (
                    BlsValidatorCommitment::BlsWithdrawalCredential([variant; 32]),
                    None,
                ),
            ] {
                let statement = BlsMigrationStatement {
                    commitment: kind,
                    validator_index: variant as u64,
                    withdrawal_credentials: [variant; 32],
                    target_pq_address: target(),
                    epoch_anchor: 1,
                    migration_domain: [variant; 32],
                    migration_nullifier: [variant as u64; 4],
                };
                let c = build_bls_ownership_circuit(&statement, affine, &[variant; 32]);
                assert_eq!(bls(&statement.commitment), measured(&c.0));
            }
        }
    }
}
