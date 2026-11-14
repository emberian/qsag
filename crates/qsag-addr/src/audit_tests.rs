use super::*;
use alloc::vec;

fn envelope(suite: WitnessSuiteTag) -> HybridPinnedEnvelope {
    let spec = HybridSuiteSpec::for_suite(suite).unwrap();
    let mut pk = vec![2; spec.classical.public_key_len()];
    pk[0] = 2;
    let mut sig = vec![0; 64];
    sig[31] = 1;
    sig[32] = 1;
    sig[63] = 1;
    HybridPinnedEnvelope::sign_with(
        suite,
        pk,
        vec![3; spec.pq.public_key_len()],
        b"m",
        |_| sig,
        |_| vec![4; spec.pq.signature_len()],
    )
    .unwrap()
}

const SUITES: [WitnessSuiteTag; 2] = [
    WitnessSuiteTag::HybridSecp256k1MlDsa44,
    WitnessSuiteTag::HybridEd25519MlDsa65,
];

#[test]
fn address_canonicality_and_version_confusion() {
    for suite in SUITES {
        let env = envelope(suite);
        for version in [AddressVersion::V1Cshake256, AddressVersion::V2Poseidon2] {
            let address = env.to_address("qsp", version).unwrap();
            let encoded = address.encode().unwrap();
            assert_eq!(
                QsagAddress::decode(&encoded.to_ascii_uppercase()).unwrap(),
                address
            );
            let (_, mut data) = bech32m_decode_5bit(&encoded).unwrap();
            for hrp in ["a".repeat(16), "a".repeat(17)] {
                let text = bech32m_encode_5bit(&hrp, &data).unwrap();
                assert_eq!(QsagAddress::decode(&text).is_ok(), hrp.len() == 16);
            }
            // A valid checksum cannot authorize relabeling the hash version.
            data[0] = if version == AddressVersion::V1Cshake256 {
                2
            } else {
                1
            };
            let relabeled = bech32m_encode_5bit("qsp", &data).unwrap();
            assert!(
                env.verify_bound_encoded_address(
                    &relabeled,
                    "qsp",
                    b"m",
                    |_, _, _| panic!("version confusion reached verifier"),
                    |_, _, _| panic!("version confusion reached verifier")
                )
                .is_err()
            );
            for version in [0, 3, 16, 31] {
                data[0] = version;
                assert_eq!(
                    QsagAddress::decode(&bech32m_encode_5bit("qsp", &data).unwrap()),
                    Err(AddrError::UnsupportedVersion(version))
                );
            }
            data[0] = 1;
            data.push(0);
            assert!(QsagAddress::decode(&bech32m_encode_5bit("qsp", &data).unwrap()).is_err());
        }
        let mut address = env.to_address("qsp", AddressVersion::V2Poseidon2).unwrap();
        for limb in 0..4 {
            let original = address.commitment_256;
            for value in [GOLDILOCKS_PRIME, u64::MAX] {
                address.commitment_256[limb * 8..limb * 8 + 8]
                    .copy_from_slice(&value.to_le_bytes());
                assert_eq!(address.encode(), Err(AddrError::NonCanonicalPoseidonLimb));
                let mut raw = vec![5, if suite == SUITES[0] { 1 } else { 2 }, 2];
                raw.extend_from_slice(&address.commitment_256);
                let mut data = vec![2];
                data.extend(convert_bits(&raw, 8, 5, true).unwrap());
                assert_eq!(
                    QsagAddress::decode(&bech32m_encode_5bit("qsp", &data).unwrap()),
                    Err(AddrError::NonCanonicalPoseidonLimb)
                );
            }
            address.commitment_256 = original;
        }
    }
}

#[test]
fn wire_rejects_every_truncation_length_mutation_and_algorithm_swap() {
    for suite in SUITES {
        let env = envelope(suite);
        let wire = env.to_bytes().unwrap();
        for end in 0..wire.len() {
            assert!(HybridPinnedEnvelope::from_bytes(&wire[..end]).is_err());
        }
        for suffix in [&[0][..], &[0xff, 0, 0][..], wire.as_slice()] {
            let mut changed = wire.clone();
            changed.extend_from_slice(suffix);
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&changed),
                Err(AddrError::InvalidEnvelopeWireFormat)
            );
        }
        let mut offset = HYBRID_ENVELOPE_WIRE_MAGIC.len() + 6 + 96;
        for len in [
            env.pk_classical.len(),
            env.pk_pq.len(),
            env.sig_classical.len(),
            env.sig_pq.len(),
        ] {
            for bad_len in [0, len as u32 - 1, len as u32 + 1, u32::MAX] {
                let mut changed = wire.clone();
                changed[offset..offset + 4].copy_from_slice(&bad_len.to_be_bytes());
                assert!(HybridPinnedEnvelope::from_bytes(&changed).is_err());
            }
            offset += 4 + len;
        }
        for offset in [18, 20, 22] {
            for tag in [0, 1, 2, 0x0101, 0x0102, 0x0501, 0x0502, 0xffffu16] {
                if wire[offset..offset + 2] == tag.to_be_bytes() {
                    continue;
                }
                let mut changed = wire.clone();
                changed[offset..offset + 2].copy_from_slice(&tag.to_be_bytes());
                assert!(HybridPinnedEnvelope::from_bytes(&changed).is_err());
            }
        }
        for version in *b"029" {
            let mut changed = wire.clone();
            changed[HYBRID_ENVELOPE_WIRE_MAGIC.len() - 1] = version;
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&changed),
                Err(AddrError::InvalidEnvelopeWireFormat)
            );
        }
        // Each bit of each carried digest and of the pinned identity matters.
        for i in 0..96 {
            let mut changed = wire.clone();
            changed[24 + i] ^= 1;
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&changed),
                Err(AddrError::HybridCommitmentMismatch)
            );
        }
        for i in 0..32 {
            let mut expected = env.id_commit;
            expected[i] ^= 1;
            assert_eq!(
                env.verify_with(&expected, b"m", |_, _, _| panic!(), |_, _, _| panic!()),
                Err(AddrError::HybridCommitmentMismatch)
            );
        }
    }
}

#[test]
fn transcript_and_hash_framing_match_lean_bytes() {
    use qsag_accel::keccak::{finalize_cshake256, init_cshake256};
    // Independent materialization of the Lean encodeFramedU64Le preimage.
    let hash = |domain: &[u8], frames: &[&[u8]]| {
        let mut bytes = (frames.len() as u64).to_le_bytes().to_vec();
        for frame in frames {
            bytes.extend_from_slice(&(frame.len() as u64).to_le_bytes());
            bytes.extend_from_slice(frame);
        }
        let mut sponge = init_cshake256(b"", domain);
        sponge.absorb(&bytes);
        finalize_cshake256(&mut sponge, true);
        let mut out = [0; 32];
        sponge.squeeze(&mut out);
        out
    };
    for suite in SUITES {
        let env = envelope(suite);
        let spec = HybridSuiteSpec::for_suite(suite).unwrap();
        let s = (suite as u16).to_be_bytes();
        let c = (spec.classical as u16).to_be_bytes();
        let p = (spec.pq as u16).to_be_bytes();
        assert_eq!(
            env.pk_classical_digest,
            hash(b"QSAG.HYBRID.PK_CLASSICAL.V2", &[&s, &c, &env.pk_classical])
        );
        assert_eq!(
            env.pk_pq_digest,
            hash(b"QSAG.HYBRID.PK_PQ.V2", &[&s, &p, &env.pk_pq])
        );
        assert_eq!(
            env.id_commit,
            hash(
                b"QSAG.HYBRID.ID_COMMIT.V2",
                &[&s, &c, &p, &env.pk_classical_digest, &env.pk_pq_digest]
            )
        );
        for role in [HybridRole::Classical, HybridRole::PostQuantum] {
            for len in [0usize, 1, 255, 256] {
                let msg = vec![0x42; len];
                let tr = HybridPinnedEnvelope::signing_transcript(
                    role,
                    &spec,
                    &env.id_commit,
                    &env.pk_classical_digest,
                    &env.pk_pq_digest,
                    &msg,
                );
                let mut expected = b"QSAG.HYBRID.V2".to_vec();
                expected.push(role as u8);
                expected.extend_from_slice(&s);
                expected.extend_from_slice(&c);
                expected.extend_from_slice(&p);
                expected.extend_from_slice(&env.id_commit);
                expected.extend_from_slice(&env.pk_classical_digest);
                expected.extend_from_slice(&env.pk_pq_digest);
                expected.extend_from_slice(&(len as u64).to_be_bytes());
                expected.extend_from_slice(&msg);
                assert_eq!(tr, expected);
            }
        }
    }
    let domain = b"QSAG.HYBRID.ID_COMMIT.V2";
    assert_ne!(hash(domain, &[b"ab", b"c"]), hash(domain, &[b"a", b"bc"]));
    assert_ne!(hash(domain, &[b"a"]), hash(domain, &[b"a", b""]));
    assert_ne!(
        hash(domain, &[b"a"]),
        hash(b"QSAG.HYBRID.ID_COMMIT.V1", &[b"a"])
    );
}
