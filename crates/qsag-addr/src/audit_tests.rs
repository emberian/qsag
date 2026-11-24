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

/// Pinned encodings: an address is a long-lived identifier, so any change to its hash
/// profile or framing must show up here. The `V2Poseidon2` line depends on the workspace
/// Poseidon2 profile (matrices, round constants, sponge padding) through the single accel
/// entry point `poseidon2_hash_framed_limbs4`, and has to be regenerated with it.
#[test]
fn pinned_address_encodings() {
    let preimage = [0x5a; 48];
    let v1 = QsagAddress::from_pubkey_cshake256(
        "qsp",
        WitnessSuiteTag::MlDsa65,
        KeyIdentityKind::SingleOrThreshold,
        &preimage,
    )
    .unwrap();
    assert_eq!(
        v1.encode().unwrap(),
        "qsp1pqypqz4s9532yap0ujqxrleyll5c7amlwcljae2deya8d62jpxny0jpta6szewe"
    );
    let v2 = QsagAddress::from_pubkey_poseidon2(
        "qsp",
        WitnessSuiteTag::PolicyPredicateScript,
        KeyIdentityKind::ScriptPredicate,
        &preimage,
    )
    .unwrap();
    assert_eq!(
        v2.encode().unwrap(),
        "qsp1zqcqs8q9dpcanthu7s02cjf0wymexxz0th5vrtgyppu9t93g52tvhlqwgk8y6yw"
    );
}

#[test]
fn canonical_intent_128_aligns_suite_tags_and_enforces_identity_kind_consistency() {
    let all_suites = [
        WitnessSuiteTag::MlDsa44,
        WitnessSuiteTag::MlDsa65,
        WitnessSuiteTag::MlDsa87,
        WitnessSuiteTag::SlhDsa128s,
        WitnessSuiteTag::SlhDsa128f,
        WitnessSuiteTag::SlhDsa192s,
        WitnessSuiteTag::SlhDsa192f,
        WitnessSuiteTag::SlhDsa256s,
        WitnessSuiteTag::SlhDsa256f,
        WitnessSuiteTag::Baggy,
        WitnessSuiteTag::Jorts,
        WitnessSuiteTag::QuorumJorts,
        WitnessSuiteTag::JortsPoseidon2,
        WitnessSuiteTag::CorduroyPoseidon2,
        WitnessSuiteTag::FrontierSumFts,
        WitnessSuiteTag::PiHdCommitInventory,
        WitnessSuiteTag::HybridSecp256k1MlDsa44,
        WitnessSuiteTag::HybridEd25519MlDsa65,
        WitnessSuiteTag::PolicyPredicateScript,
    ];
    let all_kinds = [
        KeyIdentityKind::SingleOrThreshold,
        KeyIdentityKind::HybridConjunctive,
        KeyIdentityKind::ScriptPredicate,
    ];
    for suite in all_suites {
        let expected_kind = suite.expected_identity_kind();
        let addr = QsagAddress::from_pubkey_cshake256("qsp", suite, expected_kind, &[0x42; 64])
            .expect("valid suite/kind pair must derive address");
        for kind in all_kinds {
            let intent = CanonicalIntent128 {
                suite_tag: suite,
                address_version: AddressVersion::V1Cshake256,
                identity_kind: kind,
                chain_id: 7,
                nonce: 9,
                timestamp_secs: 11,
                amount_units: 13,
                rolling_window_spent: 17,
                recipient_commitment: addr.commitment_256,
                payload_digest: [0xEE; 32],
            };
            let raw = encode_intent_128(&intent);
            assert_eq!(u16::from_be_bytes([raw[4], raw[5]]), suite as u16);
            assert_eq!(raw[6], AddressVersion::V1Cshake256 as u8);
            assert_eq!(raw[7], kind as u8);
            if kind == expected_kind {
                assert_eq!(try_encode_intent_128(&intent), Ok(raw));
                let decoded = decode_intent_128(&raw).expect("consistent pair must decode");
                assert_eq!(decoded, intent);
                assert!(decoded.matches_address_profile(&addr));
            } else {
                assert!(try_encode_intent_128(&intent).is_err());
                assert!(
                    decode_intent_128(&raw).is_none(),
                    "inconsistent ({suite:?}, {kind:?}) must be rejected by decode_intent_128"
                );
            }
        }
    }
    // Verify hybrid suite codes never invert 0x0501 / 0x0502.
    assert_eq!(IntentSuiteTag::HybridSecp256k1MlDsa44 as u16, 0x0501);
    assert_eq!(IntentSuiteTag::HybridEd25519MlDsa65 as u16, 0x0502);
    assert_eq!(IntentIdentityKind::SingleOrThreshold as u8, 0x01);
    assert_eq!(IntentIdentityKind::HybridConjunctive as u8, 0x02);
    assert_eq!(IntentIdentityKind::ScriptPredicate as u8, 0x03);
}

fn verified_intent(
    suite_tag: VerifiedIntentSuiteTag,
    identity_kind: VerifiedIntentIdentityKind,
) -> VerifiedCanonicalIntent128 {
    VerifiedCanonicalIntent128 {
        suite_tag,
        address_version: VerifiedIntentAddressVersion::V2,
        identity_kind,
        chain_id: 7,
        nonce: 9,
        timestamp_secs: 11,
        amount_units: 13,
        rolling_window_spent: 17,
        recipient_commitment: [0xA5; 32],
        payload_digest: [0xEE; 32],
    }
}

/// H-01: the verified intent namespace carries the canonical names and wire words, so the bridge
/// is the identity on frames, and it still enforces the canonical `(suite, kind)` rule that the
/// verified decoder does not.
#[test]
fn verified_intent_namespace_agrees_with_canonical_and_is_validated() {
    use VerifiedIntentIdentityKind as VK;
    use VerifiedIntentSuiteTag as VS;
    let suites = [
        (VS::MlDsa65, WitnessSuiteTag::MlDsa65, 0x0102u16),
        (VS::SlhDsa128f, WitnessSuiteTag::SlhDsa128f, 0x0202),
        (VS::JortsPoseidon2, WitnessSuiteTag::JortsPoseidon2, 0x0214),
        (
            VS::HybridSecp256k1MlDsa44,
            WitnessSuiteTag::HybridSecp256k1MlDsa44,
            0x0501,
        ),
        (
            VS::HybridEd25519MlDsa65,
            WitnessSuiteTag::HybridEd25519MlDsa65,
            0x0502,
        ),
    ];
    let kinds = [
        (VK::SingleOrThreshold, KeyIdentityKind::SingleOrThreshold),
        (VK::HybridConjunctive, KeyIdentityKind::HybridConjunctive),
        (VK::ScriptPredicate, KeyIdentityKind::ScriptPredicate),
    ];
    let mut accepted = 0;
    for (verified_suite, canonical_suite, word) in suites {
        // Same name, same wire word on both sides, and the word round-trips in both.
        assert_eq!(intent_suite_from_verified(verified_suite), canonical_suite);
        assert_eq!(verified_suite.to_u16(), word);
        assert_eq!(canonical_suite as u16, word);
        assert_eq!(VS::from_u16(word), Some(verified_suite));
        assert_eq!(WitnessSuiteTag::from_u16(word), Ok(canonical_suite));
        for (verified_kind, canonical_kind) in kinds {
            assert_eq!(
                intent_identity_kind_from_verified(verified_kind),
                canonical_kind
            );
            assert_eq!(verified_kind.to_u8(), canonical_kind as u8);
            let verified = verified_intent(verified_suite, verified_kind);
            let frame = qsag_verified::encode_intent_128(&verified);
            let translated = intent_from_verified(&verified);
            assert_eq!(decode_verified_intent_128(&frame), translated.ok());
            let valid = canonical_suite
                .validate_identity_kind(canonical_kind)
                .is_ok();
            assert_eq!(translated.is_ok(), valid);
            // The verified decoder checks the pair exactly as the canonical one does.
            assert_eq!(verified_suite.admits_identity_kind(verified_kind), valid);
            assert_eq!(qsag_verified::decode_intent_128(&frame).is_some(), valid);
            if !valid {
                // The verified encoder is total, so the frame exists; the verified decoder,
                // the bridge and the canonical decoder all refuse it.
                assert!(decode_verified_intent_128(&frame).is_none());
                assert!(decode_intent_128(&frame).is_none());
                continue;
            }
            let canonical = translated.unwrap();
            accepted += 1;
            assert_eq!(canonical.suite_tag, canonical_suite);
            assert_eq!(canonical.identity_kind, canonical_kind);
            assert_eq!(canonical.address_version, AddressVersion::V2Poseidon2);
            assert_eq!(canonical.validate(), Ok(()));
            assert_eq!(
                (
                    canonical.chain_id,
                    canonical.nonce,
                    canonical.timestamp_secs
                ),
                (7, 9, 11)
            );
            assert_eq!(
                (canonical.amount_units, canonical.rolling_window_spent),
                (13, 17)
            );
            assert_eq!(canonical.recipient_commitment, [0xA5; 32]);
            assert_eq!(canonical.payload_digest, [0xEE; 32]);
            // The frames are byte-identical and both decoders read the same intent.
            assert_eq!(try_encode_intent_128(&canonical).unwrap(), frame);
            assert_eq!(decode_intent_128(&frame), Some(canonical));
        }
    }
    // Exactly one valid kind per suite: single-or-threshold for the three non-hybrid suites,
    // hybrid-conjunctive for the two hybrid ones.
    assert_eq!(accepted, 5);

    // The pair the audit named, hybrid suite with a single key: the verified decoder refuses
    // its frame, and the bridge refuses the struct however it was built.
    let invalid = verified_intent(VS::HybridEd25519MlDsa65, VK::SingleOrThreshold);
    assert!(
        qsag_verified::decode_intent_128(&qsag_verified::encode_intent_128(&invalid)).is_none()
    );
    assert_eq!(
        intent_from_verified(&invalid),
        Err(AddrError::InconsistentSuiteIdentityKind {
            suite_tag: 0x0502,
            kind: 0x01,
        })
    );
    // Words of canonical suites outside the verified subset are refused by the verified decoder.
    for word in [0x0101u16, 0x0201, 0x0302] {
        assert_eq!(VS::from_u16(word), None);
        let mut frame = qsag_verified::encode_intent_128(&verified_intent(
            VS::JortsPoseidon2,
            VK::SingleOrThreshold,
        ));
        frame[4..6].copy_from_slice(&word.to_be_bytes());
        assert!(decode_verified_intent_128(&frame).is_none());
    }
    let mut bad_magic = qsag_verified::encode_intent_128(&verified_intent(
        VS::JortsPoseidon2,
        VK::SingleOrThreshold,
    ));
    assert!(decode_verified_intent_128(&bad_magic).is_some());
    bad_magic[0] ^= 1;
    assert!(decode_verified_intent_128(&bad_magic).is_none());
}

#[test]
fn decode_verified_intent_128_canonical_roundtrip_and_rejects_noncanonical_bytes() {
    use VerifiedIntentIdentityKind as VK;
    use VerifiedIntentSuiteTag as VS;

    for (vs, vk) in [
        (VS::MlDsa65, VK::SingleOrThreshold),
        (VS::SlhDsa128f, VK::SingleOrThreshold),
        (VS::JortsPoseidon2, VK::SingleOrThreshold),
        (VS::HybridSecp256k1MlDsa44, VK::HybridConjunctive),
        (VS::HybridEd25519MlDsa65, VK::HybridConjunctive),
    ] {
        let raw = qsag_verified::encode_intent_128(&verified_intent(vs, vk));
        let v_intent = decode_verified_intent_128(&raw).expect("valid verified intent");
        assert_eq!(v_intent.validate(), Ok(()));
        assert_eq!(
            decode_intent_128(&encode_intent_128(&v_intent)),
            Some(v_intent)
        );
        assert_eq!(encode_intent_128(&v_intent), raw);

        // Invalid discriminators in header bytes (address_version / identity_kind) are rejected by both.
        for bad_idx in [6usize, 7usize] {
            let mut dirty = raw;
            dirty[bad_idx] ^= 0x80;
            assert_eq!(decode_verified_intent_128(&dirty), None);
            assert_eq!(decode_intent_128(&dirty), None);
        }
    }
}

/// H-01: the hybrid kernels take canonical suites only, and agree with the envelope.
#[test]
fn typed_hybrid_kernels_refuse_non_hybrid_suites_and_match_the_envelope() {
    let id = [0x77; 32];
    let (dc, dp) = ([0x11; 32], [0x22; 32]);
    for suite in SUITES {
        let spec = HybridSuiteSpec::for_suite(suite).unwrap();
        for (role, other) in [
            (HybridRole::Classical, HybridRole::PostQuantum),
            (HybridRole::PostQuantum, HybridRole::Classical),
        ] {
            assert!(hybrid_domain_framing_ok(
                HYBRID_PINNED_MAGIC,
                role as u8,
                role,
                suite,
                &id,
                &id
            ));
            assert!(!hybrid_domain_framing_ok(
                HYBRID_PINNED_MAGIC,
                role as u8,
                other,
                suite,
                &id,
                &id
            ));
            assert!(!hybrid_domain_framing_ok(
                HYBRID_PINNED_MAGIC,
                role as u8,
                role,
                suite,
                &id,
                &[0x78; 32]
            ));
            let transcript =
                HybridPinnedEnvelope::signing_transcript(role, &spec, &id, &dc, &dp, b"m");
            assert_eq!(
                hybrid_transcript_digest(role, suite, &id, &dc, &dp, b"m"),
                Ok(qsag_verified::shake256_32(&transcript))
            );
        }
    }
    for suite in [
        WitnessSuiteTag::MlDsa44,
        WitnessSuiteTag::SlhDsa128s,
        WitnessSuiteTag::PolicyPredicateScript,
    ] {
        assert!(!hybrid_domain_framing_ok(
            HYBRID_PINNED_MAGIC,
            HybridRole::Classical as u8,
            HybridRole::Classical,
            suite,
            &id,
            &id
        ));
        assert_eq!(
            hybrid_transcript_digest(HybridRole::Classical, suite, &id, &dc, &dp, b"m"),
            Err(AddrError::HybridUnsupportedSuite(suite as u16))
        );
    }
}
