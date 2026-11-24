use super::*;
use qsag_core::field::goldilocks::GOLDILOCKS_PRIME;

fn fp5_pow_u64(mut base: Fp5, mut exp: u64) -> Fp5 {
    let mut acc = Fp5::ONE;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = acc.mul(base);
        }
        base = base.mul(base);
        exp >>= 1;
    }
    acc
}

#[test]
fn fp5_irreducibility_and_field_axioms() {
    // Serret's criterion: 5 | (p - 1) and 3^((p - 1) / 5) != 1 (mod p).
    assert_eq!((GOLDILOCKS_PRIME - 1) % 5, 0);
    let z5 = Goldilocks::from_u64_reduced(3).pow((GOLDILOCKS_PRIME - 1) / 5);
    assert_ne!(z5, Goldilocks::ONE);
    assert_eq!(z5.pow(5), Goldilocks::ONE);

    // T^5 == 3 in GF(p)[T]/(T^5 - 3).
    let t = Fp5::from_limbs([0, 1, 0, 0, 0]);
    assert_eq!(fp5_pow_u64(t, 5), Fp5::from_limbs([3, 0, 0, 0, 0]));

    // Frobenius endomorphism: a^(p^5) == a for non-trivial element a.
    let a = Fp5::from_limbs([
        0x1234_5678_9ABC_DEF0,
        GOLDILOCKS_PRIME - 17,
        42,
        0xDEAD_BEEF_CAFE_BABE % GOLDILOCKS_PRIME,
        7,
    ]);
    let b = Fp5::from_limbs([99, 1, GOLDILOCKS_PRIME - 3, 888_888, 55]);
    let c = Fp5::from_limbs([7, 8, 9, 10, 11]);
    assert_eq!(a.mul(b), b.mul(a));
    assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
    assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));

    let mut frob = a;
    for _ in 0..5 {
        frob = fp5_pow_u64(frob, GOLDILOCKS_PRIME);
    }
    assert_eq!(frob, a);
}

#[test]
fn shake256_party_batch8_matches_scalar_shake256_bit_for_bit() {
    let nonce = [0x3Cu8; 32];
    let rep = 19u32;
    let base_party = 40usize;
    let seeds: [[u8; 32]; 8] = core::array::from_fn(|i| [(i as u8).wrapping_mul(29) ^ 0xA5; 32]);

    let mut batch = Shake256PartyBatch8::new(&nonce, rep, base_party, &seeds);
    let salts = batch.extract_salts_1();
    let mut outs: [Vec<u64>; 8] = core::array::from_fn(|_| Vec::new());
    batch.squeeze_canonical_gl(
        [true, false, true, true, true, false, true, true],
        &mut outs,
        512,
    );

    for inst in 0..8 {
        let mut sp = Shake256::new();
        sp.absorb(PARTY_TAPE_DOMAIN_24);
        sp.absorb(&nonce);
        sp.absorb(&seeds[inst]);
        let tag = (rep as u64) | (((base_party + inst) as u64) << 32);
        sp.absorb(&tag.to_le_bytes());
        sp.finalize(0x1F);

        let mut ref_salt = [0u8; 32];
        sp.squeeze(&mut ref_salt);
        assert_eq!(salts[inst], ref_salt);

        if !matches!(inst, 1 | 5) {
            let mut expected = Vec::with_capacity(512);
            let mut word_bytes = [0u8; 8];
            while expected.len() < 512 {
                sp.squeeze(&mut word_bytes);
                let w = u64::from_le_bytes(word_bytes);
                if w < GOLDILOCKS_PRIME {
                    expected.push(w);
                }
            }
            assert_eq!(outs[inst], expected);
        } else {
            assert!(outs[inst].is_empty());
        }
    }
}

#[test]
fn ggm_tree_256_roundtrip_and_hidden_leaf_isolation() {
    let root = [0x77u8; 32];
    let nonce = [0x21u8; 32];
    let mut full = SecretBuffer(vec![[0u8; 32]; 2 * VC_SD_LIMBO_PARTIES]);
    expand_ggm_tree_256_into(&root, &nonce, 3, &mut full.0);
    for hidden in [0u8, 1, 127, 128, 254, 255] {
        let copath = extract_ggm_copath(&full, hidden);
        let rec = reconstruct_ggm_leaves_256(&copath, hidden, &nonce, 3);
        for (p, &leaf) in rec.iter().enumerate() {
            if p == hidden as usize {
                assert_eq!(leaf, [0u8; 32]);
            } else {
                assert_eq!(leaf, full.0[VC_SD_LIMBO_PARTIES + p]);
            }
        }
    }
}

#[test]
fn accumulator_indexes_duplicates_and_updates_paths_incrementally() {
    let mut accumulator = IssuerCredentialAccumulator::new(PublicKey::test_key(), 7);
    for i in 0..65u64 {
        let session = cshake256_framed_32(b"session", &[&i.to_le_bytes()]);
        let token = cshake256_framed_32(b"token", &[&i.to_le_bytes()]);
        let leaf = [i + 1; 6];
        assert_eq!(
            accumulator.enroll_issued(session, leaf, token).unwrap(),
            i as usize
        );
        let before = accumulator.clone();
        assert!(accumulator.enroll_issued(session, [0; 6], [9; 32]).is_err());
        assert!(accumulator.enroll_issued([8; 32], leaf, token).is_err());
        assert_eq!(accumulator, before);
        // Independent full recomputation, including every incomplete right subtree.
        let mut nodes = accumulator.leaves.clone();
        let mut empty = accumulator.empty[0];
        for level in 0..VC_ACCUMULATOR_DEPTH {
            nodes = nodes
                .chunks(2)
                .map(|pair| {
                    merkle_hash_pair(&pair[0], pair.get(1).unwrap_or(&empty), 7, level as u32)
                })
                .collect();
            empty = merkle_hash_pair(&empty, &empty, 7, level as u32);
        }
        assert_eq!(accumulator.root(), nodes[0]);
        for index in [0, i as usize / 2, i as usize] {
            let witness = accumulator.membership_witness(index).unwrap();
            let mut root = accumulator.leaves[index];
            for (level, sibling) in witness.siblings.iter().enumerate() {
                root = if (index >> level) & 1 == 0 {
                    merkle_hash_pair(&root, sibling, 7, level as u32)
                } else {
                    merkle_hash_pair(sibling, &root, 7, level as u32)
                };
            }
            assert_eq!(root, accumulator.root());
        }
    }
}

#[test]
fn issuance_binds_all_32_attributes() {
    let mut attrs: [u64; MAX_VC_ATTRS] = core::array::from_fn(|i| i as u64 + 1);
    let (request, _) =
        holder_prepare_blind_issuance(42, &attrs, [3; 32], 7, [4; 32], [5; 32]).unwrap();
    assert!(verify_blind_issuance_request(&request, &attrs, 42));
    let original = compute_vc_poseidon2_commit(42, &attrs, &[17; 4], VC_ATTR_COMMIT_TAG).unwrap();
    for index in 0..MAX_VC_ATTRS {
        attrs[index] += 1;
        assert!(!verify_blind_issuance_request(&request, &attrs, 42));
        assert_ne!(
            original,
            compute_vc_poseidon2_commit(42, &attrs, &[17; 4], VC_ATTR_COMMIT_TAG).unwrap()
        );
        attrs[index] -= 1;
    }
    assert!(
        compute_vc_poseidon2_commit(42, &[0; MAX_VC_ATTRS + 1], &[17; 4], VC_ATTR_COMMIT_TAG)
            .is_err()
    );
}

#[test]
fn arity_commitment_distinguishes_trailing_zero() {
    let blind = [17, 18, 19, 20];
    let one = compute_vc_poseidon2_commit(42, &[7], &blind, VC_ATTR_COMMIT_TAG).unwrap();
    let two = compute_vc_poseidon2_commit(42, &[7, 0], &blind, VC_ATTR_COMMIT_TAG).unwrap();
    assert_ne!(one, two);
    assert!(compute_vc_poseidon2_commit(42, &[], &blind, VC_ATTR_COMMIT_TAG).is_err());
    assert!(
        compute_vc_poseidon2_commit(42, &[0; MAX_VC_ATTRS + 1], &blind, VC_ATTR_COMMIT_TAG)
            .is_err()
    );
}

#[test]
fn issuance_profile_tags_are_explicit_for_both_profiles() {
    let classical = ZkSoundnessProfile::Classical128;
    let quantum = ZkSoundnessProfile::Quantum128;
    assert_eq!(
        classical.issuance_statement_tag(),
        b"QSAG.VC.PROFILE.Classical128:219"
    );
    assert_eq!(
        quantum.issuance_statement_tag(),
        b"QSAG.VC.PROFILE.Quantum128:438"
    );
    assert_eq!(classical.issuance_transcript_tag(), b"Classical128:219");
    assert_eq!(quantum.issuance_transcript_tag(), b"Quantum128:438");
    for profile in [classical, quantum] {
        let suffix = std::format!(":{}", profile.repetitions());
        assert!(
            profile
                .issuance_statement_tag()
                .ends_with(suffix.as_bytes())
        );
        assert!(
            profile
                .issuance_transcript_tag()
                .ends_with(suffix.as_bytes())
        );
    }
    // The tagged classical statement still proves and verifies, under its
    // own profile only.
    let (req, _) = holder_prepare_blind_issuance_with_profile(
        42,
        &[1, 2],
        [3; 32],
        7,
        [4; 32],
        [5; 32],
        classical,
    )
    .unwrap();
    assert_eq!(req.opened_reps.len(), 219);
    assert!(verify_blind_issuance_request_with_profile(
        &req,
        &[1, 2],
        42,
        classical
    ));
    assert!(!verify_blind_issuance_request_with_profile(
        &req,
        &[1, 2],
        42,
        quantum
    ));
}

#[test]
fn credential_tokens_are_redacted_compared_in_full_and_erased() {
    let token = [0xA7u8; 32];
    let printed_token = "167, 167";
    let mut accumulator = IssuerCredentialAccumulator::new(PublicKey::test_key(), 7);
    let index = accumulator.enroll_issued([1; 32], [5; 6], token).unwrap();
    let witness = accumulator.membership_witness(index).unwrap();
    assert_eq!(witness.issuance_token, Some(token));
    let cred = BlindVerifiableCredential {
        issuer_epoch: 7,
        schema_id: 42,
        attr_commit: [5; 6],
        issuance_token: token,
        accumulator_leaf_index: index,
    };
    for text in [
        std::format!("{cred:?}"),
        std::format!("{witness:?}"),
        std::format!("{accumulator:?}"),
    ] {
        assert!(!text.contains(printed_token), "{text}");
        assert!(text.contains("<REDACTED>"), "{text}");
    }

    // Equality still distinguishes every token byte.
    for byte in [0, 13, 31] {
        let mut other = cred.clone();
        assert_eq!(cred, other);
        other.issuance_token[byte] ^= 1;
        assert_ne!(cred, other);

        let mut other = witness.clone();
        assert_eq!(witness, other);
        let mut changed = token;
        changed[byte] ^= 0x80;
        other.issuance_token = Some(changed);
        assert_ne!(witness, other);

        let mut other = accumulator.clone();
        assert_eq!(accumulator, other);
        other.enrolled_tokens[index] = Some(changed);
        assert_ne!(accumulator, other);
    }
    let mut other = witness.clone();
    other.issuance_token = None;
    assert_ne!(witness, other);
    let mut other = cred.clone();
    other.accumulator_leaf_index += 1;
    assert_ne!(cred, other);
    let mut other = witness.clone();
    other.siblings[3][2] ^= 1;
    assert_ne!(witness, other);

    // The duplicate-issuance index holds a digest, not the token, and still
    // refuses the same `(commitment, token)` pair under a new session.
    assert_eq!(accumulator.issued_tokens.len(), 1);
    assert!(!accumulator.issued_tokens.contains(&token));
    assert!(
        accumulator
            .issued_tokens
            .contains(&issued_token_index(&[5; 6], &token))
    );
    assert_eq!(
        accumulator.enroll_issued([2; 32], [5; 6], token),
        Err(BlindVcError::InvalidOprfEvaluation)
    );
    assert_eq!(accumulator.enroll_issued([2; 32], [6; 6], token), Ok(1));

    // What `Drop` runs.
    let mut cred = cred;
    cred.erase_secrets();
    assert_eq!(cred.issuance_token, [0; 32]);
    let mut witness = witness;
    witness.erase_secrets();
    assert_eq!(witness.issuance_token, Some([0; 32]));
    assert_eq!(witness.siblings, [[0; 6]; VC_ACCUMULATOR_DEPTH]);
    accumulator.erase_secrets();
    assert!(
        accumulator
            .enrolled_tokens
            .iter()
            .all(|token| token.is_none_or(|bytes| bytes == [0; 32]))
    );
    assert_eq!(accumulator.enrolled_tokens.len(), 2);
}

#[test]
fn quantum_issuance_roundtrip_and_downgrade_rejection() {
    let (mut req, _) = holder_prepare_blind_issuance_with_profile(
        42,
        &[1, 2],
        [3; 32],
        7,
        [4; 32],
        [5; 32],
        ZkSoundnessProfile::Quantum128,
    )
    .unwrap();
    assert_eq!(req.opened_reps.len(), 438);
    let (classical, _) = holder_prepare_blind_issuance_with_profile(
        42,
        &[1, 2],
        [3; 32],
        7,
        [4; 32],
        [5; 32],
        ZkSoundnessProfile::Classical128,
    )
    .unwrap();
    assert_ne!(
        classical.opened_reps[0].tape_seed_e,
        req.opened_reps[0].tape_seed_e
    );
    assert_ne!(
        classical.opened_reps[0].in_shares_e,
        req.opened_reps[0].in_shares_e
    );
    assert!(!verify_blind_issuance_request_with_profile(
        &classical,
        &[1, 2],
        42,
        ZkSoundnessProfile::Quantum128
    ));

    assert!(verify_blind_issuance_request_with_profile(
        &req,
        &[1, 2],
        42,
        ZkSoundnessProfile::Quantum128
    ));
    assert!(verify_blind_issuance_request(&req, &[1, 2], 42));
    req.opened_reps[0].gate_outs_e[0] = gl_add(req.opened_reps[0].gate_outs_e[0], 1);
    assert!(!verify_blind_issuance_request_with_profile(
        &req,
        &[1, 2],
        42,
        ZkSoundnessProfile::Quantum128
    ));
}

#[test]
fn selective_disclosure_rejects_round_and_gate_tampering() {
    for profile in [
        ZkSoundnessProfile::Classical128,
        ZkSoundnessProfile::Quantum128,
    ] {
        selective_disclosure_profile(profile);
    }
}

fn selective_disclosure_profile(profile: ZkSoundnessProfile) {
    let holder = HolderCredentialSecret {
        schema_id: 42,
        arity: 5,
        attrs: core::array::from_fn(|i| [840, 1994, 3, 9910, 2030, 0].get(i).copied().unwrap_or(0)),
        holder_blind: [17, 18, 19, 20],
    };
    let commitment = compute_vc_poseidon2_commit(
        holder.schema_id,
        &holder.attrs[..holder.arity],
        &holder.holder_blind,
        VC_ATTR_COMMIT_TAG,
    )
    .unwrap();
    let oprf_pk = PublicKey::test_key();
    let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk.clone(), 7);
    let index = accumulator.enroll(commitment).unwrap();
    let cred = BlindVerifiableCredential {
        issuer_epoch: 7,
        schema_id: 42,
        attr_commit: commitment,
        issuance_token: [0; 32],
        accumulator_leaf_index: index,
    };
    let (issuer_mldsa_pk, issuer_mldsa_sk) =
        crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x41; 32]);
    let root_attestation = accumulator
        .attest_root_deterministic(
            MlDsaLevel::MlDsa44,
            &issuer_mldsa_sk,
            issuer_mldsa_pk.clone(),
        )
        .unwrap();
    let mode = PresentationMode::ScopedPseudonym([0x5Au8; 32]);
    let mut presentation = prove_selective_disclosure_with_profile(
        &cred,
        &holder,
        &accumulator.membership_witness(index).unwrap(),
        &[0, 2],
        PresentationRequest {
            verifier_scope: b"verifier",
            verifier_challenge: &[73; 32],
            mode,
        },
        [72; 32],
        profile,
    )
    .unwrap();
    assert_eq!(presentation.opened_reps.len(), profile.sd_repetitions());
    assert!(verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));

    // Cross-profile downgrade rejection:
    let other_profile = match profile {
        ZkSoundnessProfile::Classical128 => ZkSoundnessProfile::Quantum128,
        ZkSoundnessProfile::Quantum128 => ZkSoundnessProfile::Classical128,
    };
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        other_profile,
    ));

    // Arity mismatch & tampering:
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        6,
        profile,
    ));
    presentation.arity = 6;
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        6,
        profile,
    ));
    presentation.arity = holder.arity;

    // Disclosed value tampering must be rejected!
    let orig_val = presentation.disclosed_attrs[0].1;
    presentation.disclosed_attrs[0].1 = gl_add(orig_val, 1);
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));
    presentation.disclosed_attrs[0].1 = orig_val;

    // Tampering the issuer's attested epoch or signature must be rejected!
    let mut wrong_epoch_att = root_attestation.clone();
    wrong_epoch_att.issuer_epoch = 8;
    assert!(!verify_presentation_with_profile(
        &presentation,
        &wrong_epoch_att,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));
    let (rogue_pk, rogue_sk) =
        crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x99; 32]);
    let rogue_att = accumulator
        .attest_root_deterministic(MlDsaLevel::MlDsa44, &rogue_sk, rogue_pk)
        .unwrap();
    assert!(!verify_presentation_with_profile(
        &presentation,
        &rogue_att,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));

    // Tampering GGM copath, hidden commitment, r_poly, alpha, beta, and aux must all fail!
    presentation.opened_reps[0].ggm_copath[0][0] ^= 1;
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));
    presentation.opened_reps[0].ggm_copath[0][0] ^= 1;

    presentation.opened_reps[0].com_1_hidden[0] ^= 1;
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));
    presentation.opened_reps[0].com_1_hidden[0] ^= 1;

    presentation.opened_reps[0].r_poly_without_b[0][0] =
        gl_add(presentation.opened_reps[0].r_poly_without_b[0][0], 1);
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));
    presentation.opened_reps[0].r_poly_without_b[0][0] =
        gl_sub(presentation.opened_reps[0].r_poly_without_b[0][0], 1);

    presentation.opened_reps[0].alpha[0][0] = gl_add(presentation.opened_reps[0].alpha[0][0], 1);
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));
    presentation.opened_reps[0].alpha[0][0] = gl_sub(presentation.opened_reps[0].alpha[0][0], 1);

    presentation.opened_reps[0].beta[0][0] = gl_add(presentation.opened_reps[0].beta[0][0], 1);
    assert!(!verify_presentation_with_profile(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &oprf_pk,
        b"verifier",
        &mut ReplayNotPrevented(&[73; 32]),
        mode,
        42,
        holder.arity,
        profile
    ));
    presentation.opened_reps[0].beta[0][0] = gl_sub(presentation.opened_reps[0].beta[0][0], 1);

    if let Some(aux_rep) = presentation
        .opened_reps
        .iter_mut()
        .find(|r| r.aux.is_some())
    {
        let aux = aux_rep.aux.as_mut().unwrap();
        aux.delta_z[0] = gl_add(aux.delta_z[0], 1);
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &mut ReplayNotPrevented(&[73; 32]),
            mode,
            42,
            holder.arity,
            profile
        ));
        let aux = presentation
            .opened_reps
            .iter_mut()
            .find(|r| r.aux.is_some())
            .unwrap()
            .aux
            .as_mut()
            .unwrap();
        aux.delta_z[0] = gl_sub(aux.delta_z[0], 1);
    }
}

#[test]
fn colluding_verifier_challenges_do_not_link_fresh_presentations() {
    let holder = HolderCredentialSecret {
        schema_id: 42,
        arity: 6,
        attrs: core::array::from_fn(|i| {
            [840, 1994, 3, 9910, 2030, 777].get(i).copied().unwrap_or(0)
        }),
        holder_blind: [17, 18, 19, 20],
    };
    let commitment = compute_vc_poseidon2_commit(
        holder.schema_id,
        &holder.attrs[..holder.arity],
        &holder.holder_blind,
        VC_ATTR_COMMIT_TAG,
    )
    .unwrap();
    let oprf_pk = PublicKey::test_key();
    let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk.clone(), 7);
    let index = accumulator.enroll(commitment).unwrap();
    let cred = BlindVerifiableCredential {
        issuer_epoch: 7,
        schema_id: 42,
        attr_commit: commitment,
        issuance_token: [0; 32],
        accumulator_leaf_index: index,
    };
    let (issuer_pk, issuer_sk) =
        crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x55; 32]);
    let root = accumulator
        .attest_root_deterministic(MlDsaLevel::MlDsa44, &issuer_sk, issuer_pk.clone())
        .unwrap();
    let membership = accumulator.membership_witness(index).unwrap();
    let profile = ZkSoundnessProfile::Classical128;
    let challenge = [0xC7; 32];
    let present = |holder: &HolderCredentialSecret, scope: &[u8], entropy| {
        prove_selective_disclosure_with_profile(
            &cred,
            holder,
            &membership,
            &[0],
            PresentationRequest {
                verifier_scope: scope,
                verifier_challenge: &challenge,
                mode: PresentationMode::UnlinkableFresh,
            },
            entropy,
            profile,
        )
    };
    let verify = |pres: &SelectiveDisclosurePresentation, scope: &[u8], challenge| {
        verify_presentation_with_profile(
            pres,
            &root,
            &issuer_pk,
            &oprf_pk,
            scope,
            &mut ReplayNotPrevented(challenge),
            PresentationMode::UnlinkableFresh,
            42,
            holder.arity,
            profile,
        )
    };
    // Verifier A tags this holder with C. B must not distinguish it from
    // an untagged holder by offering C in another scope.
    let a = present(&holder, b"verifier-a", [1; 32]).unwrap();
    let b = present(&holder, b"verifier-b", [2; 32]);
    assert!(
        b.is_ok(),
        "a prior verifier's challenge must not cause refusal: {:?}",
        b.as_ref().err()
    );
    let b = b.unwrap();
    assert!(verify(&a, b"verifier-a", &challenge));
    assert!(verify(&b, b"verifier-b", &challenge));
    assert!(!verify(&a, b"verifier-b", &challenge));
    assert!(!verify(&a, b"verifier-a", &[0xC8; 32]));
    assert_ne!(a.presentation_nonce, b.presentation_nonce);
    assert_ne!(a.scope_tag, b.scope_tag);
    assert_ne!(a.pres_commit, b.pres_commit);

    // Even in the same scope, fresh holder entropy permits the same
    // challenge without a stable pseudonym or reused proof randomness.
    // Refusing repeated challenges locally is deliberately not a promise.
    let b_again = present(&holder, b"verifier-b", [3; 32]).unwrap();
    assert!(verify(&b_again, b"verifier-b", &challenge));
    assert_ne!(b.presentation_nonce, b_again.presentation_nonce);
    assert_ne!(b.scope_tag, b_again.scope_tag);
    assert_ne!(b.pres_commit, b_again.pres_commit);
    for (r1, r2) in b.opened_reps.iter().zip(&b_again.opened_reps) {
        assert_ne!(r1.ggm_copath, r2.ggm_copath);
        assert_ne!(r1.com_1_hidden, r2.com_1_hidden);
    }
    // This test is about the holder side: the proofs are checked with the
    // replay opt-out. Refusing a second showing is the verifier ledger's job
    // (`memory_ledger_accepts_a_presentation_once`).
    assert!(verify(&b_again, b"verifier-b", &challenge));
}

/// One enrolled credential and everything a verifier pins. Deterministic, so a
/// child process rebuilds the same issuer root.
struct ReplayFixture {
    holder: HolderCredentialSecret,
    cred: BlindVerifiableCredential,
    membership: CredentialMembershipWitness,
    root: IssuerRootAttestation,
    issuer_pk: Vec<u8>,
    oprf_pk: PublicKey,
}

impl ReplayFixture {
    const PROFILE: ZkSoundnessProfile = ZkSoundnessProfile::Classical128;

    fn new() -> Self {
        let holder = HolderCredentialSecret {
            schema_id: 42,
            arity: 3,
            attrs: core::array::from_fn(|i| [840, 1994, 3].get(i).copied().unwrap_or(0)),
            holder_blind: [21, 22, 23, 24],
        };
        let commitment = compute_vc_poseidon2_commit(
            holder.schema_id,
            &holder.attrs[..holder.arity],
            &holder.holder_blind,
            VC_ATTR_COMMIT_TAG,
        )
        .unwrap();
        let oprf_pk = PublicKey::test_key();
        let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk.clone(), 7);
        let index = accumulator.enroll(commitment).unwrap();
        let (issuer_pk, issuer_sk) =
            crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x61; 32]);
        Self {
            holder,
            cred: BlindVerifiableCredential {
                issuer_epoch: 7,
                schema_id: 42,
                attr_commit: commitment,
                issuance_token: [0; 32],
                accumulator_leaf_index: index,
            },
            membership: accumulator.membership_witness(index).unwrap(),
            root: accumulator
                .attest_root_deterministic(MlDsaLevel::MlDsa44, &issuer_sk, issuer_pk.clone())
                .unwrap(),
            issuer_pk,
            oprf_pk,
        }
    }

    fn present(
        &self,
        scope: &[u8],
        challenge: &[u8; 32],
        entropy: [u8; 32],
    ) -> SelectiveDisclosurePresentation {
        prove_selective_disclosure_with_profile(
            &self.cred,
            &self.holder,
            &self.membership,
            &[0],
            PresentationRequest {
                verifier_scope: scope,
                verifier_challenge: challenge,
                mode: PresentationMode::UnlinkableFresh,
            },
            entropy,
            Self::PROFILE,
        )
        .unwrap()
    }

    fn verify(
        &self,
        pres: &SelectiveDisclosurePresentation,
        scope: &[u8],
        challenges: &mut dyn PresentationChallenges,
    ) -> bool {
        verify_presentation_with_profile(
            pres,
            &self.root,
            &self.issuer_pk,
            &self.oprf_pk,
            scope,
            challenges,
            PresentationMode::UnlinkableFresh,
            42,
            self.holder.arity,
            Self::PROFILE,
        )
    }
}

#[test]
fn memory_ledger_accepts_a_presentation_once() {
    let fx = ReplayFixture::new();
    let mut ledger = VerifierChallengeLedger::new(2);
    let challenge = ledger.issue(b"verifier-a", 1_000, 60, [0xE1; 32]).unwrap();
    let pres = fx.present(b"verifier-a", &challenge, [1; 32]);

    // An invalid proof for a live challenge leaves the challenge outstanding.
    let mut forged = pres.clone();
    forged.disclosed_attrs[0].1 = gl_add(forged.disclosed_attrs[0].1, 1);
    assert!(!fx.verify(&forged, b"verifier-a", &mut ledger.at(1_001)));
    assert_eq!(ledger.outstanding(), 1);

    // A's challenge relayed by verifier B: the holder's proof for B's scope is
    // valid, B's ledger position is refused, and A's challenge is not spent.
    let relayed = fx.present(b"verifier-b", &challenge, [2; 32]);
    assert!(fx.verify(&relayed, b"verifier-b", &mut ReplayNotPrevented(&challenge)));
    assert!(!fx.verify(&relayed, b"verifier-b", &mut ledger.at(1_001)));
    assert_eq!(ledger.outstanding(), 1);

    // Expired at 1_060; live at 1_059; accepted exactly once.
    assert!(!fx.verify(&pres, b"verifier-a", &mut ledger.at(1_060)));
    assert!(fx.verify(&pres, b"verifier-a", &mut ledger.at(1_059)));
    assert_eq!(ledger.outstanding(), 0);
    assert!(!fx.verify(&pres, b"verifier-a", &mut ledger.at(1_059)));
    assert!(!fx.verify(&pres, b"verifier-a", &mut ledger.at(1_001)));

    // A valid proof for a challenge this verifier never issued is refused.
    let stray = fx.present(b"verifier-a", &[0xC7; 32], [3; 32]);
    assert!(fx.verify(&stray, b"verifier-a", &mut ReplayNotPrevented(&[0xC7; 32])));
    assert!(!fx.verify(&stray, b"verifier-a", &mut ledger.at(1_001)));

    // The same holder answers a fresh challenge, once.
    let fresh = ledger.issue(b"verifier-a", 1_100, 60, [0xE2; 32]).unwrap();
    assert_ne!(fresh, challenge);
    let pres = fx.present(b"verifier-a", &fresh, [4; 32]);
    assert!(fx.verify(&pres, b"verifier-a", &mut ledger.at(1_101)));
    assert!(!fx.verify(&pres, b"verifier-a", &mut ledger.at(1_101)));
}

// The presentation is accepted by one process and refused by the next, which
// only shares the ledger file with it.
#[cfg(all(feature = "std", unix))]
#[test]
fn fs_ledger_refuses_a_replayed_presentation_in_another_process() {
    let _serial = crate::presentation_challenge::test_support::serial();
    const ROLE: &str = "QSAG_VC_CHALLENGE_CHILD_ROLE";
    const DIR: &str = "QSAG_VC_CHALLENGE_CHILD_DIR";
    let fx = ReplayFixture::new();
    if let Some(role) = std::env::var_os(ROLE) {
        let dir = std::path::PathBuf::from(std::env::var_os(DIR).unwrap());
        let ledger = FsVerifierChallengeLedger::open_existing(dir.join("challenges"), 4);
        if role == "locked" {
            assert!(ledger.is_err());
            return;
        }
        let pres = SelectiveDisclosurePresentation::from_compact_wire_bytes(
            &std::fs::read(dir.join("presentation")).unwrap(),
        )
        .unwrap();
        let accepted = fx.verify(&pres, b"verifier-a", &mut ledger.unwrap().at(1_001));
        assert_eq!(accepted, role == "accept");
        return;
    }
    let dir = crate::presentation_challenge::test_support::temporary_directory("process");
    let path = dir.join("challenges");
    let child = |role: &str| {
        std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "blind_vc::tests::fs_ledger_refuses_a_replayed_presentation_in_another_process",
                "--nocapture",
            ])
            .env(ROLE, role)
            .env(DIR, &dir)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .unwrap()
            .success()
    };
    let mut ledger = FsVerifierChallengeLedger::create_new(&path, 4).unwrap();
    let challenge = ledger.issue(b"verifier-a", 1_000, 60, [0xE3; 32]).unwrap();
    let pres = fx.present(b"verifier-a", &challenge, [5; 32]);
    std::fs::write(
        dir.join("presentation"),
        pres.to_compact_wire_bytes().unwrap(),
    )
    .unwrap();
    assert!(child("locked"));
    drop(ledger);
    assert!(child("accept"));
    // A second child that expects acceptance fails: the children really verify.
    assert!(!child("accept"));
    assert!(child("refuse"));
    let mut ledger = FsVerifierChallengeLedger::open_existing(&path, 4).unwrap();
    assert_eq!(ledger.outstanding(), 0);
    assert!(!fx.verify(&pres, b"verifier-a", &mut ledger.at(1_001)));
    drop(ledger);
    std::fs::remove_dir_all(dir).unwrap();
}

// A presentation accepted after a backup must stay refused when the backup is
// put back over the ledger. The unanchored ledger in the same scenario accepts
// it a second time: that is the gap the anchor closes.
#[cfg(all(feature = "std", unix))]
#[test]
fn anchored_fs_ledger_refuses_a_restored_file_and_the_bare_one_replays() {
    let _serial = crate::presentation_challenge::test_support::serial();
