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
    use crate::presentation_challenge::test_support::{TestAnchor, dir_files, temporary_directory};
    use alloc::boxed::Box;
    let fx = ReplayFixture::new();
    for anchored in [false, true] {
        let dir = temporary_directory(if anchored { "anchored" } else { "bare" });
        let path = dir.join("challenges");
        let anchor = TestAnchor::default();
        let open = || {
            if anchored {
                FsVerifierChallengeLedger::open_existing_anchored(
                    &path,
                    4,
                    Box::new(anchor.clone()),
                )
            } else {
                FsVerifierChallengeLedger::open_existing(&path, 4)
            }
        };
        let mut ledger = if anchored {
            FsVerifierChallengeLedger::create_new_anchored(&path, 4, Box::new(anchor.clone()))
        } else {
            FsVerifierChallengeLedger::create_new(&path, 4)
        }
        .unwrap();
        assert_eq!(ledger.is_anchored(), anchored);
        let challenge = ledger.issue(b"verifier-a", 1_000, 60, [0xE4; 32]).unwrap();
        drop(ledger);
        let pres = fx.present(b"verifier-a", &challenge, [6; 32]);
        let backup = dir_files(&dir);

        let mut ledger = open().unwrap();
        assert!(fx.verify(&pres, b"verifier-a", &mut ledger.at(1_001)));
        assert!(!fx.verify(&pres, b"verifier-a", &mut ledger.at(1_001)));
        drop(ledger);
        let current = dir_files(&dir);

        // In place: same inodes, earlier bytes, as a volume snapshot restore.
        for (file, bytes) in &backup {
            std::fs::write(file, bytes).unwrap();
        }
        let restored = open();
        if anchored {
            let err = restored.err().expect("rolled-back ledger must not open");
            assert!(std::format!("{err}").contains("rollback"), "{err}");
            for (file, bytes) in &current {
                std::fs::write(file, bytes).unwrap();
            }
            let mut ledger = open().unwrap();
            assert!(!fx.verify(&pres, b"verifier-a", &mut ledger.at(1_001)));
        } else {
            // No anchor: the consumed challenge is outstanding again.
            let mut ledger = restored.unwrap();
            assert!(fx.verify(&pres, b"verifier-a", &mut ledger.at(1_001)));
        }
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn repeated_entropy_across_distinct_statements_produces_independent_zkboo_shares() {
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
    let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk, 7);
    let index = accumulator.enroll(commitment).unwrap();
    let cred = BlindVerifiableCredential {
        issuer_epoch: 7,
        schema_id: 42,
        attr_commit: commitment,
        issuance_token: [0; 32],
        accumulator_leaf_index: index,
    };
    let reused_entropy = [0xAAu8; 32];
    let pres1 = prove_selective_disclosure(
        &cred,
        &holder,
        &accumulator.membership_witness(index).unwrap(),
        &[0],
        PresentationRequest {
            verifier_scope: b"scope-alpha",
            verifier_challenge: &[0x11; 32],
            mode: PresentationMode::UnlinkableFresh,
        },
        reused_entropy,
    )
    .unwrap();
    let pres2 = prove_selective_disclosure(
        &cred,
        &holder,
        &accumulator.membership_witness(index).unwrap(),
        &[0],
        PresentationRequest {
            verifier_scope: b"scope-alpha",
            verifier_challenge: &[0x22; 32],
            mode: PresentationMode::UnlinkableFresh,
        },
        reused_entropy,
    )
    .unwrap();

    // Statement hedging must make all repetition GGM trees, commitments, and aux vectors independent:
    assert_ne!(pres1.presentation_nonce, pres2.presentation_nonce);
    assert_ne!(pres1.pres_commit, pres2.pres_commit);
    assert_ne!(pres1.scope_tag, pres2.scope_tag);
    for (r1, r2) in pres1.opened_reps.iter().zip(&pres2.opened_reps) {
        assert_ne!(r1.ggm_copath, r2.ggm_copath);
        assert_ne!(r1.com_1_hidden, r2.com_1_hidden);
        if let (Some(a1), Some(a2)) = (&r1.aux, &r2.aux) {
            assert_ne!(a1.delta_w, a2.delta_w);
            assert_ne!(a1.delta_z, a2.delta_z);
        }
    }
}

#[test]
fn flat_view_wire_known_answer() {
    let expected = [
        61, 135, 171, 82, 130, 136, 55, 10, 124, 33, 88, 220, 132, 3, 153, 201, 11, 135, 206, 216,
        80, 196, 219, 81, 24, 19, 238, 51, 219, 46, 207, 21,
    ];
    assert_eq!(digest_party_view(&[2], &[1; 32], &[3], &[4]), expected);
    assert_ne!(digest_party_view(&[2, 3], &[1; 32], &[], &[4]), expected);
    assert_ne!(digest_party_view(&[2], &[1; 32], &[3, 0], &[4]), expected);
}

#[test]
fn selective_disclosure_compact_wire_sub_15mib_and_roundtrips() {
    let holder = HolderCredentialSecret {
        schema_id: 42,
        arity: MAX_VC_ATTRS,
        attrs: core::array::from_fn(|i| {
            [840, 1994, 3, 9910, 2030, 0]
                .get(i)
                .copied()
                .unwrap_or(i as u64 + 100)
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
    let (issuer_mldsa_pk, issuer_mldsa_sk) =
        crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x55; 32]);
    let root_attestation = accumulator
        .attest_root_deterministic(
            MlDsaLevel::MlDsa44,
            &issuer_mldsa_sk,
            issuer_mldsa_pk.clone(),
        )
        .unwrap();
    let cred = BlindVerifiableCredential {
        issuer_epoch: 7,
        schema_id: 42,
        attr_commit: commitment,
        issuance_token: [0; 32],
        accumulator_leaf_index: index,
    };

    for (profile, challenge_byte, max_bytes) in [
        (ZkSoundnessProfile::Classical128, 0x73u8, 6 * 1024 * 1024),
        (ZkSoundnessProfile::Quantum128, 0x74u8, 15 * 1024 * 1024),
    ] {
        let pres = prove_selective_disclosure_with_profile(
            &cred,
            &holder,
            &accumulator.membership_witness(index).unwrap(),
            &[0, 2, MAX_VC_ATTRS - 1],
            PresentationRequest {
                verifier_scope: b"compact-wire",
                verifier_challenge: &[challenge_byte; 32],
                mode: PresentationMode::UnlinkableFresh,
            },
            [0x42; 32],
            profile,
        )
        .unwrap();

        let compact = pres.to_compact_wire_bytes().unwrap();
        assert!(
            compact.len() < max_bytes,
            "{profile:?} wire size {} exceeded cap {max_bytes}",
            compact.len()
        );
        assert_eq!(pres.to_wire_bytes().unwrap(), compact);

        let decoded = SelectiveDisclosurePresentation::from_compact_wire_bytes(&compact).unwrap();
        assert_eq!(decoded, pres);
        assert!(verify_presentation_with_profile(
            &decoded,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"compact-wire",
            &mut ReplayNotPrevented(&[challenge_byte; 32]),
            PresentationMode::UnlinkableFresh,
            42,
            holder.arity,
            profile,
        ));

        // Truncated, trailing-byte, and bit-flipped payloads fail cleanly.
        assert!(
            SelectiveDisclosurePresentation::from_compact_wire_bytes(&compact[..compact.len() - 1])
                .is_err()
        );
        let mut trailing = compact.clone();
        trailing.push(0);
        assert!(SelectiveDisclosurePresentation::from_compact_wire_bytes(&trailing).is_err());

        let mut tampered = compact;
        let last = tampered.len() - 64;
        tampered[last] ^= 1;
        if let Ok(bad_pres) = SelectiveDisclosurePresentation::from_compact_wire_bytes(&tampered) {
            assert!(!verify_presentation_with_profile(
                &bad_pres,
                &root_attestation,
                &issuer_mldsa_pk,
                &oprf_pk,
                b"compact-wire",
                &mut ReplayNotPrevented(&[challenge_byte; 32]),
                PresentationMode::UnlinkableFresh,
                42,
                holder.arity,
                profile,
            ));
        }
    }
}

fn kat_hex(digest: &[u8; 32]) -> std::string::String {
    digest.iter().map(|b| std::format!("{b:02x}")).collect()
}

fn kat_absorb_u64s(sp: &mut Shake256, xs: &[u64]) {
    sp.absorb(&(xs.len() as u64).to_le_bytes());
    for x in xs {
        sp.absorb(&x.to_le_bytes());
    }
}

fn kat_issuance_digest(req: &BlindIssuanceRequest) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(&req.issuer_pk_digest);
    sp.absorb(&req.issuer_epoch.to_le_bytes());
    kat_absorb_u64s(&mut sp, &req.issuer_attested_attrs);
    sp.absorb(&req.session_id);
    sp.absorb(&req.schema_id.to_le_bytes());
    kat_absorb_u64s(&mut sp, &req.attr_commit);
    sp.absorb(&(req.opened_reps.len() as u64).to_le_bytes());
    for o in &req.opened_reps {
        sp.absorb(&[o.e]);
        sp.absorb(&o.unopened_commitment);
        sp.absorb(&o.salt_e);
        sp.absorb(&o.salt_e1);
        kat_absorb_u64s(&mut sp, &o.in_shares_e);
        kat_absorb_u64s(&mut sp, &o.in_shares_e1);
        sp.absorb(&o.tape_seed_e);
        sp.absorb(&o.tape_seed_e1);
        kat_absorb_u64s(&mut sp, &o.gate_outs_e);
        kat_absorb_u64s(&mut sp, &o.gate_outs_e1);
        for row in &o.final_outs_all3 {
            kat_absorb_u64s(&mut sp, row);
        }
        sp.absorb(&(o.num_active_final_outs as u64).to_le_bytes());
    }
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

fn kat_bytes_digest(bytes: &[u8]) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(bytes);
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// Wire-compatibility pin: a fixed-seed issuance request and fixed-seed presentations under
/// both profiles and both presentation modes must keep these exact bytes.
#[test]
fn fixed_seed_issuance_and_presentation_bytes_known_answer() {
    let attrs = [840u64, 1994, 3, 9910, 2030, 0, 77];
    let oprf_pk = PublicKey::test_key();
    let (req, holder) = holder_prepare_blind_issuance_with_profile(
        42,
        &attrs,
        oprf_pk.commitment(),
        7,
        [0x11; 32],
        [0x22; 32],
        ZkSoundnessProfile::Classical128,
    )
    .unwrap();
    assert!(verify_blind_issuance_request_with_profile(
        &req,
        &attrs,
        42,
        ZkSoundnessProfile::Classical128,
    ));

    let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk.clone(), 7);
    accumulator.enroll([1, 2, 3, 4, 5, 6]).unwrap();
    let index = accumulator.enroll(req.attr_commit).unwrap();
    accumulator.enroll([9; 6]).unwrap();
    let (issuer_mldsa_pk, issuer_mldsa_sk) =
        crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x55; 32]);
    let root_attestation = accumulator
        .attest_root_deterministic(
            MlDsaLevel::MlDsa44,
            &issuer_mldsa_sk,
            issuer_mldsa_pk.clone(),
        )
        .unwrap();
    let cred = BlindVerifiableCredential {
        issuer_epoch: 7,
        schema_id: 42,
        attr_commit: req.attr_commit,
        issuance_token: [0; 32],
        accumulator_leaf_index: index,
    };

    let mut actual = std::vec![
        kat_hex(&kat_issuance_digest(&req)),
        kat_hex(&kat_bytes_digest(
            &accumulator
                .root()
                .iter()
                .flat_map(|limb| limb.to_le_bytes())
                .collect::<Vec<u8>>(),
        )),
    ];
    for (profile, mode, challenge_byte) in [
        (
            ZkSoundnessProfile::Classical128,
            PresentationMode::UnlinkableFresh,
            0x73u8,
        ),
        (
            ZkSoundnessProfile::Quantum128,
            PresentationMode::ScopedPseudonym([0x5A; 32]),
            0x74u8,
        ),
    ] {
        let pres = prove_selective_disclosure_with_profile(
            &cred,
            &holder,
            &accumulator.membership_witness(index).unwrap(),
            &[0, 2, 6],
            PresentationRequest {
                verifier_scope: b"kat-scope",
                verifier_challenge: &[challenge_byte; 32],
                mode,
            },
            [0x42; 32],
            profile,
        )
        .unwrap();
        let wire = pres.to_compact_wire_bytes().unwrap();
        let decoded = SelectiveDisclosurePresentation::from_compact_wire_bytes(&wire).unwrap();
        assert!(verify_presentation_with_profile(
            &decoded,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"kat-scope",
            &mut ReplayNotPrevented(&[challenge_byte; 32]),
            mode,
            42,
            attrs.len(),
            profile,
        ));
        actual.push(kat_hex(&kat_bytes_digest(&wire)));
    }
    std::println!("BVC_KAT {actual:?}");
    // The first digest is the classical issuance request. It was re-pinned when
    // the `Classical128` statement and transcript gained their explicit profile
    // tag (before that only `Quantum128` was tagged); the accumulator root and
    // both presentation wires below did not change.
    assert_eq!(
        actual,
        [
            "5c060f825fb8fbe4367879bb70cde5b53f2bd6d5e856cd85dd45ea289be47cbc",
            "ac05d706c5c72c17f54a06fbcd0b6fcc3b1bc9b447529ab75a7cb587201d86b1",
            "d4bfec08995d0f69f759734b211a542e9e590b2aa9faad9f94a50fc6f2381839",
            "07813ef70176b90e6e06c194853794a20189acba1d2c4bd6eb4c73a1b82e1e7b",
        ]
    );
}

// ------------------------------------------------------------------------
// Independent reference of the canonical Poseidon2-12 profile. Nothing below
// calls `qsag_accel::poseidon2`: field arithmetic is `u128 % p`, the linear
// layers are explicit 12x12 matrices built from their definitions, and the
// round constants are re-derived from the `POS2_GL1` generator.
// ------------------------------------------------------------------------

const REF_P: u128 = 0xFFFF_FFFF_0000_0001;
type RefMat = [[u64; 12]; 12];

fn ref_add(a: u64, b: u64) -> u64 {
    ((a as u128 + b as u128) % REF_P) as u64
}

fn ref_mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % REF_P) as u64
}

/// `M_E = M_4 (x) P_3`: entry `(3i + a, 3j + b) = M_4[i][j] * P_3[a][b]` with
/// `M_4 = circ(2, 3, 1, 1)` and `P_3 = circ(2, 1, 1)`.
fn ref_dense_me() -> RefMat {
    const M4: [[u64; 4]; 4] = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]];
    const P3: [[u64; 3]; 3] = [[2, 1, 1], [1, 2, 1], [1, 1, 2]];
    let mut m = [[0u64; 12]; 12];
    for i in 0..4 {
        for a in 0..3 {
            for j in 0..4 {
                for b in 0..3 {
                    m[3 * i + a][3 * j + b] = M4[i][j] * P3[a][b];
                }
            }
        }
    }
    m
}

/// The superseded external matrix `P_3 (x) M_4`: entry `(4a + i, 4b + j)`.
fn ref_dense_me_superseded() -> RefMat {
    let canonical = ref_dense_me();
    let mut m = [[0u64; 12]; 12];
    for i in 0..4 {
        for a in 0..3 {
            for j in 0..4 {
                for b in 0..3 {
                    m[4 * a + i][4 * b + j] = canonical[3 * i + a][3 * j + b];
                }
            }
        }
    }
    m
}

/// `M_I = J + diag(-64, 1, 2, 4, ..., 1024)`.
fn ref_dense_mi() -> RefMat {
    let mut m = [[1u64; 12]; 12];
    m[0][0] = ref_add(1, (REF_P - 64) as u64);
    for (k, row) in m.iter_mut().enumerate().skip(1) {
        row[k] = 1 + (1u64 << (k - 1));
    }
    m
}

fn ref_mat_vec(m: &RefMat, v: &[u64; 12]) -> [u64; 12] {
    core::array::from_fn(|i| {
        (0..12).fold(0u64, |acc, j| {
            ref_add(acc, ref_mul(m[i][j], v[j] % REF_P as u64))
        })
    })
}

fn ref_mix13(x: u64) -> u64 {
    let z0 = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let z1 = (z0 ^ (z0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z2 = (z1 ^ (z1 >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z2 ^ (z2 >> 31)
}

fn ref_round_constant(tag: u64, round: u64, lane: u64) -> u64 {
    const IV: u64 = u64::from_be_bytes(*b"POS2_GL1");
    (ref_mix13(ref_mix13(ref_mix13(IV ^ tag) ^ round) ^ lane) as u128 % REF_P) as u64
}

fn ref_pow7(x: u64) -> u64 {
    let x2 = ref_mul(x, x);
    let x4 = ref_mul(x2, x2);
    ref_mul(ref_mul(x4, x2), x)
}

/// Initial `M_E`; 4 full rounds (tag 0); 22 partial rounds (tag 1, lane 0); 4 full rounds (tag 2).
fn ref_perm12(st: &mut [u64; 12]) {
    let (me, mi) = (ref_dense_me(), ref_dense_mi());
    *st = ref_mat_vec(&me, st);
    for tag in [0u64, 1, 2] {
        let rounds = if tag == 1 { 22 } else { 4 };
        for r in 0..rounds {
            if tag == 1 {
                st[0] = ref_pow7(ref_add(st[0], ref_round_constant(1, r, 0)));
                *st = ref_mat_vec(&mi, st);
            } else {
                for (lane, x) in st.iter_mut().enumerate() {
                    *x = ref_pow7(ref_add(*x, ref_round_constant(tag, r, lane as u64)));
                }
                *st = ref_mat_vec(&me, st);
            }
        }
    }
}

/// Rate-6, capacity-6 sponge of this module over the reference permutation.
fn ref_sponge12(message: &[u64]) -> [u64; 12] {
    let mut state = [0u64; 12];
    for chunk in message.chunks(6) {
        for (lane, &value) in state.iter_mut().zip(chunk) {
            *lane = ref_add(*lane, value);
        }
        if chunk.len() < 6 {
            state[chunk.len()] = ref_add(state[chunk.len()], 1);
        }
        ref_perm12(&mut state);
    }
    if message.len().is_multiple_of(6) {
        state[0] = ref_add(state[0], 1);
        ref_perm12(&mut state);
    }
    state
}

struct TestRng(u64);

impl TestRng {
    fn next_field(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0xA076_1D64_78BD_642F);
        (ref_mix13(self.0) as u128 % REF_P) as u64
    }

    fn state(&mut self) -> [u64; 12] {
        core::array::from_fn(|_| self.next_field())
    }
}

const GATES_PER_RAW_PERM12: usize = GATES_PER_PERM12 / 3;

fn poseidon2_test_states() -> Vec<[u64; 12]> {
    let max = (REF_P - 1) as u64;
    let mut states = vec![
        [0u64; 12],
        [max; 12],
        core::array::from_fn(|i| i as u64),
        core::array::from_fn(|i| if i.is_multiple_of(2) { max } else { 1 }),
    ];
    for lane in 0..12 {
        states.push(core::array::from_fn(|i| u64::from(i == lane)));
    }
    let mut rng = TestRng(0x5EED_0001);
    for _ in 0..24 {
        states.push(rng.state());
    }
    states
}

#[test]
fn poseidon2_reference_permutation_reproduces_the_canonical_kat() {
    let mut st: [u64; 12] = core::array::from_fn(|i| i as u64);
    ref_perm12(&mut st);
    assert_eq!(
        st,
        [
            13782584570844608145,
            13136387643152332171,
            7171133015474200819,
            7643370872200861694,
            14144755201299840503,
            16470027036684692562,
            1748465969625202405,
            1718729118078964347,
            6141020819996733037,
            16322330185628708898,
            11650380702735067362,
            2734959974607798415,
        ]
    );
    // The superseded profile is a different function, so every comparison below can fail.
    assert_ne!(ref_dense_me(), ref_dense_me_superseded());
}

#[test]
fn circuit_linear_layers_equal_the_dense_canonical_matrices() {
    let (me, mi) = (ref_dense_me(), ref_dense_mi());
    let superseded = ref_dense_me_superseded();
    let mut rng = TestRng(0x5EED_0002);

    // Exact matrices of the shared kernels, column by column.
    let mut saw_superseded_difference = false;
    for j in 0..12 {
        let unit: [u64; 12] = core::array::from_fn(|i| u64::from(i == j));
        let (mut e_col, mut i_col) = (unit, unit);
        poseidon2_apply_me(&mut e_col);
        poseidon2_apply_mi(&mut i_col);
        for row in 0..12 {
            assert_eq!(e_col[row], me[row][j], "M_E[{row}][{j}]");
            assert_eq!(i_col[row], mi[row][j], "M_I[{row}][{j}]");
            saw_superseded_difference |= e_col[row] != superseded[row][j];
        }
    }
    assert!(saw_superseded_difference);

    // The per-share wrappers of both ZKBoo tapes act as the same matrix on every share slot.
    for _ in 0..32 {
        let slots: [[u64; 12]; 3] = core::array::from_fn(|_| rng.state());
        let st3: [[u64; 3]; 12] = core::array::from_fn(|lane| [0, 1, 2].map(|m| slots[m][lane]));
        let st2: [[u64; 2]; 12] = core::array::from_fn(|lane| [0, 1].map(|m| slots[m][lane]));

        let (mut e3, mut i3, mut e2, mut i2) = (st3, st3, st2, st2);
        apply_me_3(&mut e3);
        apply_mi_3(&mut i3);
        apply_me_2(&mut e2);
        apply_mi_2(&mut i2);
        for (m, slot) in slots.iter().enumerate() {
            let want_e = ref_mat_vec(&me, slot);
            let want_i = ref_mat_vec(&mi, slot);
            for lane in 0..12 {
                assert_eq!(e3[lane][m], want_e[lane]);
                assert_eq!(i3[lane][m], want_i[lane]);
                if m < 2 {
                    assert_eq!(e2[lane][m], want_e[lane]);
                    assert_eq!(i2[lane][m], want_i[lane]);
                }
            }
        }

        // Plaintext and N-party engines call the shared kernels directly on one share.
        let (mut e1, mut i1) = (slots[0], slots[0]);
        poseidon2_apply_me(&mut e1);
        poseidon2_apply_mi(&mut i1);
        assert_eq!(e1, ref_mat_vec(&me, &slots[0]));
        assert_eq!(i1, ref_mat_vec(&mi, &slots[0]));
    }
}

/// Run one raw permutation (`sponge == false`, `input.len() == 12`) or one sponge call of
/// every in-circuit engine on `input`; returns the reconstructed 12-lane outputs of the
/// plaintext recorder, the 3-party ZKBoo tapes and the N-party share evaluator.
fn run_all_circuit_engines(input: &[u64], sponge: bool, rng: &mut TestRng) -> [[u64; 12]; 3] {
    let gates = if sponge {
        (input.len() / 6 + 1) * GATES_PER_RAW_PERM12
    } else {
        GATES_PER_RAW_PERM12
    };

    // Plaintext gate recorder (selective-disclosure prover trace).
    let mut rec = PlaintextGateRecorder::new();
    let mut plain = input.to_vec();
    if sponge {
        rec.perm12(&mut plain);
    } else {
        rec.raw_perm12((&mut plain[..]).try_into().unwrap());
    }
    assert_eq!(rec.x.len(), gates);
    let plain_out: [u64; 12] = plain[..12].try_into().unwrap();

    // 3-party ZKBoo prover, then the verifier replay of each opened pair of views.
    let tape_seeds: [[u8; 32]; 3] = core::array::from_fn(|m| [0xA0 + m as u8; 32]);
    let shares: Vec<[u64; 3]> = input
        .iter()
        .map(|&v| split_secret_3(v, rng.next_field(), rng.next_field()))
        .collect();
    let mut prover = ZkBooProverTape::new(&tape_seeds, gates);
    let mut prover_st = shares.clone();
    if sponge {
        prover.perm12(&mut prover_st);
    } else {
        prover.raw_perm12((&mut prover_st[..]).try_into().unwrap());
    }
    assert_eq!(prover.gate_cursor, gates);
    let zkboo_out: [u64; 12] =
        core::array::from_fn(|lane| prover_st[lane].iter().fold(0, |acc, &s| gl_add(acc, s)));
    for e in 0..3 {
        let e1 = (e + 1) % 3;
        let mut verifier = ZkBooVerifierTape::new(
            e,
            &tape_seeds[e],
            &tape_seeds[e1],
            &prover.out[e],
            &prover.out[e1],
            gates,
        );
        let mut verifier_st: Vec<[u64; 2]> = shares.iter().map(|s| [s[e], s[e1]]).collect();
        if sponge {
            verifier.perm12(&mut verifier_st);
        } else {
            verifier.raw_perm12((&mut verifier_st[..]).try_into().unwrap());
        }
        assert!(verifier.ok, "opened views {e},{e1} replay");
        assert_eq!(verifier.gate_cursor, gates);
        for lane in 0..12 {
            assert_eq!(verifier_st[lane], [prover_st[lane][e], prover_st[lane][e1]]);
        }
    }

    // N-party additive-share evaluator (selective-disclosure parties), N = 5.
    const PARTIES: usize = 5;
    let mut share_sum = [0u64; 12];
    let mut x_sum = vec![0u64; gates];
    let mut y_sum = vec![0u64; gates];
    let mut in_rest = vec![0u64; input.len()];
    let mut z_rest = vec![0u64; gates];
    for party in 0..PARTIES {
        let last = party == PARTIES - 1;
        let mut st: Vec<u64> = (0..input.len())
            .map(|k| {
                if last {
                    gl_sub(input[k], in_rest[k])
                } else {
                    let s = rng.next_field();
                    in_rest[k] = gl_add(in_rest[k], s);
                    s
                }
            })
            .collect();
        let z_shares: Vec<u64> = (0..gates)
            .map(|g| {
                if last {
                    gl_sub(rec.z[g], z_rest[g])
                } else {
                    let s = rng.next_field();
                    z_rest[g] = gl_add(z_rest[g], s);
                    s
                }
            })
            .collect();
        let (mut x_out, mut y_out, mut z_out) =
            (vec![0u64; gates], vec![0u64; gates], vec![0u64; gates]);
        let mut ev = LinearShareEvaluator {
            is_party_zero: party == 0,
            z_shares: &z_shares,
            gate_cursor: 0,
            x_out: &mut x_out,
            y_out: &mut y_out,
            z_out: &mut z_out,
        };
        if sponge {
            ev.perm12(&mut st);
        } else {
            ev.raw_perm12((&mut st[..]).try_into().unwrap());
        }
        assert_eq!(ev.gate_cursor, gates);
        for lane in 0..12 {
            share_sum[lane] = gl_add(share_sum[lane], st[lane]);
        }
        for g in 0..gates {
            x_sum[g] = gl_add(x_sum[g], x_out[g]);
            y_sum[g] = gl_add(y_sum[g], y_out[g]);
        }
    }
    // The parties' multiplication inputs reconstruct the plaintext trace gate by gate.
    assert_eq!(x_sum, rec.x);
    assert_eq!(y_sum, rec.y);

    [plain_out, zkboo_out, share_sum]
}

#[test]
fn in_circuit_poseidon2_perm12_matches_canonical_permutation() {
    let mut rng = TestRng(0x5EED_0003);
    for state in poseidon2_test_states() {
        let mut reference = state;
        ref_perm12(&mut reference);
        let mut canonical = state;
        poseidon2_perm12(&mut canonical);
        assert_eq!(canonical, reference, "accel permutation vs dense reference");

        for (engine, out) in run_all_circuit_engines(&state, false, &mut rng)
            .iter()
            .enumerate()
        {
            assert_eq!(*out, canonical, "engine {engine} on {state:?}");
        }
    }
}

#[test]
fn in_circuit_sponge_and_clear_commitments_match_reference_sponge() {
    let mut rng = TestRng(0x5EED_0004);
    for len in [12usize, 13, 16, 17, 18, 39] {
        let message: Vec<u64> = (0..len).map(|_| rng.next_field()).collect();
        let reference = ref_sponge12(&message);
        let mut clear = message.clone();
        sponge12(&mut clear);
        assert_eq!(clear[..12], reference, "clear sponge, len {len}");
        for (engine, out) in run_all_circuit_engines(&message, true, &mut rng)
            .iter()
            .enumerate()
        {
            assert_eq!(*out, reference, "engine {engine}, len {len}");
        }
    }

    // Clear commitment layouts over the reference sponge.
    let reduce = |x: u64| (x as u128 % REF_P) as u64;
    let (schema_id, epoch) = (0x0123_4567_89AB_CDEFu64, 0xFEDC_BA98_7654_3210u64);
    let blind = [
        rng.next_field(),
        rng.next_field(),
        rng.next_field(),
        rng.next_field(),
    ];
    for arity in [1usize, 6, 7, MAX_VC_ATTRS] {
        let attrs: Vec<u64> = (0..arity).map(|_| rng.next_field()).collect();
        for tag in [VC_ATTR_COMMIT_TAG, VC_PRES_COMMIT_TAG] {
            let mut message = attrs.clone();
            message.resize(arity.max(6), 0);
            message.extend_from_slice(&blind);
            message.extend_from_slice(&[
                schema_id & 0xffff_ffff,
                ref_add(schema_id >> 32, reduce(tag)),
                arity as u64,
            ]);
            assert_eq!(
                compute_vc_poseidon2_commit(schema_id, &attrs, &blind, tag).unwrap(),
                ref_sponge12(&message)[..6],
            );
        }
    }

    let scope = [
        rng.next_field(),
        rng.next_field(),
        rng.next_field(),
        rng.next_field(),
    ];
    let mut message = blind.to_vec();
    message.extend_from_slice(&scope);
    message.extend_from_slice(&[
        0,
        0,
        schema_id & 0xffff_ffff,
        ref_add(schema_id >> 32, reduce(VC_SCOPE_TAG_DOM)),
    ]);
    assert_eq!(
        compute_vc_scope_tag(schema_id, &blind, &scope),
        ref_sponge12(&message)[..6],
    );

    let left: [u64; 6] = core::array::from_fn(|_| rng.next_field());
    let right: [u64; 6] = core::array::from_fn(|_| rng.next_field());
    let mut message = left.to_vec();
    message.extend_from_slice(&right);
    message.extend_from_slice(&[
        epoch & 0xffff_ffff,
        9,
        reduce(VC_MERKLE_NODE_TAG),
        ref_add(epoch >> 32, reduce(u64::from_be_bytes(*b"POS2_GL1"))),
    ]);
    assert_eq!(
        merkle_hash_pair(&left, &right, epoch, 9),
        ref_sponge12(&message)[..6],
    );
}

#[test]
fn fp5_arithmetic_matches_schoolbook_reference() {
    fn ref_fp5_mul(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
        let mut wide = [0u64; 9];
        for i in 0..5 {
            for j in 0..5 {
                wide[i + j] = ref_add(wide[i + j], ref_mul(a[i], b[j]));
            }
        }
        // T^5 = 3.
        core::array::from_fn(|k| {
            if k < 4 {
                ref_add(wide[k], ref_mul(3, wide[k + 5]))
            } else {
                wide[k]
            }
        })
    }

    let max = (REF_P - 1) as u64;
    let mut rng = TestRng(0x5EED_0005);
    let mut elems = vec![[0u64; 5], [1, 0, 0, 0, 0], [max; 5], [0, 0, 0, 0, max]];
    for _ in 0..24 {
        elems.push(core::array::from_fn(|_| rng.next_field()));
    }
    for &a in &elems {
        let fa = Fp5::from_limbs(a);
        assert_eq!(fa.to_limbs(), a);
        assert_eq!(Fp5::from_canonical_limbs(a), Some(fa));
        assert_eq!(fa.is_zero(), a == [0; 5]);
        let bytes: Vec<u8> = a.iter().flat_map(|limb| limb.to_le_bytes()).collect();
        assert_eq!(fa.to_le_bytes()[..], bytes[..]);
        let scalar = rng.next_field();
        assert_eq!(
            fa.scale_fp(scalar).to_limbs(),
            a.map(|limb| ref_mul(limb, scalar))
        );
        for &b in &elems {
            let fb = Fp5::from_limbs(b);
            assert_eq!(fa.mul(fb).to_limbs(), ref_fp5_mul(a, b));
            assert_eq!(
                fa.add(fb).to_limbs(),
                core::array::from_fn(|i| ref_add(a[i], b[i]))
            );
            assert_eq!(
                fa.sub(fb).to_limbs(),
                core::array::from_fn(|i| ref_add(a[i], (REF_P as u64) - b[i]))
            );
        }
    }
    // The alias band is rejected limb by limb, and wide reduction agrees with `u128 % p`.
    for k in 0..5 {
        for bad in [REF_P as u64, u64::MAX] {
            let alias: [u64; 5] = core::array::from_fn(|i| if i == k { bad } else { 7 });
            assert_eq!(Fp5::from_canonical_limbs(alias), None);
        }
    }
    for _ in 0..64 {
        let lo = ((rng.next_field() as u128) << 64) | ref_mix13(rng.0) as u128;
        let hi = ((rng.next_field() as u128) << 64) | ref_mix13(!rng.0) as u128;
        // lo + 2^64 * hi (mod p), reduced limb-wise in u128 without overflow.
        let two_64 = (1u128 << 64) % REF_P;
        let want = ((lo % REF_P) + ((hi % REF_P) * two_64) % REF_P) % REF_P;
        assert_eq!(
            gl_reduce_split_u192(lo, hi).to_canonical_u64() as u128,
            want
        );
    }
}

#[test]
fn holder_credential_secret_accessors_match_attr_commit() {
    let attrs = [101u64, 202, 303, 404];
    let (req, holder) = holder_prepare_blind_issuance_with_profile(
        0x77,
        &attrs,
        [0x11; 32],
        5,
        [0x22; 32],
        [0x33; 32],
        ZkSoundnessProfile::Classical128,
    )
    .unwrap();
    assert_eq!(holder.arity(), 4);
    assert_eq!(holder.attrs(), &attrs);
    let recomputed = compute_vc_poseidon2_commit(
        holder.schema_id,
        holder.attrs(),
        holder.holder_blind(),
        VC_ATTR_COMMIT_TAG,
    )
    .unwrap();
    assert_eq!(recomputed, req.attr_commit);
}
