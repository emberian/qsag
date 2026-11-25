use super::*;
use crate::field::GOLDILOCKS_PRIME;
use crate::{AggSigProfile, ValidatorKeypair};

fn exercise(scheme: AggSigProfile, profile: HemQuinticProfile, n: usize) {
    let mut keys: Vec<_> = (0..n)
        .map(|i| ValidatorKeypair::keygen_deterministic(scheme, &[9; 32], i as u32))
        .collect();
    let pks: Vec<_> = keys.iter().map(|k| k.pk).collect();
    let messages: Vec<_> = (0..n).map(|i| [i as u8, 17]).collect();
    let refs: Vec<_> = messages.iter().map(|m| m.as_slice()).collect();
    let mode = SigningMode::PerSignerMessages(&refs);
    let mut sigs: Vec<_> = keys
        .iter_mut()
        .zip(&refs)
        .map(|(key, m)| {
            {
                if scheme.is_jorts() {
                    key.sign_stateful_for_unit_test(m, 0)
                } else {
                    key.sign_stateless_for_unit_test(m)
                }
            }
            .unwrap()
        })
        .collect();
    let bitmap = SignerBitmap::from_active_indices(n as u32, &(0..n).collect::<Vec<_>>()).unwrap();
    let proof = prove_hem_quintic_128(profile, &pks, &bitmap, &mode, &sigs).unwrap();
    assert!(verify_hem_quintic_128(profile, &pks, &mode, &proof));
    let other_profile = match profile {
        HemQuinticProfile::TurboShake400 => HemQuinticProfile::Poseidon2Gl24,
        HemQuinticProfile::Poseidon2Gl24 => HemQuinticProfile::TurboShake400,
    };
    assert!(!verify_hem_quintic_128(other_profile, &pks, &mode, &proof));
    let bytes = proof.to_bytes();
    assert_eq!(HemQuinticProof::from_bytes(&bytes).unwrap(), proof);
    assert!(HemQuinticProof::from_bytes(&bytes[..bytes.len() - 1]).is_none());
    assert!(HemQuinticProof::from_bytes(&[bytes.as_slice(), &[0]].concat()).is_none());
    if scheme.is_jorts() {
        assert_eq!(
            prove_hem_quintic_128(profile, &pks, &bitmap, &mode, &sigs).unwrap(),
            proof
        );
    }
    let mut different_keys = pks.clone();
    different_keys[0].pk_seed[2] += F::ONE;
    assert!(!verify_hem_quintic_128(
        profile,
        &different_keys,
        &mode,
        &proof
    ));
    let mut different_messages = refs.clone();
    different_messages[0] = &[0, 16];
    assert!(!verify_hem_quintic_128(
        profile,
        &pks,
        &SigningMode::PerSignerMessages(&different_messages),
        &proof
    ));
    for (chain, limb) in [(0, 0), (3, 1), (sigs[0].layers[0].wots_chains.len() - 1, 3)] {
        sigs[0].layers[0].wots_chains[chain][limb] += F::ONE;
        assert_eq!(
            prove_hem_quintic_128(profile, &pks, &bitmap, &mode, &sigs),
            Err(Error::Signature)
        );
        sigs[0].layers[0].wots_chains[chain][limb] -= F::ONE;
    }
    let digest = if profile == HemQuinticProfile::TurboShake400 {
        50
    } else {
        56
    };
    let st = statement(profile, &pks, &bitmap, &mode).unwrap();
    let first_fold = digest + 40 * (9 * st.circuit.log_rows() + NUM_TRACE_COLS + 5);
    for offset in (0..5).map(|i| first_fold + 40 * i).chain([
        0,
        proof.payload.len() - digest,
        proof.payload.len() - 1,
    ]) {
        let mut bad = proof.clone();
        bad.payload[offset] ^= 1;
        assert!(
            !verify_hem_quintic_128(profile, &pks, &mode, &bad),
            "mutation at {offset}"
        );
    }
    let columns = digest + 360 * st.circuit.log_rows();
    for offset in [digest + 352, columns + 40 * (NUM_TRACE_COLS - 1) + 32] {
        let mut bad = proof.clone();
        bad.payload[offset..offset + 8].copy_from_slice(&GOLDILOCKS_PRIME.to_le_bytes());
        assert!(!verify_hem_quintic_128(profile, &pks, &mode, &bad));
    }
    let mut bad = proof.clone();
    bad.payload[digest] ^= 1;
    assert!(!verify_hem_quintic_128(profile, &pks, &mode, &bad));
    if profile == HemQuinticProfile::Poseidon2Gl24 {
        let mut bad = proof.clone();
        let last = bad.payload.len() - 8;
        bad.payload[last..].copy_from_slice(&GOLDILOCKS_PRIME.to_le_bytes());
        assert!(!verify_hem_quintic_128(profile, &pks, &mode, &bad));
    }
    let mut bad = proof.clone();
    bad.payload.push(0);
    assert!(!verify_hem_quintic_128(profile, &pks, &mode, &bad));
    bad.payload.truncate(proof.payload.len() - 1);
    assert!(!verify_hem_quintic_128(profile, &pks, &mode, &bad));
}

#[test]
fn tooth_jorts_turbo_batch() {
    exercise(
        AggSigProfile::JortsPoseidon2,
        HemQuinticProfile::TurboShake400,
        2,
    );
}

#[test]
fn tooth_jorts_gl24() {
    exercise(
        AggSigProfile::JortsPoseidon2,
        HemQuinticProfile::Poseidon2Gl24,
        1,
    );
}

#[test]
fn tooth_corduroy_turbo() {
    exercise(
        AggSigProfile::CorduroyPoseidon2,
        HemQuinticProfile::TurboShake400,
        1,
    );
}

fn check_each_sibling_byte<const N: usize>(hash: impl tree::Hash<N>) {
    use crate::zk_hem::v2::hash::{CanopyTree, verify_canopy};
    let leaves: Vec<_> = (0..16).map(|i| hash.leaf(1, i, &[i as u8])).collect();
    let indices = [1, 7, 8];
    let selected = indices.map(|i| (i, leaves[i]));
    let tree = CanopyTree::build(hash, 1, leaves);
    let mut siblings = tree.open(&indices);
    assert!(verify_canopy(
        hash,
        1,
        4,
        &tree.root(),
        &selected,
        &siblings
    ));
    for i in 0..siblings.len() {
        for j in 0..N {
            siblings[i][j] ^= 1;
            assert!(!verify_canopy(
                hash,
                1,
                4,
                &tree.root(),
                &selected,
                &siblings
            ));
            siblings[i][j] ^= 1;
        }
    }
}

#[test]
fn tooth_each_sibling_byte() {
    check_each_sibling_byte(tree::Turbo);
    check_each_sibling_byte(tree::Gl24);
}

#[test]
fn tooth_invalid_table_below_signer_precheck() {
    let pk = ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[8; 32], 0).pk;
    let bitmap = SignerBitmap::from_active_indices(1, &[0]).unwrap();
    let mut st = statement(
        HemQuinticProfile::TurboShake400,
        &[pk],
        &bitmap,
        &SigningMode::SharedMessage(b"witness"),
    )
    .unwrap();
    let rows = vec![[F::ZERO; NUM_TRACE_COLS]; 1 << st.circuit.log_rows()];
    assert!(rows::prove(&mut st, rows, &mut Vec::new()).is_none());
}

#[test]
fn tooth_transcript_budget_exhaustion() {
    let mut transcript = Transcript::turbo_domain(&FS_DOMAIN, 1, &[MAGIC], 2);
    assert!(!transcript.exhausted());
    transcript.absorb(b"test", b"budget");
    assert!(transcript.exhausted());
    assert_eq!(transcript.squeeze_fp5_nonzero(b"x"), E::ONE);
    assert_eq!(transcript.squeeze_distinct_indices(b"q", 8, 3), [0, 1, 2]);
}

// Three active keys exercise the deterministic fourth padding slot. Pin the entire
// public wire so that the qsag and dregg-sig builds also check each other's format.
#[test]
fn tooth_sparse_committee_wire_vectors() {
    let mut keys: Vec<_> = (0..4)
        .map(|i| {
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[37; 32], i)
        })
        .collect();
    let pks: Vec<_> = keys.iter().map(|key| key.pk).collect();
    let msg = b"public Hem quintic vector v2";
    let mode = SigningMode::SharedMessage(msg);
    let active = [0, 2, 3];
    let sigs: Vec<_> = active
        .iter()
        .map(|&i| keys[i].sign_stateful_for_unit_test(msg, 0).unwrap())
        .collect();
    let bitmap = SignerBitmap::from_active_indices(4, &active).unwrap();
    for (profile, length, expected_hash) in [
        (
            HemQuinticProfile::TurboShake400,
            360391,
            [
                0x4d, 0x2c, 0xde, 0x0e, 0xbe, 0x42, 0xb7, 0x84, 0x03, 0x38, 0xb7, 0x59, 0xa8, 0xb7,
                0x21, 0x85, 0x92, 0x97, 0x36, 0xe1, 0xab, 0x04, 0xd4, 0x0f, 0xac, 0xa9, 0xb1, 0x63,
                0x3a, 0x14, 0x5f, 0x7d,
            ],
        ),
        (
            HemQuinticProfile::Poseidon2Gl24,
            381661,
            [
                0xd3, 0xc3, 0x57, 0x1e, 0x35, 0xef, 0xdc, 0x85, 0x25, 0x87, 0xde, 0x5c, 0x3e, 0xf7,
                0x93, 0x19, 0x42, 0xe5, 0x43, 0x93, 0x6f, 0xda, 0xb2, 0x75, 0xbd, 0x0d, 0x4e, 0x7f,
                0xb9, 0x20, 0xec, 0x71,
            ],
        ),
    ] {
        let proof = prove_hem_quintic_128(profile, &pks, &bitmap, &mode, &sigs).unwrap();
        let bytes = proof.to_bytes();
        assert_eq!(bytes.len(), length);
        assert_eq!(qsag_accel::sha2::sha256(&bytes), expected_hash);
        assert!(verify_hem_quintic_128(profile, &pks, &mode, &proof));
        let mut changed = pks.clone();
        changed[1] = pks[0];
        assert!(!verify_hem_quintic_128(profile, &changed, &mode, &proof));
        assert!(!verify_hem_quintic_128(
            profile,
            &pks,
            &SigningMode::PerSignerMessages(&[msg.as_slice(); 3]),
            &proof
        ));
        let mut substituted = proof;
        substituted.bitmap = SignerBitmap::from_active_indices(4, &[0, 1, 3]).unwrap();
        assert!(!verify_hem_quintic_128(profile, &pks, &mode, &substituted));
    }
}

#[test]
fn tooth_inactive_slot_noncanonical_witness_rejected_by_prover_and_verifier() {
    // `#tooth`: With 3 active signers, the trace pads to 4 signer slots (slot 3 inactive).
    // Previously `gated_op_sels == 0` on slot 3 left `COL_AUX`, `COL_ST_IN` (with matching
    // `record_poseidon2_perm12` S-boxes), and internal `COL_NEXT_STATE[t] == COL_PREV_STATE[t+1]`
    // completely unconstrained, allowing non-canonical witness stuffing inside `QSAGHQM2` proofs.
    use crate::trace::{
        COL_AUX, COL_NEXT_STATE, COL_PREV_STATE, COL_SBOX_OUT, COL_ST_IN, record_poseidon2_perm12,
    };
    use crate::zk_hem::v2::protocol::{eq_table, evals_to_coeffs};

    let mut keys: Vec<_> = (0..3)
        .map(|i| {
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[53; 32], i)
        })
        .collect();
    let pks: Vec<_> = keys.iter().map(|k| k.pk).collect();
    let msg = b"inactive slot canonical zero check";
    let mode = SigningMode::SharedMessage(msg);
    let sigs: Vec<_> = keys
        .iter_mut()
        .map(|k| k.sign_stateful_for_unit_test(msg, 0).unwrap())
        .collect();
    let bitmap = SignerBitmap::from_active_indices(3, &[0, 1, 2]).unwrap();

    let base_st = statement(HemQuinticProfile::TurboShake400, &pks, &bitmap, &mode).unwrap();
    let rps = base_st.circuit.rows_per_signer();
    let total_rows = 1 << base_st.circuit.log_rows();
    assert_eq!(total_rows, 4 * rps);

    let mut honest_rows = vec![[F::ZERO; NUM_TRACE_COLS]; total_rows];
    for (i, slot) in honest_rows.chunks_mut(rps).enumerate() {
        if let Some(s) = base_st.signers.get(i) {
            populate_active_signer_rows(&base_st.circuit.program, &s.pk, s.mu, &sigs[i], slot);
        } else {
            populate_inactive_signer_rows(slot, &[]);
        }
    }
    let honest_payload = whir::prove(
        tree::Turbo,
        base_st,
        honest_rows.clone(),
        #[cfg(feature = "vulkan")]
        None,
    )
    .unwrap();
    let honest_proof = HemQuinticProof {
        profile: HemQuinticProfile::TurboShake400,
        bitmap: bitmap.clone(),
        payload: honest_payload,
    };
    assert!(verify_hem_quintic_128(
        HemQuinticProfile::TurboShake400,
        &pks,
        &mode,
        &honest_proof
    ));

    // Three distinct inactive-slot witness stuffings that previously satisfied all active gates:
    // (0) `COL_AUX` blinding limbs on slot 3,
    // (1) `COL_ST_IN` != 0 paired with valid Poseidon2 S-box trajectory `COL_SBOX_OUT`,
    // (2) Internal `COL_NEXT_STATE[0] == COL_PREV_STATE[1] == 1` carry inside slot 3.
    for case in 0..3 {
        let mut stuffed = honest_rows.clone();
        let slot3 = 3 * rps;
        match case {
            0 => populate_inactive_signer_rows(&mut stuffed[slot3..], &[[F::ONE; 4]]),
            1 => {
                let mut st_in = [F::ZERO; 12];
                st_in[0] = F::from_u64_reduced(99);
                let mut sbox = [F::ZERO; 118];
                let _ = record_poseidon2_perm12(st_in, &mut sbox);
                stuffed[slot3][COL_ST_IN..COL_ST_IN + 12].copy_from_slice(&st_in);
                stuffed[slot3][COL_SBOX_OUT..COL_SBOX_OUT + 118].copy_from_slice(&sbox);
            }
            _ => {
                stuffed[slot3][COL_NEXT_STATE] = F::ONE;
                stuffed[slot3 + 1][COL_PREV_STATE] = F::ONE;
            }
        }
        let st_bad = statement(HemQuinticProfile::TurboShake400, &pks, &bitmap, &mode).unwrap();
        assert_eq!(
            whir::prove(
                tree::Turbo,
                st_bad,
                stuffed.clone(),
                #[cfg(feature = "vulkan")]
                None
            ),
            Err(Error::InconsistentTrace),
            "case {case}: prover sumcheck must reject non-zero inactive-slot trace"
        );

        // Also simulate a malicious prover that bypasses the prover-side `poly[0] + poly[1] == claim`
        // check by forging `poly[0] = claim - poly[1]` in every round while opening the true
        // multilinear column evaluation `cols` of `stuffed` at `rx`: `rows::verify` must reject!
        let mut st_forged =
            statement(HemQuinticProfile::TurboShake400, &pks, &bitmap, &mode).unwrap();
        let mut st_ver = statement(HemQuinticProfile::TurboShake400, &pks, &bitmap, &mode).unwrap();
        let log_rows = st_forged.circuit.log_rows();
        for _ in 0..log_rows {
            let _ = st_forged.transcript.squeeze_fp5(b"TAU");
        }
        let _ = st_forged.transcript.squeeze_fp5(b"GAMMA");

        let mut forged_wire = Vec::new();
        let mut claim = E::ZERO;
        let mut rx = Vec::with_capacity(log_rows);
        for round in 0..log_rows {
            let mut poly = [E::ZERO; 9];
            poly[1] = E::from_u64((round + 3) as u64);
            poly[0] = claim - poly[1];
            write_es(&mut forged_wire, &poly);
            st_forged.transcript.absorb_fp5_slice(b"ROW_VALUES", &poly);
            let r = st_forged.transcript.squeeze_fp5(b"ROW_POINT");
            claim = pcs::eval_poly(&evals_to_coeffs(&poly), [r])[0];
            rx.push(r);
        }
        let eq_rx = eq_table(&rx);
        let mut cols = [E::ZERO; NUM_TRACE_COLS];
        for (row_vals, w) in stuffed.iter().zip(eq_rx) {
            for (c_acc, &v) in cols.iter_mut().zip(row_vals) {
                *c_acc += w.mul_base(v);
            }
        }
        // Sanity check: the non-canonical inactive column survives multilinear folding at `rx`.
        if case == 0 {
            assert_ne!(cols[COL_AUX + 34], E::ZERO);
        }
        write_es(&mut forged_wire, &cols);
        let mut cursor = forged_wire.as_slice();
        assert!(
            rows::verify(&mut st_ver, &mut cursor).is_none(),
            "case {case}: verifier must reject forged sumcheck over non-canonical inactive slot"
        );
    }
}

#[test]
fn tooth_lean_cross_kat_v2_quintic_gl24_turbo400_golden_anchors() {
    // Golden parity anchors generated directly by the Lean `qsag-kat --cross-kat` oracle
    // (`fp5`, `p2gl24`, `turbo400`, and `hqm2fs` families), ensuring standalone workspace
    // exports enforce identical bit-level QuinticFp5, Poseidon2-GL-w24, Canopy-400, and
    // `QSAGHQM2` Fiat-Shamir transcripts.
    use crate::zk_hem::v2::hash::Hasher as V2Hasher;
    use crate::zk_hem::v2::params::Profile as V2Profile;

    let unhex = |s: &str| -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    };

    // 1. `fp5` (`F_p[u]/(u^5 - 3)`): mul, frob, norm, inv
    let x = E::from_limbs([0, 1, 2, 3, 14627333965257922168].map(F::from_u64_reduced));
    let y = E::from_limbs([17, 31, 43, 59, 71].map(F::from_u64_reduced));
    assert_eq!(
        (x * y).to_limbs().map(|l| l.to_canonical_u64()),
        [
            13729741701722107145,
            5358186437984359904,
            6493942132610419500,
            16569130938287256012,
            8857004506995080921,
        ]
    );
    assert_eq!(
        x.frobenius().to_limbs().map(|l| l.to_canonical_u64()),
        [
            0,
            1041288259238279555,
            13194905898746733771,
            634762665416849091,
            284589176297925570,
        ]
    );
    assert_eq!(x.norm().to_canonical_u64(), 5814368380213037458);
    assert_eq!(
        x.inverse().to_limbs().map(|l| l.to_canonical_u64()),
        [
            2626233429256260300,
            12881251338871382336,
            2767005421542732395,
            7208037282534645600,
            8301303084274083852,
        ]
    );

    // 2. `p2gl24`: perm(0..24), jive(0..16), hash56(0, b"")
    let mut s24: [F; 24] = core::array::from_fn(|i| F::from_u64_reduced(i as u64));
    crate::sponge::poseidon2_gl24_perm(&mut s24);
    assert_eq!(s24[0].to_canonical_u64(), 9262813872168818283);
    assert_eq!(s24[23].to_canonical_u64(), 5468252370409873572);
    let jive = crate::sponge::poseidon2_gl24_compress_merkle(
        &core::array::from_fn(|i| F::from_u64_reduced(i as u64)),
        &core::array::from_fn(|i| F::from_u64_reduced((7 + i) as u64)),
        &[F::from_u64_reduced(14), F::from_u64_reduced(15)],
    );
    assert_eq!(
        jive.map(|v| v.to_canonical_u64()),
        [
            12421113816819528209,
            5964777418184518184,
            9509415340955667808,
            15910131723573320644,
            12190451853870384647,
            5350766770573166117,
            7329339403964687157,
        ]
    );
    assert_eq!(
        crate::sponge::poseidon2_gl24_hash56(0, b"").as_slice(),
        unhex(
            "0c61498d6d7527cc27cc876c131b459a0cd093aafc7a0f05181f095151f8623080faecd73fe41181d276a5f0cafd498d59e479a52de827ee"
        )
    );

    // 3. `turbo400`: Canopy-400 (`QSAG.ZKHEM2.TREE/v1` & `QSAG.HEM.QUINTIC.TREE/v2`)
    let h_v2 = V2Hasher::new(V2Profile::TurboShakeJohnson400);
    let seed32: [u8; 32] = core::array::from_fn(|i| i as u8);
    assert_eq!(
        h_v2.salt(&seed32, 7).as_slice(),
        unhex("b73b37439a31798f552c1605e3743641767cb059691e577ebd561327b56e7519")
    );
    let sym40: [u8; 40] = core::array::from_fn(|i| i as u8);
    assert_eq!(
        HemQuinticProfile::turbo_canopy_leaf(0, 9, &sym40).as_slice(),
        unhex(
            "b83f7f4b1cb9f2856b53868f2d239d94a6e92972914f02a3b0e166d6bd5b4d69a6f6da09d76b698f577fc34d8c6707bc1b3a"
        )
    );
    assert_eq!(
        HemQuinticProfile::gl24_canopy_leaf(0, 9, &sym40).as_slice(),
        unhex(
            "f7a6922b01905a47d855e46bfb305fd71fa3ff4df54090c7b4db9dd4a16ce0e3401d61cd38349d5b1da9c742b8c55ea70c242e8d3a18e5f9"
        )
    );

    // 4. `hqm2fs`: `QSAGHQM2` Fiat-Shamir midstate, `squeeze_fp5`, and `squeeze_distinct_indices`
    let mk_pk = |base: u64| ValidatorPublicKey {
        profile: AggSigProfile::JortsPoseidon2,
        pk_seed: core::array::from_fn(|i| F::from_u64_reduced(base + i as u64)),
        pk_root: core::array::from_fn(|i| F::from_u64_reduced(base + 4 + i as u64)),
    };
    let pks = [mk_pk(1), mk_pk(9)];
    let bm1 = SignerBitmap::from_active_indices(2, &[0]).unwrap();
    let mut tr_shared = HemQuinticProfile::TurboShake400
        .open_transcript(&pks, &bm1, &SigningMode::SharedMessage(b"hqm2-shared"))
        .unwrap();
    assert_eq!(
        tr_shared.digest().as_slice(),
        unhex(
            "06dc1633f494c5c182e92aa3d91778cb09cdb78bc7006558243319b50e0e79d4be815def74a484363928b11fa4a2b2cb66c0"
        )
    );
    assert_eq!(
        tr_shared
            .squeeze_fp5(b"OOD")
            .to_limbs()
            .map(|l| l.to_canonical_u64()),
        [
            18387187861061076228,
            17649359886185840600,
            6841352488675881424,
            12027542479934323084,
            8651229268583364616,
        ]
    );
    let bm2 = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
    let msgs: [&[u8]; 2] = [b"sig-a", b"sig-bb"];
    let mut tr_persig = HemQuinticProfile::TurboShake400
        .open_transcript(&pks, &bm2, &SigningMode::PerSignerMessages(&msgs))
        .unwrap();
    assert_eq!(
        tr_persig.digest().as_slice(),
        unhex(
            "ca5774c88fcbb98aeae2469d9aaaefe9d5fdbde00486eedf5c8812fcb85f0d69971d193aec1f85176b281b3dc06808ac82da"
        )
    );
    assert_eq!(
        tr_persig.squeeze_distinct_indices(b"QUERY", 64, 6),
        [2, 26, 31, 47, 50, 56]
    );
}

#[test]
#[cfg(feature = "vulkan")]
#[ignore = "requires an audited Vulkan device"]
fn vulkan_wire_parity_hqm2() {
    let backend = qsag_accel::VulkanSpirvBackend::try_new_audited().unwrap();
    let session = backend.fp5_session().unwrap();
    let msg = b"quintic GPU parity";
    let mode = SigningMode::SharedMessage(msg);
    for n in [1, 8] {
        let mut keys: Vec<_> = (0..n)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[11; 32], i)
            })
            .collect();
        let pks: Vec<_> = keys.iter().map(|k| k.pk).collect();
        let sigs: Vec<_> = keys
            .iter_mut()
            .map(|k| k.sign_stateful_for_unit_test(msg, 0).unwrap())
            .collect();
        let bitmap =
            SignerBitmap::from_active_indices(n, &(0..n as usize).collect::<Vec<_>>()).unwrap();
        for profile in [
            HemQuinticProfile::TurboShake400,
            HemQuinticProfile::Poseidon2Gl24,
        ] {
            let start = std::time::Instant::now();
            let cpu = prove_hem_quintic_128(profile, &pks, &bitmap, &mode, &sigs).unwrap();
            let cpu_time = start.elapsed();
            let before = backend.gpu_submission_count();
            let start = std::time::Instant::now();
            let gpu =
                prove_hem_quintic_128_with_vulkan(&session, profile, &pks, &bitmap, &mode, &sigs)
                    .unwrap();
            let gpu_time = start.elapsed();
            assert!(backend.gpu_submission_count() > before);
            assert!(cpu.to_bytes() == gpu.to_bytes());
            assert!(verify_hem_quintic_128(profile, &pks, &mode, &gpu));
            std::println!(
                "{n} signer(s) {profile:?} {} bytes, CPU {cpu_time:?}, GPU {gpu_time:?}",
                gpu.to_bytes().len()
            );
        }
    }
    assert_eq!(backend.cpu_fallback_count(), 0);
}
