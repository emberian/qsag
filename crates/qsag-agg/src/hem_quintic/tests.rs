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
    assert!(verify_hem_quintic_128(&pks, &mode, &proof));
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
    assert!(!verify_hem_quintic_128(&different_keys, &mode, &proof));
    let mut different_messages = refs.clone();
    different_messages[0] = &[0, 16];
    assert!(!verify_hem_quintic_128(
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
            !verify_hem_quintic_128(&pks, &mode, &bad),
            "mutation at {offset}"
        );
    }
    let mut bad = proof.clone();
    bad.payload[digest..digest + 8].copy_from_slice(&GOLDILOCKS_PRIME.to_le_bytes());
    assert!(!verify_hem_quintic_128(&pks, &mode, &bad));
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
            362391,
            [
                0xfd, 0x02, 0xae, 0xc7, 0x1f, 0x4b, 0xf6, 0xad, 0xc3, 0xfa, 0x47, 0x65, 0x29, 0x57,
                0xe5, 0x69, 0x83, 0xc1, 0x20, 0xef, 0x78, 0x21, 0x33, 0x92, 0xe3, 0x92, 0xe5, 0x7f,
                0xdd, 0xfe, 0x93, 0xe1,
            ],
        ),
        (
            HemQuinticProfile::Poseidon2Gl24,
            381045,
            [
                0x7c, 0x3c, 0x30, 0xe9, 0x6d, 0x8f, 0x2a, 0x78, 0x1d, 0xe8, 0x4f, 0x63, 0x35, 0x32,
                0x64, 0x02, 0x54, 0x68, 0x82, 0xb7, 0xe6, 0x9e, 0x26, 0x27, 0x75, 0xe1, 0x82, 0xf9,
                0x2e, 0xab, 0xa0, 0xe3,
            ],
        ),
    ] {
        let proof = prove_hem_quintic_128(profile, &pks, &bitmap, &mode, &sigs).unwrap();
        let bytes = proof.to_bytes();
        assert_eq!(bytes.len(), length);
        assert_eq!(qsag_accel::sha2::sha256(&bytes), expected_hash);
        assert!(verify_hem_quintic_128(&pks, &mode, &proof));
        let mut changed = pks.clone();
        changed[1] = pks[0];
        assert!(!verify_hem_quintic_128(&changed, &mode, &proof));
        assert!(!verify_hem_quintic_128(
            &pks,
            &SigningMode::PerSignerMessages(&[msg.as_slice(); 3]),
            &proof
        ));
        let mut substituted = proof;
        substituted.bitmap = SignerBitmap::from_active_indices(4, &[0, 1, 3]).unwrap();
        assert!(!verify_hem_quintic_128(&pks, &mode, &substituted));
    }
}
