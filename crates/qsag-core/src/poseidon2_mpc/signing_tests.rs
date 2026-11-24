use super::tests::*;
use super::*;
use crate::dkg::{
    QuorumEpochLatchCluster, run_dealerless_dkg_seed32_goldilocks,
    shamir_reconstruct_seed32_goldilocks,
};
use crate::sponge::poseidon2::poseidon2_hash32;
use crate::tsw_baggy::{
    MonotonicEpochLatch, compute_wots_pk, derive_public_key, derive_stateless_r_rand,
    eval_single_sign_stateful, retry_single_sign_stateful,
};

/// Split-view regression for `(t, n) = (2, 3)`.
///
/// `{P0, P1}` signs message A at epoch 0. P2 took no part, so its latch still says 0. A
/// corrupt P1 (its latch rolled back) then asks P2 to sign message B: their two local latches
/// agree on epoch 0, which P0 has already used. Every route to that second signature is
/// refused before a latch moves or a share is touched.
///
/// No preprocessing is provisioned (one signature's worth takes hours to generate), so the
/// first signature is represented by its latch step, the reservation `{P0, P1}` make against
/// the certificate, and any attempt that got past the gate into MPC would exhaust the vaults
/// and poison every share.
#[test]
fn test_stateful_jorts_poseidon2_mpc_split_view_refused_without_committee_latch() {
    let params = PqHashParams {
        w: 4,
        ell1: 128,
        max_sigs_log2: 1,
        num_layers: 1,
        subtree_height: 1,
        fors_trees: 0,
        fors_height: 0,
        stateful: true,
    };
    assert!(params.is_well_formed());
    let (t, n) = (2usize, 3usize);
    let (mut key_shares, mut vaults, mut rngs, ref_sk) = setup_poseidon2_committee(t, n, (0, 0, 0));
    assert!(key_shares.iter().all(|ks| ks.committee_size == n));
    let pk = derive_public_key(Poseidon2Suite, &params, &ref_sk);
    let cache = DkgCachedSubtrees {
        top_layer: 0,
        top_leaves: (0..2u32)
            .map(|kp| compute_wots_pk(Poseidon2Suite, &params, &ref_sk, 0, 0, kp))
            .collect(),
        pk,
    };
    let [k0, k1, k2] = key_shares.as_mut_slice() else {
        panic!("three key shares");
    };
    let [v0, v1, v2] = vaults.as_mut_slice() else {
        panic!("three vaults");
    };

    let msg_a = b"message A";
    let msg_b = b"message B";
    let mu_a = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg_a);
    let mu_b = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, msg_b);
    let bind = |epoch: u64, mu: &[u8; 32]| epoch_latch_binding(&pk.pk_seed, &pk.pk_root, epoch, mu);

    // The latch quorum of a (2, 3) committee with one corruption is all three members.
    let mut cluster = QuorumEpochLatchCluster::new(n, t - 1).unwrap();
    let cluster_auth = cluster.authority();
    assert_eq!(cluster.latch_quorum(), 3);
    for ks in [&mut *k0, &mut *k1, &mut *k2] {
        ks.enroll_key_profile(params, pk).unwrap();
        ks.enroll_latch_authority(cluster_auth.clone()).unwrap();
    }
    let (mut l0, mut l1, mut l2) = (
        MonotonicEpochLatch::new(0),
        MonotonicEpochLatch::new(0),
        MonotonicEpochLatch::new(0),
    );

    // 1. {P0, P1} without a certificate: refused, although both latches agree on epoch 0.
    let uncertified = sign_jorts_poseidon2_mpc_cached(
        [0x70; 32],
        &params,
        &pk,
        Some(&cache),
        t,
        None,
        &mut [&mut l0, &mut l1],
        msg_a,
        100_000,
        &mut [&mut *k0, &mut *k1],
        &mut [&mut *v0, &mut *v1],
        &mut rngs[0..2],
    );
    assert_eq!(
        uncertified,
        Err(Poseidon2MpcError::LatchCertificateRequired {
            signers: 2,
            committee: 3
        })
    );
    assert_eq!(l0, MonotonicEpochLatch::new(0));
    assert_eq!(l1, MonotonicEpochLatch::new(0));
    assert!(!k0.poisoned && !k1.poisoned);

    // 2. Two acknowledgements are not a latch quorum; three are.
    assert!(cluster.certify_epoch(&[0, 1], 0, bind(0, &mu_a)).is_err());
    let cert_a = cluster
        .certify_epoch(&[0, 1, 2], 0, bind(0, &mu_a))
        .unwrap();
    assert_eq!(cert_a.acknowledging_parties(), &[0, 1, 2]);

    // 3. {P0, P1} reserve epoch 0 for A against the certificate, as their signature does.
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            t,
            n,
            Some(&cluster_auth),
            Some(&cert_a),
            &mut [&mut l0, &mut l1],
            &mu_a
        ),
        Ok(0)
    );
    assert_eq!(l0.in_flight(), Some((0, mu_a)));
    assert_eq!(l1.in_flight(), Some((0, mu_a)));
    assert_eq!(l2, MonotonicEpochLatch::new(0));

    // 4. The split view. P1 presents a rolled-back latch; P2's is honestly at 0.
    let mut l1_rolled_back = MonotonicEpochLatch::new(0);

    // The committee will not certify B at epoch 0, whoever asks.
    assert_eq!(
        cluster.certify_epoch(&[0, 1, 2], 0, bind(0, &mu_b)),
        Err(QuorumLatchError::EquivocationRefused { epoch: 0 })
    );
    assert!(cluster.certify_epoch(&[1, 2], 0, bind(0, &mu_b)).is_err());

    // A second cluster stands in for certificates the committee never issued for this key,
    // including an attacker-minted certificate with the EXACT `(n, t, epoch, bind(0, &mu_b))`.
    let mut rogue_same_epoch = QuorumEpochLatchCluster::new(n, t - 1).unwrap();
    let rogue_exact = rogue_same_epoch
        .certify_epoch(&[0, 1, 2], 0, bind(0, &mu_b))
        .unwrap();
    let mut other = QuorumEpochLatchCluster::new(n, t - 1).unwrap();
    let foreign_key = other
        .certify_epoch(
            &[0, 1, 2],
            0,
            epoch_latch_binding(&[0x5a; 32], &pk.pk_root, 0, &mu_b),
        )
        .unwrap();
    let other_epoch = other.certify_epoch(&[0, 1, 2], 1, bind(1, &mu_b)).unwrap();
    // Bound to epoch 0 but reserved at epoch 2: the signer recomputes the binding per epoch.
    let rebound_epoch = other.certify_epoch(&[0, 1, 2], 2, bind(0, &mu_b)).unwrap();
    let mut two_member = QuorumEpochLatchCluster::new(2, t - 1).unwrap();
    let other_committee = two_member
        .certify_epoch(&[0, 1], 0, bind(0, &mu_b))
        .unwrap();

    let attempts: [(Option<&EpochLatchCertificate>, Poseidon2MpcError); 5] = [
        (
            None,
            Poseidon2MpcError::LatchCertificateRequired {
                signers: 2,
                committee: 3,
            },
        ),
        // Exact `(n=3, t=2, epoch=0, bind(0, &mu_b))` from an attacker-controlled cluster
        // MUST be rejected because its custodian MAC keys do not match `cluster_auth`!
        (
            Some(&rogue_exact),
            Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch,
            ),
        ),
        // The certificate issued for message A does not authorise message B.
        (
            Some(&cert_a),
            Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateBindingMismatch { epoch: 0 },
            ),
        ),
        (
            Some(&foreign_key),
            Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateBindingMismatch { epoch: 0 },
            ),
        ),
        (
            Some(&other_committee),
            Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch,
            ),
        ),
    ];
    for (latch_cert, expected) in attempts {
        let second = sign_jorts_poseidon2_mpc_cached(
            [0x72; 32],
            &params,
            &pk,
            Some(&cache),
            t,
            latch_cert,
            &mut [&mut l1_rolled_back, &mut l2],
            msg_b,
            100_000,
            &mut [&mut *k1, &mut *k2],
            &mut [&mut *v1, &mut *v2],
            &mut rngs[1..3],
        );
        assert_eq!(second, Err(expected.clone()));
        // The same holds for the retry entry point, which reserves nothing itself.
        let retry = retry_jorts_poseidon2_mpc_cached(
            [0x73; 32],
            &params,
            &pk,
            Some(&cache),
            t,
            latch_cert,
            &mut [&mut l1_rolled_back, &mut l2],
            0,
            msg_b,
            100_000,
            &mut [&mut *k1, &mut *k2],
            &mut [&mut *v1, &mut *v2],
            &mut rngs[1..3],
        );
        assert_eq!(retry, Err(expected));
    }
    let rebound = sign_jorts_poseidon2_mpc_cached(
        [0x74; 32],
        &params,
        &pk,
        Some(&cache),
        t,
        Some(&rebound_epoch),
        &mut [&mut l1_rolled_back, &mut l2],
        msg_b,
        100_000,
        &mut [&mut *k1, &mut *k2],
        &mut [&mut *v1, &mut *v2],
        &mut rngs[1..3],
    );
    assert_eq!(
        rebound,
        Err(Poseidon2MpcError::LatchCertificateRejected(
            QuorumLatchError::CertificateBindingMismatch { epoch: 2 }
        ))
    );
    // A certificate for epoch 1 does not cover a retry of epoch 0.
    let wrong_epoch_retry = retry_jorts_poseidon2_mpc_cached(
        [0x75; 32],
        &params,
        &pk,
        Some(&cache),
        t,
        Some(&other_epoch),
        &mut [&mut l1_rolled_back, &mut l2],
        0,
        msg_b,
        100_000,
        &mut [&mut *k1, &mut *k2],
        &mut [&mut *v1, &mut *v2],
        &mut rngs[1..3],
    );
    assert_eq!(
        wrong_epoch_retry,
        Err(Poseidon2MpcError::LatchCertificateRejected(
            QuorumLatchError::CertificateEpochMismatch {
                certified_epoch: 1,
                requested_epoch: 0
            }
        ))
    );

    // No refused attempt reserved an epoch or reached MPC.
    assert_eq!(l1_rolled_back, MonotonicEpochLatch::new(0));
    assert_eq!(l2, MonotonicEpochLatch::new(0));
    assert!(!k0.poisoned && !k1.poisoned && !k2.poisoned);
    assert!(!v0.is_poisoned() && !v1.is_poisoned() && !v2.is_poisoned());
}

/// The stateless signers' `R` is a function of the key and the message only. Two sessions
/// with different session ids and different party randomness open the same `R`, equal to the
/// single-holder reference. The public entry points take no randomiser argument (see the
/// calls in `test_poseidon2_mpc_cached_top_subtree_rejects_mismatched_cache`).
#[test]
fn test_stateless_poseidon2_mpc_randomiser_is_deterministic_per_key_and_message() {
    let t = 2usize;
    let (mut key_shares, mut vaults, mut rngs, ref_sk) =
        setup_poseidon2_committee_material(2, 2, (2 * 5 * POSEIDON2_SBOXES_PER_PERM, 0, 0), true);
    let pts: Vec<Goldilocks> = key_shares.iter().map(|ks| ks.eval_point).collect();
    let [k0, k1] = key_shares.as_mut_slice() else {
        panic!("two key shares");
    };
    let [v0, v1] = vaults.as_mut_slice() else {
        panic!("two vaults");
    };
    let pk = PqPublicKey {
        pk_seed: ref_sk.pk_seed,
        pk_root: [0x3c; 32],
    };
    let mu = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, b"same message");
    let mu_other = th_pre_hash(Poseidon2Suite, &pk.pk_seed, &pk.pk_root, b"other message");

    let r_first = eval_stateless_r_rand_mpc(
        &[0x81; 32],
        t,
        &pts,
        &pk,
        &mu,
        &mut [&mut *k0, &mut *k1],
        &mut [&mut *v0, &mut *v1],
        &mut rngs,
    )
    .unwrap();
    // A second session: new session id, and party randomness unrelated to the first run's.
    let mut other_rngs = make_rngs(2, 0x90);
    let r_second = eval_stateless_r_rand_mpc(
        &[0x82; 32],
        t,
        &pts,
        &pk,
        &mu,
        &mut [&mut *k0, &mut *k1],
        &mut [&mut *v0, &mut *v1],
        &mut other_rngs,
    )
    .unwrap();
    assert_eq!(r_first, r_second);
    assert_eq!(
        r_first,
        derive_stateless_r_rand(Poseidon2Suite, &ref_sk.sk_prf, &pk.pk_seed, &mu)
    );

    assert_ne!(
        r_first,
        derive_stateless_r_rand(Poseidon2Suite, &ref_sk.sk_prf, &pk.pk_seed, &mu_other)
    );
    assert!(!k0.poisoned && !k1.poisoned);
}

#[test]
fn test_stateful_jorts_poseidon2_mpc_exact_parity_latch_and_dishonest_majority_abort() {
    let _memory = crate::test_budget::reserve_mb(1900);
    // Compact stateful `JortsPoseidon2` parameter set (`w = 4, ell1 = 128, target_sum = 192, h = 2, d = 2`)
    let params = PqHashParams {
        w: 4,
        ell1: 128,
        max_sigs_log2: 2,
        num_layers: 2,
        subtree_height: 1,
        fors_trees: 0,
        fors_height: 0,
        stateful: true,
    };
    assert!(params.is_well_formed());
    let t = 2usize;

    let (kg_pow7, kg_beaver, kg_a2b) = required_poseidon2_keygen_preprocessing_budget(&params);
    let (sg_pow7, sg_beaver, sg_a2b) = required_poseidon2_sign_preprocessing_budget(&params);

    // 1. Run real dealerless Goldilocks DKG for `SK.seed` and `SK.prf`
    let (mut key_shares, mut vaults, mut rngs, ref_sk) = setup_poseidon2_committee_material(
        2,
        2,
        (
            kg_pow7 + 2 * sg_pow7,
            kg_beaver + 2 * sg_beaver,
            kg_a2b + 2 * sg_a2b,
        ),
        true,
    );
    let ref_pk = derive_public_key(Poseidon2Suite, &params, &ref_sk);

    // 2. Build distributed public key in MPC and assert bit-for-bit equality with `derive_public_key`
    let (ks0, ks1) = key_shares.split_at_mut(1);
    let (v0, v1) = vaults.split_at_mut(1);
    let mut ks_refs = [&mut ks0[0], &mut ks1[0]];
    let mut v_refs = [&mut v0[0], &mut v1[0]];

    let mpc_pk = build_distributed_poseidon2_key(
        [0x64; 32],
        &params,
        t,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap();
    assert_eq!(mpc_pk, ref_pk);

    // 3. Sign message at epoch 0 via SPDZ MPC and assert bit-for-bit parity with `eval_single_sign_stateful`!
    let msg = b"JortsPoseidon2 threshold signature parity vector";
    let mut l0 = MonotonicEpochLatch::new(0);
    let mut l1 = MonotonicEpochLatch::new(0);
    let mut latch_refs = [&mut l0, &mut l1];

    let (ep, mpc_sig) = sign_jorts_poseidon2_mpc(
        [0x65; 32],
        &params,
        &mpc_pk,
        t,
        None,
        &mut latch_refs,
        msg,
        100_000,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap();
    assert_eq!(ep, 0);

    let mut ref_latch = MonotonicEpochLatch::new(0);
    let ref_sig = eval_single_sign_stateful(
        Poseidon2Suite,
        &params,
        &ref_sk,
        &ref_pk,
        &mut ref_latch,
        msg,
        100_000,
    )
    .unwrap();
    assert_eq!(mpc_sig, ref_sig);
    assert!(verify_pq_hash_sig(
        Poseidon2Suite,
        &params,
        &mpc_pk,
        msg,
        &mpc_sig
    ));

    // 4. Crash-retry on `(epoch = 0, same msg)` succeeds with bit-identical signature, while
    //    equivocating `(epoch = 0, different msg)` is strictly refused BEFORE any MPC wire opens!
    let mut latch_refs = [&mut l0, &mut l1];
    let eq_err = retry_jorts_poseidon2_mpc(
        [0x66; 32],
        &params,
        &mpc_pk,
        t,
        None,
        &mut latch_refs,
        0,
        b"equivocated second message at epoch 0",
        100_000,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap_err();
    assert_eq!(
        eq_err,
        Poseidon2MpcError::EpochLatch(EpochLatchError::EquivocationRefused)
    );

    let retry_sig = retry_jorts_poseidon2_mpc(
        [0x67; 32],
        &params,
        &mpc_pk,
        t,
        None,
        &mut latch_refs,
        0,
        msg,
        100_000,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap();
    let ref_retry = retry_single_sign_stateful(
        Poseidon2Suite,
        &params,
        &ref_sk,
        &ref_pk,
        &mut ref_latch,
        0,
        msg,
        100_000,
    )
    .unwrap();
    assert_eq!(retry_sig, mpc_sig);
    assert_eq!(retry_sig, ref_retry);

    // 5. Active dishonest-majority Byzantine fault: corrupt party `1`'s `sk_prf_bytes[0]` share;
    //    pre-cut SPDZ `MacCheck` MUST abort AND permanently poison both `key_shares` and `vaults`!
    ks_refs[1].sk_prf_bytes[0] += Goldilocks::ONE;
    let abort_err = sign_jorts_poseidon2_mpc(
        [0x68; 32],
        &params,
        &mpc_pk,
        t,
        None,
        &mut latch_refs,
        b"epoch 1 message under active fault",
        100_000,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap_err();
    assert!(matches!(
        abort_err,
        Poseidon2MpcError::Preprocess(PreprocessError::MacCheckFailed { .. })
    ));
    assert!(ks_refs[0].poisoned && ks_refs[1].poisoned);
    assert!(v_refs[0].is_poisoned() && v_refs[1].is_poisoned());

    let _ = poseidon2_hash32(b"keep import exercised");
}

#[test]
fn multilayer_corduroy_poseidon2_mpc_end_to_end() {
    let _memory = crate::test_budget::reserve_mb(1200);
    let params = PqHashParams {
        w: 4,
        ell1: 128,
        max_sigs_log2: 2,
        num_layers: 2,
        subtree_height: 1,
        fors_trees: 1,
        fors_height: 1,
        stateful: false,
    };
    assert!(params.is_well_formed());
    let kg = required_poseidon2_keygen_preprocessing_budget(&params);
    let sg = required_poseidon2_sign_preprocessing_budget(&params);
    // Real DKG, authentication, and online MPC; offline correlations are a test fixture.
    let (mut keys, mut vaults, mut rngs, sk) =
        setup_poseidon2_committee_material(2, 2, (kg.0 + sg.0, kg.1 + sg.1, kg.2 + sg.2), true);
    let (ka, kb) = keys.split_at_mut(1);
    let (va, vb) = vaults.split_at_mut(1);
    let mut keys = [&mut ka[0], &mut kb[0]];
    let mut vaults = [&mut va[0], &mut vb[0]];
    let pk =
        build_distributed_poseidon2_key([0xa1; 32], &params, 2, &mut keys, &mut vaults, &mut rngs)
            .unwrap();
    assert_eq!(pk, derive_public_key(Poseidon2Suite, &params, &sk));
    let message = b"Corduroy two-layer online MPC";
    let sig = sign_stateless_tsw_poseidon2_mpc(
        [0xa2; 32],
        &params,
        &pk,
        2,
        message,
        100_000,
        &mut keys,
        &mut vaults,
        &mut rngs,
    )
    .unwrap();
    assert!(verify_pq_hash_sig(
        Poseidon2Suite,
        &params,
        &pk,
        message,
        &sig
    ));
    assert!(!verify_pq_hash_sig(
        Poseidon2Suite,
        &params,
        &pk,
        b"different",
        &sig
    ));
}

/// Slippage U5: sign -> policy circuit -> verify for a multi-layer `Corduroy` key.
///
/// The policy barrier of `qsag-policy` releases an [`AuthorizedSignReleaseToken`] for one
/// canonical intent envelope; the threshold signer signs exactly those bytes and the stock
/// verifier accepts exactly those bytes. A refused intent yields no token, and a token does
/// not cover any other payload, key, context or quorum.
#[test]
fn multilayer_corduroy_policy_gated_sign_and_verify_end_to_end() {
    let _memory = crate::test_budget::reserve_mb(1200);
    use crate::corduroy::Corduroy;
    use crate::sponge::keccak::cshake256_32;
    use qsag_accel::CpuReferenceBackend;
    use qsag_addr::{KeyIdentityKind, QsagAddress, WitnessSuiteTag};
    use qsag_policy::{
        AuthorizedSignReleaseToken, PolicyViolation, QuorumTierRule, SigningPayloadBinding,
        TransactionIntent, TransactionPolicy, evaluate_policy_committed_barrier_authenticated,
        trusted_dealer_setup_for_testing,
    };

    // Two-layer stateless hypertree, 2-of-2 signing committee (guard ids 1 and 2).
    // Message-substitution assertions need a nontrivial FORS selector space: the old
    // one-bit FORS plus two-bit leaf geometry had only eight selectors and could
    // accept a distinct message by an ordinary selector collision. Keep the small
    // trees, but bind 128 FORS bits instead of changing either rejection assertion.
    let params = PqHashParams {
        w: 4,
        ell1: 128,
        max_sigs_log2: 2,
        num_layers: 2,
        subtree_height: 1,
        fors_trees: 128,
        fors_height: 1,
        stateful: false,
    };
    assert!(params.is_well_formed() && params.num_layers > 1);
    assert!(params.fors_trees * params.fors_height >= 128);
    let kg = required_poseidon2_keygen_preprocessing_budget(&params);
    let sg = required_poseidon2_sign_preprocessing_budget(&params);
    let (mut keys, mut vaults, mut rngs, sk) =
        setup_poseidon2_committee_material(2, 2, (kg.0 + sg.0, kg.1 + sg.1, kg.2 + sg.2), true);
    let (ka, kb) = keys.split_at_mut(1);
    let (va, vb) = vaults.split_at_mut(1);
    let mut keys = [&mut ka[0], &mut kb[0]];
    let mut vaults = [&mut va[0], &mut vb[0]];
    let pk =
        build_distributed_poseidon2_key([0xb1; 32], &params, 2, &mut keys, &mut vaults, &mut rngs)
            .unwrap();
    assert_eq!(pk, derive_public_key(Poseidon2Suite, &params, &sk));
