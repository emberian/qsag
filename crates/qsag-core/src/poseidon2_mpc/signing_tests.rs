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
    let key_id = cshake256_32(
        b"QSAG.TEST.CORDUROY.KEY_ID",
        &[pk.pk_seed, pk.pk_root].concat(),
    );

    // Policy: one allowlisted recipient, a single-transaction cap, two approvers including
    // the hardware guardian (guard 2, whose presence in every quorum carries the velocity
    // window), and an initiator (guard 3) who may not approve their own request.
    let accel = CpuReferenceBackend::new();
    let recipient = QsagAddress::from_pubkey_cshake256(
        "qsp",
        WitnessSuiteTag::SlhDsa128f,
        KeyIdentityKind::SingleOrThreshold,
        b"corduroy-cold-vault",
    )
    .unwrap();
    let policy = TransactionPolicy {
        chain_id: 7,
        pinned_suite: WitnessSuiteTag::SlhDsa128f,
        recipient_allowlist: vec![recipient.commitment_256],
        max_single_tx_amount: 1_000,
        velocity_window_cap: 5_000,
        valid_not_before_secs: 100,
        valid_not_after_secs: 10_000,
        forbid_initiator_self_approval: true,
        hardware_guardian_party: Some(2),
        quorum_tiers: vec![QuorumTierRule {
            max_amount_units: 1_000,
            min_approvers: 2,
            require_hardware_guardian: true,
        }],
    };
    let policy_digest = policy.canonical_digest();
    let authority_pk = [0x5a; 32];
    let quorum = [1u16, 2];
    let ctx = b"corduroy:treasury:v1";
    let mut guards: Vec<_> = trusted_dealer_setup_for_testing([0x91; 32], &[1, 2, 3])
        .into_iter()
        .map(|g| g.with_window_authority([0x42; 32], [0x43; 32]).unwrap())
        .collect();
    let initiator = guards.pop().unwrap();

    let request = |amount: u128,
                   session: u8|
     -> Result<(TransactionIntent, Vec<u8>), PolicyViolation> {
        let (mut intent, _) =
            TransactionIntent::builder(7, WitnessSuiteTag::SlhDsa128f, recipient.clone(), amount)
                .timestamp_secs(500)
                .initiator_and_approvers(3, &quorum)
                .bind_signing_payload(
                    &SigningPayloadBinding {
                        key_id,
                        payload: b"transfer to cold vault",
                        ctx,
                        session_id: [session; 32],
                        policy_revision: 1,
                        quorum: &quorum,
                        authority_pk,
                    },
                    &policy,
                )?;
        let bytes = initiator.authenticate_initiated_intent(&policy, &mut intent)?;
        Ok((intent, bytes))
    };
    let covers = |token: &AuthorizedSignReleaseToken,
                  key: &[u8; 32],
                  msg: &[u8],
                  ctx: &[u8],
                  quorum: &[u16]| {
        token.matches_signing_for_policy(key, msg, ctx, quorum, &policy_digest, &authority_pk)
    };

    // A request over the cap is refused before any guard is asked: nothing to sign.
    assert!(request(1_001, 0xc0).is_err());

    // The approved request: both guards run the committed barrier and release a token.
    let (intent, approved) = request(250, 0xc1).unwrap();
    let token = evaluate_policy_committed_barrier_authenticated(
        &policy,
        &intent,
        intent.session_id,
        intent.timestamp_secs,
        &mut guards,
        &accel,
    )
    .unwrap();
    assert!(covers(&token, &key_id, &approved, ctx, &quorum));

    // The token covers neither a different amount, key, context nor quorum.
    let mut inflated = intent.clone();
    inflated.amount_units = 251;
    let inflated_bytes = inflated.to_canonical_signing_bytes(&policy_digest);
    assert!(!covers(&token, &key_id, &inflated_bytes, ctx, &quorum));
    assert!(!covers(&token, &[0; 32], &approved, ctx, &quorum));
    assert!(!covers(&token, &key_id, &approved, b"other", &quorum));
    assert!(!covers(&token, &key_id, &approved, ctx, &[1, 3]));

    // An intent edited after the initiator authenticated it gets no token, and the same
    // approved intent cannot be replayed through the barrier for a second token.
    assert!(
        evaluate_policy_committed_barrier_authenticated(
            &policy,
            &inflated,
            inflated.session_id,
            inflated.timestamp_secs,
            &mut guards,
            &accel,
        )
        .is_err()
    );
    assert!(
        evaluate_policy_committed_barrier_authenticated(
            &policy,
            &intent,
            intent.session_id,
            intent.timestamp_secs,
            &mut guards,
            &accel,
        )
        .is_err()
    );

    // Sign exactly the released bytes under MPC; the stock verifier accepts only them.
    assert!(covers(&token, &key_id, &approved, ctx, &quorum));
    let sig = sign_stateless_tsw_poseidon2_mpc(
        *token.session_id(),
        &params,
        &pk,
        2,
        &approved,
        100_000,
        &mut keys,
        &mut vaults,
        &mut rngs,
    )
    .unwrap();
    assert!(Corduroy::verify(&params, &pk, &approved, &sig));
    assert!(!Corduroy::verify(&params, &pk, &inflated_bytes, &sig));
    assert!(!Corduroy::verify(
        &params,
        &pk,
        b"transfer to cold vault",
        &sig
    ));
}

#[test]
fn test_uncached_signing_and_keygen_reject_unenrolled_or_forged_pk_and_params() {
    let _memory = crate::test_budget::reserve_mb(450);
    let stateful_params = PqHashParams {
        w: 4,
        ell1: 128,
        max_sigs_log2: 1,
        num_layers: 1,
        subtree_height: 1,
        fors_trees: 0,
        fors_height: 0,
        stateful: true,
    };
    let alt_stateful_params = PqHashParams {
        max_sigs_log2: 2,
        num_layers: 2,
        ..stateful_params
    };
    let stateless_params = PqHashParams {
        w: 4,
        ell1: 128,
        max_sigs_log2: 1,
        num_layers: 1,
        subtree_height: 1,
        fors_trees: 1,
        fors_height: 1,
        stateful: false,
    };
    assert!(
        stateful_params.is_well_formed()
            && alt_stateful_params.is_well_formed()
            && stateless_params.is_well_formed()
    );

    let kg = required_poseidon2_keygen_preprocessing_budget(&stateful_params);
    let (mut key_shares, mut vaults, mut rngs, ref_sk) =
        setup_poseidon2_committee_material(2, 2, kg, true);
    let ref_pk = derive_public_key(Poseidon2Suite, &stateful_params, &ref_sk);
    let (ks0, ks1) = key_shares.split_at_mut(1);
    let (v0, v1) = vaults.split_at_mut(1);
    let mut ks_refs = [&mut ks0[0], &mut ks1[0]];
    let mut v_refs = [&mut v0[0], &mut v1[0]];

    // 1. Unenrolled shares must refuse all uncached signing entry points before latching or spending.
    let mut l0 = MonotonicEpochLatch::new(0);
    let mut l1 = MonotonicEpochLatch::new(0);
    let before = remaining_budget(v_refs[0]);
    assert_eq!(
        sign_jorts_poseidon2_mpc(
            [0xb0; 32],
            &stateful_params,
            &ref_pk,
            2,
            None,
            &mut [&mut l0, &mut l1],
            b"unenrolled",
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        ),
        Err(Poseidon2MpcError::KeyNotEnrolled)
    );
    assert_eq!(
        retry_jorts_poseidon2_mpc(
            [0xb1; 32],
            &stateful_params,
            &ref_pk,
            2,
            None,
            &mut [&mut l0, &mut l1],
            0,
            b"unenrolled",
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        ),
        Err(Poseidon2MpcError::KeyNotEnrolled)
    );
    assert_eq!(
        sign_stateless_tsw_poseidon2_mpc(
            [0xb2; 32],
            &stateless_params,
            &ref_pk,
            2,
            b"unenrolled",
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        ),
        Err(Poseidon2MpcError::KeyNotEnrolled)
    );
    assert_eq!(remaining_budget(v_refs[0]), before);
    assert_eq!((l0.next_epoch(), l1.next_epoch()), (0, 0));

    // 2. Enroll via `build_distributed_poseidon2_key` (`stateful_params`, `mpc_pk`).
    let mpc_pk = build_distributed_poseidon2_key(
        [0xb3; 32],
        &stateful_params,
        2,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap();
    assert_eq!(mpc_pk, ref_pk);
    assert_eq!(remaining_budget(v_refs[0]), (0, 0, 0));

    // 3. Re-running keygen under a different parameter profile is rejected before touching vaults.
    assert_eq!(
        build_distributed_poseidon2_key(
            [0xb4; 32],
            &alt_stateful_params,
            2,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        ),
        Err(Poseidon2MpcError::KeyProfileMismatch)
    );

    // 4. Uncached signing (`cache = None`) with forged `pk_root`, forged `pk_seed`, or mismatched
    //    `params` is rejected strictly before latch reservation or MPC execution (`0` tuples left,
    //    so reaching MPC would fail with `VaultExhausted` and poison the shares!).
    let mut forged_root_pk = mpc_pk;
    forged_root_pk.pk_root[0] ^= 0x80;
    let mut forged_seed_pk = mpc_pk;
    forged_seed_pk.pk_seed[0] ^= 0x01;

    for (bad_params, bad_pk, exp_err) in [
        (
            &stateful_params,
            &forged_root_pk,
            Poseidon2MpcError::KeyProfileMismatch,
        ),
        (
            &stateful_params,
            &forged_seed_pk,
            Poseidon2MpcError::PublicSeedMismatch,
        ),
        (
            &alt_stateful_params,
            &mpc_pk,
            Poseidon2MpcError::KeyProfileMismatch,
        ),
    ] {
        assert_eq!(
            sign_jorts_poseidon2_mpc(
                [0xb5; 32],
                bad_params,
                bad_pk,
                2,
                None,
                &mut [&mut l0, &mut l1],
                b"forged profile",
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            ),
            Err(exp_err.clone())
        );
        assert_eq!(
            retry_jorts_poseidon2_mpc(
                [0xb6; 32],
                bad_params,
                bad_pk,
                2,
                None,
                &mut [&mut l0, &mut l1],
                0,
                b"forged profile",
                100_000,
                &mut ks_refs,
                &mut v_refs,
                &mut rngs,
            ),
            Err(exp_err)
        );
    }
    assert_eq!(
        sign_stateless_tsw_poseidon2_mpc(
            [0xb7; 32],
            &stateless_params,
            &mpc_pk,
            2,
            b"wrong mode",
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        ),
        Err(Poseidon2MpcError::KeyProfileMismatch)
    );
    assert_eq!((l0.next_epoch(), l1.next_epoch()), (0, 0));
    assert!(!ks_refs[0].poisoned && !ks_refs[1].poisoned);
    assert!(!v_refs[0].is_poisoned() && !v_refs[1].is_poisoned());
}

#[test]
fn test_hem_jorts_native_spdz_sign_and_reshare_zero_a2b() {
    use crate::dkg::run_dealerless_reshare_seed32_goldilocks;

    let t = 2usize;
    let n = 2usize;
    let active_leaves = 1usize;
    let keygen_budget = required_hem_jorts_keygen_preprocessing_budget(active_leaves).unwrap();
    let sign_budget = required_hem_jorts_sign_preprocessing_budget_cached();
    let verify_budget = required_hem_jorts_reshare_verify_preprocessing_budget();
    assert_eq!(keygen_budget.1, 0);
    assert_eq!(keygen_budget.2, 0);
    assert_eq!(sign_budget, (38_232, 0, 0));
    assert_eq!(verify_budget, (826, 0, 0));

    let pts: Vec<Goldilocks> = (1..=n as u64).map(Goldilocks::from_u64_reduced).collect();
    let mut rngs = make_rngs(n, 0x91);
    let mut mesh = OtMesh::establish_ideal_for_test([0x92; 32], &mut rngs);

    let dkg_seed =
        run_dealerless_dkg_seed32_goldilocks([0x93; 32], t, &pts, &mut mesh, &mut rngs).unwrap();
    let dkg_prf =
        run_dealerless_dkg_seed32_goldilocks([0x94; 32], t, &pts, &mut mesh, &mut rngs).unwrap();
    let pk_seed = dkg_seed.1;

    let (mut key_shares, mut vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
        [0x95; 32],
        t,
        &pts,
        pk_seed,
        &dkg_seed.0,
        &dkg_prf.0,
        0,
        0,
        0,
        &mut mesh,
        &mut rngs,
    )
    .unwrap();
    let total_budget = (keygen_budget.0 + 2 * sign_budget.0, 0, 0);
    PreprocessedPoseidonPartyVault::fill_two_party_online_fixture(
        &mut vaults,
        total_budget,
        &mut rngs[0],
    );

    let ref_seed =
        shamir_reconstruct_seed32_goldilocks(&dkg_seed.0[..t].iter().collect::<Vec<_>>()).unwrap();
    let ref_prf =
        shamir_reconstruct_seed32_goldilocks(&dkg_prf.0[..t].iter().collect::<Vec<_>>()).unwrap();
    let clear_cache =
        derive_hem_jorts_cached_tree_clear(pk_seed, &ref_seed, &ref_prf, active_leaves).unwrap();

    let cache = {
        let (ks0, ks1) = key_shares.split_at_mut(1);
        let (v0, v1) = vaults.split_at_mut(1);
        build_distributed_hem_jorts_key_mpc_with_active_leaves(
            [0x96; 32],
            active_leaves,
            t,
            &mut [&mut ks0[0], &mut ks1[0]],
            &mut [&mut v0[0], &mut v1[0]],
            &mut rngs[..t],
        )
        .unwrap()
    };
    assert_eq!(cache, clear_cache);
    assert!(cache.verify_consistency());

    let mut cluster = QuorumEpochLatchCluster::new(n, t - 1).unwrap();
    for ks in &mut key_shares {
        ks.enroll_latch_authority(cluster.authority()).unwrap();
    }
    let latch_pk = cache.pk.latch_pq_public_key(cache.dkg_pk_seed);
    let msg0 = b"hem native poseidon2 epoch 0";
    let (mu0_bytes, _) = hem_compute_message_mu(&cache.pk, msg0);
    let bind0 = epoch_latch_binding(&latch_pk.pk_seed, &latch_pk.pk_root, 0, &mu0_bytes);
    let cert0 = cluster.certify_epoch(&[0, 1], 0, bind0).unwrap();

    let (ep0, sig0) = {
        let (ks0, ks1) = key_shares.split_at_mut(1);
        let (v0, v1) = vaults.split_at_mut(1);
        let before = remaining_budget(v0.first().unwrap());
        let mut l0 = MonotonicEpochLatch::new(0);
        let mut l1 = MonotonicEpochLatch::new(0);
        let out = sign_hem_jorts_poseidon2_mpc_cached(
            [0x97; 32],
            &cache,
            t,
            Some(&cert0),
            &mut [&mut l0, &mut l1],
            msg0,
            100_000,
            &mut [&mut ks0[0], &mut ks1[0]],
            &mut [&mut v0[0], &mut v1[0]],
            &mut rngs[..t],
        )
        .unwrap();
        let after = remaining_budget(v0.first().unwrap());
        assert_eq!(spent(before, after), sign_budget);

        let retry_sig = retry_hem_jorts_poseidon2_mpc_cached(
            [0x98; 32],
            &cache,
            t,
            Some(&cert0),
            &mut [&mut l0, &mut l1],
            out.0,
            msg0,
            100_000,
            &mut [&mut ks0[0], &mut ks1[0]],
            &mut [&mut v0[0], &mut v1[0]],
            &mut rngs[..t],
        )
        .unwrap();
        assert_eq!(retry_sig, out.1);
        out
    };
    assert_eq!(ep0, 0);
    assert_eq!(sig0.to_bytes().len(), HEM_JORTS_SIG_BYTES);
    assert!(verify_hem_jorts_signature(&cache.pk, msg0, &sig0));
    assert_eq!(
        HemJortsSignature::from_bytes_canonical(&sig0.to_bytes()).as_ref(),
        Some(&sig0)
    );
    drop(vaults);
    drop(key_shares);

    // Reshare (2, 2) -> (3, 4) and verify reshared shares in 100% live Gilboa OLE SPDZ MPC
    // (`798` pow7 tuples, `0` Beaver triples, `0` A2B masks) without reconstructing secrets!
    let new_t = 3usize;
    let new_n = 4usize;
    let new_pts: Vec<Goldilocks> = (1..=new_n as u64)
        .map(Goldilocks::from_u64_reduced)
        .collect();
    let mut old_seed = dkg_seed.0;
    let mut old_prf = dkg_prf.0;
    let mut old_rngs = make_rngs(t, 0xA1);
    let mut new_rngs = make_rngs(new_n, 0xA2);
    let mut new_mesh = OtMesh::establish_ideal_for_test([0xA3; 32], &mut new_rngs);

    let enrolled_root = hem_digest4_to_bytes(&cache.pk.pk_root);
    let reshared_prf = run_dealerless_reshare_seed32_goldilocks(
        [0xA4; 32],
        t,
        &[0, 1],
        &mut old_prf,
        new_t,
        &new_pts,
        &mut new_mesh,
        &mut old_rngs,
        &mut new_rngs,
        &enrolled_root,
        |_| Ok(enrolled_root),
    )
    .unwrap();
    let mut v_rngs = make_rngs(new_n, 0xA8);
    let mut v_mesh = OtMesh::establish_ideal_for_test([0xA9; 32], &mut v_rngs);
    let reshared_seed = run_dealerless_reshare_seed32_goldilocks(
        [0xA5; 32],
        t,
        &[0, 1],
        &mut old_seed,
        new_t,
        &new_pts,
        &mut new_mesh,
        &mut old_rngs,
        &mut new_rngs,
        &enrolled_root,
        |candidate_seed| {
            let (mut new_ks, mut new_vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
                [0xA6; 32],
                new_t,
                &new_pts,
                pk_seed,
                candidate_seed,
                &reshared_prf,
                0,
                0,
                0,
                &mut v_mesh,
                &mut v_rngs,
            )
            .map_err(|_| crate::dkg::DkgError::PublicRootMismatch)?;
            PreprocessedPoseidonPartyVault::fill_quorum_online_fixture(
                new_t,
                &mut new_vaults,
                verify_budget,
                &mut v_rngs[0],
            );
            let mut ks_refs: Vec<&mut Poseidon2SpdzAuthenticatedKeyShare> =
                new_ks[..new_t].iter_mut().collect();
            let mut v_refs: Vec<&mut PreprocessedPoseidonPartyVault> =
                new_vaults[..new_t].iter_mut().collect();
            let before = remaining_budget(v_refs[0]);
            verify_reshared_hem_jorts_key_mpc(
                [0xA7; 32],
                &cache,
                new_t,
                &mut ks_refs,
                &mut v_refs,
                &mut v_rngs[..new_t],
            )
            .map_err(|_| crate::dkg::DkgError::PublicRootMismatch)?;
            let after = remaining_budget(v_refs[0]);
            assert_eq!(spent(before, after), verify_budget);
            Ok(enrolled_root)
        },
    )
    .unwrap();
    assert_eq!(reshared_seed.len(), new_n);
}

#[test]
fn additive_lane_release_matches_clear_digest_and_mac_catches_a_changed_share() {
    let m = 3usize;
    let pts: Vec<Goldilocks> = (1..=m as u64).map(Goldilocks::from_u64_reduced).collect();
    let secret: HemDigest4 = core::array::from_fn(|i| Goldilocks::from_u64_reduced(77 + i as u64));
    let pk_seed: HemDigest4 =
        core::array::from_fn(|i| Goldilocks::from_u64_reduced(900 + i as u64));
    let lanes = |tag: u64| -> Vec<SecretBuffer<[Goldilocks; 4]>> {
        let a: HemDigest4 = core::array::from_fn(|i| Goldilocks::from_u64_reduced(tag + i as u64));
        let b: HemDigest4 =
            core::array::from_fn(|i| Goldilocks::from_u64_reduced(3 * tag + i as u64));
        let c: HemDigest4 = core::array::from_fn(|i| secret[i] - a[i] - b[i]);
        vec![SecretBuffer(a), SecretBuffer(b), SecretBuffer(c)]
    };
    let mut rngs = make_rngs(m, 0x51);
    let mut mesh = OtMesh::establish_ideal_for_test([0x52; 32], &mut rngs);
    let opened = release_additive_hem_prf_check_mpc(
        [0x53; 32],
        m,
        &pts,
        pk_seed,
        &lanes(11),
        &mut mesh,
        &mut rngs,
    )
    .unwrap();
    assert_eq!(opened, hem_prf_check_digest_clear(secret, pk_seed));
    // A share changed after authentication never reaches an opened digest.
    assert!(matches!(
        release_additive_hem_prf_check_inner(
            [0x54; 32],
            m,
            &pts,
            pk_seed,
            &lanes(19),
            &mut mesh,
            &mut rngs,
            Some(1),
        ),
        Err(Poseidon2MpcError::Preprocess(_))
    ));
    // Malformed quorums are refused before any protocol message.
    assert!(matches!(
        release_additive_hem_prf_check_mpc(
            [0x55; 32],
            1,
            &pts,
            pk_seed,
            &lanes(23),
            &mut mesh,
            &mut rngs,
        ),
        Err(Poseidon2MpcError::InvalidQuorum { .. })
    ));
}
