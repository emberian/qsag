#[test]
fn intermediate_mac_failure_precedes_cut_access() {
    let points = [Goldilocks::ONE, Goldilocks::from_u64_reduced(2)];
    let mut vaults: Vec<_> = points
        .iter()
        .enumerate()
        .map(|(p, &x)| PreprocessedPoseidonPartyVault::empty_for_barrier_test(p, x))
        .collect();
    let mut keys: Vec<_> = points
        .iter()
        .enumerate()
        .map(|(p, &x)| Poseidon2SpdzAuthenticatedKeyShare {
            party_id: p,
            committee_size: 2,
            eval_point: x,
            pk_seed: [0; 32],
            mac_alpha_share: GoldilocksExt2::ONE,
            sk_seed_bytes: [Goldilocks::ZERO; 32],
            sk_seed_macs: [GoldilocksExt2::ZERO; 32],
            sk_prf_bytes: [Goldilocks::ZERO; 32],
            sk_prf_macs: [GoldilocksExt2::ZERO; 32],
            enrolled_profile: None,
            enrolled_hem_profile: None,
            enrolled_latch_authority: None,
            poisoned: false,
        })
        .collect();
    let mut pending = SpdzGoldilocksPendingChecks::new(2);
    pending.shares_per_party = vec![vec![Goldilocks::ONE]; 2];
    pending.macs_per_party = vec![vec![GoldilocksExt2::ZERO]; 2];
    let mut rngs = make_rngs(2, 45);
    let cut = vec![
        vec![
            [AuthGlWire {
                val: Goldilocks::ZERO,
                mac: GoldilocksExt2::ZERO,
            }; 4],
        ],
        vec![],
    ];
    // The malformed second cut would panic if the implementation reached it.
    let result = flush_verify_and_open_cut_states4(
        &[42; 32],
        "barrier",
        2,
        &points,
        &cut,
        &vec![vec![]; 2],
        &mut pending,
        &mut keys.iter_mut().collect::<Vec<_>>(),
        &mut vaults.iter_mut().collect::<Vec<_>>(),
        &mut rngs,
    );
    assert!(matches!(
        result,
        Err(Poseidon2MpcError::Preprocess(
            PreprocessError::MacCheckFailed {
                accused_party: None,
                ..
            }
        ))
    ));
    assert!(vaults.iter().all(|v| v.is_poisoned()));
}

use super::*;
use crate::dkg::{
    QuorumEpochLatchCluster, run_dealerless_dkg_seed32_goldilocks,
    shamir_reconstruct_seed32_goldilocks,
};
use crate::field::goldilocks::GOLDILOCKS_PRIME;
use crate::tsw_baggy::{
    MonotonicEpochLatch, PqSecretKey, compute_wots_pk, derive_public_key, eval_single_sign_stateful,
};

pub(super) fn make_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
    (0..n)
        .map(|p| PartyPrivateRng::from_seed([tag.wrapping_add(p as u8 + 1); 32], b"POS2_MPC_TEST"))
        .collect()
}

#[test]
fn test_canonical_a2b_boundary_values_exact_no_wraparound() {
    let sid = [0x31; 32];
    let t = 2usize;
    let n = 2usize;
    let pts: Vec<Goldilocks> = (1..=2).map(Goldilocks::from_u64_reduced).collect();
    let mut rngs = make_rngs(n, 0x10);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

    let (alpha_c, alpha_sh) = spdz_setup_alpha_goldilocks(&sid, t, &pts, &mut rngs).unwrap();
    let mut vaults = run_dealerless_pi_pow7_with_alpha(
        sid, t, &pts, 0, 0, 0, &alpha_c, &alpha_sh, &mut mesh, &mut rngs,
    )
    .unwrap();

    // This test exercises the online canonical A2B circuit. Offline mask
    // generation/sacrifice has dedicated adversarial preprocessing tests.
    PreprocessedPoseidonPartyVault::fill_two_party_online_fixture(
        &mut vaults,
        (0, 2 * POSEIDON2_BEAVER_PER_A2B_HASH32, 8),
        &mut rngs[0],
    );

    // Test all critical Goldilocks edge cases: 0, 1, 2^32 - 1, 2^32, p - 2, p - 1, random!
    let s0 = [
        Goldilocks::ZERO,
        Goldilocks::ONE,
        Goldilocks::from_u64_reduced((1u64 << 32) - 1),
        Goldilocks::from_u64_reduced(1u64 << 32),
    ];
    let s1 = [
        Goldilocks::from_u64_reduced(GOLDILOCKS_PRIME - 2),
        Goldilocks::from_u64_reduced(GOLDILOCKS_PRIME - 1),
        Goldilocks::from_u64_reduced(0xDEAD_BEEF_CAFE_BABEu64),
        Goldilocks::from_u64_reduced(0xFFFF_FFFE_FFFF_FFFFu64),
    ];

    // Share s0 and s1 genuinely with random degree-1 polynomials (NOT public constants!)
    let mut in_per_party = vec![vec![[AuthGlWire::ZERO; 4]; 2]; t];
    let alpha_global =
        crate::preprocessing::open_and_check_degree_ext2(t, &pts, &alpha_sh, "ag").unwrap();
    for (item, arr) in [s0, s1].iter().enumerate() {
        for lane in 0..4 {
            let x = arr[lane];
            let slope = rngs[0].next_goldilocks();
            let mac_global = alpha_global.mul_base(x);
            let mac_slope = rngs[0].next_ext2();
            for p in 0..t {
                in_per_party[p][item][lane] = AuthGlWire {
                    val: x + slope * pts[p],
                    mac: mac_global + mac_slope.mul_base(pts[p]),
                };
            }
        }
    }

    let mut v_refs: Vec<&mut PreprocessedPoseidonPartyVault> = vaults.iter_mut().take(t).collect();
    let mut pending = SpdzGoldilocksPendingChecks::new(t);
    let out_bytes = eval_spdz_canonical_a2b_state4_batch_to_bytes32(
        t,
        &pts[..t],
        &in_per_party,
        &mut v_refs,
        &mut pending,
    )
    .unwrap();

    let mut dummy_ks = [
        Poseidon2SpdzAuthenticatedKeyShare {
            party_id: 0,
            committee_size: 3,
            eval_point: pts[0],
            pk_seed: [0; 32],
            mac_alpha_share: v_refs[0].mac_alpha_share,
            sk_seed_bytes: [Goldilocks::ZERO; 32],
            sk_seed_macs: [GoldilocksExt2::ZERO; 32],
            sk_prf_bytes: [Goldilocks::ZERO; 32],
            sk_prf_macs: [GoldilocksExt2::ZERO; 32],
            enrolled_profile: None,
            enrolled_hem_profile: None,
            enrolled_latch_authority: None,
            poisoned: false,
        },
        Poseidon2SpdzAuthenticatedKeyShare {
            party_id: 1,
            committee_size: 3,
            eval_point: pts[1],
            pk_seed: [0; 32],
            mac_alpha_share: v_refs[1].mac_alpha_share,
            sk_seed_bytes: [Goldilocks::ZERO; 32],
            sk_seed_macs: [GoldilocksExt2::ZERO; 32],
            sk_prf_bytes: [Goldilocks::ZERO; 32],
            sk_prf_macs: [GoldilocksExt2::ZERO; 32],
            enrolled_profile: None,
            enrolled_hem_profile: None,
            enrolled_latch_authority: None,
            poisoned: false,
        },
    ];
    let (k0, k1) = dummy_ks.split_at_mut(1);
    let mut ks_refs = [&mut k0[0], &mut k1[0]];
    let empty_st = vec![Vec::new(); t];
    let (_, opened_bytes) = flush_verify_and_open_cut_states4(
        &sid,
        "a2b_edge_test",
        t,
        &pts[..t],
        &empty_st,
        &out_bytes,
        &mut pending,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs[..t],
    )
    .unwrap();

    for (item, arr) in [s0, s1].iter().enumerate() {
        let mut exp = [0u8; 32];
        for lane in 0..4 {
            exp[8 * lane..8 * (lane + 1)].copy_from_slice(&arr[lane].to_be_bytes());
        }
        assert_eq!(opened_bytes[item], exp);
    }
}

/// Dishonest-majority 2-of-2 quorum (`2t - 1 = 3 > 2`: 1 of 2 signers may be actively corrupt)
/// from a real dealerless Goldilocks DKG, with `budget = (pow7, beaver, a2b)` preprocessing.
/// The reference single-signer key is reconstructed ONLY inside the test harness.
fn setup_two_party_poseidon2_quorum(
    budget: (usize, usize, usize),
) -> (
    Vec<Poseidon2SpdzAuthenticatedKeyShare>,
    Vec<PreprocessedPoseidonPartyVault>,
    Vec<PartyPrivateRng>,
    PqSecretKey,
) {
    setup_poseidon2_committee(2, 2, budget)
}

/// A `t`-of-`n` committee from a real dealerless Goldilocks DKG, with
/// `budget = (pow7, beaver, a2b)` preprocessing. The reference single-signer key is
/// reconstructed ONLY inside the test harness.
pub(super) fn setup_poseidon2_committee(
    t: usize,
    n: usize,
    budget: (usize, usize, usize),
) -> (
    Vec<Poseidon2SpdzAuthenticatedKeyShare>,
    Vec<PreprocessedPoseidonPartyVault>,
    Vec<PartyPrivateRng>,
    PqSecretKey,
) {
    setup_poseidon2_committee_material(t, n, budget, false)
}

pub(super) fn setup_poseidon2_committee_material(
    t: usize,
    n: usize,
    budget: (usize, usize, usize),
    online_fixture: bool,
) -> (
    Vec<Poseidon2SpdzAuthenticatedKeyShare>,
    Vec<PreprocessedPoseidonPartyVault>,
    Vec<PartyPrivateRng>,
    PqSecretKey,
) {
    let sid = [0x52; 32];
    let pts: Vec<Goldilocks> = (1..=n as u64).map(Goldilocks::from_u64_reduced).collect();
    let mut rngs = make_rngs(n, 0x30);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

    let dkg_seed =
        run_dealerless_dkg_seed32_goldilocks([0x61; 32], t, &pts, &mut mesh, &mut rngs).unwrap();
    let dkg_prf =
        run_dealerless_dkg_seed32_goldilocks([0x62; 32], t, &pts, &mut mesh, &mut rngs).unwrap();
    let pk_seed = dkg_seed.1;

    let production_budget = if online_fixture { (0, 0, 0) } else { budget };
    let (key_shares, mut vaults) = authenticate_poseidon_dkg_shares_and_preprocess(
        [0x63; 32],
        t,
        &pts,
        pk_seed,
        &dkg_seed.0,
        &dkg_prf.0,
        production_budget.0,
        production_budget.1,
        production_budget.2,
        &mut mesh,
        &mut rngs,
    )
    .unwrap();

    if online_fixture {
        PreprocessedPoseidonPartyVault::fill_two_party_online_fixture(
            &mut vaults,
            budget,
            &mut rngs[0],
        );
    }
    let ref_sk = PqSecretKey {
        sk_seed: shamir_reconstruct_seed32_goldilocks(&dkg_seed.0[..t].iter().collect::<Vec<_>>())
            .unwrap(),
        sk_prf: shamir_reconstruct_seed32_goldilocks(&dkg_prf.0[..t].iter().collect::<Vec<_>>())
            .unwrap(),
        pk_seed,
    };
    (key_shares, vaults, rngs, ref_sk)
}

pub(super) fn remaining_budget(v: &PreprocessedPoseidonPartyVault) -> (usize, usize, usize) {
    (v.remaining_pow7(), v.remaining_beaver(), v.remaining_a2b())
}

pub(super) fn spent(
    before: (usize, usize, usize),
    after: (usize, usize, usize),
) -> (usize, usize, usize) {
    (before.0 - after.0, before.1 - after.1, before.2 - after.2)
}

/// Flip one bit of one leaf, swap the public key, name the wrong layer, add a leaf.
fn mismatched_caches(cache: &DkgCachedSubtrees) -> [DkgCachedSubtrees; 4] {
    let mut corrupted_leaf = cache.clone();
    corrupted_leaf.top_leaves[0][7] ^= 0x01;
    let mut other_pk = cache.clone();
    other_pk.pk.pk_root[0] ^= 0x80;
    let mut wrong_layer = cache.clone();
    wrong_layer.top_layer ^= 1;
    let mut wrong_len = cache.clone();
    wrong_len.top_leaves.push([0u8; 32]);
    [corrupted_leaf, other_pk, wrong_layer, wrong_len]
}

/// A top-subtree leaf cache that does not belong to `(params, pk)` is refused by every `_cached`
/// entry point before an epoch is latched or any MPC runs. No preprocessing is provisioned
/// here, so reaching MPC at all would fail with a different error.
#[test]
fn test_poseidon2_mpc_cached_top_subtree_rejects_mismatched_cache() {
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
    let stateless_params = PqHashParams {
        fors_trees: 1,
        fors_height: 1,
        stateful: false,
        ..params
    };
    assert!(params.is_well_formed() && stateless_params.is_well_formed());
    let t = 2usize;
    let (mut key_shares, mut vaults, mut rngs, ref_sk) =
        setup_two_party_poseidon2_quorum((0, 0, 0));
    let (ks0, ks1) = key_shares.split_at_mut(1);
    let (v0, v1) = vaults.split_at_mut(1);
    let mut ks_refs = [&mut ks0[0], &mut ks1[0]];
    let mut v_refs = [&mut v0[0], &mut v1[0]];

    // The true top-subtree leaves, derived in the clear from the harness-only reference key.
    let pk = derive_public_key(Poseidon2Suite, &params, &ref_sk);
    assert_eq!(
        pk,
        derive_public_key(Poseidon2Suite, &stateless_params, &ref_sk)
    );
    let cache = DkgCachedSubtrees {
        top_layer: 1,
        top_leaves: (0..2u32)
            .map(|kp| compute_wots_pk(Poseidon2Suite, &params, &ref_sk, 1, 0, kp))
            .collect(),
        pk,
    };
    assert_eq!(
        validate_top_subtree_cache(&params, &pk, Some(&cache)),
        Ok(())
    );
    assert_eq!(validate_top_subtree_cache(&params, &pk, None), Ok(()));

    let msg = b"mismatched top subtree cache";
    let mut l0 = MonotonicEpochLatch::new(3);
    let mut l1 = MonotonicEpochLatch::new(3);
    let mut foreign_pk = pk;
    foreign_pk.pk_seed[31] ^= 0x01;
    let bad_caches = mismatched_caches(&cache);
    let attempts = bad_caches
        .iter()
        .map(|bad| (bad, pk))
        .chain(core::iter::once((&cache, foreign_pk)));
    for (bad_cache, with_pk) in attempts {
        assert_eq!(
            validate_top_subtree_cache(&params, &with_pk, Some(bad_cache)),
            Err(Poseidon2MpcError::CachedSubtreeMismatch)
        );
        let stateful = sign_jorts_poseidon2_mpc_cached(
            [0x69; 32],
            &params,
            &with_pk,
            Some(bad_cache),
            t,
            None,
            &mut [&mut l0, &mut l1],
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        );
        assert_eq!(stateful, Err(Poseidon2MpcError::CachedSubtreeMismatch));
        let retry = retry_jorts_poseidon2_mpc_cached(
            [0x6a; 32],
            &params,
            &with_pk,
            Some(bad_cache),
            t,
            None,
            &mut [&mut l0, &mut l1],
            3,
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        );
        assert_eq!(retry, Err(Poseidon2MpcError::CachedSubtreeMismatch));
        let stateless = sign_stateless_tsw_poseidon2_mpc_cached(
            [0x6b; 32],
            &stateless_params,
            &with_pk,
            Some(bad_cache),
            t,
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        );
        assert_eq!(stateless, Err(Poseidon2MpcError::CachedSubtreeMismatch));
    }
    // Nothing was latched and nothing was burned.
    assert_eq!(l0, MonotonicEpochLatch::new(3));
    assert_eq!(l1, MonotonicEpochLatch::new(3));
    assert!(!ks_refs[0].poisoned && !ks_refs[1].poisoned);
    assert!(!v_refs[0].is_poisoned() && !v_refs[1].is_poisoned());
}

/// A signature made with the keygen's top-subtree leaf cache is byte-identical to the uncached
/// one and spends exactly one full subtree less preprocessing; a cache that does not belong
/// to `(params, pk)` yields no signature.
///
/// Real DKG and key authentication, with trusted authenticated preprocessing fixtures
/// for the online protocol. Dealerless material generation has separate integration tests.
#[test]
fn test_poseidon2_mpc_cached_top_subtree_signature_byte_identical() {
    let _memory = crate::test_budget::reserve_mb(1100);
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
    let t = 2usize;
    let kg = required_poseidon2_keygen_preprocessing_budget(&params);
    let sg = required_poseidon2_sign_preprocessing_budget(&params);
    let sgc = required_poseidon2_sign_preprocessing_budget_cached(&params);
    assert_eq!((sg.0 - sgc.0, sg.1 - sgc.1, sg.2 - sgc.2), kg);

    // Keygen + one uncached signature + a cached signature and a cached retry.
    let (mut key_shares, mut vaults, mut rngs, ref_sk) = setup_poseidon2_committee_material(
        2,
        2,
        (
            kg.0 + sg.0 + 2 * sgc.0,
            kg.1 + sg.1 + 2 * sgc.1,
            kg.2 + sg.2 + 2 * sgc.2,
        ),
        true,
    );
    let ref_pk = derive_public_key(Poseidon2Suite, &params, &ref_sk);
    let (ks0, ks1) = key_shares.split_at_mut(1);
    let (v0, v1) = vaults.split_at_mut(1);
    let mut ks_refs = [&mut ks0[0], &mut ks1[0]];
    let mut v_refs = [&mut v0[0], &mut v1[0]];

    // 1. Keygen keeps the top subtree's leaves; they are the reference key's leaves.
    let before = remaining_budget(v_refs[0]);
    let cache = build_distributed_poseidon2_key_cached(
        [0x64; 32],
        &params,
        t,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap();
    let spent_keygen = spent(before, remaining_budget(v_refs[0]));
    assert_eq!(spent_keygen, kg);
    assert_eq!(cache.pk, ref_pk);
    assert_eq!(cache.top_layer, 0);
    let ref_leaves: Vec<[u8; 32]> = (0..2u32)
        .map(|kp| compute_wots_pk(Poseidon2Suite, &params, &ref_sk, 0, 0, kp))
        .collect();
    assert_eq!(cache.top_leaves, ref_leaves);
    let pk = cache.pk;

    // 2. Uncached signature at epoch 1 (the second leaf, so the auth path is leaf 0).
    let msg = b"JortsPoseidon2 cached top subtree parity vector";
    let mut a0 = MonotonicEpochLatch::new(1);
    let mut a1 = MonotonicEpochLatch::new(1);
    let before = remaining_budget(v_refs[0]);
    let (ep_plain, sig_plain) = sign_jorts_poseidon2_mpc(
        [0x65; 32],
        &params,
        &pk,
        t,
        None,
        &mut [&mut a0, &mut a1],
        msg,
        100_000,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap();
    let spent_plain = spent(before, remaining_budget(v_refs[0]));
    assert_eq!(ep_plain, 1);
    let mut ref_latch = MonotonicEpochLatch::new(1);
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
    assert_eq!(sig_plain, ref_sig);
    let plain_bytes = sig_plain.to_wire_bytes(&params).unwrap();

    // 3. A corrupted leaf or a different public key: no signature, nothing latched or spent.
    let mut b0 = MonotonicEpochLatch::new(1);
    let mut b1 = MonotonicEpochLatch::new(1);
    let before = remaining_budget(v_refs[0]);
    for bad in &mismatched_caches(&cache) {
        let refused = sign_jorts_poseidon2_mpc_cached(
            [0x69; 32],
            &params,
            &pk,
            Some(bad),
            t,
            None,
            &mut [&mut b0, &mut b1],
            msg,
            100_000,
            &mut ks_refs,
            &mut v_refs,
            &mut rngs,
        );
        assert_eq!(refused, Err(Poseidon2MpcError::CachedSubtreeMismatch));
    }
    assert_eq!(remaining_budget(v_refs[0]), before);
    assert_eq!(b0, MonotonicEpochLatch::new(1));
    assert_eq!(b1, MonotonicEpochLatch::new(1));

    // 4. Cached signature on fresh latches: the same bytes, one full subtree less MPC.
    let (ep_cached, sig_cached) = sign_jorts_poseidon2_mpc_cached(
        [0x6c; 32],
        &params,
        &pk,
        Some(&cache),
        t,
        None,
        &mut [&mut b0, &mut b1],
        msg,
        100_000,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap();
    let spent_cached = spent(before, remaining_budget(v_refs[0]));
    assert_eq!(ep_cached, 1);
    assert_eq!(sig_cached.to_wire_bytes(&params).unwrap(), plain_bytes);
    assert!(verify_pq_hash_sig(
        Poseidon2Suite,
        &params,
        &pk,
        msg,
        &sig_cached
    ));
    assert_eq!(spent(spent_plain, spent_cached), spent_keygen);

    // 5. Cached crash-retry of the epoch latched in step 2 reproduces the same bytes.
    let retry_cached = retry_jorts_poseidon2_mpc_cached(
        [0x6d; 32],
        &params,
        &pk,
        Some(&cache),
        t,
        None,
        &mut [&mut a0, &mut a1],
        1,
        msg,
        100_000,
        &mut ks_refs,
        &mut v_refs,
        &mut rngs,
    )
    .unwrap();
    assert_eq!(retry_cached.to_wire_bytes(&params).unwrap(), plain_bytes);
}

/// The latch gate on its own, without MPC: which signing sets may reserve an epoch, and that
/// a refusal leaves every latch where it was.
#[test]
fn test_committee_latch_gate_full_attendance_certificate_and_lagging_latch() {
    let params = PqHashParams {
        max_sigs_log2: 3,
        num_layers: 1,
        subtree_height: 3,
        ..PqHashParams::COMPACT_JORTS
    };
    assert!(params.is_well_formed());
    let pk = PqPublicKey {
        pk_seed: [0x11; 32],
        pk_root: [0x22; 32],
    };
    let (mu_a, mu_b) = ([0xa1; 32], [0xb2; 32]);
    let bind = |epoch: u64, mu: &[u8; 32]| epoch_latch_binding(&pk.pk_seed, &pk.pk_root, epoch, mu);

    // n == t == 2: both members attend, so their two latches are the whole committee.
    let (mut a0, mut a1) = (MonotonicEpochLatch::new(0), MonotonicEpochLatch::new(0));
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            2,
            None,
            None,
            &mut [&mut a0, &mut a1],
            &mu_a
        ),
        Ok(0)
    );
    assert_eq!((a0.next_epoch(), a1.next_epoch()), (1, 1));
    assert_eq!(a0.in_flight(), Some((0, mu_a)));

    // (t, n) = (2, 3): two members' latches authorise nothing by themselves.
    let mut l = [
        MonotonicEpochLatch::new(0),
        MonotonicEpochLatch::new(0),
        MonotonicEpochLatch::new(0),
    ];
    let [l0, l1, l2] = &mut l;
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            None,
            None,
            &mut [&mut *l0, &mut *l1],
            &mu_a
        ),
        Err(Poseidon2MpcError::LatchCertificateRequired {
            signers: 2,
            committee: 3
        })
    );
    assert_eq!((l0.next_epoch(), l1.next_epoch()), (0, 0));

    // All three attend: accepted without a certificate.
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            None,
            None,
            &mut [&mut *l0, &mut *l1, &mut *l2],
            &mu_a
        ),
        Ok(0)
    );

    // A certified signature by {P0, P1} leaves P2's latch behind.
    let mut cluster = QuorumEpochLatchCluster::new(3, 1).unwrap();
    let auth = cluster.authority();
    cluster
        .certify_epoch(&[0, 1, 2], 0, bind(0, &mu_a))
        .unwrap();
    let cert1 = cluster
        .certify_epoch(&[0, 1, 2], 1, bind(1, &mu_a))
        .unwrap();
    // Without a pinned authority, a certificate is rejected even if structurally valid.
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            None,
            Some(&cert1),
            &mut [&mut *l0, &mut *l1],
            &mu_a
        ),
        Err(Poseidon2MpcError::LatchCertificateRejected(
            QuorumLatchError::CertificateCommitteeMismatch
        ))
    );
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            Some(&auth),
            Some(&cert1),
            &mut [&mut *l0, &mut *l1],
            &mu_a
        ),
        Ok(1)
    );
    assert_eq!(
        (l0.next_epoch(), l1.next_epoch(), l2.next_epoch()),
        (2, 2, 1)
    );

    // Full attendance with the lagging latch and no certificate: refused, nothing advanced.
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            Some(&auth),
            None,
            &mut [&mut *l0, &mut *l1, &mut *l2],
            &mu_b
        ),
        Err(Poseidon2MpcError::EpochLatch(
            EpochLatchError::LatchesDisagree
        ))
    );
    assert_eq!(
        (l0.next_epoch(), l1.next_epoch(), l2.next_epoch()),
        (2, 2, 1)
    );
    assert_eq!(l0.in_flight(), Some((1, mu_a)));

    // A certificate minted by a distinct rogue cluster is rejected by the pinned authority.
    let mut rogue = QuorumEpochLatchCluster::new(3, 1).unwrap();
    let rogue_cert = rogue.certify_epoch(&[0, 1, 2], 1, bind(1, &mu_b)).unwrap();
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            Some(&auth),
            Some(&rogue_cert),
            &mut [&mut *l2, &mut *l1],
            &mu_b
        ),
        Err(Poseidon2MpcError::LatchCertificateRejected(
            QuorumLatchError::CertificateCommitteeMismatch
        ))
    );

    // Even under a harness-simulated split authority sharing the same MAC keys, the epoch
    // P0 and P1 already hold for `mu_a` cannot be taken for `mu_b`, and two-phase latch
    // checking leaves `l2` untouched.
    let mut shared_second = cluster.new_with_shared_test_authority();
    let shared_cert = shared_second
        .certify_epoch(&[0, 1, 2], 1, bind(1, &mu_b))
        .unwrap();
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            Some(&auth),
            Some(&shared_cert),
            &mut [&mut *l2, &mut *l1],
            &mu_b
        ),
        Err(Poseidon2MpcError::EpochLatch(
            EpochLatchError::EquivocationRefused
        ))
    );
    // P2 was checked first and would have accepted; it must not have moved.
    assert_eq!(l2.next_epoch(), 1);
    assert_eq!(l2.in_flight(), Some((0, mu_a)));

    // The certified next epoch resynchronises the lagging latch: P2 skips epoch 1, which it
    // never used, and all three hold epoch 2.
    assert_eq!(cluster.next_unreserved_epoch(), Some(2));
    let cert2 = cluster
        .certify_epoch(&[0, 1, 2], 2, bind(2, &mu_b))
        .unwrap();
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            Some(&auth),
            Some(&cert2),
            &mut [&mut *l1, &mut *l2],
            &mu_b
        ),
        Ok(2)
    );
    assert_eq!((l1.next_epoch(), l2.next_epoch()), (3, 3));
    // Presenting the same certificate again changes nothing.
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            Some(&auth),
            Some(&cert2),
            &mut [&mut *l1, &mut *l2],
            &mu_b
        ),
        Ok(2)
    );
    assert_eq!((l1.next_epoch(), l2.next_epoch()), (3, 3));

    // An old certificate cannot move a latch backwards.
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            Some(&auth),
            Some(&cert1),
            &mut [&mut *l0, &mut *l1],
            &mu_a
        ),
        Err(Poseidon2MpcError::EpochLatch(EpochLatchError::StaleEpoch))
    );
    assert_eq!(l0.in_flight(), Some((1, mu_a)));

    // Epochs beyond the key's capacity are refused before any latch moves.
    let cert8 = cluster
        .certify_epoch(&[0, 1, 2], 8, bind(8, &mu_b))
        .unwrap();
    assert_eq!(
        reserve_authorised_epoch(
            &params,
            &pk,
            2,
            3,
            Some(&auth),
            Some(&cert8),
            &mut [&mut *l0, &mut *l2],
            &mu_b
        ),
        Err(Poseidon2MpcError::EpochLatch(EpochLatchError::Exhausted))
    );
    assert_eq!((l0.next_epoch(), l2.next_epoch()), (2, 3));
}
