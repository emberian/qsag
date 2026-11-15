// SPDX-License-Identifier: Apache-2.0 OR MIT
#![cfg(feature = "quorum")]
//! Cross-Crate `Poseidon2`, Merkle-Compression & `QS <-> AG` (`Hem` Quorum) Differential Validation
//!
//! Validates:
//! 1. End-to-end compatibility of `qsag-quorum` (`HemCommitteePartitionedQuorum` QS-A,
//!    `HemDynamicShamirQuorum` QS-B with proactive refresh `Π_refresh` and `(2, 3) -> (3, 5)`
//!    quorum-switching `Π_reshare`, and dealerless `HemSpdzSeedQuorum`) with `qsag-agg`
//!    (`ValidatorPublicKey`, `ValidatorSignature`, `verify_individual_signature`, and untrusted
//!    `HemAggregator` WHIR aggregation under `BciksJohnsonQrom128`), plus negative adversarial
//!    tamper/bitmap/message rejection checks.
//! 2. Four-way bit-for-bit `poseidon2_perm12` consistency across `qsag-core`, `qsag-agg`,
//!    `qsag-accel` CPU, live `VulkanRdna2Backend` GPU (when available on Linux), and independent
//!    Gauss-Jordan inverse matrices `poseidon2_perm12_inv_with_mats`.
//! 3. Exact consistency of the `QS <-> AG` `Hem` Merkle/compression bridge
//!    (`hem_poseidon2_compress12_ff == poseidon2_compress12_ff` and
//!    `hem_merkle_node_hash == merkle_node_hash`), alongside explicit characterization of
//!    `qsag_accel::poseidon2::merkle_layer_poseidon2_at_cpu`'s distinct 1-permutation compression
//!    domain and its pre-feed-forward capacity-sum collision `(s2 + 1, parent_idx - 1)` under
//!    adversarially chosen `pk_seed`.

use proptest::prelude::*;
use qsag_accel::goldilocks::{gl_add, gl_sub};
use qsag_accel::poseidon2::{
    merkle_layer_poseidon2_at_cpu, poseidon2_perm12 as accel_poseidon2_perm12,
};
use qsag_agg::field::Goldilocks as AggGoldilocks;
use qsag_agg::sig::{DOMAIN_MERKLE_NODE, MerkleNodeAddr, merkle_node_hash};
use qsag_agg::sponge::{
    poseidon2_compress12_ff, poseidon2_perm12 as agg_poseidon2_perm12,
};
use qsag_agg::{
    AggSigProfile, HemAggConfig, HemAggregator, SignerBitmap, SigningMode, ValidatorPublicKey,
    ValidatorSignature, WhirSecurityRegime, verify_individual_signature,
};
use qsag_core::field::goldilocks::Goldilocks as CoreGoldilocks;
use qsag_core::poseidon2_mpc::{
    hem_merkle_node_hash, hem_poseidon2_compress12_ff, verify_hem_jorts_signature,
};
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_core::sponge::poseidon2::poseidon2_perm12 as core_poseidon2_perm12;
use qsag_external_validation::{build_poseidon2_inverse_matrices, poseidon2_perm12_inv_with_mats};
use qsag_quorum::{
    HemCommitteePartitionedQuorum, HemDynamicShamirQuorum, HemSpdzSeedQuorum,
};

fn party_rngs(seed: u8, n: usize) -> Vec<PartyPrivateRng> {
    (0..n)
        .map(|p| {
            PartyPrivateRng::from_seed(
                [seed.wrapping_add(p as u8); 32],
                b"VALIDATION.HEM.QUORUM.RNG/v1",
            )
        })
        .collect()
}

#[test]
fn e2e_quorum_qsa_qsb_spdz_to_hem_whir_aggregation_and_adversarial_rejection() {
    // 1. Validator 0: QS-B Dynamic Shamir Quorum `(2, 3)` -> reshare `(3, 5)` -> refresh -> sign
    let mut qsb = HemDynamicShamirQuorum::stage([0x21; 32], 2, 3, 4).unwrap();
    let pk0 = qsb.public_key();
    qsb.reshare_quorum(
        [0x22; 32],
        &[0, 2],
        3,
        5,
        &mut party_rngs(10, 3),
        &mut party_rngs(20, 5),
    )
    .unwrap();
    assert_eq!(qsb.public_key(), pk0);
    assert_eq!(qsb.threshold_and_size(), (3, 5));

    qsb.proactive_refresh([0x23; 32], &mut party_rngs(30, 5))
        .unwrap();
    assert_eq!(qsb.public_key(), pk0);

    // 2. Validator 1: QS-A Committee-Partitioned Quorum `(2, 3)`
    let mut qsa = HemCommitteePartitionedQuorum::stage([0x31; 32], 2, 3, 4).unwrap();
    let pk1 = qsa.public_key();

    // 3. Validator 2: 100% Dealerless SPDZ Seed Quorum `(2, 2)` (OT + Gilboa + SPDZ online MPC)
    let mut spdz = HemSpdzSeedQuorum::keygen_dealerless_online_fixture(
        [0x41; 32],
        2,
        2,
        1,
        &mut party_rngs(40, 2),
    )
    .unwrap();
    let pk2 = spdz.public_key();

    let consensus_msg = b"external-validation: QS-A + QS-B(3,5) + Dealerless-SPDZ -> Hem QROM-128";
    // Note: on a `(3, 5)` BFT latch cluster, quorum requires `2*q > 5 + 2 => q >= 4` ackers.
    let (ep_qsb, sig_qsb) = qsb
        .sign_quorum(&[0, 2, 4], &[0, 1, 2, 4], consensus_msg)
        .unwrap();
    assert_eq!(ep_qsb, 0);
    assert!(verify_hem_jorts_signature(&pk0, consensus_msg, &sig_qsb));

    let (_, sig_qsa) = qsa.sign_with_committee(&[1, 2], consensus_msg).unwrap();
    assert!(verify_hem_jorts_signature(&pk1, consensus_msg, &sig_qsa));

    let (ep_spdz, sig_spdz) = spdz
        .sign_quorum_online_fixture(
            [0x42; 32],
            &[0, 1],
            &[0, 1],
            None,
            consensus_msg,
            &mut party_rngs(50, 2),
        )
        .unwrap();
    assert_eq!(ep_spdz, 0);
    assert!(verify_hem_jorts_signature(&pk2, consensus_msg, &sig_spdz));

    // Convert all 3 threshold custody keys (65 B) & signatures (4,328 B) into `qsag_agg` wire types
    let agg_pks: Vec<ValidatorPublicKey> = [pk0, pk1, pk2]
        .iter()
        .map(|pk| ValidatorPublicKey::from_bytes_canonical(&pk.to_bytes()).unwrap())
        .collect();
    let agg_sigs: Vec<ValidatorSignature> = [sig_qsb, sig_qsa, sig_spdz]
        .iter()
        .map(|s| {
            ValidatorSignature::from_bytes_canonical(AggSigProfile::JortsPoseidon2, &s.to_bytes())
                .unwrap()
        })
        .collect();
    for (pk, sig) in agg_pks.iter().zip(agg_sigs.iter()) {
        assert!(verify_individual_signature(pk, consensus_msg, sig));
        assert!(!verify_individual_signature(pk, b"tampered-msg", sig));
    }

    // Aggregate all 3 heterogeneous threshold-quorum validators into a single WHIR QROM-128 proof
    let bitmap = SignerBitmap::from_active_indices(3, &[0, 1, 2]).unwrap();
    let mode = SigningMode::SharedMessage(consensus_msg);
    let cfg = HemAggConfig {
        regime: WhirSecurityRegime::BciksJohnsonQrom128,
        ..HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [0x88; 32])
    };
    let agg_proof =
        HemAggregator::aggregate_with_config(&agg_pks, &bitmap, &mode, &agg_sigs, &cfg).unwrap();
    assert!(HemAggregator::verify_with_regime(
        &agg_pks,
        &mode,
        &agg_proof,
        WhirSecurityRegime::BciksJohnsonQrom128,
    ));

    // Adversarial rejection checks: wrong message or swapped committee roster must be rejected
    let wrong_mode = SigningMode::SharedMessage(b"forged-consensus-block");
    assert!(!HemAggregator::verify_with_regime(
        &agg_pks,
        &wrong_mode,
        &agg_proof,
        WhirSecurityRegime::BciksJohnsonQrom128,
    ));
    let swapped_pks = vec![agg_pks[1], agg_pks[0], agg_pks[2]];
    assert!(!HemAggregator::verify_with_regime(
        &swapped_pks,
        &mode,
        &agg_proof,
        WhirSecurityRegime::BciksJohnsonQrom128,
    ));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Verifies bit-identity of `poseidon2_perm12` across `qsag-core`, `qsag-agg`, `qsag-accel` CPU,
    /// and independent Gauss-Jordan inverse `poseidon2_perm12_inv_with_mats`, plus bit-identity of
    /// `hem_poseidon2_compress12_ff` and `hem_merkle_node_hash` between `qsag-core` and `qsag-agg`.
    #[test]
    fn poseidon2_cpu_mpc_agg_and_merkle_bridge_equivalence(
        raw_state in any::<[u64; 12]>(),
        layer in 0u32..0xFFFEu32,
        tree_idx in any::<u64>(),
        level in 0u32..32u32,
        node_idx in 0u32..65536u32,
    ) {
        let (me_inv, mi_inv) = build_poseidon2_inverse_matrices();

        let mut core_st = raw_state.map(CoreGoldilocks::from_u64_reduced);
        let mut agg_st = raw_state.map(AggGoldilocks::from_u64_reduced);
        let mut accel_st = core_st.map(|x| x.to_canonical_u64());
        let canon_in = accel_st;

        core_poseidon2_perm12(&mut core_st);
        agg_poseidon2_perm12(&mut agg_st);
        accel_poseidon2_perm12(&mut accel_st);

        let core_u64 = core_st.map(|x| x.to_canonical_u64());
        let agg_u64 = agg_st.map(|x| x.to_canonical_u64());
        prop_assert_eq!(core_u64, agg_u64);
        prop_assert_eq!(core_u64, accel_st);

        let mut back = core_st;
        poseidon2_perm12_inv_with_mats(&mut back, &me_inv, &mi_inv);
        prop_assert_eq!(back.map(|x| x.to_canonical_u64()), canon_in);

        // Compare `Hem` compression & 2-permutation sponge Merkle node hash (`qsag-core` vs `qsag-agg`)
        let c_left: [CoreGoldilocks; 4] = core::array::from_fn(|i| CoreGoldilocks::from_u64_reduced(raw_state[i]));
        let c_right: [CoreGoldilocks; 4] = core::array::from_fn(|i| CoreGoldilocks::from_u64_reduced(raw_state[4 + i]));
        let c_seed: [CoreGoldilocks; 4] = core::array::from_fn(|i| CoreGoldilocks::from_u64_reduced(raw_state[8 + i]));

        let a_left = c_left.map(|x| AggGoldilocks::from_u64_reduced(x.to_canonical_u64()));
        let a_right = c_right.map(|x| AggGoldilocks::from_u64_reduced(x.to_canonical_u64()));
        let a_seed = c_seed.map(|x| AggGoldilocks::from_u64_reduced(x.to_canonical_u64()));

        let hem_comp = hem_poseidon2_compress12_ff(c_left, c_right, c_seed).map(|x| x.to_canonical_u64());
        let agg_comp = poseidon2_compress12_ff(a_left, a_right, a_seed).map(|x| x.to_canonical_u64());
        prop_assert_eq!(hem_comp, agg_comp);

        let hem_node = hem_merkle_node_hash(
            c_seed,
            layer,
            tree_idx,
            level,
            node_idx,
            c_left,
            c_right,
        ).map(|x| x.to_canonical_u64());
        let agg_node = merkle_node_hash(
            DOMAIN_MERKLE_NODE,
            a_seed,
            MerkleNodeAddr { layer, tree_idx, level, node_idx },
            a_left,
            a_right,
        ).map(|x| x.to_canonical_u64());
        prop_assert_eq!(hem_node, agg_node);
    }
}

#[test]
fn accel_poseidon2_gpu_perm12_and_merkle_layer_domain_characterization() {
    // 1. Characterize `qsag_accel::merkle_layer_poseidon2_at_cpu` vs `qsag_agg::sig::merkle_node_hash`:
    //    `merkle_layer_poseidon2_at_cpu` uses a 1-permutation Hirose/Davies-Meyer construction
    //    (`st = [left, right, s0 + tweak, s1 + layer, s2 + node_tweak, s3 + IV]`,
    //     `out = perm12(st)[0..4] + left + right + pk_seed`), distinct from `merkle_node_hash`'s
    //    2-permutation rate-8 sponge.
    let left = [11u64, 22, 33, 44];
    let right = [55u64, 66, 77, 88];
    let pk_seed = [100u64, 200, 300, 400];
    let mut accel_parent = [[0u64; 4]; 1];
    merkle_layer_poseidon2_at_cpu(&[left, right], &pk_seed, 3, 7, &mut accel_parent).unwrap();

    let agg_parent = merkle_node_hash(
        0x4D52_4B4C_5F50_3231,
        pk_seed.map(AggGoldilocks::from_u64_reduced),
        MerkleNodeAddr {
            layer: 0,
            tree_idx: 0,
            level: 3,
            node_idx: 7,
        },
        left.map(AggGoldilocks::from_u64_reduced),
        right.map(AggGoldilocks::from_u64_reduced),
    )
    .map(|x| x.to_canonical_u64());
    assert_ne!(
        accel_parent[0], agg_parent,
        "qsag-accel 1-perm MerkleLayerPoseidon2 and qsag-agg 2-perm merkle_node_hash are distinct primitives"
    );

    // 2. Document the exact multi-key / chosen-`pk_seed` additive capacity invariance in
    //    `merkle_layer_poseidon2_at_cpu`: shifting `pk_seed[2]' = pk_seed[2] + 1` and
    //    `start_parent_idx' = start_parent_idx - 1` keeps `s2 + node_tweak` (and all other 11
    //    `poseidon2_perm12` input lanes!) 100% identical, so `parent'` differs from `parent`
    //    purely by `+1` in lane 2 from the outer `s2` feed-forward (`parent'[2] - parent[2] == 1`)!
    let pk_seed_shifted = [pk_seed[0], pk_seed[1], gl_add(pk_seed[2], 1), pk_seed[3]];
    let mut accel_parent_shifted = [[0u64; 4]; 1];
    merkle_layer_poseidon2_at_cpu(
        &[left, right],
        &pk_seed_shifted,
        3,
        6,
        &mut accel_parent_shifted,
    )
    .unwrap();
    assert_eq!(accel_parent_shifted[0][0], accel_parent[0][0]);
    assert_eq!(accel_parent_shifted[0][1], accel_parent[0][1]);
    assert_eq!(
        gl_sub(accel_parent_shifted[0][2], accel_parent[0][2]),
        1,
        "pre-feed-forward perm12 input collided identically across distinct (pk_seed, parent_idx)"
    );
    assert_eq!(accel_parent_shifted[0][3], accel_parent[0][3]);

    // 3. When running on a Linux host with a Vulkan GPU (e.g. RDNA2 / RDNA3.5), also verify
    //    `VulkanRdna2Backend` hardware `batch_poseidon2_perm12` matches `qsag-core` & `qsag-agg`!
    #[cfg(target_os = "linux")]
    if let Ok(gpu) = qsag_accel::VulkanRdna2Backend::try_new() {
        use qsag_accel::AcceleratorBackend;
        let mut states: Vec<[u64; 12]> = (0..64)
            .map(|i| {
                core::array::from_fn(|lane| {
                    ((i as u64) * 0x9E37_79B9_7F4A_7C15 + (lane as u64) * 17)
                        % 0xFFFF_FFFF_0000_0001
                })
            })
            .collect();
        let expected: Vec<[u64; 12]> = states
            .iter()
            .map(|s| {
                let mut c = s.map(CoreGoldilocks::from_u64_reduced);
                core_poseidon2_perm12(&mut c);
                c.map(|x| x.to_canonical_u64())
            })
            .collect();
        gpu.batch_poseidon2_perm12(&mut states);
        assert_eq!(states, expected, "Vulkan GPU Poseidon2 != qsag-core CPU");
    }
}
