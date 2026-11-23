// SPDX-License-Identifier: Apache-2.0 OR MIT
#![cfg(feature = "quorum")]
//! Cross-Crate `Poseidon2`, Merkle-Compression & `QS <-> AG` (`Hem` Quorum) Differential Validation
//!
//! Validates:
//! 1. End-to-end compatibility of `qsag-quorum` (`HemCommitteePartitionedQuorum` QS-A,
//!    `HemDynamicShamirQuorum` QS-B with proactive refresh `Π_refresh` and `(2, 3) -> (3, 5)`
//!    quorum-switching `Π_reshare`, and dealerless `HemSpdzSeedQuorum`) with `qsag-agg`
//!    (`ValidatorPublicKey`, `ValidatorSignature`, `verify_individual_signature`, and untrusted
//!    `prove_hem_quintic_128` Quintic `Fp5` WHIR aggregation under `[DKT26]` `< 2^{-128}` QROM), plus negative adversarial
//!    tamper/bitmap/message rejection checks.
//! 2. Exact consistency of the `QS <-> AG` `Hem` Merkle/compression bridge: the canonical weighted
//!    compression `perm(in0 ‖ in1 ‖ tweak)[0..4] + in0 + 2·in1 + 4·tweak` agrees between
//!    `hem_poseidon2_compress12_ff`, `poseidon2_compress12_ff` and the dense-matrix reference, and
//!    `hem_merkle_node_hash == merkle_node_hash`.
//! 3. `qsag_accel::poseidon2::merkle_layer_poseidon2_at_cpu` is that same weighted compression
//!    under an additive `pk_seed + position` tweak, a primitive distinct from the two-permutation
//!    `merkle_node_hash`; the additive tweak makes `(pk_seed, position)` pairs with equal sums
//!    collide, which is pinned here as a property of the construction.
//! 4. The live `VulkanSpirvBackend` permutation (when a GPU is present on Linux) against the
//!    reference. CPU permutation parity of the three crates lives in `simd_fields_goldilocks.rs`.

use proptest::prelude::*;
use qsag_accel::poseidon2::merkle_layer_poseidon2_at_cpu;
use qsag_agg::field::Goldilocks as AggGoldilocks;
use qsag_agg::sig::{DOMAIN_MERKLE_NODE, MerkleNodeAddr, merkle_node_hash};
use qsag_agg::sponge::poseidon2_compress12_ff;
use qsag_agg::{
    AggSigProfile, HemQuinticProfile, SignerBitmap, SigningMode, ValidatorPublicKey,
    ValidatorSignature, prove_hem_quintic_128, verify_hem_quintic_128, verify_individual_signature,
};
use qsag_core::field::goldilocks::Goldilocks as CoreGoldilocks;
use qsag_core::poseidon2_mpc::{
    hem_merkle_node_hash, hem_poseidon2_compress12_ff, verify_hem_jorts_signature,
};
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_external_validation::{GOLDILOCKS_P, poseidon2_ref};
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

    // Aggregate all 3 heterogeneous threshold-quorum validators into a single Quintic Fp5 QROM-128 proof
    let bitmap = SignerBitmap::from_active_indices(3, &[0, 1, 2]).unwrap();
    let mode = SigningMode::SharedMessage(consensus_msg);
    let agg_proof = prove_hem_quintic_128(
        HemQuinticProfile::TurboShake400,
        &agg_pks,
        &bitmap,
        &mode,
        &agg_sigs,
    )
    .unwrap();
    assert!(verify_hem_quintic_128(&agg_pks, &mode, &agg_proof));

    // Adversarial rejection checks: wrong message or swapped committee roster must be rejected
    let wrong_mode = SigningMode::SharedMessage(b"forged-consensus-block");
    assert!(!verify_hem_quintic_128(&agg_pks, &wrong_mode, &agg_proof));
    let swapped_pks = vec![agg_pks[1], agg_pks[0], agg_pks[2]];
    assert!(!verify_hem_quintic_128(&swapped_pks, &mode, &agg_proof));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// The weighted compression agrees between `qsag-core`, `qsag-agg` and the dense-matrix
    /// reference, and the two-permutation Merkle node hash agrees between `qsag-core` and `qsag-agg`.
    #[test]
    fn poseidon2_compression_and_merkle_bridge_equivalence(
        raw_state in any::<[u64; 12]>(),
        layer in 0u32..0xFFFEu32,
        tree_idx in any::<u64>(),
        level in 0u32..32u32,
        node_idx in 0u32..65536u32,
    ) {
        let [left, right, seed]: [[u64; 4]; 3] =
            core::array::from_fn(|b| core::array::from_fn(|i| raw_state[4 * b + i]));
        let [c_left, c_right, c_seed] =
            [left, right, seed].map(|b| b.map(CoreGoldilocks::from_u64_reduced));
        let [a_left, a_right, a_seed] =
            [left, right, seed].map(|b| b.map(AggGoldilocks::from_u64_reduced));

        let expected = poseidon2_ref::compress(left, right, seed);
        let hem_comp = hem_poseidon2_compress12_ff(c_left, c_right, c_seed).map(|x| x.to_canonical_u64());
        let agg_comp = poseidon2_compress12_ff(a_left, a_right, a_seed).map(|x| x.to_canonical_u64());
        prop_assert_eq!(hem_comp, expected);
        prop_assert_eq!(agg_comp, expected);

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
fn accel_merkle_layer_is_the_weighted_compression_and_gpu_matches_reference() {
    const MERKLE_DOMAIN_IV: u64 = 0x4D52_4B4C_5F50_3231;
    const NODE_TWEAK_IV: u64 = 0x4C52_5F4E_4F44_4531;
    let add = |a: u64, b: u64| ((a as u128 + b as u128) % GOLDILOCKS_P as u128) as u64;

    // 1. One accelerator Merkle parent is the weighted compression of its children under the
    //    additive tweak `pk_seed + (domain + layer·2^32, layer, node IV + parent index, "POS2_GL1")`.
    let left = [11u64, 22, 33, 44];
    let right = [55u64, 66, 77, 88];
    let pk_seed = [100u64, 200, 300, 400];
    let (layer, parent_idx) = (3u32, 7u64);
    let tweak = |seed: [u64; 4], idx: u64| {
        [
            add(seed[0], MERKLE_DOMAIN_IV + ((layer as u64) << 32)),
            add(seed[1], layer as u64),
            add(seed[2], NODE_TWEAK_IV + idx),
            add(seed[3], poseidon2_ref::CONST_IV),
        ]
    };
    let mut accel_parent = [[0u64; 4]; 1];
    merkle_layer_poseidon2_at_cpu(&[left, right], &pk_seed, layer, parent_idx, &mut accel_parent)
        .unwrap();
    assert_eq!(
        accel_parent[0],
        poseidon2_ref::compress(left, right, tweak(pk_seed, parent_idx))
    );

    // A batch layer numbers its parents from `start_parent_idx`.
    let children = [left, right, right, left, [1, 2, 3, 4], [5, 6, 7, 8]];
    let mut batch = [[0u64; 4]; 3];
    merkle_layer_poseidon2_at_cpu(&children, &pk_seed, layer, parent_idx, &mut batch).unwrap();
    for (k, parent) in batch.iter().enumerate() {
        assert_eq!(
            *parent,
            poseidon2_ref::compress(
                children[2 * k],
                children[2 * k + 1],
                tweak(pk_seed, parent_idx + k as u64)
            )
        );
    }

    // 2. It is a different primitive from the two-permutation sponge `merkle_node_hash`.
    let agg_parent = merkle_node_hash(
        MERKLE_DOMAIN_IV,
        pk_seed.map(AggGoldilocks::from_u64_reduced),
        MerkleNodeAddr {
            layer: 0,
            tree_idx: 0,
            level: layer,
            node_idx: parent_idx as u32,
        },
        left.map(AggGoldilocks::from_u64_reduced),
        right.map(AggGoldilocks::from_u64_reduced),
    )
    .map(|x| x.to_canonical_u64());
    assert_ne!(accel_parent[0], agg_parent);

    // 3. The tweak is a sum, so `(pk_seed[2] + 1, parent_idx - 1)` has the same tweak as
    //    `(pk_seed[2], parent_idx)` and the two parents are equal. Positions are separated only
    //    under one fixed `pk_seed`.
    let shifted_seed = [pk_seed[0], pk_seed[1], pk_seed[2] + 1, pk_seed[3]];
    assert_eq!(tweak(shifted_seed, parent_idx - 1), tweak(pk_seed, parent_idx));
    let mut shifted_parent = [[0u64; 4]; 1];
    merkle_layer_poseidon2_at_cpu(
        &[left, right],
        &shifted_seed,
        layer,
        parent_idx - 1,
        &mut shifted_parent,
    )
    .unwrap();
    assert_eq!(shifted_parent, accel_parent);

    // 4. With a Vulkan GPU on a Linux host, the hardware permutation matches the reference.
    #[cfg(target_os = "linux")]
    if let Ok(gpu) = qsag_accel::VulkanSpirvBackend::try_new() {
        use qsag_accel::AcceleratorBackend;
        let mut states: Vec<[u64; 12]> = (0..64)
            .map(|i| {
                core::array::from_fn(|lane| {
                    ((i as u64) * 0x9E37_79B9_7F4A_7C15 + (lane as u64) * 17) % GOLDILOCKS_P
                })
            })
            .collect();
        let expected: Vec<[u64; 12]> = states.iter().map(poseidon2_ref::perm12).collect();
        gpu.batch_poseidon2_perm12(&mut states);
        assert_eq!(states, expected, "Vulkan GPU Poseidon2 != canonical reference");
    }
}
