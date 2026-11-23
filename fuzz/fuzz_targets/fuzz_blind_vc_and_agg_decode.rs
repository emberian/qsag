// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided untrusted wire-decoder & verifier fuzzer for Quintic `Fp5` zero-knowledge
//! credentials, capabilities, multisignatures, and regional hierarchy proofs:
//! 1. `zk_hem::blind_vc` (`ZkHemV2Proof` `QSAGZKH2`),
//! 2. `zk_hem::multisig` (`ZkHemV2Proof` `QSAGZKH2`),
//! 3. `zk_hem::capability::ZkCapabilityBatchProof` (`QSAGCAP1`), and
//! 4. `HierarchicalHemAggregate` (`QSAGHEM\x04`).

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::zk_hem::blind_vc::{
    BlindVcStatement, BlindVcWitness, prove_presentation, verify_presentation,
};
use qsag_agg::zk_hem::capability::{
    CAPABILITY_WIRE_MAGIC, CapabilityParams, CapabilityRelation, ZkCapabilityBatchProof,
};
use qsag_agg::zk_hem::multisig::{MultisigParams, MultisigRelation, Policy};
use qsag_agg::zk_hem::relation::Shape;
use qsag_agg::zk_hem::v2::{params::Profile, protocol::ZkHemV2Proof};
use qsag_agg::{
    AggSigProfile, Goldilocks, HIERARCHICAL_HEM_WIRE_MAGIC, HemQuinticProfile,
    HierarchicalHemAggregate, PreparedPolicyRegistry, ShardHemPolicy, ValidatorKeypair,
    verify_hierarchical_hem_prepared,
};

struct ZkFixtures {
    vc_stmt: BlindVcStatement,
    vc_shape: Shape,
    vc_wire: Vec<u8>,
    ms_rel: MultisigRelation,
    ms_addr: [Goldilocks; 4],
    cap_rel: CapabilityRelation,
    prepared: PreparedPolicyRegistry,
}

fn fixtures() -> &'static ZkFixtures {
    static FX: OnceLock<ZkFixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let gl = Goldilocks::from_u64_reduced;
        let vc_wit = BlindVcWitness {
            attrs: (0..4).map(|i| gl(100 + i)).collect(),
            holder_blind: [gl(11), gl(12), gl(13), gl(14)],
            presentation_blind: [gl(21), gl(22), gl(23), gl(24)],
            path_bits: core::array::from_fn(|i| i % 2 == 1),
            siblings: core::array::from_fn(|l| {
                core::array::from_fn(|j| gl((l * 6 + j + 1) as u64))
            }),
        };
        let vc_stmt = BlindVcStatement::derive(&vc_wit, 7, 99, [gl(1), gl(2), gl(3), gl(4)], &[0]);
        let vc_shape = vc_stmt.shape().unwrap();
        let vc_wire = prove_presentation(
            &vc_stmt,
            &vc_wit,
            b"fuzz-vc-ctx",
            Profile::TurboShakeJohnson400,
            &[0x55; 32],
        )
        .unwrap()
        .to_bytes();

        let kp0 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[0x61; 32], 0);
        let kp1 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[0x62; 32], 1);
        let ms_params = MultisigParams {
            capacity: 2,
            depth: 2,
        };
        let ms_rel = MultisigRelation::new(ms_params).unwrap();
        let ms_policy = Policy::new(vec![kp0.pk, kp1.pk], 1, 2).unwrap();
        let ms_addr = ms_policy.address();
        let cap_rel = CapabilityRelation::new(CapabilityParams {
            batch_size: 1,
            max_hops: 2,
            issuer_depth: 4,
            revocation_depth: 4,
        })
        .unwrap();
        let prepared = PreparedPolicyRegistry::new(vec![ShardHemPolicy {
            shard_id: 1,
            custodian_cluster: [0x71; 32],
            quorum_keys: vec![kp0.pk, kp1.pk],
            minimum_quorums: 1,
        }])
        .unwrap();

        ZkFixtures {
            vc_stmt,
            vc_shape,
            vc_wire,
            ms_rel,
            ms_addr,
            cap_rel,
            prepared,
        }
    })
}

fn with_prefix(prefix: &[u8], body: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(prefix.len() + body.len());
    v.extend_from_slice(prefix);
    v.extend_from_slice(body);
    v
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();
    let Some((&sel, rest)) = data.split_first() else {
        return;
    };

    // 1. `ZkHemV2Proof` (`QSAGZKH2`) BlindVC presentation decoder + verifier + seeded mutation
    for cand in [rest.to_vec(), with_prefix(b"QSAGZKH2", rest)] {
        if let Some(proof) = ZkHemV2Proof::from_bytes(&cand, &fx.vc_shape) {
            assert_eq!(proof.to_bytes(), cand);
            let _ = verify_presentation(
                &fx.vc_stmt,
                b"fuzz-vc-ctx",
                Profile::TurboShakeJohnson400,
                &proof,
            );
        }
    }
    if sel & 1 == 0 {
        let mut mutated = fx.vc_wire.clone();
        for edit in rest.chunks_exact(5).take(6) {
            let idx = (u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize)
                % mutated.len();
            mutated[idx] ^= edit[4];
        }
        if mutated != fx.vc_wire
            && let Some(dec) = ZkHemV2Proof::from_bytes(&mutated, &fx.vc_shape)
        {
            assert_eq!(dec.to_bytes(), mutated);
            assert!(!verify_presentation(
                &fx.vc_stmt,
                b"fuzz-vc-ctx",
                Profile::TurboShakeJohnson400,
                &dec,
            ));
        }
    }

    // 2. `MultisigRelation` & `ZkCapabilityBatchProof` (`QSAGCAP1`) canonical decoders
    let ms_msg = *b"fuzz-multisig-32-byte-message-01";
    for cand in [rest.to_vec(), with_prefix(b"QSAGZKH2", rest)] {
        if let Some(proof) = ZkHemV2Proof::from_bytes(&cand, fx.ms_rel.shape()) {
            assert_eq!(proof.to_bytes(), cand);
            let _ = fx.ms_rel.verify(
                &fx.ms_addr,
                &ms_msg,
                Profile::TurboShakeJohnson400,
                &proof,
            );
        }
    }
    for cand in [rest.to_vec(), with_prefix(CAPABILITY_WIRE_MAGIC, rest)] {
        if let Some(proof) = ZkCapabilityBatchProof::from_bytes(
            &cand,
            &fx.cap_rel,
            Profile::TurboShakeJohnson400,
        ) {
            assert_eq!(proof.to_bytes(), cand);
        }
    }

    // 3. `HierarchicalHemAggregate` (`QSAGHEM\x04`) canonical decoder
    for cand in [
        rest.to_vec(),
        with_prefix(HIERARCHICAL_HEM_WIRE_MAGIC, rest),
    ] {
        if let Ok(agg) = HierarchicalHemAggregate::from_bytes_canonical(&cand) {
            assert_eq!(agg.to_bytes(), cand);
            let _ = verify_hierarchical_hem_prepared(
                &fx.prepared,
                1,
                b"fuzz-hier",
                1,
                HemQuinticProfile::TurboShake400,
                &agg,
            );
        }
    }
});
