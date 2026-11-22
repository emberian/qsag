// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder, canonical roundtrip, and adversarial verifier fuzzer
//! across the `zk-Hem v2`, public `Hem`, recursive shard/WHIR merge, `Corduroy-Poseidon2`, and
//! height-20 `Jorts-Poseidon2` wire codecs in `qsag-agg`:
//!
//! 1. `zk_hem::v2::protocol::ZkHemV2Proof::from_bytes` + `v2::protocol::verify`
//! 2. `zk_hem::protocol::PublicHemProof::from_bytes` + `protocol::verify_public`
//! 3. `zk_hem::blind_vc`: `ZkHemV2Proof::from_bytes` + `verify_presentation`
//! 4. `zk_hem::multisig`: `ZkHemV2Proof::from_bytes` + `MultisigRelation::verify`
//! 5. `zk_hem::capability::ZkCapabilityBatchProof::from_bytes` (`QSAGCAP1`) + `CapabilityRelation::verify`
//! 6. `zk_hem::recursive_whir::FixedPathWhirProof::from_bytes` (`QSAGFWP1`) + `verify_fixed_path`
//!    and `SuccinctChildWhirMerge::from_bytes` (`QSAGFWP1`) + `verify_succinct_children_whir_merge`
//! 7. `zk_hem::full_shard::RecursiveShardProof::from_bytes` (`QSAGRSP1`) + `verify_recursive_shard`
//! 8. `sig::ValidatorSignature::from_bytes_canonical` for `CorduroyPoseidon2` (`76,896` B) and
//!    `JortsPoseidon2H20` (`4,776` B) + `verify_individual_signature`.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::field::{Goldilocks, GoldilocksExt4};
use qsag_agg::pcs::WhirSecurityRegime;
use qsag_agg::zk_hem::blind_vc::{
    BlindVcStatement, BlindVcWitness, VC_ACCUMULATOR_DEPTH, verify_presentation,
};
use qsag_agg::zk_hem::capability::{
    BearerCapability, CAPABILITY_WIRE_MAGIC, CapCaveat, CapabilityBatchStatement,
    CapabilityIssuerDirectory, CapabilityParams, CapabilityPresentationInput, CapabilityRelation,
    CapabilityRequest, SortedRevocationTree, ZkCapabilityBatchProof,
};
use qsag_agg::zk_hem::full_shard::{
    FullShardParams, RECURSIVE_SHARD_WIRE_MAGIC, RecursiveShardProof, RecursiveShardStatement,
    verify_recursive_shard,
};
use qsag_agg::zk_hem::multisig::{MultisigParams, MultisigRelation};
use qsag_agg::zk_hem::protocol::{self, PublicHemProof};
use qsag_agg::zk_hem::recursive_whir::{
    ChildWhirMergeRelation, ChildWhirStatement, FixedPathWhirParams, FixedPathWhirProof,
    SuccinctChildWhirMerge, verify_fixed_path, verify_succinct_children_whir_merge,
};
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape, sponge12};
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{self as v2, ZkHemV2Proof};
use qsag_agg::{
    AggSigProfile, SignerBitmap, ValidatorPublicKey, ValidatorSignature,
    verify_individual_signature,
};

struct FuzzFixtures {
    generic_public_shape: Shape,
    generic_v2_shape: Shape,
    blind_vc_stmt: BlindVcStatement,
    blind_vc_shape: Shape,
    multisig_rel: MultisigRelation,
    cap_rel: CapabilityRelation,
    cap_stmt: CapabilityBatchStatement,
    cap_seed: Vec<u8>,
    fp_params: FixedPathWhirParams,
    fp_stmt: ChildWhirStatement,
    child_whir_rel: ChildWhirMergeRelation,
    fs_params: FullShardParams,
    fs_shard_stmt: RecursiveShardStatement,
    corduroy_pk: ValidatorPublicKey,
    jorts20_pk: ValidatorPublicKey,
}

const CAP_SEED_PROFILE: Profile = Profile::TurboShakeJohnson400;
const FIXED_PATH_NUM_VARS: usize = 6;

fn fixtures() -> &'static FuzzFixtures {
    static FX: OnceLock<FuzzFixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let f = Goldilocks::from_u64_reduced;

        let build_generic = || {
            let mut cs = ConstraintSystem::new();
            let pub_in: Lc = cs.public_input(f(7)).into();
            let sec_var: Lc = cs.alloc(f(1)).into();
            cs.enforce_boolean(&sec_var);
            let st = sponge12(&mut cs, &[pub_in, sec_var]);
            let _ = cs.mul(&st[0], &st[1]);
            cs
        };
        let (generic_public_shape, _) = build_generic().finish();
        let (generic_v2_shape, _) = build_generic().finish_v2();

        let vc_witness = BlindVcWitness {
            attrs: vec![f(10), f(20), f(30), f(40)],
            holder_blind: [f(1), f(2), f(3), f(4)],
            presentation_blind: [f(5), f(6), f(7), f(8)],
            path_bits: [false; VC_ACCUMULATOR_DEPTH],
            siblings: [[f(9); 6]; VC_ACCUMULATOR_DEPTH],
        };
        let blind_vc_stmt = BlindVcStatement::derive(&vc_witness, 1, 0xCAFE, [f(11); 4], &[0]);
        let blind_vc_shape = blind_vc_stmt.shape().expect("valid BlindVc shape");

        let multisig_rel = MultisigRelation::new(MultisigParams {
            capacity: 1,
            depth: 1,
        })
        .expect("valid MultisigRelation");

        let cap_rel = CapabilityRelation::new(CapabilityParams {
            batch_size: 1,
            max_hops: 2,
            issuer_depth: 2,
            revocation_depth: 2,
        })
        .expect("valid CapabilityRelation");
        let mut cap = BearerCapability::issue(&[f(7); 4], [f(1); 4], [f(0x33); 4]).unwrap();
        cap.attenuate(CapCaveat::Actions(1)).unwrap();
        let directory = CapabilityIssuerDirectory::new(2, &[cap.mint_leaf()]).unwrap();
        let revocations = SortedRevocationTree::new(2, 1, &[]).unwrap();
        let non_membership = revocations.prove_non_membership(cap.token_id()).unwrap();
        let mut inputs = [CapabilityPresentationInput {
            capability: cap,
            issuer_index: 0,
            issuer_siblings: directory.opening(0).unwrap(),
            non_membership,
        }];
        let cap_stmt = CapabilityBatchStatement::prepare_sorted(
            directory.root(),
            revocations.root(),
            1,
            CapabilityRequest {
                audience: [f(0x33); 4],
                resource: [f(0x44); 4],
                actions: 1,
                amount: 100,
                now: 1_700_000_000,
            },
            &mut inputs,
            b"fuzz-cap",
        )
        .unwrap();
        let cap_seed = cap_rel
            .prove(
                &cap_stmt,
                &inputs,
                b"fuzz-cap",
                CAP_SEED_PROFILE,
                &[0x42; 32],
            )
            .expect("capability seed proof")
            .to_bytes();
        let seeded = ZkCapabilityBatchProof::from_bytes(&cap_seed, &cap_rel, CAP_SEED_PROFILE)
            .expect("canonical capability seed");
        assert!(cap_rel.verify(&cap_stmt, b"fuzz-cap", CAP_SEED_PROFILE, &seeded));

        let fp_regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let fp_params =
            FixedPathWhirParams::new(fp_regime, FIXED_PATH_NUM_VARS).expect("FixedPathWhirParams");
        let fp_stmt = ChildWhirStatement {
            shard_header: [0xAB; 32],
            commitment: [f(3); 4],
            point: vec![GoldilocksExt4::ZERO; FIXED_PATH_NUM_VARS],
            value: GoldilocksExt4::ZERO,
        };
        let child_whir_rel =
            ChildWhirMergeRelation::with_children(fp_params.clone(), 1).expect("ChildWhirMerge");

        let fs_params = FullShardParams::new(fp_regime, 2).expect("FullShardParams");
        let jorts_pk0 = ValidatorPublicKey {
            profile: AggSigProfile::JortsPoseidon2,
            pk_seed: [f(0x101); 4],
            pk_root: [f(0x202); 4],
        };
        let jorts_pk1 = ValidatorPublicKey {
            profile: AggSigProfile::JortsPoseidon2,
            pk_seed: [f(0x303); 4],
            pk_root: [f(0x404); 4],
        };
        let fs_shard_stmt = RecursiveShardStatement {
            keys: vec![jorts_pk0, jorts_pk1],
            bitmap: SignerBitmap::from_active_indices(2, &[0]).expect("bitmap"),
            message: [0x5A; 32],
        };

        let corduroy_pk = ValidatorPublicKey {
            profile: AggSigProfile::CorduroyPoseidon2,
            pk_seed: [f(0x77); 4],
            pk_root: [f(0x88); 4],
        };
        let jorts20_pk = ValidatorPublicKey {
            profile: AggSigProfile::JortsPoseidon2H20,
            pk_seed: [f(0x99); 4],
            pk_root: [f(0xAA); 4],
        };

        FuzzFixtures {
            generic_public_shape,
            generic_v2_shape,
            blind_vc_stmt,
            blind_vc_shape,
            multisig_rel,
            cap_rel,
            cap_stmt,
            cap_seed,
            fp_params,
            fp_stmt,
            child_whir_rel,
            fs_params,
            fs_shard_stmt,
            corduroy_pk,
            jorts20_pk,
        }
    })
}

fn with_magic(magic: &[u8; 8], data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + data.len());
    out.extend_from_slice(magic);
    out.extend_from_slice(data);
    out
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();
    let f = Goldilocks::from_u64_reduced;
    let zk_profile = if data.first().copied().unwrap_or(0) & 1 == 0 {
        Profile::TurboShakeJohnson400
    } else {
        Profile::CshakeJohnson400
    };
    let pub_regime = if data.first().copied().unwrap_or(0) & 1 == 0 {
        WhirSecurityRegime::BciksJohnsonQrom128
    } else {
        WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128
    };
    let rec_regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;

    // 1. Generic `ZkHemV2Proof` & `PublicHemProof` decoders + canonical roundtrip + verifiers
    if let Some(proof) = ZkHemV2Proof::from_bytes(data, &fx.generic_v2_shape) {
        assert_eq!(proof.to_bytes(), data);
        let _ = v2::verify(
            &fx.generic_v2_shape,
            &[f(7)],
            b"fuzz-generic",
            zk_profile,
            &proof,
        );
    }
    if let Some(proof) = PublicHemProof::from_bytes(data, &fx.generic_public_shape, pub_regime) {
        assert_eq!(proof.to_bytes(), data);
        let _ = protocol::verify_public(
            &fx.generic_public_shape,
            &[f(7)],
            b"fuzz-public",
            pub_regime,
            &proof,
        );
    }

    // 2. `BlindVC` selective-disclosure `ZkHemV2Proof` decoder + verifier
    if let Some(proof) = ZkHemV2Proof::from_bytes(data, &fx.blind_vc_shape) {
        assert_eq!(proof.to_bytes(), data);
        let _ = verify_presentation(&fx.blind_vc_stmt, b"fuzz-bvc", zk_profile, &proof);
    }

    // 3. `Multisig` private-policy `ZkHemV2Proof` decoder + verifier
    if let Some(proof) = ZkHemV2Proof::from_bytes(data, fx.multisig_rel.shape()) {
        assert_eq!(proof.to_bytes(), data);
        let _ = fx
            .multisig_rel
            .verify(&[f(1); 4], &[0x42; 32], zk_profile, &proof);
    }

    // 4. `Capability` batched capability + `SortedRevocationTree` (`QSAGCAP1`) decoder + verifier
    for candidate in [data.to_vec(), with_magic(CAPABILITY_WIRE_MAGIC, data)] {
        if let Some(proof) =
            ZkCapabilityBatchProof::from_bytes(&candidate, &fx.cap_rel, zk_profile)
        {
            assert_eq!(proof.to_bytes(), candidate);
            let _ = fx
                .cap_rel
                .verify(&fx.cap_stmt, b"fuzz-cap", zk_profile, &proof);
        }
    }

    if let Some(edits) = data.strip_prefix(&[0xca, 0x50]) {
        let mut candidate = fx.cap_seed.clone();
        for edit in edits.as_chunks::<5>().0 {
            let offset = u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize;
            let index = offset % candidate.len();
            candidate[index] ^= edit[4];
        }
        if let Some(proof) =
            ZkCapabilityBatchProof::from_bytes(&candidate, &fx.cap_rel, CAP_SEED_PROFILE)
        {
            assert_eq!(proof.to_bytes(), candidate);
            let verified = fx
                .cap_rel
                .verify(&fx.cap_stmt, b"fuzz-cap", CAP_SEED_PROFILE, &proof);
            if candidate == fx.cap_seed {
                assert!(verified);
            }
        }
    }

    // 5. `FixedPathWhirProof` & `SuccinctChildWhirMerge` (`QSAGFWP1`) decoders + verifiers
    for candidate in [data.to_vec(), with_magic(b"QSAGFWP1", data)] {
        if let Some(proof) = FixedPathWhirProof::from_bytes(&candidate, &fx.fp_params) {
            assert_eq!(proof.to_bytes(), candidate);
            let _ = verify_fixed_path(&fx.fp_params, &fx.fp_stmt, &proof);
        }
        if let Some(merge) =
            SuccinctChildWhirMerge::from_bytes(&candidate, &fx.child_whir_rel, rec_regime)
        {
            assert_eq!(merge.to_bytes(), candidate);
            let _ = verify_succinct_children_whir_merge(
                &fx.child_whir_rel,
                std::slice::from_ref(&fx.fp_stmt),
                rec_regime,
                &merge,
            );
        }
    }

    // 6. `RecursiveShardProof` (`QSAGRSP1`) decoder + `verify_recursive_shard`
    for candidate in [data.to_vec(), with_magic(RECURSIVE_SHARD_WIRE_MAGIC, data)] {
        if let Some(proof) = RecursiveShardProof::from_bytes(&fx.fs_params, &candidate) {
            assert_eq!(proof.to_bytes(), candidate);
            let _ = verify_recursive_shard(&fx.fs_params, &fx.fs_shard_stmt, &proof);
        }
    }

    // 7. `CorduroyPoseidon2` (`76,896` B) & height-20 `JortsPoseidon2H20` (`4,776` B) codecs + verifiers
    if let Ok(sig) =
        ValidatorSignature::from_bytes_canonical(AggSigProfile::CorduroyPoseidon2, data)
    {
        assert_eq!(sig.to_bytes(), data);
        let _ = verify_individual_signature(&fx.corduroy_pk, b"fuzz-corduroy", &sig);
    }
    if let Ok(sig) =
        ValidatorSignature::from_bytes_canonical(AggSigProfile::JortsPoseidon2H20, data)
    {
        assert_eq!(sig.to_bytes(), data);
        let _ = verify_individual_signature(&fx.jorts20_pk, b"fuzz-jorts20", &sig);
    }
});
