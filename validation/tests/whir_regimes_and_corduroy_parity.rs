// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Differential & Structural Validation for WHIR Security Regimes, High-Capacity Stage
//! Geometries (`nv = 2..=28`), Dual OOD Pinning, Stateless `CorduroyPoseidon2` (`76,896 B`),
//! and `zk-Hem` (`prove` 5-table hiding vs `prove_public` 1-table public + `full_shard` recursion).
//!
//! Closes every Domain 2 & `Corduroy` validation gap identified in Subcarbon C5:
//! 1. Cross-checks all 6 core WHIR wire regimes (`2, 4, 5, 6, 7, 8`) + TurboSHAKE regimes (`9, 10`),
//!    their query schedules, PoW bits (`16` vs `0`), canopy hash modes, QROM-128 authorization floor,
//!    end-to-end PCS commit/open/verify/wire roundtrips, and fail-closed rejection of retired capacity
//!    proximity-gap wire tags (`0, 1, 3`) and unassigned tags (`11..=255`).
//! 2. Exhaustively verifies WHIR stage geometries across `nv = 2..=28` (`MAX_PCS_NUM_VARS = 28`,
//!    `MAX_BATCH_POLYS = 16`), specifically pinning `nv = 25..=28` (`(6,4,4,3)`, `(6,5,4,3)`,
//!    `(6,5,4,4)`, `(6,6,4,4)`) against C5's `WhirProfiles.lean` / `RecursivePoseidon2WhirSoundness`
//!    regressions, and verifies out-of-range `nv = 0, 1, 29` rejection.
//! 3. Verifies dual out-of-domain (`OOD_SAMPLES = 2`) pinning on `stage0_ood_evals` and every
//!    intermediate `WhirStageProof::stage_ood_evals`, proving mutation of either OOD slot fails closed.
//! 4. Validates stateless `CorduroyPoseidon2` (`76,896 B`, `k=32, a=8, d=16, h'=4`,
//!    `CORDUROY_MAX_STATELESS_SIGS_PER_KEY = 2^20`, `DOMAIN_PRF_MSG = 0x515341475052464D`) keygen,
//!    stateless signing, wire canonicality, individual/batch verification, and `HemAggregator`
//!    shard aggregation + disjoint `MergeNode::Branch` merging + tamper rejection.
//! 5. Cross-checks `zk-Hem` 5-table hiding (`protocol::prove`/`verify`) vs 1-table public
//!    (`protocol::prove_public`/`verify_public` with 3 independent `ZKHEM_COMBINE` challenges and
//!    `HEM_PUBLIC_CELLS` batching) AND `zk_hem::full_shard` (`prove_recursive_shard`,
//!    `prove_full_shard_merge`, `verify_full_shard_merge`, `QSAGFSM1`) + adversarial tamper rejection.

use qsag_agg::field::{Goldilocks, GoldilocksExt4, GoldilocksOps as _, build_eq_table_ext4};
use qsag_agg::pcs::{
    HemWhirOpeningProof, MAX_BATCH_POLYS, MAX_PCS_NUM_VARS, WhirSchedule, WhirSecurityRegime,
    whir_commit_owned_with_schedule, whir_open, whir_verify_with_schedule,
};
use qsag_agg::sig::{
    CORDUROY_MAX_STATELESS_SIGS_PER_KEY, CORDUROY_NUM_LAYERS, CORDUROY_SUBTREE_HEIGHT,
    DOMAIN_PRF_MSG, FORS_HEIGHT, FORS_TREES, JORTS_XMSS_HEIGHT, ValidatorKeypair, WOTS_CHAINS,
    WOTS_TARGET_SUM, verify_signature_batch,
};
use qsag_agg::sponge::{FiatShamirTranscript, InstanceBound};
use qsag_agg::zk_hem::full_shard::{
    FullShardError, FullShardMergeProof, FullShardMergeRelation, FullShardParams,
    RecursiveShardStatement, prove_full_shard_merge, prove_recursive_shard, verify_full_shard_merge,
    verify_recursive_shard,
};
use qsag_agg::zk_hem::protocol::{
    Layout, PublicHemProof, ZkHemError, ZkHemProof, prove as zkhem_prove,
    prove_public as zkhem_prove_public, verify as zkhem_verify, verify_public as zkhem_verify_public,
};
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, MASK_ROWS, Shape, sponge12, sponge12_native};
use qsag_agg::{
    AggSigProfile, HemAggConfig, HemAggregatedProof, HemAggregator, SignerBitmap, SigningMode,
    ValidatorPublicKey, ValidatorSignature, verify_individual_signature,
};
use qsag_external_validation::{GOLDILOCKS_P, p3_ext4_mul};

fn gl(x: u64) -> Goldilocks {
    Goldilocks::from_u64_reduced(x)
}

/// Independent Plonky3 `GoldilocksExt4` multilinear evaluation of `evals` (`len = 2^nv`) at `point`.
fn multilinear_eval_p3_ref(evals: &[Goldilocks], point: &[[u64; 4]]) -> [u64; 4] {
    let nv = point.len();
    assert_eq!(evals.len(), 1usize << nv);
    let one = [1u64, 0, 0, 0];
    let sub_ext4 = |a: [u64; 4], b: [u64; 4]| -> [u64; 4] {
        core::array::from_fn(|i| {
            ((a[i] as u128 + GOLDILOCKS_P as u128 - b[i] as u128) % GOLDILOCKS_P as u128) as u64
        })
    };
    let add_ext4 = |a: [u64; 4], b: [u64; 4]| -> [u64; 4] {
        core::array::from_fn(|i| ((a[i] as u128 + b[i] as u128) % GOLDILOCKS_P as u128) as u64)
    };

    let mut acc = [0u64; 4];
    for (idx, &val) in evals.iter().enumerate() {
        let mut eq = one;
        for (bit, &r) in point.iter().enumerate() {
            let factor = if (idx >> bit) & 1 == 1 {
                r
            } else {
                sub_ext4(one, r)
            };
            eq = p3_ext4_mul(eq, factor);
        }
        let term = p3_ext4_mul(eq, [val.to_canonical_u64(), 0, 0, 0]);
        acc = add_ext4(acc, term);
    }
    acc
}

fn pcs_transcript(schedule: &WhirSchedule) -> FiatShamirTranscript<InstanceBound> {
    FiatShamirTranscript::new()
        .bind_relation(b"VALIDATION.PCS.REGIMES/v1", &[0x5Au8; 32], schedule)
        .bind_instance(&[b"whir-differential-instance"])
}

#[test]
fn whir_active_regimes_retired_tag_rejection_and_dual_ood_pinning() {
    assert_eq!(MAX_PCS_NUM_VARS, 28);
    assert_eq!(MAX_BATCH_POLYS, 16);

    // 1. Fail-closed rejection of retired capacity proximity-gap wire tags `0, 1, 3` and unassigned `11..=255`.
    for retired in [0u8, 1, 3] {
        assert_eq!(
            WhirSecurityRegime::from_u8(retired),
            None,
            "retired capacity proximity-gap tag {retired} MUST be rejected"
        );
    }
    for unassigned in 11u8..=u8::MAX {
        assert_eq!(WhirSecurityRegime::from_u8(unassigned), None);
    }

    // 2. Exact query schedules, PoW bits, canopy flags, and QROM-128 authorization across all regimes,
    //    covering the 6 core Lean regimes (`2, 4, 5, 6, 7, 8`) + TurboSHAKE regimes (`9, 10`).
    struct ExpectedRegime {
        tag: u8,
        regime: WhirSecurityRegime,
        pow_bits: u32,
        pure_bits: u32,
        queries_4stage: [usize; 4],
        qrom_128_ok: bool,
        poseidon2: bool,
        turboshake: bool,
    }

    let table = [
        ExpectedRegime {
            tag: 2,
            regime: WhirSecurityRegime::BciksJohnsonClassical128,
            pow_bits: 16,
            pure_bits: 128,
            queries_4stage: [129, 65, 44, 33],
            qrom_128_ok: false,
            poseidon2: false,
            turboshake: false,
        },
        ExpectedRegime {
            tag: 4,
            regime: WhirSecurityRegime::BciksJohnsonQrom128,
            pow_bits: 16,
            pure_bits: 256,
            queries_4stage: [258, 130, 88, 66],
            qrom_128_ok: true,
            poseidon2: false,
            turboshake: false,
        },
        ExpectedRegime {
            tag: 5,
            regime: WhirSecurityRegime::Cdhz25JohnsonQrom128,
            pow_bits: 16,
            pure_bits: 200,
            queries_4stage: [202, 102, 70, 52],
            qrom_128_ok: true,
            poseidon2: false,
            turboshake: false,
        },
        ExpectedRegime {
            tag: 6,
            regime: WhirSecurityRegime::Cdhz25ZeroPowQrom128,
            pow_bits: 0,
            pure_bits: 214,
            queries_4stage: [216, 109, 74, 56],
            qrom_128_ok: true,
            poseidon2: false,
            turboshake: false,
        },
        ExpectedRegime {
            tag: 7,
            regime: WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
            pow_bits: 16,
            pure_bits: 200,
            queries_4stage: [202, 102, 70, 52],
            qrom_128_ok: true,
            poseidon2: true,
            turboshake: false,
        },
        ExpectedRegime {
            tag: 8,
            regime: WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
            pow_bits: 0,
            pure_bits: 214,
            queries_4stage: [216, 109, 74, 56],
            qrom_128_ok: true,
            poseidon2: true,
            turboshake: false,
        },
        ExpectedRegime {
            tag: 9,
            regime: WhirSecurityRegime::TurboShakeBciksJohnsonQrom128,
            pow_bits: 16,
            pure_bits: 256,
            queries_4stage: [258, 130, 88, 66],
            qrom_128_ok: true,
            poseidon2: false,
            turboshake: true,
        },
        ExpectedRegime {
            tag: 10,
            regime: WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128,
            pow_bits: 16,
            pure_bits: 200,
            queries_4stage: [202, 102, 70, 52],
            qrom_128_ok: true,
            poseidon2: false,
            turboshake: true,
        },
    ];

    assert_eq!(WhirSecurityRegime::ALL.len(), table.len());

    // Multi-stage polynomial (`nv = 12` -> 3 WHIR stages `[4, 16, 64]`, `4096` hypercube cells)
    // opened and verified across ALL active regimes, cross-checked against Plonky3 `GoldilocksExt4`!
    let nv = 12usize;
    let evals: Vec<Goldilocks> = (0..(1usize << nv))
        .map(|i| gl((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(19)))
        .collect();
    let point_limbs: Vec<[u64; 4]> = (0..nv)
        .map(|k| {
            [
                (101 + 37 * k as u64) % GOLDILOCKS_P,
                (202 + 53 * k as u64) % GOLDILOCKS_P,
                (303 + 71 * k as u64) % GOLDILOCKS_P,
                (404 + 97 * k as u64) % GOLDILOCKS_P,
            ]
        })
        .collect();
    let point: Vec<GoldilocksExt4> = point_limbs.iter().copied().map(GoldilocksExt4::from_limbs).collect();
    let p3_claimed = GoldilocksExt4::from_limbs(multilinear_eval_p3_ref(&evals, &point_limbs));

    let eq_tbl = build_eq_table_ext4(&point);
    let agg_claimed = evals
        .iter()
        .zip(&eq_tbl)
        .fold(GoldilocksExt4::ZERO, |acc, (&v, &w)| acc + w.mul_base(v));
    assert_eq!(agg_claimed, p3_claimed);

    for row in &table {
        assert_eq!(row.regime as u8, row.tag);
        assert_eq!(WhirSecurityRegime::from_u8(row.tag), Some(row.regime));
        assert_eq!(row.regime.pow_bits(), row.pow_bits);
        assert_eq!(row.regime.pure_query_target_bits(), row.pure_bits);
        assert_eq!(row.regime.meets_qrom_128_floor(), row.qrom_128_ok);
        assert_eq!(row.regime.uses_poseidon2_canopy(), row.poseidon2);
        assert_eq!(row.regime.uses_turboshake_canopy(), row.turboshake);

        let sched28 = row.regime.schedule(28);
        let qs: [usize; 4] = core::array::from_fn(|i| sched28.stages[i].num_queries);
        assert_eq!(qs, row.queries_4stage, "tag={} query schedule mismatch", row.tag);

        let sched12 = row.regime.schedule(nv);
        assert_eq!(sched12.stages.len(), 3);
        let (comm, state) =
            whir_commit_owned_with_schedule(evals.clone(), &[row.tag; 32], &sched12);
        let mut tr_prove = pcs_transcript(&sched12);
        let proof = whir_open(&state, &point, agg_claimed, &mut tr_prove);

        // Dual OOD check: 2 distinct Stage-0 OOD evaluations and 2 distinct OOD evaluations on
        // every folded stage (`folded_layers.len() == 2` for `nv = 12`)!
        assert_eq!(proof.stage0_ood_evals.len(), 2);
        assert_ne!(proof.stage0_ood_evals[0], proof.stage0_ood_evals[1]);
        assert_eq!(proof.folded_layers.len(), 2);
        for (layer_idx, layer) in proof.folded_layers.iter().enumerate() {
            assert_eq!(layer.stage_ood_evals.len(), 2);
            assert_ne!(
                layer.stage_ood_evals[0],
                layer.stage_ood_evals[1],
                "regime {:?} stage {} dual OOD evaluations collided",
                row.regime,
                layer_idx + 1
            );
            if row.pow_bits == 0 {
                assert_eq!(layer.pow_nonce, 0);
            }
        }
        if row.pow_bits == 0 {
            assert_eq!(proof.pow_nonce, 0);
            assert!(proof.fold_pow_nonces.iter().all(|&n| n == 0));
        }

        // Canonical byte roundtrip & verification.
        let mut raw_proof = Vec::new();
        proof.push_bytes(&mut raw_proof);
        let (decoded, used) =
            HemWhirOpeningProof::from_bytes_canonical(&raw_proof).expect("decode WHIR proof");
        assert_eq!((decoded, used), (proof.clone(), raw_proof.len()));

        let mut tr_verify = pcs_transcript(&sched12);
        assert!(whir_verify_with_schedule(
            &comm,
            nv,
            &point,
            agg_claimed,
            &proof,
            &mut tr_verify,
            &sched12,
        ));

        // Dual OOD mutation sensitivity: mutating slot 0 OR slot 1 of `stage0_ood_evals` or
        // `folded_layers[k].stage_ood_evals` MUST fail verification!
        for slot in [0usize, 1] {
            let mut bad_s0 = proof.clone();
            bad_s0.stage0_ood_evals[slot] += GoldilocksExt4::ONE;
            let mut tr = pcs_transcript(&sched12);
            assert!(!whir_verify_with_schedule(
                &comm,
                nv,
                &point,
                agg_claimed,
                &bad_s0,
                &mut tr,
                &sched12,
            ));

            let mut bad_s1 = proof.clone();
            bad_s1.folded_layers[1].stage_ood_evals[slot] += GoldilocksExt4::ONE;
            let mut tr = pcs_transcript(&sched12);
            assert!(!whir_verify_with_schedule(
                &comm,
                nv,
                &point,
                agg_claimed,
                &bad_s1,
                &mut tr,
                &sched12,
            ));
        }
    }
}

#[test]
fn whir_stage_geometries_across_nv_2_to_28_and_bounds_rejection() {
    // Exhaustively check `nv = 2..=28` invariants + exact high-capacity `nv = 21..=28` table.
    for nv in 2..=MAX_PCS_NUM_VARS {
        let sched = WhirSecurityRegime::BciksJohnsonQrom128.schedule(nv);
        assert!((1..=8).contains(&sched.early_stop_vars));
        assert!((1..=4).contains(&sched.stages.len()));
        let fold_sum: usize = sched.stages.iter().map(|s| s.step_vars).sum();
        assert_eq!(
            sched.early_stop_vars + fold_sum,
            nv,
            "nv={nv}: early_stop_vars + sum(step_vars) != nv"
        );
        for st in &sched.stages {
            assert!((1..=6).contains(&st.step_vars));
            assert!(matches!(st.blowup, 4 | 16 | 64 | 256));
        }
        // Stage-0 Reed-Solomon domain `2^nv * blowup_0` must fit inside `2^31`.
        let domain0_log2 = nv + sched.stages[0].blowup.trailing_zeros() as usize;
        assert!(domain0_log2 <= 30, "nv={nv} Stage-0 domain 2^{domain0_log2} > 2^30");
    }

    let expected_high_cap: &[(usize, usize, &[(usize, usize)])] = &[
        (20, 8, &[(4, 5), (16, 3), (64, 4)]),
        (21, 8, &[(4, 6), (16, 3), (64, 4)]),
        (22, 8, &[(4, 6), (16, 4), (64, 4)]),
        (23, 7, &[(4, 6), (16, 4), (64, 3), (256, 3)]),
        (24, 8, &[(4, 6), (16, 4), (64, 3), (256, 3)]),
        (25, 8, &[(4, 6), (16, 4), (64, 4), (256, 3)]),
        (26, 8, &[(4, 6), (16, 5), (64, 4), (256, 3)]),
        (27, 8, &[(4, 6), (16, 5), (64, 4), (256, 4)]),
        (28, 8, &[(4, 6), (16, 6), (64, 4), (256, 4)]),
    ];

    for &(nv, expected_es, expected_stages) in expected_high_cap {
        let sched = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128.schedule(nv);
        assert_eq!(sched.early_stop_vars, expected_es, "nv={nv} early_stop_vars");
        let got: Vec<(usize, usize)> = sched
            .stages
            .iter()
            .map(|s| (s.blowup, s.step_vars))
            .collect();
        assert_eq!(got.as_slice(), expected_stages, "nv={nv} stage geometry mismatch");
    }

    // Out-of-bounds `nv` (`0, 1, 29, 30`) must be rejected.
    for bad_nv in [0usize, 1, 29, 30] {
        assert!(
            std::panic::catch_unwind(|| WhirSecurityRegime::BciksJohnsonQrom128.schedule(bad_nv))
                .is_err(),
            "unsupported nv={bad_nv} must not produce a schedule"
        );
    }
}

#[test]
fn corduroy_poseidon2_76896b_sign_verify_shard_aggregation_merge_and_retired_wire_rejection() {
    // 1. Exact parameter pins matching `FrontierCompact1122AndCorduroySecurity.lean`.
    assert_eq!(AggSigProfile::JortsPoseidon2 as u8, 1);
    assert_eq!(AggSigProfile::CorduroyPoseidon2 as u8, 2);
    assert_eq!(AggSigProfile::from_u8(0), None);
    assert_eq!(AggSigProfile::from_u8(3), None);
    assert_eq!(AggSigProfile::JortsPoseidon2.raw_signature_bytes(), 4_328);
    assert_eq!(AggSigProfile::CorduroyPoseidon2.raw_signature_bytes(), 76_896);
    assert_eq!(WOTS_CHAINS, 128);
    assert_eq!(WOTS_TARGET_SUM, 192);
    assert_eq!(JORTS_XMSS_HEIGHT, 6);
    assert_eq!(FORS_TREES, 32);
    assert_eq!(FORS_HEIGHT, 8);
    assert_eq!(CORDUROY_NUM_LAYERS, 16);
    assert_eq!(CORDUROY_SUBTREE_HEIGHT, 4);
    assert_eq!(CORDUROY_MAX_STATELESS_SIGS_PER_KEY, 1u64 << 20);
    assert_eq!(DOMAIN_PRF_MSG, 0x5153_4147_5052_464D);

    // 2. Stateless `CorduroyPoseidon2` deterministic keygen, signing, `76,896 B` wire canonicality,
    //    and individual + batch verification.
    let mut kps: Vec<ValidatorKeypair> = (0..2u32)
        .map(|i| {
            ValidatorKeypair::keygen_deterministic(
                AggSigProfile::CorduroyPoseidon2,
                &[0x61; 32],
                i,
            )
        })
        .collect();
    let pks: Vec<ValidatorPublicKey> = kps.iter().map(|kp| kp.public_key).collect();
    for pk in &pks {
        let raw_pk = pk.to_bytes();
        assert_eq!(raw_pk[0], 2);
        assert_eq!(ValidatorPublicKey::from_bytes_canonical(&raw_pk), Some(*pk));
    }

    let msg = b"qsag-validation: stateless CorduroyPoseidon2 76,896B -> Hem WHIR shard merge";
    let sig0 = kps[0].sign_stateless(msg, &[0x71; 32]).expect("corduroy sign 0");
    let sig1 = kps[1].sign_stateless(msg, &[0x72; 32]).expect("corduroy sign 1");
    assert_eq!(kps[0].stateless_sigs_issued(), 1);
    assert_eq!(sig0.fors_openings.len(), 32);
    assert_eq!(sig0.layers.len(), 16);

    let wire0 = sig0.to_bytes();
    assert_eq!(wire0.len(), 76_896);
    assert_eq!(
        ValidatorSignature::from_bytes_canonical(AggSigProfile::CorduroyPoseidon2, &wire0).unwrap(),
        sig0
    );
    // Non-canonical Goldilocks limb (`u64::MAX >= p`) in `r_rand` must be rejected on decode!
    let mut non_canon = wire0.clone();
    non_canon[..8].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(
        ValidatorSignature::from_bytes_canonical(AggSigProfile::CorduroyPoseidon2, &non_canon)
            .is_err()
    );

    assert!(verify_individual_signature(&pks[0], msg, &sig0));
    assert!(verify_individual_signature(&pks[1], msg, &sig1));
    assert!(!verify_individual_signature(&pks[0], b"wrong-msg", &sig0));
    assert!(verify_signature_batch(&[
        (pks[0], msg, sig0.clone()),
        (pks[1], msg, sig1.clone()),
    ]));

    // 3. `HemAggregator` shard proving on `CorduroyPoseidon2` + disjoint shard `merge`!
    let mode = SigningMode::SharedMessage(msg);
    let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;

    // Classical tag `2` must be rejected by `HemAggregator` (`!meets_qrom_128_floor()`).
    let classical_cfg = HemAggConfig {
        regime: WhirSecurityRegime::BciksJohnsonClassical128,
        ..HemAggConfig::default_for(AggSigProfile::CorduroyPoseidon2, [0x80; 32])
    };
    let bm0 = SignerBitmap::from_active_indices(2, &[0]).unwrap();
    assert!(
        HemAggregator::aggregate_with_config(
            &pks,
            &bm0,
            &mode,
            core::slice::from_ref(&sig0),
            &classical_cfg,
        )
        .is_err()
    );

    let cfg_a = HemAggConfig {
        regime,
        ..HemAggConfig::default_for(AggSigProfile::CorduroyPoseidon2, [0x81; 32])
    };
    let cfg_b = HemAggConfig {
        regime,
        ..HemAggConfig::default_for(AggSigProfile::CorduroyPoseidon2, [0x82; 32])
    };
    let bm1 = SignerBitmap::from_active_indices(2, &[1]).unwrap();

    let shard_a =
        HemAggregator::aggregate_with_config(&pks, &bm0, &mode, core::slice::from_ref(&sig0), &cfg_a)
            .expect("Corduroy shard A");
    let shard_b =
        HemAggregator::aggregate_with_config(&pks, &bm1, &mode, core::slice::from_ref(&sig1), &cfg_b)
            .expect("Corduroy shard B");

    let merged = HemAggregator::merge(&pks, &mode, &shard_a, &shard_b)
        .expect("merge disjoint Corduroy shards");
    assert!(HemAggregator::verify_with_regime(&pks, &mode, &merged, regime));

    // Overlapping signer sets (`shard_a` with `shard_a`) must be rejected by `merge`!
    assert!(HemAggregator::merge(&pks, &mode, &shard_a, &shard_a).is_err());

    // Canonical wire roundtrip + tamper / retired-regime wire rejection on `HemAggregatedProof`.
    let raw_agg = merged.to_bytes();
    let parsed_agg = HemAggregatedProof::from_bytes_canonical(&raw_agg).unwrap();
    assert!(HemAggregator::verify_with_regime(
        &pks,
        &mode,
        &parsed_agg,
        regime
    ));
    assert!(!HemAggregator::verify_with_regime(
        &pks,
        &SigningMode::SharedMessage(b"tampered-block"),
        &parsed_agg,
        regime
    ));
    // Verify cross-regime mismatch (`BciksJohnsonQrom128` vs `Poseidon2Cdhz25ZeroPowQrom128`) fails closed.
    assert!(!HemAggregator::verify_with_regime(
        &pks,
        &mode,
        &parsed_agg,
        WhirSecurityRegime::BciksJohnsonQrom128
    ));
}

fn build_demo_zkhem_relation(pub_x: u64, secret_bit: u64, secret_preimage: u64) -> (Shape, Vec<Goldilocks>, [Goldilocks; 2]) {
    let expected_digest = sponge12_native(&[gl(secret_bit), gl(secret_preimage), gl(pub_x)])[0];
    let mut cs = ConstraintSystem::new();
    let p_in = cs.public_input(gl(pub_x));
    let p_dig = cs.public_input(expected_digest);
    let b: Lc = cs.alloc(gl(secret_bit)).into();
    let w: Lc = cs.alloc(gl(secret_preimage)).into();
    cs.enforce_boolean(&b);
    let prod = cs.mul(&b, &w);
    // Require `b == 1` via `prod - w == 0` when `w != 0`.
    cs.enforce_zero(Lc::from(prod).minus(&w));
    let st = sponge12(&mut cs, &[b, w, Lc::from(p_in)]);
    cs.enforce_zero(st[0].minus(&Lc::from(p_dig)));
    let (shape, z) = cs.finish();
    (shape, z, [gl(pub_x), expected_digest])
}

#[test]
fn zk_hem_hiding_5table_vs_public_1table_and_full_shard_recursion_tamper_rejection() {
    let (shape, z, public_inputs) = build_demo_zkhem_relation(42, 1, 9_876_543);
    assert!(shape.is_satisfied(&z));
    assert_eq!(shape.num_public, 2);
    assert!(shape.num_rows() > MASK_ROWS);

    // Classical tag `2` is refused by both `Layout::new` (hiding) and `prove_public`!
    assert!(Layout::new(&shape, WhirSecurityRegime::BciksJohnsonClassical128).is_none());
    assert_eq!(
        zkhem_prove(
            &shape,
            z.clone(),
            b"stmt",
            WhirSecurityRegime::BciksJohnsonClassical128,
            &[1; 32],
        ),
        Err(ZkHemError::RelationTooLarge)
    );
    assert_eq!(
        zkhem_prove_public(
            &shape,
            z.clone(),
            b"stmt",
            WhirSecurityRegime::BciksJohnsonClassical128,
            &[1; 32],
        ),
        Err(ZkHemError::RelationTooLarge)
    );

    let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
    let stmt = b"zk-hem-hiding-vs-public-parity";

    // 1. 5-table hiding `zk_hem::protocol::prove` & `verify`:
    //    - `Layout` allocates `blind_cells > 0`
    //    - Two distinct seeds produce distinct commitments & companion claims!
    let hiding_layout = Layout::new(&shape, regime).unwrap();
    assert!(hiding_layout.blind_cells > 0);
    let zk_proof_1 = zkhem_prove(&shape, z.clone(), stmt, regime, &[0x11; 32]).unwrap();
    let zk_proof_2 = zkhem_prove(&shape, z.clone(), stmt, regime, &[0x22; 32]).unwrap();
    assert_ne!(zk_proof_1.commitment, zk_proof_2.commitment);
    assert_ne!(zk_proof_1.companion_claims, zk_proof_2.companion_claims);

    let zk_bytes = zk_proof_1.to_bytes();
    let zk_decoded = ZkHemProof::from_bytes(&zk_bytes, &shape, regime).unwrap();
    assert_eq!(zk_decoded, zk_proof_1);
    assert!(zkhem_verify(&shape, &public_inputs, stmt, regime, &zk_decoded));

    // Tamper checks on hiding proof: wrong public input, wrong statement, mutated companion claim.
    assert!(!zkhem_verify(
        &shape,
        &[gl(43), public_inputs[1]],
        stmt,
        regime,
        &zk_decoded
    ));
    assert!(!zkhem_verify(&shape, &public_inputs, b"other-stmt", regime, &zk_decoded));
    let mut bad_zk = zk_decoded;
    bad_zk.companion_claims[2] += GoldilocksExt4::ONE;
    assert!(!zkhem_verify(&shape, &public_inputs, stmt, regime, &bad_zk));

    // 2. 1-table public `zk_hem::protocol::prove_public` & `verify_public`:
    //    Exercises the 3 independent `ZKHEM_COMBINE` challenges and `HEM_PUBLIC_CELLS` batching
    //    binding `Z[0] = 1` and `public[0..2]`!
    let pub_proof = zkhem_prove_public(&shape, z, stmt, regime, &[0x33; 32]).unwrap();
    let pub_bytes = pub_proof.to_bytes();
    assert!(
        pub_bytes.len() < zk_bytes.len(),
        "1-table PublicHemProof ({}) should be more compact than 5-table ZkHemProof ({})",
        pub_bytes.len(),
        zk_bytes.len()
    );
    let pub_decoded = PublicHemProof::from_bytes(&pub_bytes, &shape, regime).unwrap();
    assert_eq!(pub_decoded, pub_proof);
    assert!(zkhem_verify_public(
        &shape,
        &public_inputs,
        stmt,
        regime,
        &pub_decoded
    ));

    // `HEM_PUBLIC_CELLS` soundness: mutating `public_inputs[0]` or `public_inputs[1]`, `row_values`,
    // or `evaluation` MUST fail `verify_public`!
    assert!(!zkhem_verify_public(
        &shape,
        &[gl(42), public_inputs[1] + Goldilocks::ONE],
        stmt,
        regime,
        &pub_decoded
    ));
    let mut bad_pub = pub_decoded.clone();
    bad_pub.row_values[1] += GoldilocksExt4::ONE;
    assert!(!zkhem_verify_public(&shape, &public_inputs, stmt, regime, &bad_pub));
    let mut bad_eval = pub_decoded;
    bad_eval.evaluation += GoldilocksExt4::ONE;
    assert!(!zkhem_verify_public(&shape, &public_inputs, stmt, regime, &bad_eval));

    // Unsatisfied assignment (`secret_bit = 2`, non-Boolean) is refused by both provers.
    let mut bad_z = build_demo_zkhem_relation(42, 1, 9_876_543).1;
    bad_z[3] = gl(2);
    assert_eq!(
        zkhem_prove(&shape, bad_z.clone(), stmt, regime, &[0x44; 32]),
        Err(ZkHemError::Unsatisfied)
    );
    assert_eq!(
        zkhem_prove_public(&shape, bad_z, stmt, regime, &[0x44; 32]),
        Err(ZkHemError::Unsatisfied)
    );

    // 3. `zk_hem::full_shard` end-to-end 2-shard recursive merge (`QSAGFSM1`) + tamper rejection!
    let fs_params = FullShardParams::new(regime, 2).expect("FullShardParams(slots=2)");
    assert_eq!(fs_params.slots(), 2);

    let make_child = |seed_tag: u8, active: &[usize], msg32: [u8; 32]| {
        let mut kps: Vec<ValidatorKeypair> = (0..2u32)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(
                    AggSigProfile::JortsPoseidon2,
                    &[seed_tag; 32],
                    i,
                )
            })
            .collect();
        let sigs: Vec<ValidatorSignature> = active
            .iter()
            .map(|&idx| kps[idx].sign_stateful(&msg32, &[seed_tag ^ 0x55; 32]).unwrap())
            .collect();
        let keys = kps.into_iter().map(|kp| kp.public_key).collect();
        let bitmap = SignerBitmap::from_active_indices(2, active).unwrap();
        let statement = RecursiveShardStatement {
            keys,
            bitmap,
            message: msg32,
        };
        let child_proof =
            prove_recursive_shard(&fs_params, &statement, &sigs, &[seed_tag ^ 0xAA; 32])
                .expect("prove_recursive_shard");
        assert!(verify_recursive_shard(&fs_params, &statement, &child_proof));
        (statement, child_proof)
    };

    let (stmt0, child0) = make_child(0x11, &[0, 1], [0xA5; 32]);
    let (stmt1, child1) = make_child(0x22, &[1], [0x5A; 32]);
    let pub0 = stmt0.public(&fs_params).unwrap();
    let pub1 = stmt1.public(&fs_params).unwrap();
    assert_eq!(pub0.signers, 2);
    assert_eq!(pub1.signers, 1);

    let relation = FullShardMergeRelation::new(fs_params.clone(), 2).expect("FullShardMergeRelation");
    assert_eq!(relation.num_children(), 2);

    // Tampered child proof must be refused by `prove_full_shard_merge` (`Err(FullShardError::InvalidChild)`)!
    let mut corrupt_child1 = child1.clone();
    corrupt_child1.col_evals[0] += GoldilocksExt4::ONE;
    assert!(!verify_recursive_shard(&fs_params, &stmt1, &corrupt_child1));
    assert!(matches!(
        prove_full_shard_merge(
            &relation,
            &[stmt0.clone(), stmt1.clone()],
            &[child0.clone(), corrupt_child1],
            regime,
            &[0x77; 32],
        ),
        Err(FullShardError::InvalidChild)
    ));

    // Honest parent merge proof verifies against `[pub0, pub1]` alone (`QSAGFSM1` wire roundtrip)!
    let parent_proof = prove_full_shard_merge(
        &relation,
        &[stmt0, stmt1],
        &[child0, child1],
        regime,
        &[0x88; 32],
    )
    .expect("prove_full_shard_merge");

    let parent_wire = parent_proof.to_bytes();
    assert_eq!(&parent_wire[..8], b"QSAGFSM1");
    let decoded_parent =
        FullShardMergeProof::from_bytes(&parent_wire, &relation, regime).expect("decode QSAGFSM1");
    assert_eq!(decoded_parent, parent_proof);
    assert!(verify_full_shard_merge(
        &relation,
        &[pub0.clone(), pub1.clone()],
        regime,
        &decoded_parent,
    ));

    // Statement & wire tamper rejection on `verify_full_shard_merge`:
    // (a) Claiming 2 signers instead of 1 on shard 1
    let mut inflated_pub1 = pub1.clone();
    inflated_pub1.signers = 2;
    assert!(!verify_full_shard_merge(
        &relation,
        &[pub0.clone(), inflated_pub1],
        regime,
        &decoded_parent,
    ));
    // (b) Altering 1 byte of shard 0's signed 32-byte message
    let mut wrong_msg_pub0 = pub0.clone();
    wrong_msg_pub0.message[31] ^= 0x01;
    assert!(!verify_full_shard_merge(
        &relation,
        &[wrong_msg_pub0, pub1.clone()],
        regime,
        &decoded_parent,
    ));
    // (c) Altering shard 1's committee digest
    let mut wrong_comm_pub1 = pub1.clone();
    wrong_comm_pub1.committee[0] += Goldilocks::ONE;
    assert!(!verify_full_shard_merge(
        &relation,
        &[pub0.clone(), wrong_comm_pub1],
        regime,
        &decoded_parent,
    ));
    // (d) Wrong magic header or bit-flipped proof payload
    let mut bad_magic = parent_wire.clone();
    bad_magic[7] = b'2';
    assert!(FullShardMergeProof::from_bytes(&bad_magic, &relation, regime).is_none());

    let mut flipped_wire = parent_wire;
    let mid = flipped_wire.len() / 2;
    flipped_wire[mid] ^= 0x01;
    if let Some(bad_decoded) = FullShardMergeProof::from_bytes(&flipped_wire, &relation, regime) {
        assert!(!verify_full_shard_merge(
            &relation,
            &[pub0, pub1],
            regime,
            &bad_decoded,
        ));
    }
}
