// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Differential & Structural Validation for `[DKT26]` `< 2^{-128}` QROM Quintic `Fp5` WHIR
//! (`QSAGHQM2`, `QSAGZKH2`, `QSAGIW24`), High-Capacity Stage Geometries (`nv = 16..=28`),
//! Retired Legacy Tag Rejection (`0..=15`, `18..=255`), and Stateless `CorduroyPoseidon2` (`76,896 B`).

use qsag_agg::pcs::MAX_PCS_NUM_VARS;
use qsag_agg::sig::{
    CORDUROY_MAX_STATELESS_SIGS_PER_KEY, CORDUROY_NUM_LAYERS, CORDUROY_SUBTREE_HEIGHT,
    DOMAIN_PRF_MSG, FORS_HEIGHT, FORS_TREES, JORTS_XMSS_HEIGHT, SigError, StatelessBudgetWalSink,
    ValidatorKeypair, WOTS_CHAINS, WOTS_TARGET_SUM, verify_signature_batch,
};
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, sponge12, sponge12_native};
use qsag_agg::zk_hem::v2::field5::Fp5;
use qsag_agg::zk_hem::v2::params::{
    LATER_OOD_POINTS, MASK_POINTS, MAX_LOG_CELLS, MIN_LOG_CELLS, Profile as ZkHemProfile,
    schedule as zkhem_v2_schedule,
};
use qsag_agg::zk_hem::v2::protocol::{
    ZkHemV2Proof, prove as zkhem_v2_prove, verify as zkhem_v2_verify,
};
use qsag_agg::{
    AggSigProfile, FixedPathWhirW24, Goldilocks, HemQuinticProfile, HemQuinticProof, IvcStepConfig,
    IvcTableCommitment, SignerBitmap, SigningMode, SuccinctIvcProof, prove_hem_quintic_128,
    verify_hem_quintic_128, verify_individual_signature,
};
use qsag_external_validation::{GOLDILOCKS_P, p3_fp5_mul};

fn gl(x: u64) -> Goldilocks {
    Goldilocks::from_u64_reduced(x)
}

/// Independent Plonky3 Quintic `Fp5` multilinear evaluation of `evals` (`len = 2^nv`) at `point`.
fn multilinear_eval_p3_fp5_ref(evals: &[Goldilocks], point: &[[u64; 5]]) -> [u64; 5] {
    let nv = point.len();
    assert_eq!(evals.len(), 1usize << nv);
    let one = [1u64, 0, 0, 0, 0];
    let sub_fp5 = |a: [u64; 5], b: [u64; 5]| -> [u64; 5] {
        core::array::from_fn(|i| {
            ((a[i] as u128 + GOLDILOCKS_P as u128 - b[i] as u128) % GOLDILOCKS_P as u128) as u64
        })
    };
    let add_fp5 = |a: [u64; 5], b: [u64; 5]| -> [u64; 5] {
        core::array::from_fn(|i| ((a[i] as u128 + b[i] as u128) % GOLDILOCKS_P as u128) as u64)
    };
    let mut acc = [0u64; 5];
    for (idx, &val) in evals.iter().enumerate() {
        let mut eq = one;
        for (bit, &r) in point.iter().enumerate() {
            let factor = if (idx >> bit) & 1 == 1 {
                r
            } else {
                sub_fp5(one, r)
            };
            eq = p3_fp5_mul(eq, factor);
        }
        let term = p3_fp5_mul(eq, [val.to_canonical_u64(), 0, 0, 0, 0]);
        acc = add_fp5(acc, term);
    }
    acc
}

fn assert_wire_bit_flips_rejected<P>(
    wire: &[u8],
    decode: impl Fn(&[u8]) -> Option<P>,
    verify: impl Fn(&P) -> bool,
) {
    let mut reached_verifier = 0;
    for eighth in 1..8 {
        let mut bad = wire.to_vec();
        let pos = eighth * wire.len() / 8;
        bad[pos] ^= 0x01;
        if let Some(proof) = decode(&bad) {
            reached_verifier += 1;
            assert!(!verify(&proof), "bit flip at byte {pos} verified");
        }
    }
    assert!(reached_verifier > 0, "no bit flip reached the verifier");
}

#[derive(Default)]
struct InMemStatelessWal {
    count: u64,
}

impl StatelessBudgetWalSink for InMemStatelessWal {
    fn reserve(&mut self, _pk_root: &[u8; 32], limit: u64) -> Result<u64, SigError> {
        if self.count >= limit {
            return Err(SigError::StatelessBudgetExhausted);
        }
        self.count += 1;
        Ok(self.count)
    }
}

#[test]
fn quintic_whir_profiles_retired_tag_rejection_and_high_capacity_schedules() {
    assert_eq!(MAX_PCS_NUM_VARS, 28);
    assert_eq!(MIN_LOG_CELLS, 16);
    assert_eq!(MAX_LOG_CELLS, 28);
    assert_eq!(MASK_POINTS, 5);
    assert_eq!(LATER_OOD_POINTS, 2);
    assert_eq!(SuccinctIvcProof::encoded_len(), 639_673);

    // 1. Fail-closed rejection of ALL retired wire tags `0..=15` and unassigned `18..=255`.
    for tag in (0u8..=15).chain(18u8..=u8::MAX) {
        assert_eq!(
            ZkHemProfile::from_wire_tag(tag),
            None,
            "retired or unassigned wire tag {tag} MUST be rejected"
        );
    }
    assert_eq!(
        ZkHemProfile::from_wire_tag(16),
        Some(ZkHemProfile::CshakeJohnson400)
    );
    assert_eq!(
        ZkHemProfile::from_wire_tag(17),
        Some(ZkHemProfile::TurboShakeJohnson400)
    );

    // 2. Out-of-range dimensions `0..=15` and `29..=32` must be rejected by `[DKT26]` schedule.
    for bad_nv in (0..16).chain(29..=32) {
        assert!(zkhem_v2_schedule(bad_nv).is_none());
        assert!(IvcStepConfig::dkt26(bad_nv).is_none());
    }

    // 3. Pin exact high-capacity stage geometries across `nv = 16..=28` (`(6,4,4,3)..=(6,6,4,4)`).
    let expected_steps: &[(usize, &[usize])] = &[
        (24, &[6, 4, 3, 3]),
        (25, &[6, 4, 4, 3]),
        (26, &[6, 5, 4, 3]),
        (27, &[6, 5, 4, 4]),
        (28, &[6, 6, 4, 4]),
    ];
    for &(nv, want_steps) in expected_steps {
        let sched = zkhem_v2_schedule(nv).expect("certified DKT26 schedule");
        let steps: Vec<usize> = sched.stages.iter().map(|s| s.step_vars).collect();
        let blowups: Vec<usize> = sched.stages.iter().map(|s| s.blowup).collect();
        assert_eq!(steps, want_steps, "nv={nv}");
        assert_eq!(blowups, &[4, 16, 64, 256], "nv={nv}");
        assert_eq!(sched.early_stop_vars + steps.iter().sum::<usize>(), nv);
    }

    // 4. `[DKT26]` `FixedPathWhirW24` (`IvcStepConfig::dkt26(16)`) commit/open/verify vs Plonky3 `Fp5` MLE!
    let nv = 16usize;
    let cfg = IvcStepConfig::dkt26(nv).unwrap();
    let table: Vec<Goldilocks> = (0..(1usize << nv))
        .map(|i| gl((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(19)))
        .collect();
    let point_limbs: Vec<[u64; 5]> = (0..nv)
        .map(|k| {
            [
                (101 + 37 * k as u64) % GOLDILOCKS_P,
                (202 + 53 * k as u64) % GOLDILOCKS_P,
                (303 + 71 * k as u64) % GOLDILOCKS_P,
                (404 + 97 * k as u64) % GOLDILOCKS_P,
                (505 + 113 * k as u64) % GOLDILOCKS_P,
            ]
        })
        .collect();
    let point: Vec<Fp5> = point_limbs
        .iter()
        .map(|arr| Fp5::from_limbs(arr.map(gl)))
        .collect();
    let p3_claimed = Fp5::from_limbs(multilinear_eval_p3_fp5_ref(&table, &point_limbs).map(gl));

    let com = IvcTableCommitment::commit(&cfg, &table, &[0x44; 32]).unwrap();
    let ctx = [gl(11), gl(22)];
    let (val, op) = com.open(&ctx, &point).unwrap();
    assert_eq!(val, p3_claimed, "Fp5 MLE mismatch vs Plonky3 reference");
    assert!(op.verify(&cfg, &ctx, com.nonce(), com.root(), &point, val));
    assert!(!op.verify(&cfg, &ctx, com.nonce(), com.root(), &point, val + Fp5::ONE));

    let op_wire = op.to_bytes();
    assert_wire_bit_flips_rejected(
        &op_wire,
        |b| FixedPathWhirW24::from_bytes_canonical(&cfg, b),
        |p| p.verify(&cfg, &ctx, com.nonce(), com.root(), &point, val),
    );
}

#[test]
fn corduroy_stateless_76896_and_quintic_hem_profiles_and_zkhem_v2() {
    assert_eq!(WOTS_CHAINS, 128);
    assert_eq!(WOTS_TARGET_SUM, 192);
    assert_eq!(JORTS_XMSS_HEIGHT, 6);
    assert_eq!(CORDUROY_NUM_LAYERS, 16);
    assert_eq!(CORDUROY_SUBTREE_HEIGHT, 4);
    assert_eq!(FORS_TREES, 32);
    assert_eq!(FORS_HEIGHT, 8);
    assert_eq!(CORDUROY_MAX_STATELESS_SIGS_PER_KEY, 1 << 20);
    assert_eq!(DOMAIN_PRF_MSG, 0x5153_4147_5052_464D);
    assert_eq!(AggSigProfile::CorduroyPoseidon2.raw_signature_bytes(), 76_896);

    // 1. Stateless CorduroyPoseidon2 keygen + tracked stateless signing + Quintic Fp5 aggregation
    let mut kp0 = ValidatorKeypair::keygen_deterministic(AggSigProfile::CorduroyPoseidon2, &[0x61; 32], 0);
    let mut kp1 = ValidatorKeypair::keygen_deterministic(AggSigProfile::CorduroyPoseidon2, &[0x62; 32], 1);
    let pks = [kp0.pk, kp1.pk];
    let msg = b"corduroy-quintic-fp5-parity";
    let mut wal0 = InMemStatelessWal::default();
    let mut wal1 = InMemStatelessWal::default();
    let sig0 = kp0.sign_stateless(msg, &mut wal0).unwrap();
    let sig1 = kp1.sign_stateless(msg, &mut wal1).unwrap();
    assert_eq!(sig0.to_bytes().len(), 76_896);
    assert!(verify_individual_signature(&kp0.pk, msg, &sig0));
    assert!(verify_signature_batch(&[
        (kp0.pk, msg.as_slice(), sig0.clone()),
        (kp1.pk, msg.as_slice(), sig1.clone()),
    ]));

    let bitmap = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
    let mode = SigningMode::SharedMessage(msg);
    for profile in [
        HemQuinticProfile::TurboShake400,
        HemQuinticProfile::Poseidon2Gl24,
    ] {
        let proof = prove_hem_quintic_128(
            profile,
            &pks,
            &bitmap,
            &mode,
            &[sig0.clone(), sig1.clone()],
        )
        .unwrap();
        let wire = proof.to_bytes();
        assert!(verify_hem_quintic_128(profile, &pks, &mode, &proof));
        assert_wire_bit_flips_rejected(
            &wire,
            HemQuinticProof::from_bytes,
            |p| verify_hem_quintic_128(profile, &pks, &mode, p),
        );
    }

    // 2. Committed-mask zero-knowledge `zk-Hem v2` (`QSAGZKH2`) across both 400-bit sponge profiles
    let out_val = sponge12_native(&[gl(19), gl(23)])[0];
    let mut cs = ConstraintSystem::new();
    let pub_x: Lc = cs.public_input(gl(19)).into();
    let out: Lc = cs.public_input(out_val).into();
    let w: Lc = cs.alloc(gl(23)).into();
    let st = sponge12(&mut cs, &[pub_x, w]);
    cs.enforce_equal(&st[0], &out);
    let (shape, assignment) = cs.finish_v2();
    let public_inputs = [gl(19), out_val];

    for profile in [
        ZkHemProfile::CshakeJohnson400,
        ZkHemProfile::TurboShakeJohnson400,
    ] {
        let proof = zkhem_v2_prove(
            &shape,
            assignment.clone(),
            b"VALIDATION.ZKHEM.V2",
            profile,
            &[0x9A; 32],
        )
        .unwrap();
        let wire = proof.to_bytes();
        assert!(zkhem_v2_verify(
            &shape,
            &public_inputs,
            b"VALIDATION.ZKHEM.V2",
            profile,
            &proof
        ));
        assert_wire_bit_flips_rejected(
            &wire,
            |b| ZkHemV2Proof::from_bytes(b, &shape),
            |p| zkhem_v2_verify(&shape, &public_inputs, b"VALIDATION.ZKHEM.V2", profile, p),
        );
    }
}
