use qsag_whir_verified::{
    FP5_NONRESIDUE_W, Fp5, GOLDILOCKS_P, cwyz_bridge_claim_step_fp5, cwyz_duet_fold_fp5,
    decode_canonical_fp5, decode_canonical_gl24_digest, eval_fp5_univariate_at_base,
    eval_quadratic_sumcheck_wire_fp5, fp5_add, fp5_frobenius, fp5_mul,
    step_merkle_pair_order_400, step_merkle_pair_order_gl24, verify_affine_duet_fold_step_fp5,
    verify_cwyz_bridge_claim_step_fp5, verify_cwyz_duet_fold_step_fp5,
    verify_fp5_univariate_at_base_pin, verify_ood_pin_eq_fp5, verify_qsaghqm2_header,
    verify_quintic_schedule_envelope,
};

fn ext(x: [u64; 5]) -> Fp5 {
    Fp5 {
        c0: x[0],
        c1: x[1],
        c2: x[2],
        c3: x[3],
        c4: x[4],
    }
}

fn limbs(x: Fp5) -> [u64; 5] {
    [x.c0, x.c1, x.c2, x.c3, x.c4]
}

fn add(x: [u64; 5], y: [u64; 5]) -> [u64; 5] {
    core::array::from_fn(|i| ((x[i] as u128 + y[i] as u128) % GOLDILOCKS_P as u128) as u64)
}

fn sub(x: [u64; 5], y: [u64; 5]) -> [u64; 5] {
    core::array::from_fn(|i| {
        let rb = y[i] % GOLDILOCKS_P;
        ((x[i] as u128 + (GOLDILOCKS_P - rb) as u128) % GOLDILOCKS_P as u128) as u64
    })
}

fn scale(x: [u64; 5], y: u64) -> [u64; 5] {
    x.map(|v| ((v as u128 * y as u128) % GOLDILOCKS_P as u128) as u64)
}

// Independent schoolbook convolution, reducing X^5 = 3 term by term.
fn product(x: [u64; 5], y: [u64; 5]) -> [u64; 5] {
    let mut out = [0u64; 5];
    let p = GOLDILOCKS_P as u128;
    for i in 0..5 {
        for j in 0..5 {
            let term = (x[i] as u128 * y[j] as u128) % p;
            let term = term * if i + j >= 5 { FP5_NONRESIDUE_W as u128 } else { 1 };
            out[(i + j) % 5] = ((out[(i + j) % 5] as u128 + term) % p) as u64;
        }
    }
    out
}

fn perturb_limb(x: [u64; 5], idx: usize) -> [u64; 5] {
    let mut out = x;
    out[idx] = ((out[idx] as u128 + 1) % GOLDILOCKS_P as u128) as u64;
    out
}

#[test]
fn quintic_frobenius_matches_lean_kats_and_is_ring_endomorphism() {
    // Matches `frob_katWide` in `lean/Qsag/Math/QuinticExt5.lean`.
    let wide = [
        81_985_529_216_486_895,
        18_364_758_544_493_064_720,
        16_045_690_984_503_098_046,
        1_089_357_896_855_742_840,
        1_234_605_616_436_508_552,
    ];
    assert_eq!(
        limbs(fp5_frobenius(ext(wide))),
        [
            81_985_529_216_486_895,
            9_961_272_706_250_400_476,
            4_912_495_906_482_251_711,
            9_291_945_967_817_452_589,
            15_493_897_884_983_376_685,
        ]
    );

    let b = [7, GOLDILOCKS_P - 5, 19, 42, 999_999];
    assert_eq!(
        limbs(fp5_frobenius(fp5_mul(ext(wide), ext(b)))),
        limbs(fp5_mul(fp5_frobenius(ext(wide)), fp5_frobenius(ext(b))))
    );
    assert_eq!(
        limbs(fp5_frobenius(fp5_add(ext(wide), ext(b)))),
        limbs(fp5_add(fp5_frobenius(ext(wide)), fp5_frobenius(ext(b))))
    );
}

#[test]
fn production_quintic_fold_and_verifiers_recover_coset_and_reject_perturbations() {
    let p = GOLDILOCKS_P;
    let inv_two = p / 2 + 1;
    for y in [1u64, 2, 7, p - 1] {
        let mut iy = 1u128;
        let mut base = (2 * y as u128) % p as u128;
        let mut exp = p - 2;
        while exp > 0 {
            if exp & 1 != 0 {
                iy = iy * base % p as u128;
            }
            base = base * base % p as u128;
            exp >>= 1;
        }
        let iy = iy as u64;
        for even in [[0; 5], [1, 2, 3, 4, 5], [p - 1; 5]] {
            let odd = [p - 2, 5, 9, 13, 17];
            let theta = [3, 7, p - 1, 11, 15];
            let alpha = [17, p - 2, 19, 23, 27];
            let beta = [29, 31, 37, 41, 43];
            let yo = scale(odd, y);
            let v0 = add(even, yo);
            let v1 = sub(even, yo);
            let yy = (y as u128 * y as u128 % p as u128) as u64;

            let expected_duet = add(odd, product(alpha, even));
            assert!(verify_affine_duet_fold_step_fp5(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                ext(alpha),
                ext(expected_duet),
            ));
            for limb in 0..5 {
                assert!(!verify_affine_duet_fold_step_fp5(
                    ext(v0),
                    ext(v1),
                    iy,
                    inv_two,
                    ext(alpha),
                    ext(perturb_limb(expected_duet, limb)),
                ));
            }

            let expected_cwyz = add(
                odd,
                product(add(alpha, scale(beta, yy)), add(even, product(theta, odd))),
            );
            let actual_cwyz = cwyz_duet_fold_fp5(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                yy,
                ext(theta),
                ext(alpha),
                ext(beta),
            );
            assert_eq!(limbs(actual_cwyz), expected_cwyz);
            assert!(verify_cwyz_duet_fold_step_fp5(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                yy,
                ext(theta),
                ext(alpha),
                ext(beta),
                ext(expected_cwyz),
            ));
            for limb in 0..5 {
                assert!(!verify_cwyz_duet_fold_step_fp5(
                    ext(v0),
                    ext(v1),
                    iy,
                    inv_two,
                    yy,
                    ext(theta),
                    ext(alpha),
                    ext(beta),
                    ext(perturb_limb(expected_cwyz, limb)),
                ));
            }
        }
    }
}

#[test]
fn cwyz_bridge_and_quadratic_sumcheck_verifiers_accept_and_reject_perturbations() {
    let p = GOLDILOCKS_P;
    let a0 = [3, 5, 7, 11, 13];
    let a1 = [13, p - 2, 19, 23, 29];
    let b0 = [29, 31, 37, 41, 43];
    let b1 = [43, 47, p - 3, 53, 59];
    let kn = [59, 61, 67, 71, 73];
    let phi = [2, 4, 6, 8, 10];
    let theta = [9, 10, 12, 14, 16];
    let alpha = [15, 16, 18, 20, 22];
    let beta = [21, 22, 24, 25, 27];

    let w0 = product(a0, b0);
    let w1 = product(a0, b1);
    let w2 = product(a1, b0);
    let w3 = product(a0, kn);
    let w4 = product(a1, kn);
    let claim = add(w0, product(a1, b1));

    let folded_a = add(a0, product(theta, a1));
    let c0_prime = add(a1, product(alpha, folded_a));
    let c1_prime = product(beta, folded_a);
    let k0_prime = add(b0, product(phi, b1));
    let expected = add(product(c0_prime, k0_prime), product(c1_prime, kn));

    let actual = cwyz_bridge_claim_step_fp5(
        ext(w0),
        ext(w1),
        ext(w2),
        ext(w3),
        ext(w4),
        ext(claim),
        ext(phi),
        ext(theta),
        ext(alpha),
        ext(beta),
    );
    assert_eq!(limbs(actual), expected);
    assert!(verify_cwyz_bridge_claim_step_fp5(
        ext(w0),
        ext(w1),
        ext(w2),
        ext(w3),
        ext(w4),
        ext(claim),
        ext(phi),
        ext(theta),
        ext(alpha),
        ext(beta),
        ext(expected),
    ));
    for limb in 0..5 {
        assert!(!verify_cwyz_bridge_claim_step_fp5(
            ext(w0),
            ext(w1),
            ext(w2),
            ext(w3),
            ext(w4),
            ext(claim),
            ext(phi),
            ext(theta),
            ext(alpha),
            ext(beta),
            ext(perturb_limb(expected, limb)),
        ));
    }

    // Quadratic sumcheck wire: g(0) + g(1) == sum_claim and g(r) == c0 + c1*r + c2*r^2.
    let g0 = eval_quadratic_sumcheck_wire_fp5(ext(a0), ext(a1), ext(claim), ext([0; 5]));
    let g1 = eval_quadratic_sumcheck_wire_fp5(ext(a0), ext(a1), ext(claim), ext([1, 0, 0, 0, 0]));
    assert!(verify_ood_pin_eq_fp5(fp5_add(g0, g1), ext(claim)));
}

#[test]
fn horner_canopy_and_wire_envelope_entrypoints() {
    let raw = [
        [GOLDILOCKS_P - 1, 1, 2, 3, 4],
        [5, 6, 7, 8, 9],
        [10, 11, 12, 13, 14],
    ];
    for n in 0..=raw.len() {
        let coeffs: Vec<_> = raw[..n].iter().copied().map(ext).collect();
        for z in [0, 1, 2, GOLDILOCKS_P - 1, u64::MAX] {
            let mut power = 1u64;
            let mut expected = [0u64; 5];
            for &c in &raw[..n] {
                expected = add(expected, scale(c, power));
                power = (power as u128 * z as u128 % GOLDILOCKS_P as u128) as u64;
            }
            assert_eq!(limbs(eval_fp5_univariate_at_base(&coeffs, z)), expected);
            assert!(verify_fp5_univariate_at_base_pin(
                &coeffs,
                z,
                ext(expected),
            ));
            for limb in 0..5 {
                assert!(!verify_fp5_univariate_at_base_pin(
                    &coeffs,
                    z,
                    ext(perturb_limb(expected, limb)),
                ));
            }
        }
    }

    let mut raw40 = [0u8; 40];
    for i in 0..5 {
        raw40[8 * i..8 * (i + 1)].copy_from_slice(&(GOLDILOCKS_P - 1 - i as u64).to_le_bytes());
    }
    assert!(decode_canonical_fp5(&raw40).is_some());

    let mut raw56 = [0u8; 56];
    for i in 0..7 {
        raw56[8 * i..8 * (i + 1)].copy_from_slice(&(i as u64 + 10).to_le_bytes());
    }
    let gl24 = decode_canonical_gl24_digest(&raw56).expect("canonical gl24");
    assert_eq!(
        [gl24.l0, gl24.l1, gl24.l2, gl24.l3, gl24.l4, gl24.l5, gl24.l6],
        [10, 11, 12, 13, 14, 15, 16]
    );
    assert!(step_merkle_pair_order_400(5, 0, [0xAA; 50], [0xBB; 50]).is_some());
    assert!(
        step_merkle_pair_order_gl24(
            5,
            0,
            gl24,
            qsag_whir_verified::Gl24Digest {
                l0: 1,
                l1: 1,
                l2: 1,
                l3: 1,
                l4: 1,
                l5: 1,
                l6: 1,
            }
        )
        .is_some()
    );
    assert!(verify_qsaghqm2_header(*b"QSAGHQM2", 1, 1, 1, 64, 64).is_some());
    assert!(verify_quintic_schedule_envelope(24, 8, 16, 4));
}
