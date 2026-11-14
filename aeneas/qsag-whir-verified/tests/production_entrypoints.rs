use qsag_whir_verified::{
    Ext4, GOLDILOCKS_P, cwyz_bridge_claim_step, cwyz_duet_fold, eval_ext4_univariate_at_base,
    eval_univariate_ext4_at_base, fold_duet_affine_ext4, verify_affine_duet_fold_step,
    verify_cwyz_bridge_claim_step, verify_cwyz_duet_fold_step, verify_ext4_univariate_at_base_pin,
};

fn ext(x: [u64; 4]) -> Ext4 {
    Ext4 {
        a: x[0],
        b: x[1],
        c: x[2],
        d: x[3],
    }
}

fn limbs(x: Ext4) -> [u64; 4] {
    [x.a, x.b, x.c, x.d]
}

fn add(x: [u64; 4], y: [u64; 4]) -> [u64; 4] {
    core::array::from_fn(|i| ((x[i] as u128 + y[i] as u128) % GOLDILOCKS_P as u128) as u64)
}

fn scale(x: [u64; 4], y: u64) -> [u64; 4] {
    x.map(|v| ((v as u128 * y as u128) % GOLDILOCKS_P as u128) as u64)
}

// Independent schoolbook convolution, reducing u^4 = 7 term by term.
fn product(x: [u64; 4], y: [u64; 4]) -> [u64; 4] {
    let mut out = [0; 4];
    let p = GOLDILOCKS_P as u128;
    for i in 0..4 {
        for j in 0..4 {
            let term = (x[i] as u128 * y[j] as u128) % p;
            let term = term * if i + j >= 4 { 7 } else { 1 };
            out[(i + j) % 4] = ((out[(i + j) % 4] as u128 + term) % p) as u64;
        }
    }
    out
}

fn perturb_limb(x: [u64; 4], idx: usize) -> [u64; 4] {
    let mut out = x;
    out[idx] = ((out[idx] as u128 + 1) % GOLDILOCKS_P as u128) as u64;
    out
}

#[test]
fn production_fold_and_verifiers_recover_coset_and_reject_perturbations() {
    let p = GOLDILOCKS_P;
    let inv_two = p / 2 + 1;
    for y in [1, 2, 7, p - 1] {
        // Inverse by independent binary powering in the base field.
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
        for even in [[0; 4], [1, 2, 3, 4], [p - 1; 4]] {
            let odd = [p - 2, 5, 9, 13];
            let theta = [3, 7, p - 1, 11];
            let alpha = [17, p - 2, 19, 23];
            let beta = [29, 31, 37, 41];
            let yo = scale(odd, y);
            let v0 = add(even, yo);
            let v1 = add(even, yo.map(|v| if v == 0 { 0 } else { p - v }));
            let yy = (y as u128 * y as u128 % p as u128) as u64;

            let expected_duet = add(odd, product(alpha, even));
            assert!(verify_affine_duet_fold_step(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                ext(alpha),
                ext(expected_duet),
            ));
            for limb in 0..4 {
                assert!(!verify_affine_duet_fold_step(
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
            let actual_prod = fold_duet_affine_ext4(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                yy,
                ext(theta),
                ext(alpha),
                ext(beta),
            );
            let actual_cwyz = cwyz_duet_fold(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                yy,
                ext(theta),
                ext(alpha),
                ext(beta),
            );
            assert_eq!(limbs(actual_prod), expected_cwyz);
            assert_eq!(limbs(actual_cwyz), expected_cwyz);
            assert!(verify_cwyz_duet_fold_step(
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
            for limb in 0..4 {
                assert!(!verify_cwyz_duet_fold_step(
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
fn cwyz_bridge_verifier_accepts_dual_functional_and_rejects_perturbations() {
    let p = GOLDILOCKS_P;
    let a0 = [3, 5, 7, 11];
    let a1 = [13, p - 2, 19, 23];
    let b0 = [29, 31, 37, 41];
    let b1 = [43, 47, p - 3, 53];
    let kn = [59, 61, 67, 71];
    let phi = [2, 4, 6, 8];
    let theta = [9, 10, 12, 14];
    let alpha = [15, 16, 18, 20];
    let beta = [21, 22, 24, 25];

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

    let actual = cwyz_bridge_claim_step(
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
    assert!(verify_cwyz_bridge_claim_step(
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
    for limb in 0..4 {
        assert!(!verify_cwyz_bridge_claim_step(
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
}

#[test]
fn production_horner_and_pin_match_ascending_power_sum() {
    let raw = [[GOLDILOCKS_P - 1, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]];
    for n in 0..=raw.len() {
        let coeffs: Vec<_> = raw[..n].iter().copied().map(ext).collect();
        for z in [0, 1, 2, GOLDILOCKS_P - 1, u64::MAX] {
            let mut power = 1u64;
            let mut expected = [0; 4];
            for &c in &raw[..n] {
                expected = add(expected, scale(c, power));
                power = (power as u128 * z as u128 % GOLDILOCKS_P as u128) as u64;
            }
            assert_eq!(limbs(eval_univariate_ext4_at_base(&coeffs, z)), expected);
            assert_eq!(limbs(eval_ext4_univariate_at_base(&coeffs, z)), expected);
            assert!(verify_ext4_univariate_at_base_pin(
                &coeffs,
                z,
                ext(expected),
            ));
            for limb in 0..4 {
                assert!(!verify_ext4_univariate_at_base_pin(
                    &coeffs,
                    z,
                    ext(perturb_limb(expected, limb)),
                ));
            }
        }
    }
}
