use qsag_whir_verified::{Ext4, GOLDILOCKS_P, eval_univariate_ext4_at_base, fold_duet_affine_ext4};

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

#[test]
fn production_fold_recovers_coset_components() {
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
        for even in [[0; 4], [1, 2, 3, 4], [p - 1; 4]] {
            let odd = [p - 2, 5, 9, 13];
            let theta = [3, 7, p - 1, 11];
            let alpha = [17, p - 2, 19, 23];
            let beta = [29, 31, 37, 41];
            let yo = scale(odd, y);
            let v0 = add(even, yo);
            let v1 = add(even, yo.map(|v| if v == 0 { 0 } else { p - v }));
            let yy = (y as u128 * y as u128 % p as u128) as u64;
            let expected = add(
                odd,
                product(add(alpha, scale(beta, yy)), add(even, product(theta, odd))),
            );
            let actual = fold_duet_affine_ext4(
                ext(v0),
                ext(v1),
                iy as u64,
                inv_two,
                yy,
                ext(theta),
                ext(alpha),
                ext(beta),
            );
            assert_eq!(limbs(actual), expected);
        }
    }
}

#[test]
fn production_horner_matches_ascending_power_sum() {
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
        }
    }
}
