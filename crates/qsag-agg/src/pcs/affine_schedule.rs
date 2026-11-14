//! Exact finite witnesses for the canonical Johnson QROM folding schedule.
//! These certify stage query and affine-combiner bounds, not full PCS security.
use super::*;

// (variables, stage, A, m, D). B = A - 1. Exhaustively queried stages need no
// proximity witness. The degree d = n/B_i + 2 conservatively includes overflow.
const WITNESSES: &[(usize, usize, u128, u128, u128)] = &[
    (9, 1, 127, 1, 20),
    (10, 0, 329, 1, 14),
    (10, 1, 126, 1, 20),
    (11, 0, 328, 1, 14),
    (11, 1, 126, 1, 20),
    (12, 0, 579, 4, 75),
    (12, 1, 310, 4, 59),
    (12, 2, 174, 8, 139),
    (13, 0, 1091, 8, 143),
    (13, 1, 570, 16, 351),
    (13, 2, 173, 8, 135),
    (14, 0, 2119, 32, 863),
    (14, 1, 1092, 32, 860),
    (14, 2, 308, 32, 706),
    (15, 0, 4178, 64, 2079),
    (15, 1, 1091, 32, 844),
    (15, 2, 308, 32, 706),
    (16, 0, 8296, 128, 5567),
    (16, 1, 2137, 64, 2392),
    (16, 2, 580, 64, 1921),
    (17, 0, 8295, 128, 5503),
    (17, 1, 2137, 64, 2392),
    (17, 2, 307, 32, 691),
    (18, 0, 16531, 128, 7295),
    (18, 1, 4229, 64, 3418),
    (18, 2, 579, 64, 1890),
    (19, 0, 33003, 128, 10879),
    (19, 1, 8413, 64, 5471),
    (19, 2, 1124, 32, 1305),
    (20, 0, 65948, 128, 18111),
    (20, 1, 16782, 32, 3286),
    (20, 2, 2215, 32, 2149),
    (21, 0, 65947, 128, 18047),
    (21, 1, 16782, 32, 3286),
    (21, 2, 2215, 32, 2149),
    (22, 0, 131836, 128, 32511),
    (22, 1, 16781, 32, 3270),
    (22, 2, 2215, 32, 2149),
    (23, 0, 263614, 64, 14494),
    (23, 1, 33518, 32, 5870),
    (23, 2, 8759, 16, 2733),
    (23, 3, 2254, 32, 2672),
    (24, 0, 527170, 64, 27164),
    (24, 1, 66992, 32, 11069),
    (24, 2, 17484, 16, 5228),
    (24, 3, 4482, 16, 2067),
];

// Upper-bound the hypergeometric all-hit probability with a normalized dyadic
// rational. Every division rounds UP, so no floating-point/log approximation
// can turn a failing query budget into a passing one.
fn query_error_below_2pow_minus256(n: u128, agreement: u128, queries: usize) -> bool {
    if agreement < queries as u128 {
        return true;
    }
    let mut mantissa = 1u128 << 64;
    let mut exponent = 0;
    for i in 0..queries as u128 {
        mantissa = (mantissa * (agreement - i)).div_ceil(n - i);
        while mantissa < (1u128 << 63) {
            mantissa *= 2;
            exponent += 1;
        }
    }
    exponent >= 256 && mantissa < (1u128 << 64)
}

fn bits(n: u128) -> u32 {
    u128::BITS - n.leading_zeros()
}

#[test]
fn finite_johnson_witnesses_cover_every_canonical_stage() {
    let mut seen = 0;
    for nv in 2..=MAX_PCS_NUM_VARS {
        let schedule = WhirSecurityRegime::BciksJohnsonQrom128.schedule(nv);
        let mut rem = nv;
        for (stage, spec) in schedule.stages.iter().enumerate() {
            rem -= spec.step_vars;
            let n = (spec.blowup * (1usize << rem)) as u128;
            if spec.num_queries as u128 >= n {
                continue;
            }
            let &(_, _, a, m, big_d) = WITNESSES
                .iter()
                .find(|w| w.0 == nv && w.1 == stage)
                .expect("missing finite affine witness");
            seen += 1;
            let d = n / spec.blowup as u128 + 2;
            let b = a - 1;
            let big_m = big_d.min((m * a - big_d - 1) / d);
            assert!(big_m >= 1 && b < a && b * b > n * (d + 1));
            // CWYZ26 Eq. 4.5, evaluated as exact integer sums.
            let lhs: u128 = (0..=big_m)
                .map(|j| (m * a - big_d - d * j) * (big_d - j + 1))
                .sum();
            let rhs: u128 = n
                * (0..=big_m.min(m - 1))
                    .map(|s| (m - s) * (big_d - s + 1))
                    .sum::<u128>();
            assert!(lhs > rhs, "interpolation: nv={nv} stage={stage}");
            let loss = spec.step_vars as u128;
            assert!(
                query_error_below_2pow_minus256(n, a + loss, spec.num_queries),
                "query error: nv={nv} stage={stage}"
            );
            let list = n * (b - d - 1) / (b * b - n * (d + 1));
            let list0 = n * (a - 1 - d) / ((a - 1) * (a - 1) - n * d);
            // Upper bound the nonpersistent numerator, even dropping (A-B)^2.
            // loss * (D^2 + 4 d^2 M^2 D^3 n^2) < 2^255 < p^4,
            // hence its total contribution is < 1/p^4.
            let numerator_bits = (2 * bits(big_d))
                .max(2 + 2 * bits(d) + 2 * bits(big_m) + 3 * bits(big_d) + 2 * bits(n))
                + 1;
            assert!(bits(loss) + numerator_bits < 255);
            // Include one additional field-error unit per dual cross-term reduction.
            assert!(loss * (list + 2 * list0 + 1) + 1 < 2000);
        }
    }
    assert_eq!(seen, WITNESSES.len());
    // p^4 > 127^2 * 2^242 > 2000 * 2^245, certifying >245 stage
    // combiner bits for the bound above. This is not a protocol-wide union bound.
    let p = crate::field::GOLDILOCKS_PRIME as u128;
    assert!(p * p > 127 * (1u128 << 121));
}
