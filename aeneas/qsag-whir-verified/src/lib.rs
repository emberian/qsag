#![no_std]
#![forbid(unsafe_code)]

/// Canonical Goldilocks prime `p = 2^64 - 2^32 + 1`.
pub const GOLDILOCKS_P: u64 = 0xffff_ffff_0000_0001;

/// Maximum 64-bit unsigned word (`u64::MAX`), used for explicit overflow-free guards.
pub const MAX_U64_WORD: u64 = 0xffff_ffff_ffff_ffff;

/// Prefix-free internal-node domain tag (`0x00`) under `QSAG.PCS.CANOPY/v2`.
pub const TAG_CANOPY_MERKLE_INTERNAL: u8 = 0;

/// Strict canonical limb decoder: accepts `x` iff `x < GOLDILOCKS_P`.
pub const fn decode_canonical_u64(x: u64) -> Option<u64> {
    if x < GOLDILOCKS_P { Some(x) } else { None }
}

/// Quartic extension element in polynomial basis `[1, u, u^2, u^3]` with `u^4 = 7`.
pub struct Ext4 {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}

/// Strict canonical `Ext4` decoder: accepts iff every limb is `< GOLDILOCKS_P`.
pub const fn decode_canonical_ext4(a: u64, b: u64, c: u64, d: u64) -> Option<Ext4> {
    if a < GOLDILOCKS_P && b < GOLDILOCKS_P && c < GOLDILOCKS_P && d < GOLDILOCKS_P {
        Some(Ext4 { a, b, c, d })
    } else {
        None
    }
}

pub fn add(a: u64, b: u64) -> u64 {
    ((a as u128 + b as u128) % GOLDILOCKS_P as u128) as u64
}

pub fn sub(a: u64, b: u64) -> u64 {
    let reduced_b = b % GOLDILOCKS_P;
    add(a, GOLDILOCKS_P - reduced_b)
}

pub fn mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % GOLDILOCKS_P as u128) as u64
}

pub fn ext_eq(x: Ext4, y: Ext4) -> bool {
    x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d
}

pub fn ext_add(x: Ext4, y: Ext4) -> Ext4 {
    Ext4 {
        a: add(x.a, y.a),
        b: add(x.b, y.b),
        c: add(x.c, y.c),
        d: add(x.d, y.d),
    }
}

pub fn ext_sub(x: Ext4, y: Ext4) -> Ext4 {
    Ext4 {
        a: sub(x.a, y.a),
        b: sub(x.b, y.b),
        c: sub(x.c, y.c),
        d: sub(x.d, y.d),
    }
}

pub fn ext_scale(x: Ext4, y: u64) -> Ext4 {
    Ext4 {
        a: mul(x.a, y),
        b: mul(x.b, y),
        c: mul(x.c, y),
        d: mul(x.d, y),
    }
}

pub fn ext_mul(x: Ext4, y: Ext4) -> Ext4 {
    Ext4 {
        a: add(
            mul(x.a, y.a),
            mul(7, add(add(mul(x.b, y.d), mul(x.c, y.c)), mul(x.d, y.b))),
        ),
        b: add(
            add(mul(x.a, y.b), mul(x.b, y.a)),
            mul(7, add(mul(x.c, y.d), mul(x.d, y.c))),
        ),
        c: add(
            add(add(mul(x.a, y.c), mul(x.b, y.b)), mul(x.c, y.a)),
            mul(7, mul(x.d, y.d)),
        ),
        d: add(
            add(mul(x.a, y.d), mul(x.b, y.c)),
            add(mul(x.c, y.b), mul(x.d, y.a)),
        ),
    }
}

pub fn affine_combine(even: Ext4, odd: Ext4, alpha: Ext4) -> Ext4 {
    ext_add(odd, ext_mul(alpha, even))
}

pub fn duet_fold(v0: Ext4, v1: Ext4, inv_two_y0: u64, inv_two: u64, alpha: Ext4) -> Ext4 {
    let even = ext_scale(
        ext_add(
            Ext4 {
                a: v0.a,
                b: v0.b,
                c: v0.c,
                d: v0.d,
            },
            Ext4 {
                a: v1.a,
                b: v1.b,
                c: v1.c,
                d: v1.d,
            },
        ),
        inv_two,
    );
    let odd = ext_scale(ext_sub(v0, v1), inv_two_y0);
    affine_combine(even, odd, alpha)
}

pub fn verify_affine_duet_fold_step(
    v0: Ext4,
    v1: Ext4,
    inv_two_y0: u64,
    inv_two: u64,
    alpha: Ext4,
    claimed_folded: Ext4,
) -> bool {
    ext_eq(
        duet_fold(v0, v1, inv_two_y0, inv_two, alpha),
        claimed_folded,
    )
}

/// Asymmetric monomial coset duet fold (`odd + (alpha + beta * y0^2) * (even + theta * odd)`).
#[allow(clippy::too_many_arguments)]
pub fn cwyz_duet_fold(
    v0: Ext4,
    v1: Ext4,
    inv_two_y0: u64,
    inv_two: u64,
    y0_sq: u64,
    theta: Ext4,
    alpha: Ext4,
    beta: Ext4,
) -> Ext4 {
    let even = ext_scale(
        ext_add(
            Ext4 {
                a: v0.a,
                b: v0.b,
                c: v0.c,
                d: v0.d,
            },
            Ext4 {
                a: v1.a,
                b: v1.b,
                c: v1.c,
                d: v1.d,
            },
        ),
        inv_two,
    );
    let odd = ext_scale(ext_sub(v0, v1), inv_two_y0);
    let mixed = ext_add(
        even,
        ext_mul(
            theta,
            Ext4 {
                a: odd.a,
                b: odd.b,
                c: odd.c,
                d: odd.d,
            },
        ),
    );
    affine_combine(mixed, odd, ext_add(alpha, ext_scale(beta, y0_sq)))
}

/// Production PCS entry point, in polynomial basis `[1, u, u^2, u^3]`.
/// The PCS tower adapter must permute wire limbs `[0, 2, 1, 3]`.
#[inline]
#[allow(clippy::too_many_arguments)]
pub fn fold_duet_affine_ext4(
    v0: Ext4,
    v1: Ext4,
    inv_two_xk: u64,
    inv_two: u64,
    xk_sq: u64,
    theta: Ext4,
    alpha: Ext4,
    beta: Ext4,
) -> Ext4 {
    cwyz_duet_fold(v0, v1, inv_two_xk, inv_two, xk_sq, theta, alpha, beta)
}

/// Exact acceptance gate for one asymmetric coset duet fold step.
#[allow(clippy::too_many_arguments)]
pub fn verify_cwyz_duet_fold_step(
    v0: Ext4,
    v1: Ext4,
    inv_two_y0: u64,
    inv_two: u64,
    y0_sq: u64,
    theta: Ext4,
    alpha: Ext4,
    beta: Ext4,
    claimed_folded: Ext4,
) -> bool {
    ext_eq(
        cwyz_duet_fold(v0, v1, inv_two_y0, inv_two, y0_sq, theta, alpha, beta),
        claimed_folded,
    )
}

/// Dual linear-functional sumcheck bridge step:
/// `f = w0 + phi * w1`, `g = w2 + phi * (claim - w0)`,
/// `next = (g + alpha * (f + theta * g)) + beta * (w3 + theta * w4)`.
#[allow(clippy::too_many_arguments)]
pub fn cwyz_bridge_claim_step(
    w0: Ext4,
    w1: Ext4,
    w2: Ext4,
    w3: Ext4,
    w4: Ext4,
    claim: Ext4,
    phi: Ext4,
    theta: Ext4,
    alpha: Ext4,
    beta: Ext4,
) -> Ext4 {
    let w0_copy = Ext4 {
        a: w0.a,
        b: w0.b,
        c: w0.c,
        d: w0.d,
    };
    let phi_copy = Ext4 {
        a: phi.a,
        b: phi.b,
        c: phi.c,
        d: phi.d,
    };
    let f = ext_add(w0, ext_mul(phi, w1));
    let g = ext_add(w2, ext_mul(phi_copy, ext_sub(claim, w0_copy)));
    let g_copy = Ext4 {
        a: g.a,
        b: g.b,
        c: g.c,
        d: g.d,
    };
    let theta_copy = Ext4 {
        a: theta.a,
        b: theta.b,
        c: theta.c,
        d: theta.d,
    };
    let core_term = ext_add(g, ext_mul(alpha, ext_add(f, ext_mul(theta, g_copy))));
    let shift_term = ext_mul(beta, ext_add(w3, ext_mul(theta_copy, w4)));
    ext_add(core_term, shift_term)
}

/// Exact acceptance gate for one dual linear-functional sumcheck bridge round.
#[allow(clippy::too_many_arguments)]
pub fn verify_cwyz_bridge_claim_step(
    w0: Ext4,
    w1: Ext4,
    w2: Ext4,
    w3: Ext4,
    w4: Ext4,
    claim: Ext4,
    phi: Ext4,
    theta: Ext4,
    alpha: Ext4,
    beta: Ext4,
    claimed_next: Ext4,
) -> bool {
    ext_eq(
        cwyz_bridge_claim_step(w0, w1, w2, w3, w4, claim, phi, theta, alpha, beta),
        claimed_next,
    )
}

/// Evaluate compressed quadratic sumcheck wire `[c0, c2]` at challenge `r`, reconstructing
/// `c1 = sum_claim - 2 * c0 - c2` so `g(0) + g(1) == sum_claim` holds by construction.
pub fn eval_quadratic_sumcheck_wire(c0: Ext4, c2: Ext4, sum_claim: Ext4, r: Ext4) -> Ext4 {
    let c0_a = Ext4 {
        a: c0.a,
        b: c0.b,
        c: c0.c,
        d: c0.d,
    };
    let c0_b = Ext4 {
        a: c0.a,
        b: c0.b,
        c: c0.c,
        d: c0.d,
    };
    let c2_a = Ext4 {
        a: c2.a,
        b: c2.b,
        c: c2.c,
        d: c2.d,
    };
    let r_a = Ext4 {
        a: r.a,
        b: r.b,
        c: r.c,
        d: r.d,
    };
    let two_c0 = ext_add(c0, c0_a);
    let c1 = ext_sub(ext_sub(sum_claim, two_c0), c2);
    ext_add(ext_mul(ext_add(ext_mul(c2_a, r), c1), r_a), c0_b)
}

/// Accumulate one affine batching cascade claim step `acc + w0 * eval_at_point + w1 * shifted_eval`.
pub fn affine_cascade_claim_step(
    acc: Ext4,
    w0: Ext4,
    w1: Ext4,
    eval_at_point: Ext4,
    shifted_eval: Ext4,
) -> Ext4 {
    ext_add(
        ext_add(acc, ext_mul(w0, eval_at_point)),
        ext_mul(w1, shifted_eval),
    )
}

/// Evaluate ascending-degree univariate `Ext4` polynomial `coeffs` at base-field point `z` via Horner's rule.
pub fn eval_ext4_univariate_at_base(coeffs: &[Ext4], z: u64) -> Ext4 {
    let mut acc = Ext4 {
        a: 0,
        b: 0,
        c: 0,
        d: 0,
    };
    let mut rem = coeffs.len();
    while rem > 0 {
        rem -= 1;
        let c = &coeffs[rem];
        acc = ext_add(
            ext_scale(acc, z),
            Ext4 {
                a: c.a,
                b: c.b,
                c: c.c,
                d: c.d,
            },
        );
    }
    acc
}

/// Production PCS Horner entry point; coefficients are in ascending degree.
/// Elements use polynomial basis; the PCS tower adapter permutes `[0, 2, 1, 3]`.
#[inline]
pub fn eval_univariate_ext4_at_base(coeffs: &[Ext4], z: u64) -> Ext4 {
    eval_ext4_univariate_at_base(coeffs, z)
}

/// Exact acceptance gate pinning an early-stop univariate `Ext4` polynomial at base-field query `z`.
pub fn verify_ext4_univariate_at_base_pin(coeffs: &[Ext4], z: u64, expected: Ext4) -> bool {
    ext_eq(eval_ext4_univariate_at_base(coeffs, z), expected)
}

/// Stage proof-of-work low-bit mask gate (`pow_bits <= 32` and low `pow_bits` of `word` are zero).
pub fn verify_stage_pow_mask(word: u64, pow_bits: u32) -> bool {
    if pow_bits > 32 {
        return false;
    }
    word & ((1u64 << pow_bits) - 1) == 0
}

/// Exact limb-slice equality gate for OOD and terminal sumcheck claim pinning.
pub fn verify_ood_pin_eq(expected: &[u64], supplied: &[u64]) -> bool {
    if expected.len() != supplied.len() {
        return false;
    }
    let mut i = 0;
    while i < expected.len() {
        if expected[i] != supplied[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// Canonical query-fiber index reduction (`None` iff `groups == 0`).
pub fn canonical_query_group_idx(raw_idx: u64, groups: u64) -> Option<u64> {
    if groups == 0 {
        None
    } else {
        Some(raw_idx % groups)
    }
}

pub struct MerklePair {
    pub tag: u8,
    pub left: [u8; 32],
    pub right: [u8; 32],
}

/// Bounded Merkle internal-node preimage ordering (`tag = 0x00` matching `CANOPY` internal framing).
pub fn step_merkle_pair_order(
    idx: u64,
    level: u32,
    node: [u8; 32],
    sibling: [u8; 32],
) -> Option<MerklePair> {
    if level >= 64 {
        return None;
    }
    if (idx >> level) & 1 == 0 {
        Some(MerklePair {
            tag: TAG_CANOPY_MERKLE_INTERNAL,
            left: node,
            right: sibling,
        })
    } else {
        Some(MerklePair {
            tag: TAG_CANOPY_MERKLE_INTERNAL,
            left: sibling,
            right: node,
        })
    }
}

/// Overflow-free per-shard and global quorum weight check:
/// verifies `counts.len() == minimums.len() > 0`, `minimum_global > 0`,
/// `0 < minimums[i] <= counts[i]` for every shard, neither `sum(counts)` nor `sum(minimums)`
/// overflows `u64`, and `sum(counts) >= minimum_global`.
pub fn checked_quorum_sum(counts: &[u64], minimums: &[u64], minimum_global: u64) -> Option<u64> {
    if counts.is_empty() || counts.len() != minimums.len() || minimum_global == 0 {
        return None;
    }
    let mut total: u64 = 0;
    let mut min_total: u64 = 0;
    let mut i = 0;
    while i < counts.len() {
        let c = counts[i];
        let m = minimums[i];
        if m == 0 || c < m {
            return None;
        }
        if total > MAX_U64_WORD - c {
            return None;
        }
        total += c;
        if min_total > MAX_U64_WORD - m {
            return None;
        }
        min_total += m;
        i += 1;
    }
    if total < minimum_global {
        None
    } else {
        Some(total)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(a: u64, b: u64, c: u64, d: u64) -> Ext4 {
        Ext4 { a, b, c, d }
    }

    #[test]
    fn guards_and_extension_boundary_cases() {
        assert_eq!(decode_canonical_u64(0), Some(0));
        assert_eq!(
            decode_canonical_u64(GOLDILOCKS_P - 1),
            Some(GOLDILOCKS_P - 1)
        );
        assert_eq!(decode_canonical_u64(GOLDILOCKS_P), None);
        assert_eq!(decode_canonical_u64(u64::MAX), None);
        assert!(decode_canonical_ext4(0, 1, 2, GOLDILOCKS_P - 1).is_some());
        assert!(decode_canonical_ext4(GOLDILOCKS_P, 0, 0, 0).is_none());
        assert!(decode_canonical_ext4(0, GOLDILOCKS_P, 0, 0).is_none());
        assert!(decode_canonical_ext4(0, 0, GOLDILOCKS_P, 0).is_none());
        assert!(decode_canonical_ext4(0, 0, 0, GOLDILOCKS_P).is_none());

        assert_eq!(add(GOLDILOCKS_P - 1, 1), 0);
        assert_eq!(mul(GOLDILOCKS_P - 1, GOLDILOCKS_P - 1), 1);
        assert_eq!(sub(0, 1), GOLDILOCKS_P - 1);
        assert!(ext_eq(ext_mul(e(0, 0, 0, 1), e(0, 1, 0, 0)), e(7, 0, 0, 0)));

        for bits in 0..=32 {
            assert!(verify_stage_pow_mask(0, bits));
            assert!(verify_stage_pow_mask(1u64 << bits, bits));
            if bits > 0 {
                assert!(!verify_stage_pow_mask(1, bits));
            }
        }
        assert!(!verify_stage_pow_mask(0, 33));
        assert!(!verify_stage_pow_mask(0, u32::MAX));

        assert_eq!(canonical_query_group_idx(7, 0), None);
        assert_eq!(canonical_query_group_idx(u64::MAX, 7), Some(u64::MAX % 7));
        assert!(verify_ood_pin_eq(&[1, 2], &[1, 2]));
        assert!(!verify_ood_pin_eq(&[1, 2], &[2, 1]));
        assert!(!verify_ood_pin_eq(&[1, 2], &[1]));

        let p0 = step_merkle_pair_order(2, 0, [1; 32], [2; 32]).unwrap();
        assert_eq!((p0.tag, p0.left, p0.right), (0, [1; 32], [2; 32]));
        let p1 = step_merkle_pair_order(2, 1, [1; 32], [2; 32]).unwrap();
        assert_eq!((p1.tag, p1.left, p1.right), (0, [2; 32], [1; 32]));
        assert!(step_merkle_pair_order(0, 64, [1; 32], [2; 32]).is_none());
    }

    #[test]
    fn bridge_horner_and_quorum_sum_gates() {
        // Quadratic wire: g(0) + g(1) == sum_claim
        let g0 = eval_quadratic_sumcheck_wire(
            e(3, 4, 5, 6),
            e(9, 1, 2, 3),
            e(20, 30, 40, 50),
            e(0, 0, 0, 0),
        );
        let g1 = eval_quadratic_sumcheck_wire(
            e(3, 4, 5, 6),
            e(9, 1, 2, 3),
            e(20, 30, 40, 50),
            e(1, 0, 0, 0),
        );
        assert!(ext_eq(ext_add(g0, g1), e(20, 30, 40, 50)));

        // Horner base evaluation: c0 + c1*z + c2*z^2 at z = 3
        let coeffs = [e(2, 1, 0, 0), e(4, 0, 1, 0), e(5, 0, 0, 1)];
        let expected = e(2 + 4 * 3 + 5 * 9, 1, 3, 9);
        assert!(verify_ext4_univariate_at_base_pin(&coeffs, 3, expected));
        assert!(!verify_ext4_univariate_at_base_pin(
            &coeffs,
            3,
            e(0, 0, 0, 0)
        ));

        // Bridge claim step acceptance and perturbation rejection
        let next = cwyz_bridge_claim_step(
            e(2, 0, 0, 0),
            e(3, 0, 0, 0),
            e(5, 0, 0, 0),
            e(7, 0, 0, 0),
            e(11, 0, 0, 0),
            e(13, 0, 0, 0),
            e(17, 0, 0, 0),
            e(19, 0, 0, 0),
            e(23, 0, 0, 0),
            e(29, 0, 0, 0),
        );
        assert!(verify_cwyz_bridge_claim_step(
            e(2, 0, 0, 0),
            e(3, 0, 0, 0),
            e(5, 0, 0, 0),
            e(7, 0, 0, 0),
            e(11, 0, 0, 0),
            e(13, 0, 0, 0),
            e(17, 0, 0, 0),
            e(19, 0, 0, 0),
            e(23, 0, 0, 0),
            e(29, 0, 0, 0),
            Ext4 {
                a: next.a,
                b: next.b,
                c: next.c,
                d: next.d,
            },
        ));
        assert!(!verify_cwyz_bridge_claim_step(
            e(2, 0, 0, 0),
            e(3, 0, 0, 0),
            e(5, 0, 0, 0),
            e(7, 0, 0, 0),
            e(11, 0, 0, 0),
            e(13, 0, 0, 0),
            e(17, 0, 0, 0),
            e(19, 0, 0, 0),
            e(23, 0, 0, 0),
            e(29, 0, 0, 0),
            Ext4 {
                a: add(next.a, 1),
                b: next.b,
                c: next.c,
                d: next.d,
            },
        ));

        // Checked quorum sum: exact acceptance and overflow / under-threshold rejection
        assert_eq!(checked_quorum_sum(&[4, 4, 4], &[3, 4, 2], 12), Some(12));
        assert_eq!(checked_quorum_sum(&[4, 4, 4], &[3, 4, 2], 13), None);
        assert_eq!(checked_quorum_sum(&[3, 4], &[4, 4], 7), None);
        assert_eq!(checked_quorum_sum(&[u64::MAX, 1], &[1, 1], 2), None);
        assert_eq!(
            checked_quorum_sum(&[u64::MAX, u64::MAX], &[u64::MAX, 1], 2),
            None
        );
        assert_eq!(checked_quorum_sum(&[], &[], 1), None);
        assert_eq!(checked_quorum_sum(&[4], &[4], 0), None);
    }
}
