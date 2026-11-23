//! Shared integer-logarithm, Reed-Solomon Johnson / `[CWYZ26]` list-decoding, and Merkle sibling
//! accounting primitives used by [`super::v2::bounds`] (`[DKT26]` `< 2^{-128}` QROM Quintic `Fp5`).
//!
//! All quantities are integers. An error `eps` is carried as a lower bound on `-log2(eps)`
//! in thousandths of a bit ([`MilliBits`]); logarithms round against the claim.

/// A lower bound on `-log2` of a probability, in thousandths of a bit.
pub type MilliBits = i64;

/// `floor(1000 log2(p^5 - 1)) - 1` for `p = 2^64 - 2^32 + 1`: every nonzero Quintic `Fp5`
/// challenge set has at least `2^319.998` elements.
pub const CHALLENGE_SET_MILLIBITS: MilliBits = 319_998;

/// Default stage list cap for `[CWYZ26]` Theorem 5.1 stage witnesses.
pub const STAGE_LIST_CAP: u128 = 16_384;

/// A lower bound on `1000 log2(x)` within `0.002` of it; `x > 0`.
pub fn log2_lo(x: u128) -> MilliBits {
    assert!(x > 0);
    let lz = x.leading_zeros();
    let exponent = (127 - lz) as i64;
    let mut y = (x << lz) >> 64;
    let mut frac = 0i64;
    for bit in (0..24).rev() {
        y = (y * y) >> 63;
        if y >= 1u128 << 64 {
            y >>= 1;
            frac |= 1 << bit;
        }
    }
    exponent * 1000 + (frac * 1000) / (1 << 24)
}

/// An upper bound on `1000 log2(x)`; `x > 0`.
pub fn log2_hi(x: u128) -> MilliBits {
    if x.is_power_of_two() {
        log2_lo(x)
    } else {
        log2_lo(x) + 2
    }
}

/// An upper bound on `1000 log2(1 + 2^(-d / 1000))` for `d >= 0`: `log2(1 + x) <= x / ln 2`
/// with `x` rounded up to the next eighth of a bit, and never more than one bit.
pub(crate) fn log2_one_plus(d: MilliBits) -> MilliBits {
    const EIGHTHS: [i64; 8] = [1000, 918, 841, 772, 708, 649, 595, 546];
    assert!(d >= 0);
    let steps = d / 125;
    let shift = steps / 8;
    if shift >= 40 {
        return 1;
    }
    (((1443 * EIGHTHS[(steps % 8) as usize] + 999) / 1000) >> shift).min(999) + 1
}

/// A lower bound on `-log2(2^(-a / 1000) + 2^(-b / 1000))`.
pub(crate) fn sum_bits(a: MilliBits, b: MilliBits) -> MilliBits {
    a.min(b) - log2_one_plus((a - b).abs())
}

/// `-log2` of the probability that `queries` distinct uniform positions out of `n` all fall in
/// a set of `agreement` positions; `None` when that probability is zero.
pub fn query_bits(n: u128, agreement: u128, queries: usize) -> Option<MilliBits> {
    if agreement < queries as u128 {
        return None;
    }
    assert!(agreement <= n);
    let mut mantissa = 1u128 << 64;
    let mut exponent = 0i64;
    for i in 0..queries as u128 {
        mantissa = (mantissa * (agreement - i)).div_ceil(n - i);
        while mantissa < 1u128 << 63 {
            mantissa *= 2;
            exponent += 1;
        }
    }
    Some(exponent * 1000 + 64_000 - log2_hi(mantissa))
}

/// Johnson list bound (`[CWYZ26]` Lemma 3.2 with `a = agree / n`, `b = d / n`): the number of
/// polynomials of degree at most `d` agreeing with one word on `agree` of `n` positions.
/// `None` at or below the Johnson radius.
pub fn johnson_list(n: u128, agree: u128, d: u128) -> Option<u128> {
    let denominator = (agree * agree).checked_sub(n * d).filter(|&v| v > 0)?;
    Some(n * agree.checked_sub(d)? / denominator)
}

/// `[CWYZ26]` interpolation inequality (4.5) for multiplicity `m` and degree `big_d`, with `M`
/// from (4.1): `(M, lhs - rhs)`. The inequality holds when the margin is positive.
pub fn interpolation_margin(
    n: u128,
    d: u128,
    a: u128,
    m: u128,
    big_d: u128,
) -> Option<(u128, i128)> {
    let big_m = big_d.min((m * a).checked_sub(big_d + 1)? / d);
    if big_m == 0 {
        return None;
    }
    let lhs: u128 = (0..=big_m)
        .map(|j| (m * a - big_d - d * j) * (big_d - j + 1))
        .sum();
    let rhs: u128 = n
        * (0..=big_m.min(m - 1))
            .map(|s| (m - s) * (big_d - s + 1))
            .sum::<u128>();
    Some((big_m, lhs as i128 - rhs as i128))
}

/// Whether (4.5) holds; returns `M`.
pub fn interpolation_holds(n: u128, d: u128, a: u128, m: u128, big_d: u128) -> Option<u128> {
    interpolation_margin(n, d, a, m, big_d)
        .filter(|&(_, margin)| margin > 0)
        .map(|(big_m, _)| big_m)
}

/// The smallest `D` found for which (4.5) holds at multiplicity `m`, with its `M`.
fn interpolation_witness(n: u128, d: u128, a: u128, m: u128) -> Option<(u128, u128)> {
    let margin = |big_d: u128| interpolation_margin(n, d, a, m, big_d).map_or(i128::MIN, |v| v.1);
    let (mut lo, mut hi) = (
        1u128,
        ((2 * m + 1) * (2 * m + 1) * n).div_ceil(12 * d).max(2),
    );
    while hi - lo > 2 {
        let third = (hi - lo) / 3;
        let (left, right) = (lo + third, hi - third);
        if margin(left) < margin(right) {
            lo = left + 1;
        } else {
            hi = right - 1;
        }
    }
    let peak = (lo..=hi).max_by_key(|&v| margin(v))?;
    if margin(peak) <= 0 {
        return None;
    }
    let (mut lo, mut hi) = (1u128, peak);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if margin(mid) > 0 {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    interpolation_holds(n, d, a, m, lo).map(|big_m| (lo, big_m))
}

/// One application of `[CWYZ26]` Theorem 5.1 with linear claims: words on `n` points, output
/// degree `d`, agreement threshold `a`, with `B = a - 1`. Returns `l + 2 l0 + 1`.
pub fn affine_fold_numerator(n: u128, d: u128, a: u128) -> Option<u128> {
    let b = a.checked_sub(1)?;
    let list = johnson_list(n, b, d + 1)?;
    let list0 = johnson_list(n, b, d)?;
    let mut m = 1u128;
    while m <= 256 {
        if let Some((big_d, big_m)) = interpolation_witness(n, d, a, m) {
            let nonpersistent = (2 * log2_hi(big_d))
                .max(2000 + 2 * log2_hi(d) + 2 * log2_hi(big_m) + 3 * log2_hi(big_d))
                + 1000
                + 2 * log2_hi(n);
            if nonpersistent < CHALLENGE_SET_MILLIBITS {
                return Some(list + 2 * list0 + 1);
            }
        }
        m *= 2;
    }
    None
}

/// Bounds for one WHIR stage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StageBound {
    pub blowup: usize,
    pub step_vars: usize,
    pub queries: usize,
    pub fibers: u128,
    pub agreement: u128,
    pub word_list: u128,
    pub list: u128,
    pub query_bits: Option<MilliBits>,
    pub fold_bits: MilliBits,
}

fn stage_lists(fibers: u128, blowup: u128, folds: u32, a: u128) -> Option<u128> {
    let mut worst = 0u128;
    for level in 0..folds {
        let scale = 1u128 << level;
        let n = fibers * scale;
        worst = worst.max(affine_fold_numerator(n, n / blowup + 2, a * scale)?);
    }
    (u128::from(folds) * worst + 1 < STAGE_LIST_CAP).then_some(worst)
}

/// The stage at agreement threshold `agreement`, or at the smallest feasible one.
pub(crate) fn stage_bound(
    blowup: usize,
    step_vars: usize,
    queries: usize,
    rem_after: usize,
    agreement: Option<u128>,
) -> Option<StageBound> {
    let fibers = (blowup as u128) << rem_after;
    let folds = step_vars as u32;
    let top = fibers.checked_sub(u128::from(folds))?;
    let feasible = |a: u128| stage_lists(fibers, blowup as u128, folds, a);
    let agreement = match agreement {
        Some(a) => a.min(top),
        None => {
            feasible(top)?;
            let (mut lo, mut hi) = (1u128, top);
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                if feasible(mid).is_some() {
                    hi = mid;
                } else {
                    lo = mid + 1;
                }
            }
            lo
        }
    };
    let list = feasible(agreement)?;
    let points = fibers << folds;
    Some(StageBound {
        blowup,
        step_vars,
        queries,
        fibers,
        agreement,
        word_list: johnson_list(points, agreement << folds, points / blowup as u128 + 2)?,
        list,
        query_bits: query_bits(
            fibers,
            agreement + u128::from(folds),
            queries.min(fibers as usize),
        ),
        fold_bits: CHALLENGE_SET_MILLIBITS - log2_hi(list),
    })
}

/// Smallest number of distinct fiber queries at which a stage has query error at most
/// `2^-target` before grinding, at the smallest agreement threshold with a witness.
pub fn min_queries(
    blowup: usize,
    step_vars: usize,
    rem_after: usize,
    target: MilliBits,
) -> Option<usize> {
    let st = stage_bound(blowup, step_vars, 1, rem_after, None)?;
    let agree = st.agreement + step_vars as u128;
    let meets = |q: usize| query_bits(st.fibers, agree, q).is_none_or(|bits| bits >= target);
    let (mut lo, mut hi) = (1usize, st.fibers as usize);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if meets(mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    Some(lo)
}

/// Authentication siblings of `queries` leaves in a tree of `2^log_leaves` leaves, at most.
pub(crate) fn siblings(queries: usize, log_leaves: usize) -> usize {
    if queries >> log_leaves != 0 {
        return 0;
    }
    queries * (log_leaves - queries.ilog2() as usize)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_log2_and_query_bounds_are_conservative() {
        for k in 0..=64u32 {
            assert_eq!(log2_lo(1u128 << k), 1000 * i64::from(k));
            assert_eq!(log2_hi(1u128 << k), 1000 * i64::from(k));
        }
        assert!(log2_lo(3) <= 1584 && log2_hi(3) >= 1585);
        // Exact `-1000 * log2(prod_{i=0..9} (512 - i) / (1024 - i)) = 10_064.355...`;
        // `query_bits` rounds every division and logarithm conservatively downward to `10_062`.
        assert_eq!(query_bits(1024, 512, 10), Some(10_062));
        assert_eq!(query_bits(16, 3, 4), None);
        assert!(min_queries(4, 6, 18, 256_000).is_some());
    }
}
