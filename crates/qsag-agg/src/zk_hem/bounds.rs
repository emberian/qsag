//! Concrete security accounting for the public Hem WHIR commitment ([`crate::pcs`]) and shared
//! integer-logarithm / Reed-Solomon proximity helpers used by [`super::v2::bounds`].
//!
//! All quantities are integers. An error `eps` is carried as a lower bound on `-log2(eps)`
//! in thousandths of a bit ([`MilliBits`]); logarithms round against the claim.
//!
//! Note: the quartic `zk-Hem v1` hiding wrapper (`81`-bit QROM digest ceiling, `128`-bit leaf
//! salts) has been retired in favor of quintic `zk-Hem v2` ([`super::v2::bounds`], `400`-bit
//! digests, `256`-bit salts + `32`-byte per-tree nonces, and DKT26 Theorem 5.12). Only the
//! non-hiding public WHIR opening report ([`pcs_report`]) and shared schedule bounds remain here.

use alloc::vec::Vec;

use super::protocol::{ROW_DEGREE, ROW_MASK_BITS};
use crate::pcs::{MAX_PCS_NUM_VARS, WhirSecurityRegime};

/// A lower bound on `-log2` of a probability, in thousandths of a bit.
pub type MilliBits = i64;

/// `floor(1000 log2 |F_{p^4} \ F_{p^2}|) - 1`: every challenge set used by public Hem WHIR
/// over `GoldilocksExt4` has at least `2^255.998` elements.
pub const CHALLENGE_SET_MILLIBITS: MilliBits = 255_998;

/// Cap on `folds * (l + 2 l0 + 1) + 1` per stage, the list budget the finite witnesses of
/// `pcs/affine_schedule.rs` certify.
pub const STAGE_LIST_CAP: u128 = 2000;

/// `log2(320)` rounded up: the constant `4 * 80` of `[CDHZ25]` Theorems A.1 and 6.9.
const QROM_RBR_CONST: MilliBits = 8_322;
/// `log2(6380)` rounded up. `8 * 160 * 4 + 4 * 240 = 6080` is the leading `t^3 / 2^sigma`
/// coefficient of `8 kappa_offline(2t + 1) + 4 kappa_online(t)` in `[CDHZ25]` Theorems 11.3
/// and 8.3; `300 >= 40 e^2` bounds collisions in the 256-bit transcript chain.
const QROM_MERKLE_CONST: MilliBits = 12_640;
/// Slack for `(t + k + 1)(t + k) <= t^2 (1 + 2^-7)^2` and for the verifier's own
/// `q_V + k <= 2^15` queries inside `kappa_online`, when `t >= 2^24`.
const QROM_ROUND_SLACK: MilliBits = 23;

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
/// degree `d`, agreement threshold `a`, with `B = a - 1`. Returns `l + 2 l0 + 1`, the
/// numerator over `|F|` of the bound (5.5) with the second term of (4.13) rounded up to
/// `1 / |F|`. `None` when no interpolation witness is found.
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

/// Parameters for a single-table public WHIR opening report that are not part of
/// [`WhirSecurityRegime`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    /// Length of Merkle digests and of the Fiat-Shamir chaining value.
    pub digest_bits: u32,
    /// Length of the per-leaf Stage-0 salt.
    pub salt_bits: u32,
    /// Grinding bits in front of algebraic challenges.
    pub algebraic_pow_bits: u32,
}

impl Params {
    /// Default parameters of a public `CanopyCommitment` opening.
    pub const PUBLIC: Self = Self {
        digest_bits: 256,
        salt_bits: 128,
        algebraic_pow_bits: 0,
    };
}

/// Size of a public relation: [`super::relation::Shape::log_rows`], `log2` of the variable
/// subcube and the number of public inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapeSize {
    pub log_rows: usize,
    pub var_bits: usize,
    pub num_public: usize,
}

/// A verifier round of public Hem WHIR.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Round {
    Sumcheck,
    OutOfDomain(usize),
    KernelFold(usize),
    AffineFold(usize),
    Query(usize),
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

/// The largest round-by-round error of a public WHIR opening and where it occurs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RbrBound {
    pub bits: MilliBits,
    pub round: Round,
    pub stage0_agreement: u128,
}

/// The security bounds of one regime for a public WHIR commitment opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecurityReport {
    pub regime: WhirSecurityRegime,
    pub params: Params,
    pub log_cells: usize,
    pub stages: Vec<StageBound>,
    pub rounds: usize,
    pub classical: RbrBound,
    pub ungrounded: RbrBound,
    pub proof_bytes: usize,
    pub digests: usize,
    pub merkle_hashes: u128,
    pub grinding_hashes: u128,
}

impl SecurityReport {
    fn digest_millibits(&self) -> MilliBits {
        1000 * i64::from(self.params.digest_bits) - i64::from(self.regime.uses_poseidon2_canopy())
    }

    fn classical_sum_bits(&self, log_t: MilliBits) -> MilliBits {
        sum_bits(
            self.classical.bits - log_t,
            self.digest_millibits() - 2000 - 2 * log_t,
        )
    }

    pub fn classical_error_bits(&self, log_queries: u32) -> MilliBits {
        assert!(log_queries >= 2);
        self.classical_sum_bits(1000 * i64::from(log_queries))
    }

    pub fn classical_work_bits(&self) -> MilliBits {
        let (mut lo, mut hi) = (
            0,
            self.classical
                .bits
                .min((self.digest_millibits() - 2000) / 2),
        );
        assert!(self.classical_sum_bits(lo) >= 0);
        while lo < hi {
            let mid = lo + (hi - lo + 1) / 2;
            if self.classical_sum_bits(mid) >= 0 {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        lo
    }

    fn qrom_sum_bits_with(&self, rbr_bits: MilliBits, log_t: MilliBits) -> MilliBits {
        sum_bits(
            rbr_bits - QROM_RBR_CONST - QROM_ROUND_SLACK - 2 * log_t,
            self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK - 3 * log_t,
        )
    }

    fn qrom_sum_bits(&self, log_t: MilliBits) -> MilliBits {
        self.qrom_sum_bits_with(self.ungrounded.bits, log_t)
    }

    pub fn qrom_error_bits(&self, log_queries: u32) -> MilliBits {
        assert!(log_queries >= 24 && self.rounds < 1 << 9);
        self.qrom_sum_bits(1000 * i64::from(log_queries))
    }

    pub fn qrom_work_terms(&self) -> (MilliBits, MilliBits) {
        (
            (self.ungrounded.bits - QROM_RBR_CONST - QROM_ROUND_SLACK) / 2,
            (self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK) / 3,
        )
    }

    pub fn qrom_work_bits(&self) -> MilliBits {
        let (rbr, digest) = self.qrom_work_terms();
        let (mut lo, mut hi) = (24_000, rbr.min(digest));
        assert!(self.rounds < 1 << 9 && self.qrom_sum_bits(lo) >= 0 && hi >= lo);
        while lo < hi {
            let mid = lo + (hi - lo + 1) / 2;
            if self.qrom_sum_bits(mid) >= 0 {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        lo
    }
}

/// Authentication siblings of `queries` leaves in a tree of `2^log_leaves` leaves, at most.
pub(crate) fn siblings(queries: usize, log_leaves: usize) -> usize {
    if queries >> log_leaves != 0 {
        return 0;
    }
    queries * (log_leaves - queries.ilog2() as usize)
}

/// The report for a public opening of a `log_cells`-variable commitment.
pub fn pcs_report(
    regime: WhirSecurityRegime,
    log_cells: usize,
    params: Params,
    size: Option<ShapeSize>,
) -> Option<SecurityReport> {
    if !(2..=MAX_PCS_NUM_VARS).contains(&log_cells) {
        return None;
    }
    if let Some(s) = size
        && (!(1..usize::BITS as usize).contains(&s.log_rows)
            || !(1..=log_cells).contains(&s.var_bits)
            || 4usize.checked_add(s.num_public).is_none())
    {
        return None;
    }
    let schedule = regime.schedule(log_cells);
    let mut rem = log_cells;
    let stages: Vec<StageBound> = schedule
        .stages
        .iter()
        .map(|spec| {
            rem -= spec.step_vars;
            stage_bound(spec.blowup, spec.step_vars, spec.num_queries, rem, None)
        })
        .collect::<Option<_>>()?;

    let evaluate = |pow: MilliBits, algebraic: MilliBits| -> RbrBound {
        let mut worst = (MilliBits::MAX, Round::Sumcheck);
        let mut note = |bits: MilliBits, round: Round| {
            if bits < worst.0 {
                worst = (bits, round);
            }
        };
        if let Some(size) = size {
            let degree = size
                .log_rows
                .max(ROW_DEGREE)
                .max((1 << ROW_MASK_BITS) - 1)
                .max(4 + size.num_public) as u128;
            note(
                CHALLENGE_SET_MILLIBITS - log2_hi(degree * stages[0].word_list) + algebraic,
                Round::Sumcheck,
            );
        }
        let mut rem = log_cells;
        for (i, st) in stages.iter().enumerate() {
            let degree = (1u128 << rem) + 2;
            let mut ood =
                2 * (CHALLENGE_SET_MILLIBITS - log2_hi(degree)) + 1000 - 2 * log2_hi(st.word_list);
            if i == 0 {
                ood = ood.min(CHALLENGE_SET_MILLIBITS - log2_hi(2 * st.word_list));
            }
            note(ood + algebraic, Round::OutOfDomain(i));
            note(
                CHALLENGE_SET_MILLIBITS - log2_hi(st.list) + algebraic,
                Round::KernelFold(i),
            );
            note(st.fold_bits + pow, Round::AffineFold(i));
            let batch = stages.get(i + 1).map_or(MilliBits::MAX, |next| {
                CHALLENGE_SET_MILLIBITS - log2_hi((st.queries as u128 + 2) * next.word_list) - 1000
            });
            let query = st.query_bits.map_or(MilliBits::MAX, |bits| bits - 1000);
            if query.min(batch) != MilliBits::MAX {
                note(query.min(batch) + pow, Round::Query(i));
            }
            rem -= st.step_vars;
        }
        RbrBound {
            bits: worst.0,
            round: worst.1,
            stage0_agreement: stages[0].agreement,
        }
    };
    let pow = 1000 * i64::from(regime.pow_bits());
    let algebraic = 1000 * i64::from(params.algebraic_pow_bits);
    let classical = evaluate(pow, algebraic);
    let ungrounded = evaluate(0, 0);

    let fold_vars = log_cells - schedule.early_stop_vars;
    let mut rounds = 2 * fold_vars + 2 * stages.len() + 1;
    let mut algebraic_rounds = fold_vars + stages.len() + 1;
    if let Some(size) = size {
        rounds += 6 + size.log_rows + size.var_bits;
        algebraic_rounds += 6 + size.log_rows + size.var_bits;
    }
    let digest_bytes = params.digest_bits.div_ceil(8) as usize;
    let mut digests = stages.len();
    let mut proof_bytes = digest_bytes + 1 + 64 + fold_vars * (5 * 32 + 8) + 4 + 8;
    proof_bytes += 4 + 32 * ((1usize << schedule.early_stop_vars) + 2);
    let mut merkle_hashes = 0u128;
    let mut rem = log_cells;
    for (i, st) in stages.iter().enumerate() {
        let log_leaves = rem + st.blowup.trailing_zeros() as usize - st.step_vars;
        let opened = st.queries.min(st.fibers as usize);
        let sib = siblings(opened, log_leaves);
        digests += sib;
        merkle_hashes += 2 * st.fibers;
        proof_bytes += 4 + 4 + digest_bytes * sib;
        proof_bytes += if i == 0 {
            opened * (params.salt_bits.div_ceil(8) as usize + 8 * (1usize << st.step_vars))
        } else {
            digest_bytes + 1 + 64 + 8 + opened * 32 * (1usize << st.step_vars)
        };
        rem -= st.step_vars;
    }
    let expected = |bits: u32| if bits == 0 { 0 } else { 1u128 << bits };
    let grinding_hashes = (fold_vars + stages.len()) as u128 * expected(regime.pow_bits())
        + algebraic_rounds as u128 * expected(params.algebraic_pow_bits);
    Some(SecurityReport {
        regime,
        params,
        log_cells,
        stages,
        rounds,
        classical,
        ungrounded,
        proof_bytes,
        digests,
        merkle_hashes,
        grinding_hashes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logarithms_bracket_the_true_value() {
        for (x, milli) in [
            (1u128, 0),
            (2, 1000),
            (3, 1584),
            (10, 3321),
            (1 << 100, 100_000),
        ] {
            assert!(log2_lo(x) <= milli + 1 && log2_lo(x) >= milli - 2, "{x}");
            assert!(log2_hi(x) >= milli && log2_hi(x) <= milli + 3, "{x}");
        }
        assert_eq!(log2_lo(823_543) / 10, 1965);
        assert_eq!(log2_lo(384) / 10, 858);
        assert!(log2_lo(320) < QROM_RBR_CONST && QROM_RBR_CONST <= log2_hi(320));
        assert!(log2_lo(6380) < QROM_MERKLE_CONST && QROM_MERKLE_CONST <= log2_hi(6380));
        let p = u128::from(crate::field::GOLDILOCKS_PRIME);
        assert!(p > (1u128 << 64) - (1u128 << 33));
        assert!(p * p > (1u128 << 127));
    }

    #[test]
    fn query_error_matches_the_hypergeometric_product() {
        let bits = query_bits(16, 6, 3).unwrap();
        assert!(bits <= log2_lo(28) && bits >= log2_lo(28) - 3, "{bits}");
        assert_eq!(query_bits(16, 2, 3), None);
        assert_eq!(query_bits(16, 16, 3), Some(0));
    }

    #[test]
    fn finite_witnesses_of_the_schedule_are_reproduced() {
        for (nv, stage, a, m, big_d) in [
            (20usize, 0usize, 65_948u128, 128u128, 18_111u128),
            (20, 1, 16_782, 32, 3_286),
            (20, 2, 2_215, 32, 2_149),
            (22, 0, 131_836, 128, 32_511),
            (24, 3, 4_482, 16, 2_067),
            (28, 0, 8_433_861, 128, 6_362),
        ] {
            let schedule = WhirSecurityRegime::BciksJohnsonQrom128.schedule(nv);
            let rem: usize = nv
                - schedule.stages[..=stage]
                    .iter()
                    .map(|s| s.step_vars)
                    .sum::<usize>();
            let spec = schedule.stages[stage];
            let n = (spec.blowup as u128) << rem;
            let d = n / spec.blowup as u128 + 2;
            assert!(
                interpolation_holds(n, d, a, m, big_d).is_some(),
                "{nv}/{stage}"
            );
            let found =
                stage_bound(spec.blowup, spec.step_vars, spec.num_queries, rem, None).unwrap();
            assert!(
                found.agreement <= a,
                "{nv}/{stage}: {} > {a}",
                found.agreement
            );
            assert!(found.query_bits.unwrap() >= 256_000, "{nv}/{stage}");
            assert!(spec.step_vars as u128 * found.list + 1 < STAGE_LIST_CAP);
        }
        assert_eq!(johnson_list(1 << 17, 65_536, 32_770), None);
        assert_eq!(affine_fold_numerator(1 << 17, 32_770, 65_537), None);
        assert_eq!(interpolation_holds(1 << 17, 32_770, 65_948, 1, 2), None);
    }

    #[test]
    fn stage_bounds_against_the_constants_asserted_by_the_regimes() {
        for regime in WhirSecurityRegime::ALL {
            let mut least = MilliBits::MAX;
            for log_cells in 17..=24 {
                let report = pcs_report(regime, log_cells, Params::PUBLIC, None).unwrap();
                for st in &report.stages {
                    least = least.min(st.query_bits.unwrap());
                    assert!(st.fold_bits > 245_000);
                }
                assert!(report.ungrounded.bits <= report.classical.bits.min(249_000));
            }
            let target = 1000 * i64::from(regime.pure_query_target_bits());
            if regime == WhirSecurityRegime::BciksJohnsonClassical128 {
                assert_eq!(least, 124_467);
                let mut short = 0usize;
                for log_cells in 17..=24 {
                    let mut rem = log_cells;
                    for spec in &regime.schedule(log_cells).stages {
                        rem -= spec.step_vars;
                        let need = min_queries(spec.blowup, spec.step_vars, rem, 128_000).unwrap();
                        short = short.max(need.saturating_sub(spec.num_queries));
                    }
                }
                assert_eq!(short, 2);
            } else {
                assert!(least >= target, "{regime:?}: {least}");
            }
        }
    }

    #[test]
    fn public_pcs_reports_are_pinned() {
        use WhirSecurityRegime as R;
        let small = ShapeSize {
            log_rows: 10,
            var_bits: 10,
            num_public: 5,
        };
        let r_small = pcs_report(R::BciksJohnsonQrom128, 18, Params::PUBLIC, Some(small)).unwrap();
        let r_deg15 = pcs_report(
            R::BciksJohnsonQrom128,
            18,
            Params::PUBLIC,
            Some(ShapeSize {
                log_rows: 15,
                var_bits: 10,
                num_public: 5,
            }),
        )
        .unwrap();
        assert_eq!(r_small.classical.bits, r_deg15.classical.bits);
        let public = pcs_report(R::BciksJohnsonQrom128, 21, Params::PUBLIC, None).unwrap();
        assert_eq!(
            (public.classical.bits, public.classical.round),
            (247_505, Round::KernelFold(1))
        );
        assert_eq!(
            (public.ungrounded.bits, public.ungrounded.round),
            (240_104, Round::Query(0))
        );
        assert_eq!(public.qrom_work_terms(), (115_879, 81_112));
        assert_eq!(public.qrom_work_bits(), 81_112);

        let at = |regime, cap| {
            pcs_report(regime, 21, Params::PUBLIC, None)
                .unwrap()
                .qrom_error_bits(cap)
        };
        assert_eq!(at(R::Cdhz25JohnsonQrom128, 38), 115_512);
        assert_eq!(at(R::Cdhz25ZeroPowQrom128, 40), 122_976);
        assert_eq!(at(R::BciksJohnsonQrom128, 40), 123_336);
    }
}
