//! Concrete security accounting for committed-mask zk-Hem ([`super::protocol`]) over the Hem
//! WHIR commitment ([`crate::pcs`]): the round-by-round (RBR) soundness error of every
//! verifier round as implemented, its composition through the BCS transformation in the ROM
//! and the QROM, the zero-knowledge accounting, and a proof-size model. `crates/qsag-agg/SECURITY.md`
//! states the theorems; this module computes their numbers.
//!
//! All quantities are integers. An error `eps` is carried as a lower bound on `-log2(eps)`
//! in thousandths of a bit ([`MilliBits`]); logarithms round against the claim.
//!
//! Sources (file names in `/Users/ember/paperbin`), with what each one proves:
//!
//! * `[CWYZ26]` `2026-affine-combiners-reed-solomon-proximity-gaps-2611.15128`: Theorem 4.10
//!   (finite form of the affine-combiner MCA bound with one coordinate of agreement loss) and
//!   Theorem 5.1 with its linear-claim guarantee (5.5). Proven, every field and domain.
//! * `[BCGM25]` `bordage-chiesa-guan-manzur-all-polynomial-generators-MCA-2025-2051`:
//!   Lemma 9.3, mutual correlated agreement of the powers generator `(1, x, .., x^d)` for
//!   Reed-Solomon codes up to the Johnson bound, error
//!   `(m + 1/2)^7 d n^2 / (3 rho^(3/2) |F|)`. Proven.
//! * `[ACFY24b]` `whir`: Theorem 5.2, the shape of the RBR errors (fold, out-of-domain,
//!   shift, final). Proven for WHIR as specified there; applying it to the affine fold of
//!   this crate is this project's argument (SECURITY.md, section 2.1).
//! * `[CDHZ25]` `2025-cdhz-pq-snrdx-bcs-2025-2166`: Theorem 6.9 (RBR soundness implies
//!   post-quantum state-restoration soundness with error
//!   `80 (t + k + 1)(w + k) eps_rbr + (t + k + 1) k / 2^r_min`), Theorem 8.3 (Merkle
//!   commitments, `O(t^3 / 2^sigma)`) and Theorem A.1 / 11.3 (their composition). Proven.
//!
//! What is this project's own argument and not a cited theorem: the per-round application of
//! `[CWYZ26]` Theorem 5.1 to domain-halving folds (one fiber of agreement lost per fold), the
//! state function of the composed protocol, and the simulator of SECURITY.md section 4.

use alloc::vec::Vec;

use super::protocol::{COL_DEGREE, COL_MASK_BITS, COMPANIONS, ROW_DEGREE, ROW_MASK_BITS};
use crate::pcs::{MAX_PCS_NUM_VARS, WhirSecurityRegime};

/// A lower bound on `-log2` of a probability, in thousandths of a bit.
pub type MilliBits = i64;

/// `floor(1000 log2 |F_{p^4} \ F_{p^2}|) - 1`: every challenge set used by the protocol (the
/// field, its nonzero elements, the elements outside the quadratic subfield) has at least
/// `2^255.998` elements.
pub const CHALLENGE_SET_MILLIBITS: MilliBits = 255_998;

/// Cap on `folds * (l + 2 l0 + 1) + 1` per stage, the list budget the finite witnesses of
/// `pcs/affine_schedule.rs` certify.
pub const STAGE_LIST_CAP: u128 = 2000;

/// Committed tables: the assignment table and its companions.
const TABLES: usize = 1 + COMPANIONS;

/// `log2(320)` rounded up: the constant `4 * 80` of `[CDHZ25]` Theorems A.1 and 6.9.
const QROM_RBR_CONST: MilliBits = 8_322;
/// `log2(6380)` rounded up. `8 * 160 * 4 + 4 * 240 = 6080` is the leading `t^3 / 2^sigma`
/// coefficient of `8 kappa_offline(2t + 1) + 4 kappa_online(t)` in `[CDHZ25]` Theorems 11.3
/// and 8.3; `300 >= 40 e^2` bounds collisions in the 256-bit transcript chain
/// (`2020-cfhl-compressed-oracle-technique-pq-proofs-sequential-work-2010.11658`,
/// Theorem 5.29 with `k = 1`).
const QROM_MERKLE_CONST: MilliBits = 12_640;
/// Slack for `(t + k + 1)(t + k) <= t^2 (1 + 2^-7)^2` and for the verifier's own
/// `q_V + k <= 2^15` queries inside `kappa_online`, when `t >= 2^24`.
const QROM_ROUND_SLACK: MilliBits = 23;

/// A lower bound on `1000 log2(x)` within `0.002` of it; `x > 0`.
pub fn log2_lo(x: u128) -> MilliBits {
    assert!(x > 0);
    let lz = x.leading_zeros();
    let exponent = (127 - lz) as i64;
    // Top 64 bits, truncated: `y / 2^63` is in `[1, 2)` and at most the true mantissa.
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

/// `-log2` of the probability that `queries` distinct uniform positions out of `n` all fall in
/// a set of `agreement` positions; `None` when that probability is zero.
pub fn query_bits(n: u128, agreement: u128, queries: usize) -> Option<MilliBits> {
    if agreement < queries as u128 {
        return None;
    }
    assert!(agreement <= n);
    // Normalized dyadic product; every division rounds up (`pcs/affine_schedule.rs`).
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
    // The margin rises and then falls in `D` ((4.1) puts the useful range below
    // `(m + 1/2)^2 / (3 rho)`): locate its peak, then the first `D` left of it that qualifies.
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
            // Second term of (4.13) with `A - B = 1`: `(D^2 + 4 d^2 M^2 D^3) n^2 < |F|`.
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

/// How the five committed tables enter the opened word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Blend {
    /// `U = Z + beta C_0 + .. + beta^4 C_3`, as implemented by [`super::protocol::prove`].
    ScalarPowers,
    /// `U = sum_i (a_i + b_i X) W_i` with the weights of `pcs::affine::cascade_weights`, four
    /// applications of `[CWYZ26]` Theorem 5.1. Not implemented for the hiding protocol: its
    /// blended word reveals one `Ext4`-valued functional of `Z` and needs four more blinding
    /// cells and its own simulation lemma (SECURITY.md, section 6, R4).
    AffineCascade,
    /// No blend: the opening of a single public table (non-hiding Hem).
    Public,
}

/// Parameters that are not part of [`WhirSecurityRegime`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    /// Length of Merkle digests and of the Fiat-Shamir chaining value.
    pub digest_bits: u32,
    /// Length of the per-leaf Stage-0 salt.
    pub salt_bits: u32,
    pub blend: Blend,
    /// Grinding bits in front of the challenges that have none today: sumcheck, batching,
    /// blend, out-of-domain and kernel-fold challenges.
    pub algebraic_pow_bits: u32,
}

impl Params {
    /// The protocol as implemented.
    pub const IMPLEMENTED: Self = Self {
        digest_bits: 256,
        salt_bits: 128,
        blend: Blend::ScalarPowers,
        algebraic_pow_bits: 0,
    };
}

/// Size of a relation: [`super::relation::Shape::log_rows`], `log2` of the variable subcube
/// and the number of public inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapeSize {
    pub log_rows: usize,
    pub var_bits: usize,
    pub num_public: usize,
}

/// `(log_cells, blind_cells)` of [`super::protocol::Layout::new`].
pub fn zk_layout(regime: WhirSecurityRegime, size: ShapeSize) -> Option<(usize, usize)> {
    if !regime.is_accepted_aggregate_profile() {
        return None;
    }
    let masks = ((size.log_rows * 4) << ROW_MASK_BITS) + ((size.var_bits * 4) << COL_MASK_BITS);
    (size.var_bits + 1..=MAX_PCS_NUM_VARS).find_map(|log_cells| {
        let cells = 1usize << log_cells;
        let st0 = regime.schedule(log_cells).stages[0];
        let arity = 1usize << st0.step_vars;
        let blind = st0.num_queries.min(cells * st0.blowup / arity) * arity;
        ((1usize << size.var_bits) + masks + blind <= cells).then_some((log_cells, blind))
    })
}

/// A verifier round. Each is one random-oracle call of the compiled protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Round {
    /// Row or column sumcheck, zero-check point, mask and batching challenges.
    Sumcheck,
    /// The blend challenge.
    Blend,
    /// Out-of-domain points of a stage, and the weights of the Stage-0 samples.
    OutOfDomain(usize),
    /// Kernel fold `phi` of a stage.
    KernelFold(usize),
    /// Affine fold `(theta, alpha, beta)` of a stage; preceded by the regime's grinding.
    AffineFold(usize),
    /// Fiber queries of a stage together with the weights that batch the resulting shift
    /// claims and the next stage's out-of-domain claims; preceded by the regime's grinding.
    Query(usize),
}

/// Bounds for one WHIR stage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StageBound {
    pub blowup: usize,
    pub step_vars: usize,
    pub queries: usize,
    /// Fibers of the committed oracle (points of the fully folded word).
    pub fibers: u128,
    /// Agreement threshold `A` in fibers used by the analysis.
    pub agreement: u128,
    /// Johnson list bound of the committed word at that threshold.
    pub word_list: u128,
    /// `max (l + 2 l0 + 1)` over the stage's fold levels (`[CWYZ26]` (5.5)).
    pub list: u128,
    /// Query error before grinding; `None` when it is zero (`A + folds < queries`).
    pub query_bits: Option<MilliBits>,
    /// Affine-fold error before grinding.
    pub fold_bits: MilliBits,
}

/// The list numerator `max (l + 2 l0 + 1)` over the fold levels of a stage at threshold `a`
/// fibers, when every level has an interpolation witness within [`STAGE_LIST_CAP`].
fn stage_lists(fibers: u128, blowup: u128, folds: u32, a: u128) -> Option<u128> {
    let mut worst = 0u128;
    for level in 0..folds {
        // The output of fold `folds - level` lives on `fibers << level` points.
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
        // One fiber of agreement is lost per fold (`[CWYZ26]` agreement loss `s = 1`).
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

/// `[BCGM25]` Lemma 9.3 for the blend of five words on the Stage-0 domain: the smallest
/// agreement threshold in fibers covered by proximity parameter `m`, and the error.
fn scalar_blend(log_cells: usize, st0: &StageBound, m: u128) -> (u128, MilliBits) {
    let points = (st0.blowup as u128) << log_cells;
    let k = (1u128 << log_cells) + 2;
    // `A / fibers >= (1 + 1/(2m)) sqrt(k / points)`, squared and cleared of denominators.
    let covers = |a: u128| {
        (2 * m * a) * (2 * m * a) * points
            >= (2 * m + 1) * (2 * m + 1) * st0.fibers * st0.fibers * k
    };
    let (mut lo, mut hi) = (1u128, st0.fibers);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if covers(mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    // `(m + 1/2)^7 / (3 rho^(3/2)) * d * n^2` with `d = 4` and `rho >= 1 / blowup`.
    let numerator = 7 * log2_hi(2 * m + 1)
        + 1500 * i64::from(st0.blowup.trailing_zeros())
        + 2000
        + 2 * log2_hi(points)
        - log2_lo(384);
    (lo, CHALLENGE_SET_MILLIBITS - numerator)
}

/// The largest round-by-round error of a protocol and where it occurs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RbrBound {
    /// `-log2` of the largest per-round error.
    pub bits: MilliBits,
    pub round: Round,
    /// Proximity parameter `m` of `[BCGM25]` Lemma 9.3 at which the analysis is run.
    pub blend_m: Option<u128>,
    /// Stage-0 agreement threshold in fibers at which the analysis is run.
    pub stage0_agreement: u128,
    /// Error of the blend round.
    pub blend_bits: Option<MilliBits>,
}

/// Zero-knowledge accounting (SECURITY.md section 4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZkBound {
    /// Uniform cells at the top of the assignment table.
    pub blind_cells: usize,
    /// Symbols of the assignment codeword opened by the Stage-0 queries.
    pub opened_symbols: usize,
    /// Whether the verifier's view of the interactive oracle proof is perfectly simulated:
    /// `blind_cells >= opened_symbols`. The remaining loss is the hiding of unopened leaves.
    pub view_perfectly_simulated: bool,
    pub salt_bits: u32,
}

impl ZkBound {
    /// Classical ROM: `-log2` of the distance between real and simulated proofs of
    /// `2^log_proofs` statements against `2^log_queries` hash queries, `t P / 2^salt`.
    pub fn classical_hiding_bits(&self, log_queries: u32, log_proofs: u32) -> MilliBits {
        1000 * (i64::from(self.salt_bits) - i64::from(log_queries) - i64::from(log_proofs))
    }

    /// QROM: `2 t sqrt(P / 2^salt)`, by one-way to hiding (`2018-ahu-semi-classical-oracles-
    /// o2h-2018-904`, Theorem 3).
    pub fn quantum_hiding_bits(&self, log_queries: u32, log_proofs: u32) -> MilliBits {
        500 * (i64::from(self.salt_bits) - i64::from(log_proofs))
            - 1000 * (i64::from(log_queries) + 1)
    }
}

/// The security bounds of one regime at one relation size.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecurityReport {
    pub regime: WhirSecurityRegime,
    pub params: Params,
    /// Variables of the committed tables.
    pub log_cells: usize,
    /// Stage bounds at the thresholds of [`Self::classical`].
    pub stages: Vec<StageBound>,
    /// Verifier rounds `k`.
    pub rounds: usize,
    /// Round-by-round error with grinding credited as a factor `2^-bits` on the rounds it
    /// precedes (`2026-aborting-random-oracles-grinding-fiat-shamir-2026-016`, Corollary 3).
    /// Used for the classical bound.
    pub classical: RbrBound,
    /// Round-by-round error without any credit for grinding. Used for the QROM bound: no
    /// cited theorem covers grinding against quantum queries.
    pub ungrounded: RbrBound,
    pub zk: Option<ZkBound>,
    /// Upper bound on the serialized proof.
    pub proof_bytes: usize,
    /// Merkle digests in that bound (roots and authentication siblings).
    pub digests: usize,
    /// Leaf and node hashes of the prover's Merkle trees.
    pub merkle_hashes: u128,
    /// Expected hash evaluations spent on grinding.
    pub grinding_hashes: u128,
}

impl SecurityReport {
    fn digest_millibits(&self) -> MilliBits {
        // Four Goldilocks limbs carry `4 log2 p > 255.999` bits.
        1000 * i64::from(self.params.digest_bits) - i64::from(self.regime.uses_poseidon2_canopy())
    }

    /// `-log2` of the ROM knowledge-soundness error against `2^log_queries` classical
    /// queries, `t eps_rbr + 4 t^2 / 2^sigma`: state restoration from round-by-round
    /// soundness and `3 (t^2 + 1) / 2^sigma` from
    /// `2016-bcs-interactive-oracle-proofs-2016-116`, Theorem 7.1.
    pub fn classical_error_bits(&self, log_queries: u32) -> MilliBits {
        let t = 1000 * i64::from(log_queries);
        (self.classical.bits - t).min(self.digest_millibits() - 2000 - 2 * t) - 1000
    }

    /// Largest `log2 t` at which neither term of [`Self::classical_error_bits`] is vacuous.
    /// This is also the security level `kappa` with `eps(t) <= t / 2^kappa` for `t <= 2^kappa`.
    pub fn classical_work_bits(&self) -> MilliBits {
        self.classical
            .bits
            .min((self.digest_millibits() - 2000) / 2)
    }

    /// `-log2` of the QROM knowledge-soundness error against `2^log_queries >= 2^24` quantum
    /// queries, by `[CDHZ25]` Theorems 11.3, 6.10 and 8.3:
    /// `320 (t + k + 1)(t + k) eps_rbr + 6380 t^3 / 2^sigma`, where `6380 = 5120 + 960 + 300`
    /// collects `8 kappa_offline(2t + 1)`, `4 kappa_online(t)` and collisions in the
    /// transcript chain. Terms of lower order in `t` are below `0.02` bits.
    pub fn qrom_error_bits(&self, log_queries: u32) -> MilliBits {
        assert!(log_queries >= 24 && self.rounds < 1 << 9);
        let t = 1000 * i64::from(log_queries);
        (self.ungrounded.bits - QROM_RBR_CONST - QROM_ROUND_SLACK - 2 * t)
            .min(self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK - 3 * t)
            - 1000
    }

    /// The two terms of [`Self::qrom_error_bits`] as query counts at which each becomes
    /// vacuous: `(round-by-round, digest)`. Their minimum is the QROM security level.
    pub fn qrom_work_terms(&self) -> (MilliBits, MilliBits) {
        (
            (self.ungrounded.bits - QROM_RBR_CONST - QROM_ROUND_SLACK) / 2,
            (self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK) / 3,
        )
    }

    /// The QROM security level proven by the cited theorems.
    pub fn qrom_work_bits(&self) -> MilliBits {
        let (rbr, digest) = self.qrom_work_terms();
        rbr.min(digest)
    }

    /// [`Self::qrom_work_bits`] with grinding credited as in the classical bound. Heuristic:
    /// this is the accounting behind `WhirSecurityRegime::qrom_grover_round_bits`, and no
    /// cited theorem supports it.
    pub fn qrom_work_bits_crediting_grinding(&self) -> MilliBits {
        ((self.classical.bits - QROM_RBR_CONST - QROM_ROUND_SLACK) / 2)
            .min(self.qrom_work_terms().1)
    }
}

/// Authentication siblings of `queries` leaves in a tree of `2^log_leaves` leaves, at most.
pub(crate) fn siblings(queries: usize, log_leaves: usize) -> usize {
    if queries >> log_leaves != 0 {
        return 0;
    }
    queries * (log_leaves - queries.ilog2() as usize)
}

/// The report for the committed-mask protocol on a relation of `size`.
pub fn security_report(
    regime: WhirSecurityRegime,
    size: ShapeSize,
    params: Params,
) -> Option<SecurityReport> {
    let (log_cells, blind_cells) = zk_layout(regime, size)?;
    let front =
        33 + 32
            * (1 + (ROW_DEGREE + 1) * size.log_rows + 3 + 1 + (COL_DEGREE + 1) * size.var_bits + 4);
    let mut report = pcs_report(regime, log_cells, params, Some(size))?;
    let st0 = &report.stages[0];
    let opened_symbols = st0.queries.min(st0.fibers as usize) << st0.step_vars;
    report.zk = Some(ZkBound {
        blind_cells,
        opened_symbols,
        view_perfectly_simulated: blind_cells >= opened_symbols,
        salt_bits: params.salt_bits,
    });
    report.proof_bytes += front;
    Some(report)
}

/// The report for an opening of a `log_cells`-variable commitment. With `size`, the rounds of
/// the committed-mask protocol in front of the opening are included.
pub fn pcs_report(
    regime: WhirSecurityRegime,
    log_cells: usize,
    params: Params,
    size: Option<ShapeSize>,
) -> Option<SecurityReport> {
    if !(2..=MAX_PCS_NUM_VARS).contains(&log_cells) {
        return None;
    }
    let schedule = regime.schedule(log_cells);
    let tables = if params.blend == Blend::Public {
        1
    } else {
        TABLES
    };

    let mut rem = log_cells;
    let base: Vec<StageBound> = schedule
        .stages
        .iter()
        .map(|spec| {
            rem -= spec.step_vars;
            stage_bound(spec.blowup, spec.step_vars, spec.num_queries, rem, None)
        })
        .collect::<Option<_>>()?;
    // The same stages with a larger Stage-0 agreement threshold.
    let with_stage0 = |agreement: u128| -> Option<Vec<StageBound>> {
        let spec = schedule.stages[0];
        let mut stages = base.clone();
        stages[0] = stage_bound(
            spec.blowup,
            spec.step_vars,
            spec.num_queries,
            log_cells - spec.step_vars,
            Some(agreement),
        )?;
        Some(stages)
    };

    // The largest round error, with `pow` bits credited to the rounds the regime grinds and
    // `algebraic` bits to the others.
    let evaluate = |stages: &[StageBound],
                    blend: Option<MilliBits>,
                    pow: MilliBits,
                    algebraic: MilliBits|
     -> (MilliBits, Round) {
        let mut worst = (MilliBits::MAX, Round::Sumcheck);
        let mut note = |bits: MilliBits, round: Round| {
            if bits < worst.0 {
                worst = (bits, round);
            }
        };
        if let Some(size) = size {
            // Zero-check point, mask challenges, sumcheck rounds, row-value and claim batching:
            // one polynomial identity of at most this degree per member of the Stage-0 list.
            let degree = size.log_rows.max(ROW_DEGREE).max(4 + size.num_public) as u128;
            note(
                CHALLENGE_SET_MILLIBITS - log2_hi(degree * stages[0].word_list) + algebraic,
                Round::Sumcheck,
            );
        }
        if let Some(bits) = blend {
            note(bits + algebraic, Round::Blend);
        }
        let mut rem = log_cells;
        for (i, st) in stages.iter().enumerate() {
            // Two points: two of the `l` list members agree on both with probability at most
            // `(l^2 / 2) (deg / |F|)^2`. Stage 0 also draws its two weights here.
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
            // Queries and, in the same round, the weights batching `queries + 2` claims on
            // the next oracle: one linear identity per member of its list.
            let batch = stages.get(i + 1).map_or(MilliBits::MAX, |next| {
                CHALLENGE_SET_MILLIBITS - log2_hi((st.queries as u128 + 2) * next.word_list) - 1000
            });
            let query = st.query_bits.map_or(MilliBits::MAX, |bits| bits - 1000);
            if query.min(batch) != MilliBits::MAX {
                note(query.min(batch) + pow, Round::Query(i));
            }
            rem -= st.step_vars;
        }
        worst
    };

    // The analysis may use any Stage-0 agreement threshold at or above the smallest one with
    // an interpolation witness. A larger threshold lowers the blend error of `[BCGM25]` and
    // raises the query error: take the best for each objective.
    let optimise = |pow: MilliBits, algebraic: MilliBits| -> Option<(RbrBound, Vec<StageBound>)> {
        let finish = |stages: Vec<StageBound>, m: Option<u128>, blend: Option<MilliBits>| {
            let (bits, round) = evaluate(&stages, blend, pow, algebraic);
            let bound = RbrBound {
                bits,
                round,
                blend_m: m,
                stage0_agreement: stages[0].agreement,
                blend_bits: blend,
            };
            (bound, stages)
        };
        match params.blend {
            Blend::Public => Some(finish(base.clone(), None, None)),
            Blend::AffineCascade => {
                let blend = CHALLENGE_SET_MILLIBITS - log2_hi(4 * base[0].list);
                Some(finish(base.clone(), None, Some(blend)))
            }
            Blend::ScalarPowers => {
                let mut best: Option<(RbrBound, Vec<StageBound>)> = None;
                for m in 3..=4096u128 {
                    let (threshold, mca) = scalar_blend(log_cells, &base[0], m);
                    let binding = threshold > base[0].agreement;
                    let stages = if binding {
                        with_stage0(threshold)?
                    } else {
                        base.clone()
                    };
                    // Besides the exceptional challenges of the lemma, at most four roots of
                    // the degree-4 claim identity per member of the list.
                    let claim = CHALLENGE_SET_MILLIBITS - log2_hi(4 * stages[0].word_list);
                    let candidate = finish(stages, Some(m), Some(mca.min(claim) - 1000));
                    if best.as_ref().is_none_or(|b| candidate.0.bits > b.0.bits) {
                        best = Some(candidate);
                    }
                    if !binding {
                        break;
                    }
                }
                best
            }
        }
    };
    let pow = 1000 * i64::from(regime.pow_bits());
    let algebraic = 1000 * i64::from(params.algebraic_pow_bits);
    let (classical, stages) = optimise(pow, algebraic)?;
    let (ungrounded, _) = optimise(0, 0)?;

    // Rounds, proof bytes, digests and hash counts.
    let fold_vars = log_cells - schedule.early_stop_vars;
    // Per fold: phi, then (theta, alpha, beta). Per stage: out-of-domain points, queries.
    // Stage 0 also has its out-of-domain weights.
    let mut rounds = 2 * fold_vars + 2 * stages.len() + 1;
    let mut algebraic_rounds = fold_vars + stages.len() + 1;
    if let Some(size) = size {
        // tau, rho1, row rounds, combine, rho2, column rounds, lambda, beta.
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
            opened * (params.salt_bits.div_ceil(8) as usize + tables * 8 * (1usize << st.step_vars))
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
        zk: None,
        proof_bytes,
        digests,
        merkle_hashes,
        grinding_hashes,
    })
}

/// Smallest Stage-0 query count at which the query error of a rate-`1/blowup` stage is at
/// most `2^-target_bits` before grinding when the analysis runs at `[BCGM25]` proximity
/// parameter `m`, where the agreement fraction is `(1 + 1/(2m)) / sqrt(blowup)`. The fold
/// loss and the slack of the code dimension are ignored.
pub fn stage0_queries_for(blowup: usize, m: u128, target_bits: u32) -> usize {
    // Bits per query: `log2(sqrt(blowup) * 2m / (2m + 1))`.
    let per_query = 500 * i64::from(blowup.trailing_zeros()) + log2_lo(2 * m) - log2_hi(2 * m + 1);
    (1000 * target_bits as usize).div_ceil(per_query as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zk_hem::protocol::{Layout, prove, verify};
    use crate::zk_hem::relation::{ConstraintSystem, Lc};

    type F = crate::field::Goldilocks;

    const ZK_REGIMES: [WhirSecurityRegime; 7] = [
        WhirSecurityRegime::BciksJohnsonQrom128,
        WhirSecurityRegime::Cdhz25JohnsonQrom128,
        WhirSecurityRegime::Cdhz25ZeroPowQrom128,
        WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
        WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
        WhirSecurityRegime::TurboShakeBciksJohnsonQrom128,
        WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128,
    ];

    const PUBLIC: Params = Params {
        blend: Blend::Public,
        ..Params::IMPLEMENTED
    };

    fn square(rows: usize) -> ShapeSize {
        ShapeSize {
            log_rows: rows,
            var_bits: rows,
            num_public: 8,
        }
    }

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
        // `log2(7^7) = 19.6514...`, `log2(384) = 8.5849...`.
        assert_eq!(log2_lo(823_543) / 10, 1965);
        assert_eq!(log2_lo(384) / 10, 858);
        // The constants of the QROM bound.
        assert!(log2_lo(320) < QROM_RBR_CONST && QROM_RBR_CONST <= log2_hi(320));
        assert!(log2_lo(6380) < QROM_MERKLE_CONST && QROM_MERKLE_CONST <= log2_hi(6380));
        // `|F_{p^4}| - |F_{p^2}| > 2^255.998`: `p > 2^64 (1 - 2^-31)` gives
        // `p^4 - p^2 > 2^256 (1 - 2^-28)`, and `log2(1 - 2^-28) > -0.001`.
        assert!(u128::from(crate::field::GOLDILOCKS_PRIME) > (1u128 << 64) - (1u128 << 33));
    }

    /// The query error against a direct product over a small case, and its zero case.
    #[test]
    fn query_error_matches_the_hypergeometric_product() {
        // C(6, 3) / C(16, 3) = 20 / 560 = 1 / 28.
        let bits = query_bits(16, 6, 3).unwrap();
        assert!(bits <= log2_lo(28) && bits >= log2_lo(28) - 3, "{bits}");
        assert_eq!(query_bits(16, 2, 3), None);
        assert_eq!(query_bits(16, 16, 3), Some(0));
    }

    /// Rows of `pcs/affine_schedule.rs` (`WITNESSES`, `HIGH_CAPACITY_WITNESSES`): the stored
    /// `(A, m, D)` satisfy this module's reading of (4.5), and the searched threshold is at
    /// most the stored one.
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
            // The stored threshold meets the regime's pure query target, so does the search.
            assert!(found.query_bits.unwrap() >= 256_000, "{nv}/{stage}");
            assert!(spec.step_vars as u128 * found.list + 1 < STAGE_LIST_CAP);
        }
        // At the Johnson radius there is no list bound and no witness.
        assert_eq!(johnson_list(1 << 17, 65_536, 32_770), None);
        assert_eq!(affine_fold_numerator(1 << 17, 32_770, 65_537), None);
        // (4.5) fails for a multiplicity that is too small for the slack.
        assert_eq!(interpolation_holds(1 << 17, 32_770, 65_948, 1, 2), None);
    }

    /// Every stage of every QROM regime meets the constants `pcs.rs` asserts for it, at the
    /// sizes the project commits (`2^17 .. 2^24` cells). Tag 2 does not.
    #[test]
    fn stage_bounds_against_the_constants_asserted_by_the_regimes() {
        for regime in WhirSecurityRegime::ALL {
            let mut least = MilliBits::MAX;
            for log_cells in 17..=24 {
                let report = pcs_report(regime, log_cells, PUBLIC, None).unwrap();
                for st in &report.stages {
                    least = least.min(st.query_bits.unwrap());
                    // `2000 / p^4`: more than 245 bits (`AFFINE_PROTOCOL.md`).
                    assert!(st.fold_bits > 245_000);
                }
                // Without grinding no round is better than a list size over the field.
                assert!(report.ungrounded.bits <= report.classical.bits.min(249_000));
            }
            let target = 1000 * i64::from(regime.pure_query_target_bits());
            if regime == WhirSecurityRegime::BciksJohnsonClassical128 {
                // `ceil(256 / log2 B) + 1` queries leave no room for the Johnson slack; two
                // more per stage restore 128 bits at these sizes.
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

    /// The numbers of SECURITY.md, section 5.
    #[test]
    fn reports_are_pinned_at_the_project_sizes() {
        use WhirSecurityRegime as R;
        // (regime, rows): log_cells, classical RBR and its round, RBR without grinding and
        // its round, proof bytes.
        let pins = [
            (
                (R::BciksJohnsonQrom128, 17),
                (18, 198_919, Round::Blend, 198_919, Round::Blend, 528_380),
            ),
            (
                (R::BciksJohnsonQrom128, 20),
                (21, 192_919, Round::Blend, 192_919, Round::Blend, 896_644),
            ),
            (
                (R::BciksJohnsonQrom128, 22),
                (23, 188_919, Round::Blend, 188_919, Round::Blend, 966_957),
            ),
            (
                (R::Cdhz25JohnsonQrom128, 20),
                (21, 188_355, Round::Blend, 183_499, Round::Query(0), 716_932),
            ),
            (
                (R::Cdhz25JohnsonQrom128, 22),
                (23, 184_355, Round::Blend, 180_934, Round::Query(0), 773_101),
            ),
            (
                (R::Cdhz25ZeroPowQrom128, 20),
                (21, 186_668, Round::Blend, 186_668, Round::Blend, 764_580),
            ),
            (
                (R::Poseidon2Cdhz25ZeroPowQrom128, 21),
                (
                    22,
                    185_388,
                    Round::Query(0),
                    185_388,
                    Round::Query(0),
                    799_980,
                ),
            ),
        ];
        for ((regime, rows), want) in pins {
            let r = security_report(regime, square(rows), Params::IMPLEMENTED).unwrap();
            let got = (
                r.log_cells,
                r.classical.bits,
                r.classical.round,
                r.ungrounded.bits,
                r.ungrounded.round,
                r.proof_bytes,
            );
            assert_eq!(got, want, "{regime:?} {rows}");
        }
        // The public opening of the default regime: every round sits at a list size over the
        // field; the weakest is the batching of the 260 claims produced by the Stage-0 queries.
        let public = pcs_report(R::BciksJohnsonQrom128, 21, PUBLIC, None).unwrap();
        assert_eq!(
            (public.classical.bits, public.classical.round),
            (247_505, Round::KernelFold(1))
        );
        assert_eq!(
            (public.ungrounded.bits, public.ungrounded.round),
            (240_104, Round::Query(0))
        );
        assert_eq!(public.qrom_work_terms(), (115_879, 81_112));
    }

    /// No regime reaches the level its name or `qrom_grover_round_bits` states, for the
    /// committed-mask protocol as implemented, at any project size.
    #[test]
    fn no_regime_reaches_its_nominal_level_as_implemented() {
        for regime in ZK_REGIMES {
            for rows in 17..=22 {
                let r = security_report(regime, square(rows), Params::IMPLEMENTED).unwrap();
                let zk = r.zk.unwrap();
                assert!(zk.view_perfectly_simulated && zk.blind_cells == zk.opened_symbols);
                // Classical: bound by collisions in 256-bit digests, with more than 50 bits of
                // round-by-round margin.
                assert!((126_999..=127_000).contains(&r.classical_work_bits()));
                assert!(
                    (180_000..200_000).contains(&r.classical.bits),
                    "{regime:?} {rows}"
                );
                // The regime's per-round figure counts queries and grinding only.
                assert!(r.classical.bits < 1000 * i64::from(regime.classical_fs_round_bits()));
                // QROM: the 256-bit digests bind at 81 bits. The round-by-round term alone is
                // 86 to 96 bits, below the nominal 107, 108 and 136.
                let (rbr, digest) = r.qrom_work_terms();
                assert_eq!(digest, 81_112);
                assert_eq!(r.qrom_work_bits(), 81_112);
                assert!((86_000..96_000).contains(&rbr), "{regime:?} {rows}: {rbr}");
                assert!(rbr < 1000 * i64::from(regime.qrom_grover_round_bits()));
                assert_eq!(r.qrom_work_bits_crediting_grinding(), 81_112);
                // Bounded-query profiles: at the stated cap the proven error is not `2^-128`.
                if regime.is_bounded_query_profile() {
                    let cap = if regime.pow_bits() == 0 { 40 } else { 38 };
                    let bits = r.qrom_error_bits(cap);
                    assert!(
                        (95_000..106_000).contains(&bits),
                        "{regime:?} {rows}: {bits}"
                    );
                }
            }
        }
        // The public opening at the bounded-query caps, for comparison.
        use WhirSecurityRegime as R;
        let at = |regime, cap| {
            pcs_report(regime, 21, PUBLIC, None)
                .unwrap()
                .qrom_error_bits(cap)
        };
        assert_eq!(at(R::Cdhz25JohnsonQrom128, 38), 114_513);
        assert_eq!(at(R::Cdhz25ZeroPowQrom128, 40), 122_337);
        assert_eq!(at(R::BciksJohnsonQrom128, 40), 122_337);
    }

    /// Section 6 of SECURITY.md: what each change buys and costs, at `2^20` rows.
    #[test]
    fn required_changes_are_costed() {
        let regime = WhirSecurityRegime::BciksJohnsonQrom128;
        let size = square(20);
        let now = security_report(regime, size, Params::IMPLEMENTED).unwrap();
        assert_eq!(
            (now.proof_bytes, now.digests, now.stages[0].queries),
            (896_644, 4_199, 258)
        );

        // 32-byte salts: 16 more bytes per opened Stage-0 leaf; hiding 2 t / 2^128.
        let salted = Params {
            salt_bits: 256,
            ..Params::IMPLEMENTED
        };
        let r = security_report(regime, size, salted).unwrap();
        assert_eq!(r.proof_bytes - now.proof_bytes, 16 * 258);
        assert_eq!(now.zk.unwrap().quantum_hiding_bits(40, 0), 23_000);
        assert_eq!(r.zk.unwrap().quantum_hiding_bits(40, 0), 87_000);
        assert_eq!(now.zk.unwrap().classical_hiding_bits(64, 20), 44_000);
        assert_eq!(r.zk.unwrap().classical_hiding_bits(64, 20), 172_000);

        // 48-byte digests: the digest term rises from 81 to 123 bits and the blend binds.
        let wide = Params {
            digest_bits: 384,
            ..Params::IMPLEMENTED
        };
        let r = security_report(regime, size, wide).unwrap();
        assert_eq!(r.qrom_work_terms(), (92_287, 123_779));
        assert_eq!(r.proof_bytes - now.proof_bytes, 16 * 4_199);
        assert_eq!(r.merkle_hashes, now.merkle_hashes);
        // 50-byte digests are the shortest whose term exceeds 128.
        let wider = Params {
            digest_bits: 400,
            ..Params::IMPLEMENTED
        };
        assert_eq!(
            security_report(regime, size, wider)
                .unwrap()
                .qrom_work_terms()
                .1,
            129_112
        );

        // An affine blend removes the `n^2` loss: 115 bits, the ceiling of the quartic field.
        let cascade = Params {
            blend: Blend::AffineCascade,
            ..wide
        };
        let r = security_report(regime, size, cascade).unwrap();
        assert_eq!(
            (r.ungrounded.bits, r.ungrounded.round),
            (240_104, Round::Query(0))
        );
        assert_eq!(r.qrom_work_bits(), 115_879);
        // No parameter reaches a proven 128: every round is at least a list size over a
        // field of `2^256` elements, and the level is half of that less the constant.
        assert!(r.ungrounded.bits < CHALLENGE_SET_MILLIBITS && r.qrom_work_terms().0 < 128_000);

        // Grinding the remaining rounds helps the classical bound only.
        let ground = Params {
            algebraic_pow_bits: 24,
            ..cascade
        };
        let r = security_report(regime, size, ground).unwrap();
        assert_eq!(r.qrom_work_bits(), 115_879);
        assert_eq!(r.qrom_work_bits_crediting_grinding(), 123_779);
        assert_eq!(r.grinding_hashes, 1_058_013_184);

        // Stage-0 queries that keep the query error at `2^-256` under the scalar blend.
        assert_eq!(stage0_queries_for(4, 3, 256), 331);
        assert_eq!(stage0_queries_for(4, 80, 256), 259);
    }

    /// The size model against the measured full-shard proof of SECURITY.md, section 9.2
    /// (780,091 bytes including eight bytes of framing; tag 8, `2^21` rows).
    #[test]
    fn proof_size_model_brackets_the_measured_full_shard_proof() {
        let r = security_report(
            WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
            square(21),
            Params::IMPLEMENTED,
        )
        .unwrap();
        assert_eq!(r.log_cells, 22);
        // The model counts every authentication sibling as distinct; shared ones are not sent.
        assert!(
            (780_083..780_083 * 103 / 100).contains(&r.proof_bytes),
            "{}",
            r.proof_bytes
        );
    }

    fn tiny_relation() -> (crate::zk_hem::relation::Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        let x: Lc = cs.alloc(F::from_u64_reduced(3)).into();
        let y: Lc = cs.alloc(F::from_u64_reduced(5)).into();
        let prod = cs.mul(&x, &y);
        cs.enforce_zero(Lc::from(prod).plus_const(F::ZERO - F::from_u64_reduced(15)));
        cs.finish()
    }

    #[test]
    fn layout_matches_the_protocol() {
        let (shape, _) = tiny_relation();
        let size = ShapeSize {
            log_rows: shape.log_rows,
            var_bits: shape.num_vars.next_power_of_two().trailing_zeros().max(1) as usize,
            num_public: shape.num_public,
        };
        for regime in ZK_REGIMES {
            let layout = Layout::new(&shape, regime).unwrap();
            assert_eq!(
                zk_layout(regime, size),
                Some((layout.log_cells, layout.blind_cells))
            );
        }
        assert_eq!(
            zk_layout(WhirSecurityRegime::BciksJohnsonClassical128, size),
            None
        );
    }

    /// One seed, one witness, one statement, two regimes: the masks must not repeat. Before
    /// the schedule entered the coin derivation both proofs carried the same mask sums and
    /// the same twelve masking variables under two different row points, which determines
    /// twelve base-field linear functionals of the witness.
    #[test]
    fn coins_do_not_repeat_across_regimes() {
        let (shape, witness) = tiny_relation();
        let seed = [9u8; 32];
        let prove_with = |regime| prove(&shape, witness.clone(), b"s", regime, &seed).unwrap();
        let a = prove_with(WhirSecurityRegime::BciksJohnsonQrom128);
        let b = prove_with(WhirSecurityRegime::Cdhz25ZeroPowQrom128);
        assert!(verify(
            &shape,
            &[],
            b"s",
            WhirSecurityRegime::BciksJohnsonQrom128,
            &a
        ));
        assert!(verify(
            &shape,
            &[],
            b"s",
            WhirSecurityRegime::Cdhz25ZeroPowQrom128,
            &b
        ));
        assert_ne!(a.row_mask_sum, b.row_mask_sum);
        assert_ne!(a.col_mask_sum, b.col_mask_sum);
    }

    /// Prints the tables of SECURITY.md:
    /// `cargo test --release -p qsag-agg --lib -- zk_hem::bounds::tests::print_security_tables --ignored --nocapture`.
    #[test]
    #[ignore = "table printer"]
    fn print_security_tables() {
        let row = |r: &SecurityReport, label: &str| {
            let (rbr, digest) = r.qrom_work_terms();
            std::println!(
                "{label} tag {:2} cells 2^{} | classical rbr {} {:?} m {:?} A0 {} | no-grind rbr {} {:?} m {:?} A0 {} | level classical {} qrom {} (rbr {} digest {}) qrom+grind {} | err@2^40 {} err@2^64 {} | bytes {} digests {} k {} merkle {} grind {}",
                r.regime as u8,
                r.log_cells,
                r.classical.bits,
                r.classical.round,
                r.classical.blend_m,
                r.classical.stage0_agreement,
                r.ungrounded.bits,
                r.ungrounded.round,
                r.ungrounded.blend_m,
                r.ungrounded.stage0_agreement,
                r.classical_work_bits(),
                r.qrom_work_bits(),
                rbr,
                digest,
                r.qrom_work_bits_crediting_grinding(),
                r.qrom_error_bits(40),
                r.qrom_error_bits(64),
                r.proof_bytes,
                r.digests,
                r.rounds,
                r.merkle_hashes,
                r.grinding_hashes,
            );
        };
        for regime in ZK_REGIMES {
            for rows in 17..=22 {
                let r = security_report(regime, square(rows), Params::IMPLEMENTED).unwrap();
                row(&r, &alloc::format!("zk rows 2^{rows}"));
                for (i, st) in r.stages.iter().enumerate() {
                    std::println!(
                        "    stage {i}: B {} s {} q {} n {} A {} wl {} list {} query {:?} fold {}",
                        st.blowup,
                        st.step_vars,
                        st.queries,
                        st.fibers,
                        st.agreement,
                        st.word_list,
                        st.list,
                        st.query_bits,
                        st.fold_bits
                    );
                }
            }
        }
        for regime in WhirSecurityRegime::ALL {
            for log_cells in [18, 21, 23] {
                let r = pcs_report(regime, log_cells, PUBLIC, None).unwrap();
                row(&r, "public");
            }
        }
        let size = square(20);
        for (label, params) in [
            (
                "salt256",
                Params {
                    salt_bits: 256,
                    ..Params::IMPLEMENTED
                },
            ),
            (
                "digest384",
                Params {
                    digest_bits: 384,
                    ..Params::IMPLEMENTED
                },
            ),
            (
                "digest400",
                Params {
                    digest_bits: 400,
                    ..Params::IMPLEMENTED
                },
            ),
            (
                "digest384+cascade",
                Params {
                    digest_bits: 384,
                    blend: Blend::AffineCascade,
                    ..Params::IMPLEMENTED
                },
            ),
            (
                "digest384+cascade+pow24",
                Params {
                    digest_bits: 384,
                    blend: Blend::AffineCascade,
                    algebraic_pow_bits: 24,
                    ..Params::IMPLEMENTED
                },
            ),
            (
                "pow24",
                Params {
                    algebraic_pow_bits: 24,
                    ..Params::IMPLEMENTED
                },
            ),
        ] {
            for regime in [
                WhirSecurityRegime::BciksJohnsonQrom128,
                WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
            ] {
                let r = security_report(regime, size, params).unwrap();
                row(&r, label);
            }
        }
        for (label, params) in [
            (
                "public digest384",
                Params {
                    digest_bits: 384,
                    ..PUBLIC
                },
            ),
            (
                "public digest400",
                Params {
                    digest_bits: 400,
                    ..PUBLIC
                },
            ),
        ] {
            let r = pcs_report(WhirSecurityRegime::BciksJohnsonQrom128, 21, params, None).unwrap();
            row(&r, label);
        }
        for log_cells in 17..=24 {
            let schedule = WhirSecurityRegime::BciksJohnsonClassical128.schedule(log_cells);
            let mut rem = log_cells;
            for spec in &schedule.stages {
                rem -= spec.step_vars;
                let need = min_queries(spec.blowup, spec.step_vars, rem, 128_000).unwrap();
                std::println!(
                    "tag 2 cells 2^{log_cells} B {} has {} needs {need} (+{})",
                    spec.blowup,
                    spec.num_queries,
                    need as i64 - spec.num_queries as i64
                );
            }
        }
        for m in [3u128, 4, 6, 8, 16, 80] {
            std::println!(
                "stage0 queries for 2^-256 at m={m}: {}",
                stage0_queries_for(4, m, 256)
            );
        }
    }
}
