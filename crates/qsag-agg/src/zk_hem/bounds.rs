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
fn stage_bound(
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
fn siblings(queries: usize, log_leaves: usize) -> usize {
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
