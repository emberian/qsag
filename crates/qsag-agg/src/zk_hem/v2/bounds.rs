//! Concrete security accounting for zk-Hem v2, in the conventions of
//! [`crate::zk_hem::bounds`] (integers only; an error is a lower bound on `-log2` in
//! thousandths of a bit; logarithms round against the claim). The theorems are in
//! `crates/qsag-agg/SECURITY.md`, section V2; this module computes their numbers.
//!
//! Key structural properties of the v2 calculator:
//!
//! * the challenge field is the quintic extension $\mathbb{F}_{p^5}$ ([`FIELD_MILLIBITS`]);
//! * there is no five-table blend. The only batching of committed words is the line
//!   `fold(Z) + beta_R R` on the folded Stage-0 domain, bounded by Dao, Kominers and Thaler
//!   `[DKT26]` (`2026/2056`) Theorem 5.12 with `d = 1` ([`mask_line`]):
//!   $|\mathcal{E}_{\mathrm{line}}| < \frac{(2m + 1)^3 n^2}{3 D}$, improving the exponent on
//!   $(2m + 1)$ from $7$ (`[BCGM25]` Lemma 9.3) to $3$, lifting the certified domain cap to
//!   $N \le 2^{28}$ and reducing Stage-0 queries uniformly across `16..=28`;
//! * beyond-Johnson first-order list-decodable proximity bounds (`[DKT26]` Proposition 5.10 +
//!   Lemma 5.6 + Corollary 7.8, list size $L \le 2$ up to $\delta = 1 - R - \eta$) are computed
//!   and verified in [`dkt26_beyond_johnson_first_order`];
//! * Stage 0 has five out-of-domain points; every Stage-0 leaf binds a fresh 256-bit per-tree
//!   `tree_nonce`, eliminating the `|D'|` multi-proof salt birthday factor;
//! * no grinding, so the classical and the quantum round-by-round errors coincide;
//! * digests of 400 bits and salts of 256 bits.

use alloc::vec::Vec;

use super::params::{
    COL_DEGREE, DIGEST_BYTES, EXT_BYTES, LATER_OOD_POINTS, LIMBS, LOOKUP_DEGREE, Layout,
    LookupLayout, LookupSize, MASK_POINTS, MIN_LOG_CELLS, Profile, ROW_DEGREE, ROW_MASK_BITS,
    SALT_BYTES, Schedule, ShapeSize, TREE_NONCE_BYTES, schedule_with_stage0,
};
use crate::zk_hem::bounds::{
    MilliBits, StageBound, interpolation_holds, interpolation_margin, johnson_list, log2_hi,
    query_bits, siblings, sum_bits,
};
use crate::zk_hem::relation::{Closing, Shape};

/// `floor(1000 log2(p^5 - 1)) - 1` for `p = 2^64 - 2^32 + 1`: the field, its nonzero elements
/// and its nonzero extension-field challenge sets have at least `2^319.998` elements.
pub const FIELD_MILLIBITS: MilliBits = 319_998;

/// Cap on `folds * (l + 2 l0 + 1) + 1` per stage in v2: at `16_384`, `fold_bits` exceeds
/// `305` bits (`319.998 - 14`), over 40 bits above the Stage-0 query error.
pub const V2_STAGE_LIST_CAP: u128 = 16_384;

/// `log2(320)` rounded up (`[CDHZ25]` Theorems A.1 and 6.9).
const QROM_RBR_CONST: MilliBits = 8_322;
/// `log2(6380)` rounded up (`[CDHZ25]` Theorems 11.3 and 8.3 plus the transcript chain).
const QROM_MERKLE_CONST: MilliBits = 12_640;
/// Slack for round offsets, verifier queries and the lower-order terms (SECURITY.md V2.7).
/// Requires `t >= 2^24`, `k < 2^9`, and `q_V + k <= 2^15`.
const QROM_ROUND_SLACK: MilliBits = 23;

/// The level every accepted table size must reach, classically and in the QROM.
pub const TARGET_LEVEL_MILLIBITS: MilliBits = 128_000;

/// A verifier round of v2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Round {
    /// Row or column sumcheck, zero-check point, mask and batching challenges.
    Sumcheck,
    /// Out-of-domain points of a stage; for Stage 0 also the five weights.
    OutOfDomain(usize),
    /// Kernel fold `phi` of a stage.
    KernelFold(usize),
    /// Affine fold `(theta, alpha, beta)` of a stage.
    AffineFold(usize),
    /// The challenge of the line `fold(Z) + beta_R R`.
    MaskLine,
    /// Fiber queries of a stage and the weights batching the resulting claims.
    Query(usize),
    /// Tuple-compression challenge `gamma` of a relation with lookups.
    LookupCompression,
    /// Pole challenge `alpha` of the lookup fractions.
    LookupPoles,
    /// Lookup sumcheck and helper claim batching.
    LookupSumcheck,
}

/// Smallest `D` for which `[CWYZ26]` (4.5) holds at multiplicity `m`, with its `M`.
fn interpolation_witness_v2(n: u128, d: u128, a: u128, m: u128) -> Option<(u128, u128)> {
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

/// `[CWYZ26]` Theorem 5.1 numerator `l + 2 l0 + 1` over `F_{p^5}`, searching multiplicities up
/// to `1024` (where the second term `(D^2 + 4 d^2 M^2 D^3) n^2 / |E|^2` stays far below `1/|E|`
/// thanks to `|E| > 2^319.998`).
pub fn affine_fold_numerator_v2(n: u128, d: u128, a: u128) -> Option<u128> {
    let b = a.checked_sub(1)?;
    let list = johnson_list(n, b, d + 1)?;
    let list0 = johnson_list(n, b, d)?;
    let mut m = 1u128;
    while m <= 1024 {
        if let Some((big_d, big_m)) = interpolation_witness_v2(n, d, a, m) {
            let nonpersistent = (2 * log2_hi(big_d))
                .max(2000 + 2 * log2_hi(d) + 2 * log2_hi(big_m) + 3 * log2_hi(big_d))
                + 1000
                + 2 * log2_hi(n);
            if nonpersistent < FIELD_MILLIBITS {
                return Some(list + 2 * list0 + 1);
            }
        }
        m *= 2;
    }
    None
}

fn stage_lists_v2(fibers: u128, blowup: u128, folds: u32, a: u128) -> Option<u128> {
    let mut worst = 0u128;
    for level in 0..folds {
        let scale = 1u128 << level;
        let n = fibers * scale;
        worst = worst.max(affine_fold_numerator_v2(n, n / blowup + 2, a * scale)?);
    }
    (u128::from(folds) * worst + 1 < V2_STAGE_LIST_CAP).then_some(worst)
}

/// Stage bound over `F_{p^5}` with [`V2_STAGE_LIST_CAP`].
pub fn stage_bound_v2(
    blowup: usize,
    step_vars: usize,
    queries: usize,
    rem_after: usize,
    agreement: Option<u128>,
) -> Option<StageBound> {
    let fibers = (blowup as u128) << rem_after;
    let folds = step_vars as u32;
    let top = fibers.checked_sub(u128::from(folds))?;
    let feasible = |a: u128| stage_lists_v2(fibers, blowup as u128, folds, a);
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
        fold_bits: FIELD_MILLIBITS - log2_hi(list),
    })
}

/// Bound for the packed rate-half domain, including the two overflow coefficients.
fn rate_half_stage_bound(spec: &super::params::StageSpec, rem: usize) -> Option<StageBound> {
    let n = 2u128 << rem;
    let a = 3 * n / 4 + 2;
    if spec.blowup != 2 || !(1..=6).contains(&spec.step_vars) || a + spec.step_vars as u128 > n {
        return None;
    }
    let mut stage = stage_bound_v2(2, spec.step_vars, spec.num_queries, rem, Some(a))?;
    // A candidate at a+2 lifts to 2^s a+2 agreements before the binary folds.
    // DKT26 gives equality of the *full* agreement sets at the scalar mask line.
    stage.query_bits = query_bits(n, a + 1, spec.num_queries.min(n as usize));
    let points = n << spec.step_vars;
    // Two explanations at the entry threshold would agree beyond their degree.
    if 2 * (a << spec.step_vars) <= points + points / 2 + 2 {
        return None;
    }
    stage.word_list = 1;
    // Add the initial RVW line and four bridge exceptional challenges. At a-1
    // agreements distinct polynomials of the possible overflow degree would
    // coincide on at least 2(a-1)-n > n/2+1 points.
    stage.list += 5;
    stage.fold_bits = FIELD_MILLIBITS - log2_hi(stage.list);
    Some(stage)
}

/// `[DKT26]` (`2026/2056`) Theorem 5.12 (characteristic-free quantitative Johnson MCA) with
/// `d = 1` for two words on the folded Stage-0 domain (`fibers` points, code dimension
/// `k = 2^rem + 2`, degree bound `D = k - 1 = 2^rem + 1`): returns `(agreement_threshold, b_cf)`
/// where `b_cf = ceil((2m + 1)^3 * fibers^2 / (3 * D))` bounds the number of exceptional
/// challenges in `E^*`.
pub fn mask_line_bad_challenges(blowup: usize, rem: usize, m: u128) -> (u128, u128) {
    assert!((3..=512).contains(&m));
    assert!(blowup.is_power_of_two() && blowup <= 256 && rem <= crate::pcs::MAX_PCS_NUM_VARS);
    let fibers = (blowup as u128) << rem;
    let k = (1u128 << rem) + 2;
    let big_d = k - 1;
    // `a / fibers >= (1 + 1/(2m)) sqrt(k / fibers)`, squared and cleared of denominators.
    let covers = |a: u128| (2 * m * a) * (2 * m * a) >= (2 * m + 1) * (2 * m + 1) * fibers * k;
    assert!(covers(fibers), "line threshold exceeds the domain");
    let (mut lo, mut hi) = (1u128, fibers);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if covers(mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    let two_m_plus_1 = 2 * m + 1;
    let cube = two_m_plus_1 * two_m_plus_1 * two_m_plus_1;
    let b_cf = (cube * fibers * fibers).div_ceil(3 * big_d);
    (lo, b_cf)
}

/// `[DKT26]` Theorem 5.12 with `d = 1`: `(agreement_threshold, -log2(b_cf / |E^*|))`.
pub fn mask_line(blowup: usize, rem: usize, m: u128) -> (u128, MilliBits) {
    let (lo, b_cf) = mask_line_bad_challenges(blowup, rem, m);
    (lo, FIELD_MILLIBITS - log2_hi(b_cf.max(1)))
}

/// `[DKT26]` Proposition 5.10 + Lemma 5.6 + Corollary 7.8 (first-order list-decodable regime
/// `e = 1`, list size `L <= 2`, radius `delta = 2/3 - k/(3n) - 1/eta_inv`, i.e. agreement
/// `a / n >= 1/3 + k/(3n) + 1/eta_inv`, with MCA exceptional set `< eta_inv * n^2` over `E^*`):
/// returns `(agreement_threshold, mca_bits, min_queries_for_128b_qrom)` taking `step_vars` fold
/// agreement losses into account.
pub fn dkt26_beyond_johnson_first_order(
    blowup: usize,
    rem: usize,
    step_vars: usize,
    eta_inv: u128,
) -> (u128, MilliBits, usize) {
    assert!(blowup.is_power_of_two() && (4..=256).contains(&blowup));
    assert!(rem <= crate::pcs::MAX_PCS_NUM_VARS && step_vars <= 6);
    assert!((4..=1 << 20).contains(&eta_inv));
    let fibers = (blowup as u128) << rem;
    let k = (1u128 << rem) + 2;
    // Clear denominators of `a / fibers >= 1/3 + k / (3 * fibers) + 1 / eta_inv`:
    // `3 * eta_inv * a >= eta_inv * (fibers + k) + 3 * fibers`.
    let rhs = eta_inv * (fibers + k) + 3 * fibers;
    let denom = 3 * eta_inv;
    let threshold = rhs.div_ceil(denom);
    assert!(threshold + step_vars as u128 <= fibers);
    // Lemma 5.6 + Prop 5.10 at `e = 1`: bad challenges `<= eta_inv * fibers^2` (+ L^2 = 4 claim
    // pairs).
    let bad = eta_inv * fibers * fibers + 4;
    let mca_bits = FIELD_MILLIBITS - log2_hi(bad);
    // Required query RBR bits so `qrom_work_bits >= 128_000` alongside 400-bit digests:
    // `query_bits - 1000 >= 265_010` => `query_bits >= 266_010`.
    let agree_after_folds = threshold + step_vars as u128;
    let mut lo = 1usize;
    let mut hi = 2048usize;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if query_bits(fibers, agree_after_folds, mid.min(fibers as usize))
            .is_none_or(|b| b - 1000 >= 265_010)
        {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    (threshold, mca_bits, lo)
}

/// Round-by-round errors of the optional LogUp lookup rounds over `F_{p^5}`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LookupTerms {
    pub compression: MilliBits,
    pub poles: MilliBits,
    pub sumcheck: MilliBits,
}

/// [`LookupTerms`] at Stage-0 word list sizes `list` and `helper_list`.
pub fn lookup_terms(size: LookupSize, list: u128, helper_list: u128) -> LookupTerms {
    let (lookups, rows) = (size.lookups as u128, size.table_rows as u128);
    let bits = |numerator: u128| FIELD_MILLIBITS - log2_hi(numerator.max(1));
    let degree = size.log_entries().max(5) as u128;
    // A registered but unused table may still carry adversarial multiplicities.
    let pairs = if lookups == 0 {
        rows.saturating_sub(1)
    } else {
        lookups * rows
    };
    LookupTerms {
        compression: bits((size.width as u128).saturating_sub(1) * pairs * list),
        poles: bits((lookups + 2 * rows + 1) * list),
        sumcheck: bits(degree * list * helper_list),
    }
}

fn compiled_qrom_sum_bits(rbr: MilliBits, log_t: MilliBits) -> MilliBits {
    sum_bits(
        rbr - QROM_RBR_CONST - QROM_ROUND_SLACK - 2 * log_t,
        8000 * DIGEST_BYTES as i64 - QROM_MERKLE_CONST - QROM_ROUND_SLACK - 3 * log_t,
    )
}

/// A lookup's tuple width and number of pairs depend on the actual relation.
pub(super) fn rate_half_lookup_supported(size: LookupSize) -> bool {
    let terms = lookup_terms(size, 1, 1);
    let bits = terms.compression.min(terms.poles).min(terms.sumcheck);
    bits >= 264_500
        && compiled_qrom_sum_bits(bits, TARGET_LEVEL_MILLIBITS) >= 0
        && compiled_qrom_sum_bits(bits, 64_000) >= TARGET_LEVEL_MILLIBITS
}

/// The bounds of one profile at one relation size.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Report {
    pub profile: Profile,
    pub log_cells: usize,
    pub schedule: Schedule,
    pub stages: Vec<StageBound>,
    pub rounds: usize,
    pub rbr_bits: MilliBits,
    pub rbr_round: Round,
    pub mask_m: u128,
    pub mask_bits: MilliBits,
    pub blind_cells: usize,
    pub opened_symbols: usize,
    pub mask_values: usize,
    /// Independently salted Stage-0 trees in a single-prover proof.
    pub stage0_trees: usize,
    /// Helper blinding budget, opened base symbols and extension-field mask values.
    pub helper_mask_budget: Option<(usize, usize, usize)>,
    pub proof_bytes: usize,
    pub digests: usize,
    pub merkle_hashes: u128,
}

impl Report {
    pub fn view_perfectly_simulated(&self) -> bool {
        self.blind_cells >= self.opened_symbols + LIMBS * self.mask_values
            && self
                .helper_mask_budget
                .is_none_or(|(b, opened, masks)| b >= opened + LIMBS * masks)
    }

    fn digest_millibits(&self) -> MilliBits {
        8000 * DIGEST_BYTES as i64
    }

    fn classical_sum_bits(&self, log_t: MilliBits) -> MilliBits {
        sum_bits(
            self.rbr_bits - log_t,
            self.digest_millibits() - 2000 - 2 * log_t,
        )
    }

    pub fn classical_work_bits(&self) -> MilliBits {
        let (mut lo, mut hi) = (0, self.rbr_bits.min((self.digest_millibits() - 2000) / 2));
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

    pub fn classical_error_bits(&self, log_queries: u32) -> MilliBits {
        assert!(log_queries >= 2);
        let t = 1000 * i64::from(log_queries);
        self.classical_sum_bits(t)
    }

    pub fn qrom_work_terms(&self) -> (MilliBits, MilliBits) {
        (
            (self.rbr_bits - QROM_RBR_CONST - QROM_ROUND_SLACK) / 2,
            (self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK) / 3,
        )
    }

    fn qrom_sum_bits(&self, log_t: MilliBits) -> MilliBits {
        compiled_qrom_sum_bits(self.rbr_bits, log_t)
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

    pub fn qrom_error_bits(&self, log_queries: u32) -> MilliBits {
        assert!(log_queries >= 24 && self.rounds < 1 << 9);
        let t = 1000 * i64::from(log_queries);
        self.qrom_sum_bits(t)
    }

    /// Add the cross-proof `tree_nonce` collision hybrid for `P = 2^log_proofs` proofs:
    /// because every Stage-0 leaf binds its proof's fresh 256-bit `tree_nonce` and its own
    /// `leaf_idx`, two Stage-0 leaves collide in prefix only if two proofs draw the same
    /// `tree_nonce`, which happens with probability `binom(P, 2) / 2^256 <= P^2 / 2^257`
    /// independent of the Stage-0 fiber count `|D'|`.
    fn with_salt_collisions(&self, query_bits: MilliBits, log_proofs: u32) -> MilliBits {
        if log_proofs == 0 {
            return query_bits;
        }
        let collision_bits = 1000 * (8 * TREE_NONCE_BYTES as i64 + 1 - 2 * i64::from(log_proofs));
        sum_bits(query_bits, collision_bits)
    }

    pub fn classical_hiding_bits(&self, log_queries: u32, log_proofs: u32) -> MilliBits {
        let log_proofs = log_proofs + self.stage0_trees.ilog2();
        self.with_salt_collisions(
            1000 * (8 * SALT_BYTES as i64 - i64::from(log_queries) - i64::from(log_proofs)),
            log_proofs,
        )
    }

    pub fn quantum_hiding_bits(&self, log_queries: u32, log_proofs: u32) -> MilliBits {
        let log_proofs = log_proofs + self.stage0_trees.ilog2();
        self.with_salt_collisions(
            500 * (8 * SALT_BYTES as i64 - i64::from(log_proofs))
                - 1000 * (i64::from(log_queries) + 1),
            log_proofs,
        )
    }
}

fn opening_byte_and_digest_bounds(
    log_cells: usize,
    schedule: &Schedule,
    stages: &[StageBound],
) -> (usize, usize, u128) {
    let fold_vars = log_cells - schedule.early_stop_vars;
    let mut digests = stages.len();
    let mut bytes = TREE_NONCE_BYTES
        + DIGEST_BYTES
        + EXT_BYTES * (MASK_POINTS + 5 * fold_vars + 1 + (1usize << schedule.early_stop_vars) + 2);
    let mut merkle_hashes = 0u128;
    let mut rem = log_cells;
    for (i, st) in stages.iter().enumerate() {
        let log_leaves = rem + st.blowup.trailing_zeros() as usize - st.step_vars;
        let opened = st.queries.min(st.fibers as usize);
        let sib = siblings(opened, log_leaves);
        digests += sib;
        merkle_hashes += 2 * st.fibers;
        bytes += 4 + DIGEST_BYTES * sib;
        bytes += if i == 0 {
            opened * (SALT_BYTES + (8usize << st.step_vars) + EXT_BYTES)
        } else {
            DIGEST_BYTES + LATER_OOD_POINTS * EXT_BYTES + opened * (EXT_BYTES << st.step_vars)
        };
        rem -= st.step_vars;
    }
    (bytes, digests, merkle_hashes)
}

/// The report for a table of `2^log_cells` cells under `schedule`, with the front rounds of
/// a relation of `size`.
pub fn report_with(
    profile: Profile,
    size: ShapeSize,
    log_cells: usize,
    var_bits: usize,
    blind_cells: usize,
    schedule: &Schedule,
) -> Option<Report> {
    report_with_lookup(
        profile,
        size,
        None,
        log_cells,
        var_bits,
        blind_cells,
        schedule,
    )
}

/// [`report_with`] extended with optional LogUp lookup rounds and helper opening.
#[allow(clippy::too_many_arguments)]
pub fn report_with_lookup(
    profile: Profile,
    size: ShapeSize,
    lookup: Option<(LookupSize, &LookupLayout)>,
    log_cells: usize,
    var_bits: usize,
    blind_cells: usize,
    schedule: &Schedule,
) -> Option<Report> {
    if !(MIN_LOG_CELLS..=crate::pcs::MAX_PCS_NUM_VARS).contains(&log_cells)
        || !(5..usize::BITS as usize).contains(&size.log_rows)
        || !(16..=1usize << log_cells).contains(&size.num_vars)
        || size.num_public > size.num_vars - 16
        || !(1..=log_cells).contains(&var_bits)
        || schedule.stages.is_empty()
        || schedule.early_stop_vars >= log_cells
        || schedule.stages.iter().enumerate().any(|(i, st)| {
            st.step_vars == 0
                || st.step_vars > log_cells
                || st.num_queries == 0
                || !st.blowup.is_power_of_two()
                || !((4..=256).contains(&st.blowup)
                    || (i == 0 && profile.rate_half() && st.blowup == 2))
        })
        || schedule
            .stages
            .iter()
            .try_fold(log_cells, |rem, st| rem.checked_sub(st.step_vars))
            != Some(schedule.early_stop_vars)
    {
        return None;
    }
    let mut rem = log_cells;
    let base: Vec<StageBound> = schedule
        .stages
        .iter()
        .enumerate()
        .map(|(i, spec)| {
            rem -= spec.step_vars;
            if i == 0 && profile.rate_half() {
                rate_half_stage_bound(spec, rem)
            } else {
                stage_bound_v2(spec.blowup, spec.step_vars, spec.num_queries, rem, None)
            }
        })
        .collect::<Option<_>>()?;
    let spec0 = schedule.stages[0];
    let rem0 = log_cells - spec0.step_vars;

    let helper_report = if let Some((_, ll)) = lookup {
        let helper_size = ShapeSize {
            log_rows: 5,
            num_vars: 16,
            num_public: 0,
        };
        Some((
            ll,
            report_with_lookup(
                profile,
                helper_size,
                None,
                ll.log_cells,
                4,
                ll.blind_cells,
                &ll.schedule,
            )?,
        ))
    } else {
        None
    };

    let evaluate = |stages: &[StageBound], mask: MilliBits| -> (MilliBits, Round) {
        let mut worst = (MilliBits::MAX, Round::Sumcheck);
        let mut note = |bits: MilliBits, round: Round| {
            if bits < worst.0 {
                worst = (bits, round);
            }
        };
        let degree = size
            .log_rows
            .max(ROW_DEGREE)
            .max((1 << ROW_MASK_BITS) - 1)
            .max(4 + size.num_public) as u128;
        note(
            FIELD_MILLIBITS - log2_hi(degree * stages[0].word_list),
            Round::Sumcheck,
        );
        if let (Some((ls, _)), Some((_, hr))) = (lookup, &helper_report) {
            let terms = lookup_terms(ls, stages[0].word_list, hr.stages[0].word_list);
            note(terms.compression, Round::LookupCompression);
            note(terms.poles, Round::LookupPoles);
            note(terms.sumcheck, Round::LookupSumcheck);
            note(hr.rbr_bits, hr.rbr_round);
        }
        note(mask, Round::MaskLine);
        let mut rem = log_cells;
        for (i, st) in stages.iter().enumerate() {
            let degree = (1u128 << rem) + 2;
            let points = if i == 0 {
                MASK_POINTS
            } else {
                LATER_OOD_POINTS
            } as i64;
            let mut ood =
                points * (FIELD_MILLIBITS - log2_hi(degree)) + 1000 - 2 * log2_hi(st.word_list);
            if i == 0 {
                ood = ood.min(FIELD_MILLIBITS - log2_hi(MASK_POINTS as u128 * st.word_list));
            }
            note(ood, Round::OutOfDomain(i));
            let fold = FIELD_MILLIBITS - log2_hi(st.list);
            note(fold, Round::KernelFold(i));
            note(fold, Round::AffineFold(i));
            let batch = stages.get(i + 1).map_or(MilliBits::MAX, |next| {
                FIELD_MILLIBITS - log2_hi((st.queries as u128 + 2) * next.word_list) - 1000
            });
            let query = st.query_bits.map_or(MilliBits::MAX, |bits| bits - 1000);
            if query.min(batch) != MilliBits::MAX {
                note(query.min(batch), Round::Query(i));
            }
            rem -= st.step_vars;
        }
        worst
    };

    let mut best: Option<(MilliBits, Round, u128, MilliBits, Vec<StageBound>)> = None;
    // At rate one half, m=16 suffices at the inner agreement on every supported domain.
    let multiplicities = if profile.rate_half() {
        16..=16
    } else {
        3..=512u128
    };
    for m in multiplicities {
        let (threshold, b_cf) = mask_line_bad_challenges(spec0.blowup, rem0, m);
        let binding = threshold > base[0].agreement;
        if profile.rate_half() && binding {
            return None;
        }
        let mut stages = base.clone();
        if binding {
            stages[0] = stage_bound_v2(
                spec0.blowup,
                spec0.step_vars,
                spec0.num_queries,
                rem0,
                Some(threshold),
            )?;
        }
        let pairs = johnson_list(stages[0].fibers, stages[0].agreement, (1u128 << rem0) + 1)?;
        let mask = FIELD_MILLIBITS - log2_hi((b_cf + pairs).max(1));
        let (bits, round) = evaluate(&stages, mask);
        if best.as_ref().is_none_or(|b| bits > b.0) {
            best = Some((bits, round, m, mask, stages));
        }
        if !binding {
            break;
        }
    }
    let (rbr_bits, rbr_round, mask_m, mask_bits, stages) = best?;

    let fold_vars = log_cells - schedule.early_stop_vars;
    let mut rounds =
        5 + size.log_rows + var_bits + 2 + 2 * fold_vars + 1 + (stages.len() - 1) + stages.len();
    let front = 1 + (ROW_DEGREE + 1) * size.log_rows + 3 + 1 + (COL_DEGREE + 1) * var_bits;
    let (open_bytes, mut digests, mut merkle_hashes) =
        opening_byte_and_digest_bounds(log_cells, schedule, &stages);
    let mut proof_bytes = 8 + 1 + 1 + EXT_BYTES * front + open_bytes;

    if let (Some((ls, ll)), Some((_, hr))) = (lookup, &helper_report) {
        let d = ls.log_entries();
        let helper_folds = ll.log_cells - ll.schedule.early_stop_vars;
        // gamma, alpha, lk_tau, lk_batch, lk_rho, d rounds, helper_lambda, plus helper PCS rounds.
        rounds += 6 + d + 2 + 2 * helper_folds + 1 + (hr.stages.len() - 1) + hr.stages.len();
        let lk_front = 1 + (LOOKUP_DEGREE + 1) * d + 3;
        let (h_open_bytes, h_digests, h_hashes) =
            opening_byte_and_digest_bounds(ll.log_cells, &ll.schedule, &hr.stages);
        proof_bytes += EXT_BYTES * lk_front + h_open_bytes;
        digests += h_digests;
        merkle_hashes += h_hashes;
    }

    let opened0 = spec0.num_queries.min(stages[0].fibers as usize);
    Some(Report {
        profile,
        log_cells,
        schedule: schedule.clone(),
        stages,
        rounds,
        rbr_bits,
        rbr_round,
        mask_m,
        mask_bits,
        blind_cells,
        opened_symbols: opened0 << spec0.step_vars,
        mask_values: MASK_POINTS << spec0.step_vars,
        stage0_trees: 1 + usize::from(helper_report.is_some()),
        helper_mask_budget: helper_report
            .as_ref()
            .map(|(_, h)| (h.blind_cells, h.opened_symbols, h.mask_values)),
        proof_bytes,
        digests,
        merkle_hashes,
    })
}

/// The report for a relation of `size` (no lookups) under the canonical layout and schedule.
pub fn report(profile: Profile, size: ShapeSize) -> Option<Report> {
    let layout = Layout::for_profile(profile, size, None)?;
    report_with(
        profile,
        size,
        layout.log_cells,
        layout.var_bits,
        layout.blind_cells,
        &layout.schedule,
    )
}

/// The report for a compiled v2 [`Shape`], including any [`crate::zk_hem::relation::Lookups`].
pub fn report_for_shape(profile: Profile, shape: &Shape) -> Option<Report> {
    if shape.closing() != Closing::V2 || shape.log_rows < 5 {
        return None;
    }
    let size = ShapeSize {
        log_rows: shape.log_rows,
        num_vars: shape.num_vars,
        num_public: shape.num_public,
    };
    let ls = shape.lookups().map(LookupSize::of);
    let layout = super::protocol::layout_for_profile(shape, profile)?;
    let lookup = match (ls, &layout.lookup) {
        (Some(s), Some(ll)) => Some((s, ll)),
        (None, None) => None,
        _ => return None,
    };
    report_with_lookup(
        profile,
        size,
        lookup,
        layout.log_cells,
        layout.var_bits,
        layout.blind_cells,
        &layout.schedule,
    )
}

/// Upper bound on serialized byte length of a [`super::protocol::ZkHemV2Proof`] for `shape`.
pub fn max_proof_bytes(profile: Profile, shape: &Shape) -> Option<usize> {
    Some(report_for_shape(profile, shape)?.proof_bytes)
}

/// Upper bound on serialized byte length of a [`super::protocol::ZkHemV2SplitProof`] across
/// `committers` (`1..=255`) custodians.
pub fn max_split_proof_bytes(profile: Profile, shape: &Shape, committers: usize) -> Option<usize> {
    if !(1..=super::pcs::MAX_STAGE0_SHARES).contains(&committers) {
        return None;
    }
    if profile.rate_half() {
        super::protocol::layout_for_profile(shape, profile)?.rate_half_fs_calls(committers)?;
    }
    let single = report_for_shape(profile, shape)?;
    let extra_stage0 = |log_cells: usize, _schedule: &Schedule, stages: &[StageBound]| -> usize {
        let st0 = &stages[0];
        let log_leaves = log_cells + st0.blowup.trailing_zeros() as usize - st0.step_vars;
        let opened = st0.queries.min(st0.fibers as usize);
        let sib = siblings(opened, log_leaves);
        let one_share = TREE_NONCE_BYTES
            + DIGEST_BYTES
            + opened * (SALT_BYTES + (8usize << st0.step_vars) + EXT_BYTES)
            + 4
            + DIGEST_BYTES * sib;
        (committers - 1) * one_share
    };
    let mut total =
        single.proof_bytes + 1 + extra_stage0(single.log_cells, &single.schedule, &single.stages);
    if let Some(lookups) = shape.lookups() {
        let ls = LookupSize::of(lookups);
        let ll = LookupLayout::search(ls.log_entries(), |l| profile.schedule(l))?;
        let hr = report_with(
            profile,
            size(5, 16),
            ll.log_cells,
            4,
            ll.blind_cells,
            &ll.schedule,
        )?;
        total += extra_stage0(ll.log_cells, &ll.schedule, &hr.stages);
    }
    Some(total)
}

/// The smallest Stage-0 query count at which a table of `2^log_cells` cells has a
/// QROM level at least `target`, or `None` when no count up to 2048 does.
pub fn min_stage0_queries(log_cells: usize, target: MilliBits) -> Option<usize> {
    if !(MIN_LOG_CELLS..=crate::pcs::MAX_PCS_NUM_VARS).contains(&log_cells) {
        return None;
    }
    let size = ShapeSize {
        log_rows: log_cells,
        num_vars: 1 << (log_cells - 1),
        num_public: 0,
    };
    let meets = |q: usize| {
        schedule_with_stage0(log_cells, q)
            .and_then(|s| {
                report_with(
                    Profile::CshakeJohnson400,
                    size,
                    log_cells,
                    log_cells - 1,
                    0,
                    &s,
                )
            })
            .is_some_and(|r| r.qrom_sum_bits(24_000) >= 0 && r.qrom_work_bits() >= target)
    };
    let (mut lo, mut hi) = (1usize, 2048usize);
    if !meets(hi) {
        return None;
    }
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

/// A relation with `2^log_rows` rows and `num_vars` variables.
pub fn size(log_rows: usize, num_vars: usize) -> ShapeSize {
    ShapeSize {
        log_rows,
        num_vars,
        num_public: 0,
    }
}

#[cfg(test)]
mod tests {
    use super::super::params::{
        MAX_LOG_CELLS, MIN_LOG_CELLS, STAGE0_QUERIES, blind_cells_for, mask_cells, schedule,
    };
    use super::*;
    use crate::zk_hem::bounds::{log2_lo, log2_one_plus};

    #[test]
    fn above_johnson_rate_half_budgets_and_sizes() {
        let lookups = LookupSize {
            lookups: 1 << 23,
            table_rows: 1 << 23,
            width: 3,
        };
        assert!(rate_half_lookup_supported(lookups));
        assert!(!rate_half_lookup_supported(LookupSize {
            width: 4096,
            ..lookups
        }));

        // Maximum number of siblings: occupy min(2^level, q) nodes at each level.
        fn tight_bytes(r: &Report) -> usize {
            let mut bytes = r.proof_bytes;
            for st in &r.stages {
                let q = st.queries.min(st.fibers as usize);
                let depth = st.fibers.ilog2() as usize;
                let exact = super::super::hash::max_siblings(q, depth);
                let mut spread: Vec<_> = (0..q)
                    .map(|i| i.reverse_bits() >> (usize::BITS as usize - depth))
                    .collect();
                spread.sort_unstable();
                assert_eq!(super::super::hash::multiproof_len(depth, &spread), exact);
                bytes -= DIGEST_BYTES * (siblings(q, depth) - exact);
            }
            bytes
        }

        for l in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let shape = size(l, 1 << (l - 1));
            let old = report(Profile::CshakeJohnson400, shape).unwrap();
            let r = report(Profile::CshakeRateHalf400, shape).unwrap();
            assert_eq!((old.log_cells, r.log_cells), (l, l));
            let st = &r.stages[0];
            assert_eq!(st.fibers * 2, old.stages[0].fibers);
            let a = 3 * st.fibers / 4 + 2;
            assert_eq!(st.agreement, a);
            let layout = Layout::for_profile(r.profile, shape, None).unwrap();
            assert!(layout.rate_half_fs_calls(1).unwrap() > 1024);
            let mut with_helper = layout.clone();
            with_helper.lookup = Some(LookupLayout {
                log_cells: l,
                log_entries: l - 3,
                blind_cells: layout.blind_cells,
                schedule: layout.schedule.clone(),
            });
            assert!(with_helper.rate_half_fs_calls(1).unwrap() > 1024);
            assert!(
                layout
                    .rate_half_fs_calls(super::super::pcs::MAX_STAGE0_SHARES)
                    .is_none()
            );
            assert!(r.view_perfectly_simulated());
            assert!(r.rbr_bits >= 264_500 && r.qrom_work_bits() >= TARGET_LEVEL_MILLIBITS);
            assert!(r.qrom_error_bits(64) >= TARGET_LEVEL_MILLIBITS);
            assert!(r.mask_bits >= 264_500);
            // Worst front-round degree and number of public inputs at this table size.
            let worst = report_with(
                r.profile,
                ShapeSize {
                    log_rows: usize::BITS as usize - 1,
                    num_vars: 1 << l,
                    num_public: (1 << l) - 16,
                },
                l,
                l,
                r.blind_cells,
                &r.schedule,
            )
            .unwrap();
            assert!(worst.rbr_bits >= 264_500 && worst.qrom_work_bits() >= TARGET_LEVEL_MILLIBITS);
            std::println!(
                "{l} {} {} {} {} {} {} {} {}",
                st.step_vars,
                st.fibers,
                st.queries,
                r.rbr_bits,
                r.qrom_work_bits(),
                r.qrom_error_bits(64),
                tight_bytes(&old),
                tight_bytes(&r)
            );
        }
    }

    #[test]
    fn stage0_queries_are_minimal() {
        for log_cells in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let q = STAGE0_QUERIES[log_cells - MIN_LOG_CELLS];
            assert_eq!(
                min_stage0_queries(log_cells, TARGET_LEVEL_MILLIBITS),
                Some(q),
                "log_cells = {log_cells}"
            );
            for fewer in 1..q {
                let s = schedule_with_stage0(log_cells, fewer).unwrap();
                let r = report_with(
                    Profile::CshakeJohnson400,
                    size(log_cells, 1 << (log_cells - 1)),
                    log_cells,
                    log_cells - 1,
                    0,
                    &s,
                )
                .unwrap();
                if r.qrom_sum_bits(24_000) >= 0 {
                    assert!(
                        r.qrom_work_bits() < TARGET_LEVEL_MILLIBITS,
                        "log_cells={log_cells}, earlier certificate at {fewer} queries"
                    );
                } else {
                    assert!(r.rbr_bits < 128_000);
                }
            }
        }
        assert_eq!(
            min_stage0_queries(MAX_LOG_CELLS + 1, TARGET_LEVEL_MILLIBITS),
            None
        );
    }

    #[test]
    fn every_accepted_size_reaches_128_bits_classical_and_qrom() {
        for log_cells in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let s = schedule(log_cells).unwrap();
            let st0 = s.stages[0];
            let blind = blind_cells_for(st0.step_vars, st0.num_queries);
            let n = usize::BITS as usize - 1;
            let align = 1 << super::super::params::VAR_ALIGN_MIN.max(log_cells - 8);
            let num_vars = ((1 << log_cells) - blind - mask_cells(n, log_cells)) / align * align;
            let shape = ShapeSize {
                log_rows: n,
                num_vars,
                num_public: num_vars - 16,
            };
            assert_eq!(Layout::new(shape).unwrap().log_cells, log_cells);
            for profile in [Profile::CshakeJohnson400, Profile::TurboShakeJohnson400] {
                let mut r = report(profile, shape).unwrap();
                assert!(r.qrom_work_bits() >= 128_000, "{log_cells}");
                assert!(r.classical_work_bits() >= 128_000, "{log_cells}");
                assert!(r.view_perfectly_simulated());
                assert_eq!(r.blind_cells, r.opened_symbols + LIMBS * r.mask_values);
                assert!(r.rounds < 512);
                assert!(r.rbr_bits <= 266_500);
                assert_eq!(r.qrom_work_terms().1, 129_112);
                r.blind_cells -= 1;
                assert!(!r.view_perfectly_simulated());
            }
        }
    }

    #[test]
    fn dkt26_thm512_and_beyond_johnson_prop510_rational_verification() {
        // 1. Exact rational verification of [DKT26] Theorem 5.12 (`2026/2056`, p. 53):
        //    B_cf = ceil((2m + 1)^3 * n^2 / (3 * D)) where D = 2^rem + 1.
        //    At 2^21 cells, 6 folds (`rem = 15`, `n = 2^17 = 131_072`, `D = 32_769`), `m = 256`:
        let (a21, b_cf21) = mask_line_bad_challenges(4, 15, 256);
        let n21 = 4u128 << 15;
        let k21 = (1u128 << 15) + 2;
        assert!((512 * a21).pow(2) >= 513u128.pow(2) * n21 * k21);
        assert!((512 * (a21 - 1)).pow(2) < 513u128.pow(2) * n21 * k21);
        assert_eq!(b_cf21, (513u128.pow(3) * n21 * n21).div_ceil(3 * (k21 - 1)));
        let (_, bits21) = mask_line(4, 15, 256);
        // 319.998 - log2(23_595_299_139_184) = 319.998 - 44.425 = 275.573 bits!
        assert!((275_550..=275_580).contains(&bits21), "bits21={bits21}");

        //    At the lifted ceiling 2^28 cells, 6 folds (`rem = 22`, `n = 2^24`, `D = 2^22 + 1`),
        //    `m = 128`:
        let (_, bits28) = mask_line(4, 22, 128);
        assert!((271_540..=271_570).contains(&bits28), "bits28={bits28}");

        // 2. Exact rational verification of [DKT26] Prop 5.10 + Lemma 5.6 + Cor 7.8
        //    (beyond-Johnson first-order list-2 regime: `delta = 2/3 - k/(3n) - 1/eta_inv`):
        //    At rate ~1/4 (`blowup = 4`), `a/n ~ 5/12 + 1/eta_inv` (`~0.417` vs `0.500`),
        //    requiring <= 209..259 queries depending on blowup/slack while keeping MCA > 266b!
        for (rem, eta_inv) in [(12usize, 1024u128), (15, 1024), (18, 1024), (22, 64)] {
            let (agree, mca, q_udr) = dkt26_beyond_johnson_first_order(4, rem, 6, eta_inv);
            let n = 4u128 << rem;
            let k = (1u128 << rem) + 2;
            // Strictly beyond Johnson (`agree < sqrt(k * n)`):
            assert!(
                agree * agree < k * n,
                "rem={rem}: {agree} not below Johnson"
            );
            // Exact rational inequality `a / n >= 1/3 + k / (3n) + 1/eta_inv`:
            assert!(3 * eta_inv * agree >= eta_inv * (n + k) + 3 * n);
            assert!(3 * eta_inv * (agree - 1) < eta_inv * (n + k) + 3 * n);
            assert!(mca >= 265_010, "rem={rem}: mca={mca}");
            assert!(q_udr <= 220, "rem={rem}: q_udr={q_udr}");
        }
    }

    #[test]
    fn lookup_rbr_terms_include_padded_pole_and_both_lists() {
        for (l, t, w) in [(1, 1, 2), (2, 3, 4), (17, 29, 5)] {
            let size = LookupSize {
                lookups: l,
                table_rows: t,
                width: w,
            };
            let terms = lookup_terms(size, 11, 13);
            let bound = |n: usize| FIELD_MILLIBITS - log2_hi(n as u128);
            assert_eq!(terms.compression, bound((w - 1) * l * t * 11));
            assert_eq!(terms.poles, bound((l + 2 * t + 1) * 11));
            assert_eq!(terms.sumcheck, bound(5.max(size.log_entries()) * 11 * 13));
        }
    }

    #[test]
    fn layout_puts_everything_in_one_cube() {
        let l = Layout::new(size(21, 1_088_721)).unwrap();
        assert_eq!((l.log_cells, l.var_bits), (21, 21));
        assert!(l.var_cells >= 1_088_721 && l.var_cells.is_multiple_of(1 << l.var_align));
        let st0 = l.schedule.stages[0];
        assert_eq!(l.blind_cells, (st0.num_queries + 25) << st0.step_vars);
        assert!(l.var_cells + mask_cells(21, 21) + l.blind_cells <= 1 << 21);
        // Domain cap is now lifted to 2^28: a 2^25 variable relation fits a 2^26 table!
        let large = Layout::new(size(25, 1 << 25)).unwrap();
        assert_eq!(large.log_cells, 26);
        // Past 2^28 there is no layout.
        assert!(Layout::new(size(28, 1 << 28)).is_none());
        assert!(Layout::new(size(29, 1 << 29)).is_none());
        assert!(Layout::new(size(5, usize::MAX)).is_none());
        assert!(Layout::new(size(4, 1000)).is_none());
        assert!(Layout::new(size(5, 15)).is_none());
    }

    #[test]
    fn directed_rounding_and_summed_crossovers() {
        for e in 1..=127 {
            for x in [(1u128 << e) - 1, 1u128 << e, (1u128 << e) + 1] {
                let exact = 1000.0 * (x as f64).log2();
                assert!(log2_lo(x) as f64 <= exact + 1e-8, "lo({x})");
                assert!(log2_hi(x) as f64 + 1e-8 >= exact, "hi({x})");
            }
        }
        for d in 0..=80_000 {
            let exact =
                1000.0 * (2.0f64.powf(-(d as f64) / 1000.0)).ln_1p() / core::f64::consts::LN_2;
            assert!(log2_one_plus(d) as f64 + 1e-9 >= exact, "d={d}");
            assert!(log2_one_plus(d) <= 1000);
        }
        for l in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let s = schedule(l).unwrap();
            let r = report_with(
                Profile::CshakeJohnson400,
                size(l, 1 << (l - 1)),
                l,
                l - 1,
                0,
                &s,
            )
            .unwrap();
            let q = r.qrom_work_bits();
            let c = r.classical_work_bits();
            assert!(r.qrom_sum_bits(q) >= 0 && r.qrom_sum_bits(q + 1) < 0);
            assert!(r.classical_sum_bits(c) >= 0 && r.classical_sum_bits(c + 1) < 0);
            assert_eq!(c, 198_999);
            let x = q as f64 / 1000.0;
            let exact = 320.0
                * (2.0f64.powf(x) + r.rounds as f64 + 1.0)
                * (2.0f64.powf(x) + r.rounds as f64)
                * 2.0f64.powf(-(r.rbr_bits as f64) / 1000.0)
                + 6380.0 * 2.0f64.powf(3.0 * x - 400.0);
            assert!(exact <= 1.0, "l={l}: {exact}");
        }
    }

    #[test]
    fn tree_nonce_eliminates_fiber_count_birthday_loss_in_multiproof_hiding() {
        let r17 = report(Profile::CshakeJohnson400, size(17, 82_000)).unwrap();
        let r26 = report(Profile::CshakeJohnson400, size(25, 1 << 25)).unwrap();
        assert_eq!(r17.stages[0].fibers, 1 << 14);
        assert_eq!(r26.stages[0].fibers, 1 << 22);
        assert_eq!(r17.classical_hiding_bits(64, 0), 192_000);
        // At P = 2^64 proofs, t = 1 query: `binom(P, 2) / 2^256 <= 2^-129` independent of |D'|!
        // Without tree_nonce this dropped to 114_999 at 2^14 fibers and 106_999 at 2^22 fibers.
        assert_eq!(r17.classical_hiding_bits(0, 64), 128_999);
        assert_eq!(r26.classical_hiding_bits(0, 64), 128_999);
    }

    #[test]
    fn byte_bound_matches_serializer_fields() {
        use super::super::{
            field5::Fp5,
            pcs::{ExtQuery, LaterStage, Opening, Stage0Leaf, Stage0Query},
            protocol::{MAGIC, ZkHemV2Proof},
        };
        use crate::field::Goldilocks;
        use alloc::vec;
        assert_eq!(MAGIC.len(), 8);
        for l in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let shape = size(l, 1 << (l - 1));
            let s = schedule(l).unwrap();
            let r = report_with(Profile::CshakeJohnson400, shape, l, l - 1, 0, &s).unwrap();
            let sibling_counts: Vec<_> = r
                .stages
                .iter()
                .map(|st| siblings(st.queries, st.fibers.trailing_zeros() as usize))
                .collect();
            let first = s.stages[0];
            let opening = Opening {
                mask_evals: [Fp5::ZERO; MASK_POINTS],
                stage0_folds: vec![[Fp5::ZERO; 5]; first.step_vars],
                mask_claim: Fp5::ZERO,
                stage0_query: Stage0Query {
                    leaves: vec![
                        Stage0Leaf {
                            salt: [0; SALT_BYTES],
                            z: vec![Goldilocks::ZERO; 1 << first.step_vars],
                            r: Fp5::ZERO
                        };
                        first.num_queries
                    ],
                    siblings: vec![[0; DIGEST_BYTES]; sibling_counts[0]],
                },
                stages: s
                    .stages
                    .iter()
                    .enumerate()
                    .skip(1)
                    .map(|(i, st)| LaterStage {
                        root: [0; DIGEST_BYTES],
                        ood: [Fp5::ZERO; LATER_OOD_POINTS],
                        folds: vec![[Fp5::ZERO; 5]; st.step_vars],
                        query: ExtQuery {
                            leaves: vec![vec![Fp5::ZERO; 1 << st.step_vars]; st.num_queries],
                            siblings: vec![[0; DIGEST_BYTES]; sibling_counts[i]],
                        },
                    })
                    .collect(),
                final_coeffs: vec![Fp5::ZERO; (1 << s.early_stop_vars) + 2],
            };
            let mut proof = ZkHemV2Proof {
                profile: Profile::CshakeJohnson400,
                log_cells: l as u8,
                tree_nonce: [0; TREE_NONCE_BYTES],
                root: [0; DIGEST_BYTES],
                lookup: None,
                row_mask_sum: Fp5::ZERO,
                row_rounds: vec![vec![Fp5::ZERO; ROW_DEGREE + 1]; shape.log_rows],
                row_values: [Fp5::ZERO; 3],
                col_mask_sum: Fp5::ZERO,
                col_rounds: vec![vec![Fp5::ZERO; COL_DEGREE + 1]; l - 1],
                opening,
            };
            for profile in Profile::ALL {
                proof.profile = profile;
                assert_eq!(proof.to_bytes().len(), r.proof_bytes, "l={l}");
            }
            proof.opening.stage0_query.siblings.pop().unwrap();
            assert_eq!(proof.to_bytes().len() + DIGEST_BYTES, r.proof_bytes);
        }
    }

    #[test]
    #[ignore = "prints security and DKT26 query tables: run with --ignored --nocapture"]
    fn print_v2_tables() {
        let mins: Vec<_> = (MIN_LOG_CELLS..=MAX_LOG_CELLS)
            .map(|l| (l, min_stage0_queries(l, TARGET_LEVEL_MILLIBITS)))
            .collect();
        std::println!("MIN_STAGE0_QUERIES (16..=28): {mins:?}");
        for (rows, vars) in [
            (17, 82_000),
            (17, 1 << 17),
            (20, 1 << 20),
            (21, 1_088_721),
            (22, 1 << 22),
            (23, 1 << 23),
            (25, 1 << 25),
            (27, 1 << 27),
        ] {
            let r = report(Profile::TurboShakeJohnson400, size(rows, vars)).unwrap();
            let queries: Vec<_> = r.stages.iter().map(|s| s.queries).collect();
            let (q_rbr, q_dig) = r.qrom_work_terms();
            std::println!(
                "rows=2^{rows} vars={vars} cells=2^{} queries={queries:?} m={} rbr={:.3} ({:?}) classical={:.3} qrom={:.3} ({:.3}, {:.3}) qrom_t64=2^-{:.3} proof_bytes={}",
                r.log_cells,
                r.mask_m,
                r.rbr_bits as f64 / 1000.0,
                r.rbr_round,
                r.classical_work_bits() as f64 / 1000.0,
                r.qrom_work_bits() as f64 / 1000.0,
                q_rbr as f64 / 1000.0,
                q_dig as f64 / 1000.0,
                r.qrom_error_bits(64) as f64 / 1000.0,
                r.proof_bytes,
            );
        }
    }
}
