//! Concrete security accounting for zk-Hem v2, in the conventions of
//! [`crate::zk_hem::bounds`] (integers only; an error is a lower bound on `-log2` in
//! thousandths of a bit; logarithms round against the claim). The theorems are in
//! `crates/qsag-agg/SECURITY.md`, section V2; this module computes their numbers.
//!
//! What differs from the v1 calculator:
//!
//! * the challenge field is the quintic extension ([`FIELD_MILLIBITS`]);
//! * there is no five-table blend. The only batching of committed words is the line
//!   `fold(Z) + beta R` on the folded Stage-0 domain, bounded by `[BCGM25]` Lemma 9.3 with
//!   `d = 1` ([`mask_line`]);
//! * Stage 0 has five out-of-domain points instead of two;
//! * no grinding, so the classical and the quantum round-by-round errors coincide;
//! * digests of 400 bits and salts of 256 bits.
//!
//! The affine-fold witnesses are searched by `bounds::affine_fold_numerator`, which requires
//! numerator `C` of the second term `C / |F|^2` in `[CWYZ26]` (4.13) to be below
//! `2^255.998`. Thus `C < |F|` also for the quintic field, and that term is below `1 / |F|`.

use alloc::vec::Vec;

use super::params::{
    COL_DEGREE, DIGEST_BYTES, EXT_BYTES, LATER_OOD_POINTS, LIMBS, Layout, MASK_POINTS, Profile,
    ROW_DEGREE, ROW_MASK_BITS, SALT_BYTES, Schedule, ShapeSize, schedule_with_stage0,
};
use crate::zk_hem::bounds::{
    MilliBits, StageBound, johnson_list, log2_hi, log2_lo, siblings, stage_bound, sum_bits,
};

/// `floor(1000 log2(p^5 - 1)) - 1` for `p = 2^64 - 2^32 + 1`: the field, its nonzero elements
/// and its nonzero extension-field challenge sets have at least `2^319.998` elements.
pub const FIELD_MILLIBITS: MilliBits = 319_998;

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
    /// The challenge of the line `fold(Z) + beta R`.
    MaskLine,
    /// Fiber queries of a stage and the weights batching the resulting claims.
    Query(usize),
}

/// `[BCGM25]` Lemma 9.3 with `d = 1` for two words on the folded Stage-0 domain (`fibers`
/// points, code dimension `2^rem + 2`): the smallest agreement threshold covered by proximity
/// parameter `m >= 3`, and `-log2` of the error `(m + 1/2)^7 n^2 / (3 rho^(3/2) |F|)` for a
/// challenge uniform among the nonzero elements.
pub fn mask_line(blowup: usize, rem: usize, m: u128) -> (u128, MilliBits) {
    // The calculator searches this finite parameter range; keep all cleared-denominator
    // products within u128 and do not mistake trailing_zeros for log2 of an arbitrary rate.
    assert!((3..=256).contains(&m));
    assert!(blowup.is_power_of_two() && blowup <= 256 && rem <= crate::pcs::MAX_PCS_NUM_VARS);
    let fibers = (blowup as u128) << rem;
    let k = (1u128 << rem) + 2;
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
    // `(2m + 1)^7 / 2^7 / 3 * rho^(-3/2) * n^2` with `rho >= 1 / blowup`; `384 = 2^7 * 3`.
    let numerator =
        7 * log2_hi(2 * m + 1) + 1500 * i64::from(blowup.trailing_zeros()) + 2 * log2_hi(fibers)
            - log2_lo(384);
    (lo, FIELD_MILLIBITS - numerator - 1)
}

/// The bounds of one profile at one relation size.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Report {
    pub profile: Profile,
    pub log_cells: usize,
    pub schedule: Schedule,
    /// Stage bounds at the thresholds the analysis uses; `fold_bits` is recomputed for the
    /// quintic field.
    pub stages: Vec<StageBound>,
    /// Verifier rounds.
    pub rounds: usize,
    /// `-log2` of the largest round-by-round error, and the round where it occurs.
    pub rbr_bits: MilliBits,
    pub rbr_round: Round,
    /// Proximity parameter of `[BCGM25]` Lemma 9.3 at which the analysis runs.
    pub mask_m: u128,
    /// Error of the mask-line round.
    pub mask_bits: MilliBits,
    /// Uniform cells at the top of the table.
    pub blind_cells: usize,
    /// Base-field symbols of the assignment codeword opened by the Stage-0 queries.
    pub opened_symbols: usize,
    /// Challenge-field values of the assignment that the Stage-0 mask points expose
    /// (`MASK_POINTS * 2^step_vars` residues).
    pub mask_values: usize,
    /// Upper bound on the serialized proof.
    pub proof_bytes: usize,
    /// Merkle digests in that bound.
    pub digests: usize,
    /// Leaf, internal-node and root-wrapper hashes (excluding salt derivation).
    pub merkle_hashes: u128,
}

impl Report {
    /// The blinder-count condition of Lemma V2.2 only. The ideal-oracle simulation also
    /// requires Good, the supported statement kernel, and the front-end masks of V2.1.
    pub fn view_perfectly_simulated(&self) -> bool {
        self.blind_cells >= self.opened_symbols + LIMBS * self.mask_values
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

    /// Certified classical crossover of the SUM `t eps_rbr + 4 t^2 / 2^sigma`.
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

    /// `-log2` of the classical bound at `2^log_queries` queries.
    pub fn classical_error_bits(&self, log_queries: u32) -> MilliBits {
        // The simplification in Theorem 2 requires t >= 3.
        assert!(log_queries >= 2);
        let t = 1000 * i64::from(log_queries);
        self.classical_sum_bits(t)
    }

    /// The two terms of the QROM bound `320 (t + k + 1)(t + k) eps_rbr + 6380 t^3 / 2^sigma`
    /// (SECURITY.md Theorem 3) as query counts at which each is vacuous: `(round, digest)`.
    pub fn qrom_work_terms(&self) -> (MilliBits, MilliBits) {
        (
            (self.rbr_bits - QROM_RBR_CONST - QROM_ROUND_SLACK) / 2,
            (self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK) / 3,
        )
    }

    /// `-log2` of the sum of the two terms at `t = 2^(log_t / 1000)` queries.
    fn qrom_sum_bits(&self, log_t: MilliBits) -> MilliBits {
        sum_bits(
            self.rbr_bits - QROM_RBR_CONST - QROM_ROUND_SLACK - 2 * log_t,
            self.digest_millibits() - QROM_MERKLE_CONST - QROM_ROUND_SLACK - 3 * log_t,
        )
    }

    /// The QROM level under the cited theorems and models D1, D3 of SECURITY.md: the largest
    /// millibit `log2 t` certified by the rounded upper bound on the SUM. This is a lower
    /// bound on its real crossover, below both entries of [`Self::qrom_work_terms`].
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

    /// `-log2` of the QROM bound at `2^log_queries >= 2^24` queries.
    pub fn qrom_error_bits(&self, log_queries: u32) -> MilliBits {
        assert!(log_queries >= 24 && self.rounds < 1 << 9);
        let t = 1000 * i64::from(log_queries);
        self.qrom_sum_bits(t)
    }

    /// Add the salt-collision hybrid for P proofs, each with at most this report's number
    /// of Stage-0 leaves: `leaves * binom(P, 2) / 2^salt <= leaves * P^2 / 2^(salt+1)`.
    fn with_salt_collisions(&self, query_bits: MilliBits, log_proofs: u32) -> MilliBits {
        if log_proofs == 0 {
            return query_bits; // One proof: indices distinguish every pair of its leaves.
        }
        let collision_bits = 1000 * (8 * SALT_BYTES as i64 + 1 - 2 * i64::from(log_proofs))
            - log2_hi(self.stages[0].fibers);
        sum_bits(query_bits, collision_bits)
    }

    /// Hiding of unopened Stage-0 leaves against `2^log_queries` classical queries over
    /// `2^log_proofs` proofs of at most this size: `t P / 2^salt` plus salt collisions.
    pub fn classical_hiding_bits(&self, log_queries: u32, log_proofs: u32) -> MilliBits {
        self.with_salt_collisions(
            1000 * (8 * SALT_BYTES as i64 - i64::from(log_queries) - i64::from(log_proofs)),
            log_proofs,
        )
    }

    /// The same against quantum queries: `2 t sqrt(P / 2^salt)` plus salt collisions.
    pub fn quantum_hiding_bits(&self, log_queries: u32, log_proofs: u32) -> MilliBits {
        self.with_salt_collisions(
            500 * (8 * SALT_BYTES as i64 - i64::from(log_proofs))
                - 1000 * (i64::from(log_queries) + 1),
            log_proofs,
        )
    }
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
    if !(super::params::MIN_LOG_CELLS..=crate::pcs::MAX_PCS_NUM_VARS).contains(&log_cells)
        || !(5..usize::BITS as usize).contains(&size.log_rows)
        || !(16..=1usize << log_cells).contains(&size.num_vars)
        || size.num_public > size.num_vars - 16
        || !(1..=log_cells).contains(&var_bits)
        || schedule.stages.is_empty()
        || schedule.early_stop_vars >= log_cells
        || schedule.stages.iter().any(|st| {
            st.step_vars == 0
                || st.step_vars > log_cells
                || st.num_queries == 0
                || !st.blowup.is_power_of_two()
                || !(4..=256).contains(&st.blowup)
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
        .map(|spec| {
            rem -= spec.step_vars;
            stage_bound(spec.blowup, spec.step_vars, spec.num_queries, rem, None)
        })
        .collect::<Option<_>>()?;
    let spec0 = schedule.stages[0];
    let rem0 = log_cells - spec0.step_vars;

    let evaluate = |stages: &[StageBound], mask: MilliBits| -> (MilliBits, Round) {
        let mut worst = (MilliBits::MAX, Round::Sumcheck);
        let mut note = |bits: MilliBits, round: Round| {
            if bits < worst.0 {
                worst = (bits, round);
            }
        };
        // One polynomial identity of at most this degree per member of the Stage-0 list. A
        // committed row-mask block is any univariate of degree below `2^ROW_MASK_BITS`: the
        // verifier does not check that its coefficients above `ROW_DEGREE` are zero.
        let degree = size
            .log_rows
            .max(ROW_DEGREE)
            .max((1 << ROW_MASK_BITS) - 1)
            .max(4 + size.num_public) as u128;
        note(
            FIELD_MILLIBITS - log2_hi(degree * stages[0].word_list),
            Round::Sumcheck,
        );
        note(mask, Round::MaskLine);
        let mut rem = log_cells;
        for (i, st) in stages.iter().enumerate() {
            let degree = (1u128 << rem) + 2;
            let points = if i == 0 {
                MASK_POINTS
            } else {
                LATER_OOD_POINTS
            } as i64;
            // Two list members agree on every point with probability `(deg / |F|)^points`.
            let mut ood =
                points * (FIELD_MILLIBITS - log2_hi(degree)) + 1000 - 2 * log2_hi(st.word_list);
            if i == 0 {
                // The weights: one linear identity per list member.
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

    // A larger `m` lowers the Stage-0 threshold (more bits per query) and raises the error of
    // the line: take the `m` with the best weakest round.
    let mut best: Option<(MilliBits, Round, u128, MilliBits, Vec<StageBound>)> = None;
    for m in 3..=256u128 {
        let (threshold, mca) = mask_line(spec0.blowup, rem0, m);
        let binding = threshold > base[0].agreement;
        let mut stages = base.clone();
        if binding {
            stages[0] = stage_bound(
                spec0.blowup,
                spec0.step_vars,
                spec0.num_queries,
                rem0,
                Some(threshold),
            )?;
        }
        // Besides the exceptional challenges of the lemma, one root of the claim identity
        // per pair of codewords that agree with the two words on a common set.
        let pairs = johnson_list(stages[0].fibers, stages[0].agreement, (1u128 << rem0) + 1)?;
        let mask = mca.min(FIELD_MILLIBITS - log2_hi(pairs)) - 1000;
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
    // tau, rho1, row rounds, combine, rho2, column rounds, lambda; Stage-0 points and weights;
    // phi and (theta, alpha, beta) per fold; the line; points of later stages; queries.
    let rounds =
        5 + size.log_rows + var_bits + 2 + 2 * fold_vars + 1 + (stages.len() - 1) + stages.len();

    let front =
        1 + (ROW_DEGREE + 1) * size.log_rows + 3 + 1 + (COL_DEGREE + 1) * var_bits + MASK_POINTS;
    let mut digests = stages.len();
    // Magic, profile, table size; Stage-0 root; front; five scalars per fold; the mask claim;
    // the terminal polynomial.
    let mut proof_bytes = 8
        + 1
        + 1
        + DIGEST_BYTES
        + EXT_BYTES * (front + 5 * fold_vars + 1 + (1usize << schedule.early_stop_vars) + 2);
    let mut merkle_hashes = 0u128;
    let mut rem = log_cells;
    for (i, st) in stages.iter().enumerate() {
        let log_leaves = rem + st.blowup.trailing_zeros() as usize - st.step_vars;
        let opened = st.queries.min(st.fibers as usize);
        let sib = siblings(opened, log_leaves);
        digests += sib;
        merkle_hashes += 2 * st.fibers;
        proof_bytes += 4 + DIGEST_BYTES * sib;
        proof_bytes += if i == 0 {
            opened * (SALT_BYTES + (8usize << st.step_vars) + EXT_BYTES)
        } else {
            DIGEST_BYTES + LATER_OOD_POINTS * EXT_BYTES + opened * (EXT_BYTES << st.step_vars)
        };
        rem -= st.step_vars;
    }
    let opened0 = spec0.num_queries.min(stages[0].fibers as usize);
    Some(Report {
        profile,
        log_cells,
        schedule: schedule.clone(),
        stages: stages
            .into_iter()
            .map(|mut st| {
                st.fold_bits = FIELD_MILLIBITS - log2_hi(st.list);
                st
            })
            .collect(),
        rounds,
        rbr_bits,
        rbr_round,
        mask_m,
        mask_bits,
        blind_cells,
        opened_symbols: opened0 << spec0.step_vars,
        mask_values: MASK_POINTS << spec0.step_vars,
        proof_bytes,
        digests,
        merkle_hashes,
    })
}

/// The report for a relation of `size` under the canonical layout and schedule.
pub fn report(profile: Profile, size: ShapeSize) -> Option<Report> {
    let layout = Layout::new(size)?;
    report_with(
        profile,
        size,
        layout.log_cells,
        layout.var_bits,
        layout.blind_cells,
        &layout.schedule,
    )
}

/// The smallest Stage-0 query count at which a table of `2^log_cells` cells has a
/// QROM level at least `target`, or `None` when no count up to 2048 does.
pub fn min_stage0_queries(log_cells: usize, target: MilliBits) -> Option<usize> {
    if !(super::params::MIN_LOG_CELLS..=crate::pcs::MAX_PCS_NUM_VARS).contains(&log_cells) {
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
    use crate::zk_hem::bounds::log2_one_plus;

    #[test]
    fn stage0_queries_are_minimal() {
        for log_cells in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let q = STAGE0_QUERIES[log_cells - MIN_LOG_CELLS];
            assert_eq!(
                min_stage0_queries(log_cells, TARGET_LEVEL_MILLIBITS),
                Some(q),
                "log_cells = {log_cells}"
            );
            // Exhaustive negative controls: do not assume that integer rounding or the
            // search over m makes certification monotone in the query count.
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
                    assert!(r.rbr_bits < 128_000); // cannot reach 128 even before FS loss
                }
            }
        }
        // One size further the line no longer reaches the target at any query count.
        assert_eq!(
            min_stage0_queries(MAX_LOG_CELLS + 1, TARGET_LEVEL_MILLIBITS),
            None
        );
    }

    #[test]
    fn every_accepted_size_reaches_128_bits_classical_and_qrom() {
        for log_cells in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            // Maximal row exponent and public-input count, with a full aligned variable
            // region. These dominate the front degree and round count of smaller shapes.
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
            for profile in Profile::ALL {
                let mut r = report(profile, shape).unwrap();
                assert!(r.qrom_work_bits() >= 128_000, "{log_cells}");
                assert!(r.classical_work_bits() >= 128_000, "{log_cells}");
                assert!(r.view_perfectly_simulated());
                assert_eq!(r.blind_cells, r.opened_symbols + LIMBS * r.mask_values);
                assert!(r.rounds < 512);
                assert!(r.rbr_bits <= 266_000); // lower-order-term absorption in V2.7
                assert_eq!(r.qrom_work_terms().1, 129_112);
                // A strict negative control for the count predicate, not a leakage claim.
                r.blind_cells -= 1;
                assert!(!r.view_perfectly_simulated());
            }
        }
    }

    #[test]
    fn one_query_fewer_or_a_shorter_digest_misses_the_target() {
        for log_cells in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let q = STAGE0_QUERIES[log_cells - MIN_LOG_CELLS];
            let s = schedule_with_stage0(log_cells, q - 1).unwrap();
            let r = report_with(
                Profile::CshakeJohnson400,
                size(log_cells, 1 << (log_cells - 1)),
                log_cells,
                log_cells,
                0,
                &s,
            )
            .unwrap();
            assert!(r.qrom_work_bits() < 128_000);
        }
        // 48-byte digests: `(384 - 12.663) / 3`.
        const { assert!((384_000 - QROM_MERKLE_CONST - QROM_ROUND_SLACK) / 3 < 128_000) };
    }

    #[test]
    fn mask_line_matches_the_lemma_by_hand() {
        // 2^22 cells, six folds: 2^18 points, rate 1/4, m = 3.
        let (a, bits) = mask_line(4, 16, 3);
        // (1 + 1/6) * sqrt((2^16 + 2) / 2^18) * 2^18 = 152919.0..: the next integer.
        assert_eq!(a, 152_920);
        // 3.5^7 = 6433.9; / (3 * (1/4)^1.5) = 17157.1; * 2^36 -> 2^50.066; 319.998 - 50.066,
        // less the upward rounding of three logarithms.
        assert!((269_900..=269_932).contains(&bits), "{bits}");
        // The error grows with m and the threshold falls.
        let (a8, bits8) = mask_line(4, 16, 8);
        assert!(a8 < a && bits8 < bits);
    }

    #[test]
    fn layout_puts_everything_in_one_cube() {
        // 1.09M variables (the BIP-32 statement of the frontier note) fit a 2^21 table.
        let l = Layout::new(size(21, 1_088_721)).unwrap();
        assert_eq!((l.log_cells, l.var_bits), (21, 21));
        assert!(l.var_cells >= 1_088_721 && l.var_cells.is_multiple_of(1 << l.var_align));
        let st0 = l.schedule.stages[0];
        assert_eq!(l.blind_cells, (st0.num_queries + 25) << st0.step_vars);
        assert!(l.blind_cells.is_multiple_of(1 << st0.step_vars));
        assert!(l.var_cells + mask_cells(21, 21) + l.blind_cells <= 1 << 21);
        // A cube that is nearly full moves to the next size.
        let full = Layout::new(size(21, (1 << 21) - 100)).unwrap();
        assert_eq!(full.log_cells, 22);
        // Small relations use the smallest table that holds the blinders.
        let small = Layout::new(size(10, 1000)).unwrap();
        assert_eq!(small.log_cells, MIN_LOG_CELLS);
        // Past the largest table there is no layout.
        assert!(Layout::new(size(25, 1 << 25)).is_none());
        // Malformed dimensions are rejected before rounding, multiplication or shifting.
        assert!(Layout::new(size(5, usize::MAX)).is_none());
        assert!(Layout::new(size(usize::MAX, 1000)).is_none());
        assert!(Layout::new(size(4, 1000)).is_none());
        assert!(Layout::new(size(5, 15)).is_none());
        assert!(
            Layout::new(ShapeSize {
                log_rows: 5,
                num_vars: 16,
                num_public: 1
            })
            .is_none()
        );
        assert!(Layout::new(size(5, 16)).is_some());
        assert_eq!(min_stage0_queries(0, TARGET_LEVEL_MILLIBITS), None);
    }

    #[test]
    fn directed_rounding_and_summed_crossovers() {
        // Independent floating-point reference, only in this test; production is integer.
        for e in 1..=127 {
            for x in [(1u128 << e) - 1, 1u128 << e, (1u128 << e) + 1] {
                let exact = 1000.0 * (x as f64).log2();
                assert!(log2_lo(x) as f64 <= exact + 1e-8, "lo({x})");
                assert!(log2_hi(x) as f64 + 1e-8 >= exact, "hi({x})");
            }
        }
        // Includes every eighth-bit discontinuity and the large-gap branch at 40 bits.
        for d in 0..=80_000 {
            let exact =
                1000.0 * (2.0f64.powf(-(d as f64) / 1000.0)).ln_1p() / core::f64::consts::LN_2;
            assert!(log2_one_plus(d) as f64 + 1e-9 >= exact, "d={d}");
            assert!(log2_one_plus(d) <= 1000);
            assert_eq!(
                sum_bits(123_000, 123_000 + d),
                sum_bits(123_000 + d, 123_000)
            );
            assert!(sum_bits(123_000, 123_000 + d) as f64 <= 123_000.0 - exact + 1e-9);
        }
        assert_eq!(sum_bits(0, 0), -1000);
        assert_eq!(sum_bits(-1000, -1000), -2000);
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
            // At the smaller individual crossover the SUM already exceeds one.
            let (a, b) = r.qrom_work_terms();
            assert!(r.qrom_sum_bits(a.min(b)) < 0);
        }
    }

    #[test]
    fn hiding_counts_cross_proof_salt_collisions() {
        let r = report(Profile::CshakeJohnson400, size(17, 82_000)).unwrap();
        assert_eq!(r.stages[0].fibers, 1 << 14);
        assert_eq!(r.classical_hiding_bits(64, 0), 192_000);
        assert_eq!(r.quantum_hiding_bits(64, 0), 63_000);
        // P=2^64, t=1: the birthday term is about 2^-115, much larger than 2^-192.
        assert_eq!(r.classical_hiding_bits(0, 64), 114_999);
        assert!(r.quantum_hiding_bits(0, 64) < 95_000);
        let mut larger = r.clone();
        larger.stages[0].fibers *= 2;
        assert!(larger.classical_hiding_bits(0, 64) < r.classical_hiding_bits(0, 64));
    }

    #[test]
    fn calculator_rejects_malformed_geometry() {
        let l = MIN_LOG_CELLS;
        let shape = size(l, 1 << (l - 1));
        let mut s = schedule(l).unwrap();
        let calc = |size, schedule: &Schedule| {
            report_with(Profile::CshakeJohnson400, size, l, l - 1, 0, schedule)
        };
        assert!(calc(shape, &s).is_some());
        assert!(
            calc(
                ShapeSize {
                    num_public: usize::MAX,
                    ..shape
                },
                &s
            )
            .is_none()
        );
        assert!(
            calc(
                ShapeSize {
                    log_rows: usize::MAX,
                    ..shape
                },
                &s
            )
            .is_none()
        );
        s.stages[0].blowup = 3;
        assert!(calc(shape, &s).is_none());
        s = schedule(l).unwrap();
        s.stages[0].step_vars = l + 1;
        assert!(calc(shape, &s).is_none());
        s.stages.clear();
        assert!(calc(shape, &s).is_none());
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
                root: [0; DIGEST_BYTES],
                row_mask_sum: Fp5::ZERO,
                row_rounds: vec![vec![Fp5::ZERO; ROW_DEGREE + 1]; shape.log_rows],
                row_values: [Fp5::ZERO; 3],
                col_mask_sum: Fp5::ZERO,
                col_rounds: vec![vec![Fp5::ZERO; COL_DEGREE + 1]; l - 1],
                opening,
            };
            // Synthetic geometry-valid lengths, not a valid cryptographic proof. Maximal
            // multiproof siblings make the serialized length equal the model's bound.
            for profile in Profile::ALL {
                proof.profile = profile;
                assert_eq!(proof.to_bytes().len(), r.proof_bytes, "l={l}");
            }
            proof.opening.stage0_query.siblings.pop().unwrap();
            assert_eq!(proof.to_bytes().len() + DIGEST_BYTES, r.proof_bytes);
        }
    }

    #[test]
    fn documented_table_matches_calculator() {
        use alloc::format;
        use alloc::string::ToString;
        let doc = include_str!("../../../SECURITY.md");
        let mb = |b: MilliBits| format!("{}.{:03}", b / 1000, b % 1000);
        for (rows, vars, label) in [
            (17, 82_000, "2^17, 82,000"),
            (17, 1 << 17, "2^17, 2^17"),
            (20, 1 << 20, "2^20, 2^20"),
            (21, 1_088_721, "2^21, 1,088,721"),
            (22, 1 << 22, "2^22, 2^22"),
            (23, 1 << 23, "2^23, 2^23"),
        ] {
            let r = report(Profile::CshakeJohnson400, size(rows, vars)).unwrap();
            let line = doc
                .lines()
                .find(|line| line.starts_with(&format!("| {label} |")))
                .unwrap();
            let cells: Vec<_> = line.split('|').map(str::trim).collect();
            assert_eq!(cells[2], format!("2^{}", r.log_cells));
            assert_eq!(
                cells[3],
                r.schedule
                    .stages
                    .iter()
                    .map(|st| st.num_queries.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            assert_eq!(cells[4], r.mask_m.to_string());
            let round = match r.rbr_round {
                Round::MaskLine => "mask line",
                Round::Query(0) => "Stage-0 queries",
                _ => panic!("update the documented weakest round"),
            };
            assert_eq!(cells[5], format!("{} ({round})", mb(r.rbr_bits)));
            assert_eq!(cells[6], mb(r.classical_work_bits()));
            let (a, b) = r.qrom_work_terms();
            assert_eq!(
                cells[7],
                format!("**{}** ({}, {})", mb(r.qrom_work_bits()), mb(a), mb(b))
            );
            assert_eq!(cells[8], format!("2^-{}", mb(r.qrom_error_bits(64))));
            assert_eq!(
                cells[9].replace(',', "").parse::<usize>().unwrap(),
                r.proof_bytes
            );
        }
    }

    #[test]
    #[ignore = "prints the tables of SECURITY.md section V2"]
    fn print_v2_tables() {
        for log_cells in MIN_LOG_CELLS..=crate::pcs::MAX_PCS_NUM_VARS {
            let q = min_stage0_queries(log_cells, TARGET_LEVEL_MILLIBITS);
            assert_eq!(q, STAGE0_QUERIES.get(log_cells - MIN_LOG_CELLS).copied());
            std::println!("log_cells {log_cells}: min stage-0 queries {q:?}");
        }
        for (rows, vars) in [
            (17usize, 1usize << 17),
            (17, 82_000),
            (20, 1 << 20),
            (21, 1_088_721),
            (21, 1_719_058),
            (22, 1 << 22),
            (23, 1 << 23),
        ] {
            let r =
                report(Profile::CshakeJohnson400, size(rows, vars)).expect("table fixture fits");
            let (qr, qd) = r.qrom_work_terms();
            std::println!(
                "rows 2^{rows} vars {vars}: cells 2^{} queries {:?} m {} rbr {} ({:?}) mask {} \
                 classical {} qrom {} (round {qr}, digest {qd}) err@2^64 {} bytes {} digests {} \
                 hashes {} blind {} rounds {}",
                r.log_cells,
                r.schedule
                    .stages
                    .iter()
                    .map(|s| s.num_queries)
                    .collect::<Vec<_>>(),
                r.mask_m,
                r.rbr_bits,
                r.rbr_round,
                r.mask_bits,
                r.classical_work_bits(),
                r.qrom_work_bits(),
                r.qrom_error_bits(64),
                r.proof_bytes,
                r.digests,
                r.merkle_hashes,
                r.blind_cells,
                r.rounds,
            );
            for (i, st) in r.stages.iter().enumerate() {
                std::println!(
                    "  stage {i}: blowup {} folds {} q {} fibers {} A {} list {} word_list {} \
                     query {:?} fold {}",
                    st.blowup,
                    st.step_vars,
                    st.queries,
                    st.fibers,
                    st.agreement,
                    st.list,
                    st.word_list,
                    st.query_bits,
                    st.fold_bits
                );
            }
        }
    }
}
