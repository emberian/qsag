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
    MilliBits, StageBound, johnson_list, log2_hi, log2_lo, siblings, stage_bound,
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

/// An upper bound on `1000 log2(1 + 2^(-d / 1000))` for `d >= 0`: `log2(1 + x) <= x / ln 2`
/// with `x` rounded up to the next eighth of a bit, and never more than one bit.
fn log2_one_plus(d: MilliBits) -> MilliBits {
    // `ceil(1000 * 2^(-k / 8))`.
    const EIGHTHS: [i64; 8] = [1000, 918, 841, 772, 708, 649, 595, 546];
    assert!(d >= 0);
    let steps = d / 125;
    let shift = steps / 8;
    if shift >= 40 {
        return 1;
    }
    // `1443 >= 1000 / ln 2`.
    (((1443 * EIGHTHS[(steps % 8) as usize] + 999) / 1000) >> shift).min(999) + 1
}

/// A lower bound on `-log2(2^(-a / 1000) + 2^(-b / 1000))`.
fn sum_bits(a: MilliBits, b: MilliBits) -> MilliBits {
    a.min(b) - log2_one_plus((a - b).abs())
}

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
