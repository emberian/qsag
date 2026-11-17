//! Parameters of zk-Hem v2: profiles, schedule and cell layout. The protocol and its security
//! statement are `crates/qsag-agg/SECURITY.md`, section V2; [`super::bounds`] computes the
//! numbers these constants are chosen against and pins them.

use alloc::vec::Vec;

use crate::pcs::WhirSecurityRegime;

/// Bytes of a Merkle digest and of the Fiat-Shamir chaining value.
pub const DIGEST_BYTES: usize = 50;
/// Bytes of the salt in every Stage-0 leaf.
pub const SALT_BYTES: usize = 32;
/// Base-field limbs of a challenge-field element.
pub const LIMBS: usize = 5;
/// Bytes of a challenge-field element on the wire.
pub const EXT_BYTES: usize = 8 * LIMBS;
/// Out-of-domain points of Stage 0. Their evaluations are the masks of the five scalars each
/// Stage-0 fold reveals (SECURITY.md, Lemma V2.3), so this is not a free parameter.
pub const MASK_POINTS: usize = 5;
/// Out-of-domain points of every later stage.
pub const LATER_OOD_POINTS: usize = 2;
/// Individual degree of the row sumcheck.
pub const ROW_DEGREE: usize = 9;
/// Individual degree of the column sumcheck.
pub const COL_DEGREE: usize = 2;
/// `log2` of the cells holding one limb of one row-mask round.
pub const ROW_MASK_BITS: usize = 4;
/// `log2` of the cells holding one limb of one column-mask round.
pub const COL_MASK_BITS: usize = 2;
/// Variables per masking group of a v2 relation: one per limb.
pub const PAD_VARS: usize = LIMBS;
/// Rows reserved at the top of a v2 relation: three corners of eight rows, five used in each.
pub const PAD_ROWS: usize = 24;
/// Cells of the variable region are a multiple of `2^VAR_ALIGN_MIN` at least.
pub const VAR_ALIGN_MIN: usize = 4;
/// Smallest and largest table (`log2` cells) a v2 profile accepts. Above the maximum the mask
/// line of SECURITY.md Theorem V2.1 no longer reaches the round error the profiles are
/// computed for; below the minimum the table cannot hold the blinders.
pub const MIN_LOG_CELLS: usize = 16;
pub const MAX_LOG_CELLS: usize = 24;

/// A v2 parameter set. The names say which hash builds the trees and the transcript and how
/// long its digests are; the security levels are computed by [`super::bounds::report`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Profile {
    /// cSHAKE256 with 400-bit digests, Johnson-radius schedule, no grinding.
    CshakeJohnson400,
    /// TurboSHAKE256 with 400-bit digests, Johnson-radius schedule, no grinding.
    TurboShakeJohnson400,
}

impl Profile {
    pub const ALL: [Self; 2] = [Self::CshakeJohnson400, Self::TurboShakeJohnson400];

    /// Wire tag. Tags `0..=10` belong to the v1 regimes (`WhirSecurityRegime`).
    pub const fn wire_tag(self) -> u8 {
        match self {
            Self::CshakeJohnson400 => 16,
            Self::TurboShakeJohnson400 => 17,
        }
    }

    pub const fn from_wire_tag(tag: u8) -> Option<Self> {
        match tag {
            16 => Some(Self::CshakeJohnson400),
            17 => Some(Self::TurboShakeJohnson400),
            _ => None,
        }
    }

    pub const fn uses_turboshake(self) -> bool {
        matches!(self, Self::TurboShakeJohnson400)
    }
}

/// One WHIR stage: rate `1 / blowup`, `step_vars` folds, `num_queries` distinct fibers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StageSpec {
    pub blowup: usize,
    pub step_vars: usize,
    pub num_queries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schedule {
    /// Variables of the terminal polynomial, sent in full.
    pub early_stop_vars: usize,
    pub stages: Vec<StageSpec>,
}

/// Stage-0 queries for a table of `2^log_cells` cells, indexed from [`MIN_LOG_CELLS`]. Each is
/// the smallest count at which the QROM level computed by `bounds::Report::qrom_work_bits`
/// (the sum of the round term and the digest term, SECURITY.md Theorem 3) is at least 128
/// bits; `bounds::tests::stage0_queries_are_minimal` recomputes the table.
pub const STAGE0_QUERIES: [usize; MAX_LOG_CELLS - MIN_LOG_CELLS + 1] =
    [281, 281, 287, 295, 300, 300, 320, 342, 342];

/// Queries of a stage after the first at rate `1 / blowup`.
pub const fn later_stage_queries(blowup: usize) -> usize {
    (532usize).div_ceil(blowup.trailing_zeros() as usize) + 3
}

/// The folding geometry of v1 (`pcs.rs`, `stage_geometry`) with the v2 query counts.
pub fn schedule(log_cells: usize) -> Option<Schedule> {
    if !(MIN_LOG_CELLS..=MAX_LOG_CELLS).contains(&log_cells) {
        return None;
    }
    schedule_with_stage0(log_cells, STAGE0_QUERIES[log_cells - MIN_LOG_CELLS])
}

/// [`schedule`] with a caller-chosen Stage-0 query count, for the calculator.
pub fn schedule_with_stage0(log_cells: usize, stage0_queries: usize) -> Option<Schedule> {
    if !(MIN_LOG_CELLS..=crate::pcs::MAX_PCS_NUM_VARS).contains(&log_cells) {
        return None;
    }
    let geometry = WhirSecurityRegime::BciksJohnsonQrom128.schedule(log_cells);
    let stages = geometry
        .stages
        .iter()
        .enumerate()
        .map(|(i, st)| StageSpec {
            blowup: st.blowup,
            step_vars: st.step_vars,
            num_queries: if i == 0 {
                stage0_queries
            } else {
                later_stage_queries(st.blowup)
            },
        })
        .collect();
    Some(Schedule {
        early_stop_vars: geometry.early_stop_vars,
        stages,
    })
}

/// Size of a v2 relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapeSize {
    pub log_rows: usize,
    /// Variables, including the constant and the fifteen masking variables.
    pub num_vars: usize,
    pub num_public: usize,
}

/// Cell layout of the assignment table.
///
/// ```text
/// [ variables | zeros | row masks | column masks | zeros | blinders ]
///   0           num_vars  mask_base                        cells - blind_cells
/// ```
///
/// Everything sits in one cube of `2^log_cells` cells; the column sumcheck runs over the
/// `var_bits`-cube and its terminal functional reads the cells below `var_cells` only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub log_cells: usize,
    /// `ceil(log2 num_vars)`, at least 1: variables of the column sumcheck.
    pub var_bits: usize,
    /// End of the variable region: `num_vars` rounded up to a multiple of `2^var_align`.
    pub var_cells: usize,
    pub var_align: usize,
    /// First cell of the sumcheck masks; equals `var_cells`.
    pub mask_base: usize,
    /// Uniform cells at the top of the table: one per opened Stage-0 symbol and five per
    /// challenge-field value of the Stage-0 mask points (SECURITY.md, Lemma V2.2).
    pub blind_cells: usize,
    pub schedule: Schedule,
}

/// Cells of the two sumcheck masks.
pub const fn mask_cells(log_rows: usize, var_bits: usize) -> usize {
    ((log_rows * LIMBS) << ROW_MASK_BITS) + ((var_bits * LIMBS) << COL_MASK_BITS)
}

/// Blinding cells for a Stage-0 stage: every opened symbol, and `LIMBS` cells for each of the
/// `2^step_vars` residues at each of the [`MASK_POINTS`] points.
pub const fn blind_cells_for(step_vars: usize, opened_fibers: usize) -> usize {
    (opened_fibers + LIMBS * MASK_POINTS) << step_vars
}

impl Layout {
    /// The smallest table holding the variables, the masks and the blinders.
    pub fn new(size: ShapeSize) -> Option<Self> {
        Self::search(size, schedule)
    }

    /// [`Self::new`] over an arbitrary schedule function, for the calculator.
    pub fn search(size: ShapeSize, schedule: impl Fn(usize) -> Option<Schedule>) -> Option<Self> {
        // A v2 relation has a constant, fifteen pads and at least 24 reserved rows.
        // Bound before rounding or shifting: malformed sizes must not overflow, and the
        // finite row cube also keeps the round count within the calculator's envelope.
        if size.num_vars < 1 + 3 * PAD_VARS
            || size.num_vars > 1usize << crate::pcs::MAX_PCS_NUM_VARS
            || size.num_public > size.num_vars - 1 - 3 * PAD_VARS
            || !(5..usize::BITS as usize).contains(&size.log_rows)
        {
            return None;
        }
        let var_bits = size.num_vars.next_power_of_two().trailing_zeros().max(1) as usize;
        let var_align = VAR_ALIGN_MIN.max(var_bits.saturating_sub(8));
        let var_cells = size.num_vars.next_multiple_of(1 << var_align);
        let masks = mask_cells(size.log_rows, var_bits);
        (var_bits.max(MIN_LOG_CELLS)..=crate::pcs::MAX_PCS_NUM_VARS).find_map(|log_cells| {
            let schedule = schedule(log_cells)?;
            let st0 = schedule.stages[0];
            let cells = 1usize << log_cells;
            let fibers = (cells * st0.blowup) >> st0.step_vars;
            let blind_cells = blind_cells_for(st0.step_vars, st0.num_queries.min(fibers));
            (var_cells + masks + blind_cells <= cells).then_some(Self {
                log_cells,
                var_bits,
                var_cells,
                var_align,
                mask_base: var_cells,
                blind_cells,
                schedule,
            })
        })
    }

    #[inline]
    pub fn row_mask_block(&self, round: usize, limb: usize) -> usize {
        self.mask_base + ((round * LIMBS + limb) << ROW_MASK_BITS)
    }

    #[inline]
    pub fn col_mask_block(&self, log_rows: usize, round: usize, limb: usize) -> usize {
        self.row_mask_block(log_rows, 0) + ((round * LIMBS + limb) << COL_MASK_BITS)
    }
}
