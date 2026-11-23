//! Parameters of zk-Hem v2: profiles, schedule and cell layout. The protocol and its security
//! statement are `crates/qsag-agg/SECURITY.md`, section V2; [`super::bounds`] computes the
//! numbers these constants are chosen against and pins them.

use alloc::vec::Vec;

use crate::zk_hem::relation::{LOOKUP_CORNER_ENTRIES, Lookups};

/// Bytes of a Merkle digest and of the Fiat-Shamir chaining value.
pub const DIGEST_BYTES: usize = 50;
/// Bytes of the per-tree Stage-0 domain-separation nonce (`tree_nonce`).
pub const TREE_NONCE_BYTES: usize = 32;
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
/// Individual degree of the LogUp lookup sumcheck (`sel * eq * h * v`).
pub const LOOKUP_DEGREE: usize = 4;
/// `log2` of the cells holding one limb of one row-mask round.
pub const ROW_MASK_BITS: usize = 4;
/// `log2` of the cells holding one limb of one column-mask round.
pub const COL_MASK_BITS: usize = 2;
/// `log2` of the cells holding one limb of one lookup-mask round.
pub const LOOKUP_MASK_BITS: usize = 3;
/// Variables per masking group of a v2 relation: one per limb.
pub const PAD_VARS: usize = LIMBS;
/// Rows reserved at the top of a v2 relation: three corners of eight rows, five used in each.
pub const PAD_ROWS: usize = 24;
/// Cells of the variable region are a multiple of `2^VAR_ALIGN_MIN` at least.
pub const VAR_ALIGN_MIN: usize = 4;
/// Smallest and largest table (`log2` cells) a v2 profile accepts (`2^16..=2^28`, unlocked by
/// Dao-Kominers-Thaler `[DKT26]` Theorem 5.12).
pub const MIN_LOG_CELLS: usize = 16;
pub const MAX_LOG_CELLS: usize = 28;

/// A v2 parameter set. The names say which hash builds the trees and the transcript and how
/// long its digests are; the security levels are computed by [`super::bounds::report`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub enum Profile {
    /// cSHAKE256 with 400-bit digests, Johnson-radius schedule, no grinding.
    CshakeJohnson400,
    /// TurboSHAKE256 with 400-bit digests, Johnson-radius schedule, no grinding.
    #[default]
    TurboShakeJohnson400,
}

impl Profile {
    pub const ALL: [Self; 2] = [Self::CshakeJohnson400, Self::TurboShakeJohnson400];

    /// Canonical wire tag (`16` = `CshakeJohnson400`, `17` = `TurboShakeJohnson400`).
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

/// Stage-0 queries for a table of `2^log_cells` cells (`16..=28`), indexed from
/// [`MIN_LOG_CELLS`]. Under `[DKT26]` Theorem 5.12 (`(2m + 1)^3 * n^2 / (3 D)`), proximity
/// parameter `m <= 512` makes the mask-line round non-binding across all `2^16..=2^28` tables;
/// `bounds::tests::stage0_queries_are_minimal` recomputes and pins every entry.
pub const STAGE0_QUERIES: [usize; MAX_LOG_CELLS - MIN_LOG_CELLS + 1] =
    [267, 267, 267, 267, 267, 267, 267, 267, 266, 266, 266, 266, 266];

/// Queries of a stage after the first at rate `1 / blowup`.
pub const fn later_stage_queries(blowup: usize) -> usize {
    (532usize).div_ceil(blowup.trailing_zeros() as usize) + 3
}

/// The folding geometry of `pcs.rs` (`stage_geometry`) with the v2 query counts.
pub fn schedule(log_cells: usize) -> Option<Schedule> {
    if !(MIN_LOG_CELLS..=MAX_LOG_CELLS).contains(&log_cells) {
        return None;
    }
    let sched = schedule_with_stage0(log_cells, STAGE0_QUERIES[log_cells - MIN_LOG_CELLS])?;
    let folded_sum: u32 = sched.stages.iter().map(|s| s.step_vars as u32).sum();
    qsag_whir_verified::verify_quintic_schedule_envelope(
        log_cells as u32,
        sched.early_stop_vars as u32,
        folded_sum,
        sched.stages.len() as u32,
    )
    .then_some(sched)
}

/// [`schedule`] with a caller-chosen Stage-0 query count, for the calculator.
pub fn schedule_with_stage0(log_cells: usize, stage0_queries: usize) -> Option<Schedule> {
    if !(MIN_LOG_CELLS..=crate::pcs::MAX_PCS_NUM_VARS).contains(&log_cells) {
        return None;
    }
    let (early_stop_vars, raw_stages) = crate::pcs::stage_geometry(log_cells);
    let stages = raw_stages
        .into_iter()
        .enumerate()
        .map(|(i, (blowup, step_vars))| StageSpec {
            blowup,
            step_vars,
            num_queries: if i == 0 {
                stage0_queries
            } else {
                later_stage_queries(blowup)
            },
        })
        .collect();
    Some(Schedule {
        early_stop_vars,
        stages,
    })
}

/// Size of a v2 relation's row/variable core.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapeSize {
    pub log_rows: usize,
    /// Variables, including the constant and the masking variables.
    pub num_vars: usize,
    pub num_public: usize,
}

/// Size of the optional LogUp [`Lookups`] of a v2 relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LookupSize {
    pub lookups: usize,
    pub table_rows: usize,
    pub width: usize,
}

impl LookupSize {
    pub fn of(lookups: &Lookups) -> Self {
        Self {
            lookups: lookups.num_lookups,
            table_rows: lookups.num_table_rows,
            width: lookups.width(),
        }
    }

    pub fn log_entries(&self) -> usize {
        (self.lookups + self.table_rows + LOOKUP_CORNER_ENTRIES)
            .next_power_of_two()
            .trailing_zeros()
            .max(3) as usize
    }
}

/// Cell layout of the LogUp helper table `H`:
/// `[ limb 0..4 of h (5 * 2^d) | lookup sumcheck masks (d * 5 * 2^3) | zeros | blinders ]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupLayout {
    pub log_cells: usize,
    pub log_entries: usize,
    pub blind_cells: usize,
    pub schedule: Schedule,
}

impl LookupLayout {
    pub fn new(log_entries: usize) -> Option<Self> {
        Self::search(log_entries, schedule)
    }

    pub fn search(
        log_entries: usize,
        schedule_fn: impl Fn(usize) -> Option<Schedule>,
    ) -> Option<Self> {
        const _: () = assert!(1u64 << (MAX_LOG_CELLS - 3) < crate::field::GOLDILOCKS_PRIME);
        let d = log_entries;
        if !(3..=MAX_LOG_CELLS - 3).contains(&d) {
            return None;
        }
        let used = (LIMBS << d).checked_add((d * LIMBS) << LOOKUP_MASK_BITS)?;
        ((d + 3).max(MIN_LOG_CELLS)..=MAX_LOG_CELLS).find_map(|log_cells| {
            let schedule = schedule_fn(log_cells)?;
            let st0 = schedule.stages[0];
            let cells = 1usize << log_cells;
            let fibers = (cells * st0.blowup) >> st0.step_vars;
            let blind_cells = blind_cells_for(st0.step_vars, st0.num_queries.min(fibers));
            (used + blind_cells <= cells).then_some(Self {
                log_cells,
                log_entries: d,
                blind_cells,
                schedule,
            })
        })
    }

    #[inline]
    pub fn limb_block(&self, limb: usize) -> usize {
        limb << self.log_entries
    }

    #[inline]
    pub fn mask_block(&self, round: usize, limb: usize) -> usize {
        (LIMBS << self.log_entries) + ((round * LIMBS + limb) << LOOKUP_MASK_BITS)
    }
}

/// Cell layout of the assignment table, plus the optional LogUp helper table layout.
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
    pub lookup: Option<LookupLayout>,
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
    /// The smallest table holding the variables, the masks and the blinders (no lookups).
    pub fn new(size: ShapeSize) -> Option<Self> {
        Self::search(size, schedule)
    }

    /// [`Self::new`] with an optional LogUp fraction table of `2^log_entries` entries.
    pub fn with_lookup(size: ShapeSize, log_entries: Option<usize>) -> Option<Self> {
        let mut layout = Self::new(size)?;
        if let Some(d) = log_entries {
            layout.lookup = Some(LookupLayout::new(d)?);
        }
        Some(layout)
    }

    /// [`Self::new`] over an arbitrary schedule function, for the calculator.
    pub fn search(size: ShapeSize, schedule: impl Fn(usize) -> Option<Schedule>) -> Option<Self> {
        if size.num_vars < 1 + 3 * PAD_VARS
            || size.num_vars > 1usize << MAX_LOG_CELLS
            || size.num_public > size.num_vars - 1 - 3 * PAD_VARS
            || !(5..usize::BITS as usize).contains(&size.log_rows)
        {
            return None;
        }
        let var_bits = size.num_vars.next_power_of_two().trailing_zeros().max(1) as usize;
        let var_align = VAR_ALIGN_MIN.max(var_bits.saturating_sub(8));
        let var_cells = size.num_vars.next_multiple_of(1 << var_align);
        let masks = mask_cells(size.log_rows, var_bits);
        (var_bits.max(MIN_LOG_CELLS)..=MAX_LOG_CELLS).find_map(|log_cells| {
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
                lookup: None,
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
