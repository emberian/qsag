//! Relations proved by the committed zk-Hem v2 protocol in [`super::v2::protocol`] and the
//! public hologram / recursion protocols in [`crate::hem_quintic`] and [`super::recursive_ivc`].
//!
//! A relation is a list of rows over one assignment vector `z` (`z[0] = 1`):
//!
//! * S-box rows `<a, z>^7 = <c, z>`,
//! * multiplication rows `<a, z> * <b, z> = <c, z>`,
//! * optional LogUp lookup tuples ([`Lookups`]).
//!
//! S-box rows come first, so the row selector is a prefix indicator the verifier evaluates
//! in `O(log rows)`. Public values enter as constants of the linear forms, so they are part
//! of the [`Shape`] and of its digest.
//!
//! Two closings exist ([`Closing`]):
//! * [`Closing::V2`] ([`ConstraintSystem::finish_v2`] and [`ConstraintSystem::finish_recorded`]):
//!   the hiding zk-Hem v2 layout (`SECURITY.md`, V2.1), appending 15 row-masking variables on
//!   three 8-row corners (plus 10 lookup-masking variables on one 8-entry corner when lookups
//!   are used).
//! * [`Closing::Public`] ([`ConstraintSystem::finish`]): the 12-row layout retained exclusively
//!   for non-hiding public proofs (`PublicHemProof`, `HologramPublicProof`,
//!   `RecursivePublicHemProof`).

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;

use crate::field::{Goldilocks, GoldilocksOps as _};
use crate::sponge::{
    POSEIDON2_GL24_CAPACITY, POSEIDON2_GL24_DIGEST_LIMBS, POSEIDON2_GL24_HALF_EXTERNAL_ROUNDS,
    POSEIDON2_GL24_INTERNAL_ROUNDS, POSEIDON2_GL24_IV, POSEIDON2_GL24_MERKLE_TAG,
    POSEIDON2_GL24_RATE, POSEIDON2_GL24_RC, POSEIDON2_GL24_SBOX_COUNT, POSEIDON2_HALF_EXT_ROUNDS,
    POSEIDON2_INT_ROUNDS, cshake256_static_midstate, keccak_f1600, poseidon2_apply_me,
    poseidon2_apply_mi, poseidon2_const_at, poseidon2_gl24_apply_me, poseidon2_gl24_apply_mi,
    poseidon2_perm12, poseidon2_sbox7,
};

type F = Goldilocks;

/// Index into the assignment vector. `Var::ONE` is the constant `1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var(u32);

impl Var {
    pub const ONE: Var = Var(0);

    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Linear form over the assignment: terms sorted by variable, no zero coefficients.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Lc(Vec<(u32, F)>);

impl Lc {
    #[inline]
    pub fn zero() -> Self {
        Self(Vec::new())
    }

    #[inline]
    pub fn constant(c: F) -> Self {
        Self::term(Var::ONE, c)
    }

    #[inline]
    pub fn term(v: Var, coeff: F) -> Self {
        if coeff.is_zero() {
            Self::zero()
        } else {
            Self(vec![(v.0, coeff)])
        }
    }

    #[inline]
    pub fn terms(&self) -> &[(u32, F)] {
        &self.0
    }

    /// `sum_i scale_i * lc_i`.
    pub fn combine(parts: &[(F, &Lc)]) -> Self {
        let mut all: Vec<(u32, F)> = Vec::with_capacity(parts.iter().map(|(_, l)| l.0.len()).sum());
        for &(scale, lc) in parts {
            if !scale.is_zero() {
                all.extend(lc.0.iter().map(|&(v, c)| (v, c.const_mul(scale))));
            }
        }
        all.sort_unstable_by_key(|&(v, _)| v);
        let mut out: Vec<(u32, F)> = Vec::with_capacity(all.len());
        for (v, c) in all {
            match out.last_mut() {
                Some(last) if last.0 == v => last.1 += c,
                _ => out.push((v, c)),
            }
        }
        out.retain(|&(_, c)| !c.is_zero());
        Self(out)
    }

    pub fn plus(&self, rhs: &Lc) -> Self {
        let (a, b) = (&self.0, &rhs.0);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() && j < b.len() {
            if a[i].0 < b[j].0 {
                out.push(a[i]);
                i += 1;
            } else if a[i].0 > b[j].0 {
                out.push(b[j]);
                j += 1;
            } else {
                let c = a[i].1 + b[j].1;
                if !c.is_zero() {
                    out.push((a[i].0, c));
                }
                i += 1;
                j += 1;
            }
        }
        out.extend_from_slice(&a[i..]);
        out.extend_from_slice(&b[j..]);
        Self(out)
    }

    pub fn scaled(&self, k: F) -> Self {
        if k.is_zero() {
            return Self::zero();
        }
        Self(self.0.iter().map(|&(v, c)| (v, c.const_mul(k))).collect())
    }

    #[inline]
    pub fn minus(&self, rhs: &Lc) -> Self {
        self.plus(&rhs.scaled(F::ZERO - F::ONE))
    }

    #[inline]
    pub fn plus_const(&self, c: F) -> Self {
        self.plus(&Lc::constant(c))
    }
}

impl From<Var> for Lc {
    #[inline]
    fn from(v: Var) -> Self {
        Lc::term(v, F::ONE)
    }
}

/// The same linear forms occur at different variable offsets in repeated
/// permutation gadgets. Each row names an anchor column and a span of shared
/// (distance from anchor, coefficient) pairs. Column zero stays absolute.
#[derive(Clone, Debug, Default)]
struct RowTemplates {
    rows: Vec<(u32, u32)>,
    candidates: BTreeMap<u64, (usize, usize)>,
}

/// Sparse matrix in compressed-row form.
#[derive(Clone, Debug)]
pub struct Csr {
    ptr: Vec<u32>,
    col: Vec<u32>,
    val: Vec<F>,
    templates: Option<RowTemplates>,
}

impl PartialEq for Csr {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
            && if self.templates.is_none() && other.templates.is_none() {
                self.col == other.col && self.val == other.val
            } else {
                (0..self.num_rows()).all(|i| self.row(i).eq(other.row(i)))
            }
    }
}
impl Eq for Csr {}

impl Default for Csr {
    fn default() -> Self {
        Self::new()
    }
}

impl Csr {
    fn new() -> Self {
        Self {
            ptr: vec![0],
            col: Vec::new(),
            val: Vec::new(),
            templates: None,
        }
    }

    fn push_row(&mut self, lc: &Lc) {
        self.push_terms(lc.terms());
    }

    fn push_terms(&mut self, terms: &[(u32, F)]) {
        if let Some(t) = &mut self.templates {
            let anchor = terms.last().map_or(0, |t| t.0);
            let distance = |col| {
                if col == 0 {
                    0
                } else {
                    anchor.wrapping_sub(col).wrapping_add(1)
                }
            };
            let mut hash = 0xcbf29ce484222325u64;
            for &(col, val) in terms {
                hash = (hash ^ u64::from(distance(col))).wrapping_mul(0x100000001b3);
                hash = (hash ^ val.to_canonical_u64()).wrapping_mul(0x100000001b3);
            }
            // A hash collision can only cost space. Compare all terms before reuse.
            let hit = t.candidates.get(&hash).copied().filter(|&(off, len)| {
                len == terms.len()
                    && terms.iter().enumerate().all(|(i, &(col, val))| {
                        self.col[off + i] == distance(col) && self.val[off + i] == val
                    })
            });
            let offset = if let Some((off, _)) = hit {
                off
            } else {
                let off = self.col.len();
                self.col.extend(terms.iter().map(|&(col, _)| distance(col)));
                self.val.extend(terms.iter().map(|&(_, val)| val));
                t.candidates.insert(hash, (off, terms.len()));
                off
            };
            t.rows.push((anchor, offset as u32));
            self.ptr.push(
                self.ptr
                    .last()
                    .unwrap()
                    .checked_add(terms.len() as u32)
                    .expect("CSR nonzero count"),
            );
            return;
        }
        for &(v, c) in terms {
            self.col.push(v);
            self.val.push(c);
        }
        self.ptr.push(self.col.len() as u32);
    }

    /// `count` rows without entries.
    fn push_empty_rows(&mut self, count: usize) {
        let end = *self.ptr.last().unwrap();
        if let Some(t) = &mut self.templates {
            t.rows.resize(t.rows.len() + count, (0, 0));
        }
        self.ptr.resize(self.ptr.len() + count, end);
    }

    /// The rows of `other` after the rows of `self`.
    fn append(&mut self, other: Csr) {
        if self.num_rows() == 0 {
            *self = other;
            return;
        }
        if let (Some(t), Some(u)) = (&mut self.templates, &other.templates) {
            let base = *self.ptr.last().unwrap();
            let offset = self.col.len() as u32;
            t.rows
                .extend(u.rows.iter().map(|&(anchor, off)| (anchor, off + offset)));
            self.ptr.extend(other.ptr[1..].iter().map(|p| base + p));
            self.col.extend(other.col);
            self.val.extend(other.val);
            return;
        }
        debug_assert!(
            self.templates.is_none() && other.templates.is_none() || other.num_rows() == 0
        );
        let base = self.col.len() as u32;
        self.ptr.extend(other.ptr[1..].iter().map(|&p| base + p));
        self.col.extend_from_slice(&other.col);
        self.val.extend_from_slice(&other.val);
    }

    /// Rename every column.
    fn map_cols(&mut self, map: impl Fn(u32) -> u32) {
        for col in &mut self.col {
            *col = map(*col);
        }
    }

    /// Order the entries of every row by column. Columns of a row are distinct.
    fn sort_rows(&mut self) {
        let mut row: Vec<(u32, F)> = Vec::new();
        for bounds in self.ptr.windows(2) {
            let (lo, hi) = (bounds[0] as usize, bounds[1] as usize);
            if self.col[lo..hi].is_sorted() {
                continue;
            }
            row.clear();
            row.extend(
                self.col[lo..hi]
                    .iter()
                    .copied()
                    .zip(self.val[lo..hi].iter().copied()),
            );
            row.sort_unstable_by_key(|&(v, _)| v);
            for (k, &(v, c)) in row.iter().enumerate() {
                self.col[lo + k] = v;
                self.val[lo + k] = c;
            }
        }
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        self.ptr.len() - 1
    }

    #[inline]
    pub fn nnz(&self) -> usize {
        *self.ptr.last().unwrap() as usize
    }

    /// `(column, coefficient)` pairs of row `i`.
    #[inline]
    pub fn row(&self, i: usize) -> impl Iterator<Item = (usize, F)> + '_ {
        let lo = self.ptr[i] as usize;
        let len = self.ptr[i + 1] as usize - lo;
        let span = self.templates.as_ref().map(|t| t.rows[i]);
        let off = span.map_or(lo, |(_, start)| start as usize);
        self.col[off..off + len]
            .iter()
            .zip(&self.val[off..off + len])
            .map(move |(&col, &v)| {
                let col = match span {
                    Some((anchor, _)) if col != 0 => anchor.wrapping_add(1).wrapping_sub(col),
                    _ => col,
                };
                (col as usize, v)
            })
    }

    #[inline]
    pub fn row_dot(&self, i: usize, z: &[F]) -> F {
        self.row(i)
            .fold(F::ZERO, |acc, (c, v)| acc + v.const_mul(z[c]))
    }

    fn stream_into(&self, sponge: &mut ShapeSponge) {
        sponge.u64(self.ptr.len() as u64);
        for &p in &self.ptr {
            sponge.u32(p);
        }
        if self.templates.is_some() {
            for i in 0..self.num_rows() {
                for (c, v) in self.row(i) {
                    sponge.u32(c as u32);
                    sponge.u64(v.to_canonical_u64());
                }
            }
        } else {
            for (&c, &v) in self.col.iter().zip(&self.val) {
                sponge.u32(c);
                sponge.u64(v.to_canonical_u64());
            }
        }
    }
}

/// The cSHAKE256 sponge of [`Shape::digest`], absorbing little-endian words straight into
/// the rate lanes.
struct ShapeSponge {
    state: [u64; 25],
    pos: usize,
}

impl ShapeSponge {
    const RATE: usize = 136;

    fn new(midstate: [u64; 25]) -> Self {
        Self {
            state: midstate,
            pos: 0,
        }
    }

    #[inline(always)]
    fn word(&mut self, v: u64, bytes: usize) {
        let lane = self.pos / 8;
        let at = self.pos % 8;
        self.state[lane] ^= v << (8 * at);
        let room = 8 - at;
        if bytes < room {
            self.pos += bytes;
            return;
        }
        let next = if lane == Self::RATE / 8 - 1 {
            keccak_f1600(&mut self.state);
            0
        } else {
            lane + 1
        };
        if bytes > room {
            self.state[next] ^= v >> (8 * room);
        }
        self.pos = (self.pos + bytes) % Self::RATE;
    }

    #[inline(always)]
    fn u32(&mut self, v: u32) {
        self.word(u64::from(v), 4);
    }

    #[inline(always)]
    fn u64(&mut self, v: u64) {
        self.word(v, 8);
    }

    fn bytes(&mut self, data: &[u8]) {
        for &b in data {
            self.word(u64::from(b), 1);
        }
    }

    fn finish(mut self) -> [u8; 32] {
        self.state[self.pos / 8] ^= 0x04 << (8 * (self.pos % 8));
        self.state[Self::RATE / 8 - 1] ^= 0x80 << 56;
        keccak_f1600(&mut self.state);
        let mut out = [0u8; 32];
        for (lane, dst) in self.state.iter().take(4).zip(out.as_chunks_mut::<8>().0) {
            *dst = lane.to_le_bytes();
        }
        out
    }
}

/// Rows of one kind, `(a, b, c)` each, in the order they were recorded.
#[derive(Default)]
struct Rows {
    a: Csr,
    b: Csr,
    c: Csr,
}

impl Rows {
    #[inline]
    fn len(&self) -> usize {
        self.a.num_rows()
    }

    #[inline]
    fn push(&mut self, a: &[(u32, F)], b: &[(u32, F)], c: &[(u32, F)]) {
        self.a.push_terms(a);
        self.b.push_terms(b);
        self.c.push_terms(c);
    }

    fn append(&mut self, other: Rows) {
        let Rows { a, b, c } = other;
        self.a.append(a);
        self.b.append(b);
        self.c.append(c);
    }

    fn matrices(&mut self) -> [&mut Csr; 3] {
        [&mut self.a, &mut self.b, &mut self.c]
    }
}

/// Reserved row count of [`Closing::Public`] (`12` rows).
pub const MASK_ROWS: usize = 12;

/// How a relation was closed: which trailing rows and variables it ends with.
///
/// * [`Closing::Public`] ([`ConstraintSystem::finish`]): retained solely for non-hiding
///   public and Spark-hologram recursion proofs (`PublicHemProof`, `HologramPublicProof`,
///   `RecursivePublicHemProof`).
/// * [`Closing::V2`] ([`ConstraintSystem::finish_v2`] and [`ConstraintSystem::finish_recorded`]):
///   the layout of zk-Hem v2 (`SECURITY.md`, V2.1), with three groups of five masking variables
///   on three corners of eight rows (plus ten lookup-masking variables on one 8-entry corner
///   when [`Lookups`] are present).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Closing {
    Public,
    V2,
}

impl Closing {
    /// Masking variables per group.
    pub const fn group(self) -> usize {
        match self {
            Self::Public => 4,
            Self::V2 => 5,
        }
    }

    /// Rows of one corner.
    pub const fn corner_rows(self) -> usize {
        match self {
            Self::Public => 4,
            Self::V2 => 8,
        }
    }

    /// Row-masking variables appended to the assignment.
    pub const fn mask_vars(self) -> usize {
        3 * self.group()
    }

    /// Rows reserved at the top of the row cube.
    pub const fn pad_rows(self) -> usize {
        3 * self.corner_rows()
    }

    const fn min_log_rows(self) -> u32 {
        match self {
            Self::Public => 4,
            Self::V2 => 5,
        }
    }

    /// Append the three corners for the masking variables `mask_var_base..`.
    fn push_rows(self, mask_var_base: usize, a: &mut Csr, b: &mut Csr, c: &mut Csr) {
        let one = Lc::constant(F::ONE);
        let two = Lc::constant(F::TWO);
        let empty = Lc::zero();
        for g in 0..3 {
            for k in 0..self.corner_rows() {
                if k >= self.group() {
                    a.push_row(&empty);
                    b.push_row(&empty);
                    c.push_row(&empty);
                    continue;
                }
                let p = Lc::term(Var((mask_var_base + g * self.group() + k) as u32), F::ONE);
                match g {
                    0 => {
                        a.push_row(&p);
                        b.push_row(&one);
                        c.push_row(&p);
                    }
                    1 => {
                        a.push_row(&one);
                        b.push_row(&p);
                        c.push_row(&p);
                    }
                    _ => {
                        a.push_row(&p);
                        b.push_row(&two);
                        c.push_row(&p.scaled(F::TWO));
                    }
                }
            }
        }
    }
}

// ============================================================================
// Definitions of variables
// ============================================================================

/// Index of a [`Source`] in [`Definitions::sources`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceId(u32);

impl SourceId {
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// One coefficient of an integer written in base `2^8`: a linear form whose value under
/// any satisfying assignment is an integer in `[lo, hi]` (taken modulo the field prime to
/// its representative of least absolute value).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntCoef {
    pub lc: Lc,
    pub lo: i128,
    pub hi: i128,
}

/// A value several variables are read from. Integers `sum_k c_k 2^(8k)` are given by
/// their coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    /// Supplied from outside the relation (a secret the prover is given) as an integer
    /// of `bits` bits.
    Input { bits: u32 },
    /// The coefficients of the product of two polynomials given by their coefficients.
    PolyProduct { a: Vec<Lc>, b: Vec<Lc> },
    /// The canonical value of a linear form, which lies in `[0, 2^bits)`.
    Form { lc: Lc, bits: u32 },
    /// The integer `sum_j a_j b_j + c`, which lies in `[0, 2^bits)`; each `(a_j, b_j)`
    /// is a pair of integers multiplied as polynomials.
    Integer {
        products: Vec<(Vec<IntCoef>, Vec<IntCoef>)>,
        linear: Vec<IntCoef>,
        bits: u32,
    },
    /// The canonical residue of `(sum_j a_j b_j + c) / den` modulo the prime `modulus`
    /// (little-endian bytes). An empty `den` is one.
    Residue {
        products: Vec<(Vec<IntCoef>, Vec<IntCoef>)>,
        linear: Vec<IntCoef>,
        den: Vec<IntCoef>,
        modulus: Vec<u8>,
    },
    /// The slope of an affine addition that may be a doubling, as a canonical residue
    /// modulo the prime `modulus`.
    Slope {
        num: Vec<IntCoef>,
        den: Vec<IntCoef>,
        tangent_products: Vec<(Vec<IntCoef>, Vec<IntCoef>)>,
        tangent_linear: Vec<IntCoef>,
        tangent_den: Vec<IntCoef>,
        modulus: Vec<u8>,
    },
    /// The integer `num / divisor`, where the odd `divisor` (little-endian bytes) divides
    /// `num` exactly and the quotient lies in `[0, 2^bits)`.
    Quotient {
        num: Vec<IntCoef>,
        divisor: Vec<u8>,
        bits: u32,
    },
}

/// How the value of a variable follows from earlier variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Def {
    /// Allocated without a definition.
    Undefined,
    /// The constant one.
    One,
    /// A public input.
    Public,
    /// A masking variable appended when closing the relation.
    Mask,
    /// The multiplicity of a table row in [`Shape::lookups`].
    Multiplicity,
    /// `a b`.
    Product(Lc, Lc),
    /// `a^7`.
    Power7(Lc),
    /// `base + sum_j a_j b_j`.
    SumOfProducts { base: Lc, products: Vec<(Lc, Lc)> },
    /// `scale (num / den - minus)` in the field.
    Ratio {
        num: Lc,
        den: Lc,
        minus: Lc,
        scale: F,
    },
    /// The inverse of `of`, or zero when `of` is zero; `of` lies in `[0, max]`.
    InverseOrZero { of: Lc, max: u32 },
    /// Coefficient `index` of a [`Source::PolyProduct`].
    Coefficient { product: SourceId, index: u32 },
    /// Bits `lo..lo + width` of an integer source, as one value.
    Bits {
        source: SourceId,
        lo: u32,
        width: u32,
    },
}

/// The definitions recorded by a [`ConstraintSystem::new_recording`] builder: one
/// [`Def`] per variable of the finished shape.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Definitions {
    pub vars: Vec<Def>,
    pub sources: Vec<Source>,
}

impl Definitions {
    /// Variables allocated without a definition.
    pub fn undefined(&self) -> Vec<usize> {
        (0..self.vars.len())
            .filter(|&i| self.vars[i] == Def::Undefined)
            .collect()
    }
}

/// Active lookup-masking entries per limb of `Fp5`: entry `k in 0..5` on the top 8-entry
/// corner has a free numerator variable and a free first-column denominator variable.
pub const LOOKUP_MASK_ENTRIES: usize = 5;
/// Reserved entries at the top of the fraction list (`2^3 = 8` corner slots holding the
/// [`LOOKUP_MASK_ENTRIES`] active masking entries).
pub const LOOKUP_CORNER_ENTRIES: usize = 8;

/// Handle of a public table registered with [`ConstraintSystem::table`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TableId(u32);

/// The lookups of a v2 relation as a list of `2^log_entries` fractions.
/// Entry `i` has numerator `<num[i], z>` and value tuple `(<den[c][i], z>)_c`; column `0`
/// is the table tag. Entries `0..num_checked()` are constrained; the last
/// [`LOOKUP_CORNER_ENTRIES`] form the 3-bit masking corner whose first
/// [`LOOKUP_MASK_ENTRIES`] entries carry fresh uniform numerator/denominator variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lookups {
    pub log_entries: usize,
    /// Lookups (entries `0..num_lookups`).
    pub num_lookups: usize,
    /// Table rows over all tables (entries `num_lookups..num_lookups + num_table_rows`).
    pub num_table_rows: usize,
    /// First multiplicity variable; one per table row, in entry order.
    pub mult_var_base: usize,
    pub num: Csr,
    pub den: Vec<Csr>,
}

impl Lookups {
    #[inline]
    pub fn num_entries(&self) -> usize {
        1usize << self.log_entries
    }

    /// Entries below this index are constrained and summed; also the start of the 8-entry
    /// masking corner.
    #[inline]
    pub fn num_checked(&self) -> usize {
        self.num_entries() - LOOKUP_CORNER_ENTRIES
    }

    /// First index of the 8-entry masking corner at the top of the fraction cube.
    #[inline]
    pub fn mask_entry_base(&self) -> usize {
        self.num_entries() - LOOKUP_CORNER_ENTRIES
    }

    /// Columns of a value tuple, the table tag included.
    #[inline]
    pub fn width(&self) -> usize {
        self.den.len()
    }

    /// Whether the fractions of `z` sum to zero as rational functions: for every tuple
    /// value the numerators add up to zero. Not constant time in `z`.
    pub fn holds(&self, z: &[F]) -> bool {
        let mut sums: BTreeMap<Vec<u64>, F> = BTreeMap::new();
        for i in 0..self.num_checked() {
            let n = self.num.row_dot(i, z);
            if n.is_zero() {
                continue;
            }
            let key: Vec<u64> = self
                .den
                .iter()
                .map(|m| m.row_dot(i, z).to_canonical_u64())
                .collect();
            *sums.entry(key).or_insert(F::ZERO) += n;
        }
        sums.values().all(|s| s.is_zero())
    }

    fn stream_into(&self, sponge: &mut ShapeSponge) {
        sponge.bytes(b"QSAG.ZKHEM2.SHAPE.LOOKUP/v1");
        for n in [
            self.log_entries,
            self.num_lookups,
            self.num_table_rows,
            self.mult_var_base,
            self.den.len(),
        ] {
            sponge.u64(n as u64);
        }
        self.num.stream_into(sponge);
        for m in &self.den {
            m.stream_into(sponge);
        }
    }
}

struct LookupTable {
    width: usize,
    rows: Vec<u64>,
    mult: Vec<u64>,
}

/// Tag marking a variable allocated inside the 128-stride Poseidon2 S-box arena of a
/// hologram-aligned [`ConstraintSystem`].
const P2_VAR_TAG: u32 = 1u32 << 31;

/// Alignment metadata enabling $O(\log P)$ closed-form evaluation of the 106 interior S-box rows
/// (`rows 12..118`) of every aligned width-12 Poseidon2 permutation in a [`Shape`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HologramMeta {
    pub poseidon2_perms: usize,
    pub pub_var_blocks: usize,
}

/// Public structure of a relation: row matrices over `num_vars` variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shape {
    /// `log2` of the padded row count.
    pub log_rows: usize,
    /// Rows `0..num_sbox` are S-box rows; all others are multiplication rows.
    pub num_sbox: usize,
    /// Variables, including the constant and the masking variables.
    pub num_vars: usize,
    /// Variables `1..=num_public` are public inputs.
    pub num_public: usize,
    /// First of the masking variables appended by the closing.
    pub mask_var_base: usize,
    pub a: Csr,
    pub b: Csr,
    pub c: Csr,
    hologram_meta: HologramMeta,
    closing: Closing,
    lookups: Option<Lookups>,
    digest: [u8; 32],
}

impl Shape {
    /// The lookups of the relation; `None` when it has none.
    #[inline]
    pub fn lookups(&self) -> Option<&Lookups> {
        self.lookups.as_ref()
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        1usize << self.log_rows
    }

    /// First row of masking group `g in 0..3`.
    #[inline]
    pub fn mask_row_base(&self, g: usize) -> usize {
        self.num_rows() - self.closing.corner_rows() * (3 - g)
    }

    /// Which closing produced the trailing rows and variables.
    #[inline]
    pub fn closing(&self) -> Closing {
        self.closing
    }

    /// Binding digest of the whole relation, public constants and lookup tables included.
    #[inline]
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Block-alignment metadata for Spark hologram factorization.
    #[inline]
    pub fn hologram_meta(&self) -> HologramMeta {
        self.hologram_meta
    }

    /// Whether row `i` belongs to the residual sparse hologram.
    #[inline]
    pub fn is_residual_row(&self, row: usize) -> bool {
        let p = self.hologram_meta.poseidon2_perms;
        if p > 0 && row < 128 * p {
            (row & 127) < 12
        } else {
            true
        }
    }

    fn compute_digest(&self) -> [u8; 32] {
        const SHAPE_PUBLIC_MIDSTATE: [u64; 25] = cshake256_static_midstate(b"QSAG.ZKHEM.SHAPE/v1");
        const SHAPE_V2_MIDSTATE: [u64; 25] = cshake256_static_midstate(b"QSAG.ZKHEM.SHAPE/v2");
        let _phase = crate::profile::span("hem_shape_digest");
        let midstate = match self.closing {
            Closing::Public => SHAPE_PUBLIC_MIDSTATE,
            Closing::V2 => SHAPE_V2_MIDSTATE,
        };
        let mut sponge = ShapeSponge::new(midstate);
        for n in [
            self.log_rows,
            self.num_sbox,
            self.num_vars,
            self.num_public,
            self.mask_var_base,
        ] {
            sponge.u64(n as u64);
        }
        self.a.stream_into(&mut sponge);
        self.b.stream_into(&mut sponge);
        self.c.stream_into(&mut sponge);
        if let Some(lookups) = &self.lookups {
            lookups.stream_into(&mut sponge);
        }
        sponge.finish()
    }

    /// Whether `z` (with `z[0] = 1`) satisfies every row and lookup.
    pub fn is_satisfied(&self, z: &[F]) -> bool {
        z.len() == self.num_vars
            && z[0] == F::ONE
            && (0..self.num_rows()).all(|i| {
                let a = self.a.row_dot(i, z);
                let c = self.c.row_dot(i, z);
                if i < self.num_sbox {
                    poseidon2_sbox7(a) == c
                } else {
                    a.const_mul(self.b.row_dot(i, z)) == c
                }
            })
            && self.lookups.as_ref().is_none_or(|l| l.holds(z))
    }
}

/// Relation builder that streams rows directly into compressed-row matrices alongside an
/// assignment.
pub struct ConstraintSystem {
    values: Vec<F>,
    record_rows: bool,
    num_public: usize,
    hologram_aligned: bool,
    p2_perms: usize,
    p2_values: Vec<F>,
    p2_sbox: Rows,
    sbox: Rows,
    mul: Rows,
    defs: Option<Definitions>,
    tables: Vec<LookupTable>,
    range_tables: Vec<(usize, TableId)>,
    lookup_tables: Vec<u32>,
    lookup_columns: Vec<Csr>,
    num_lookups: usize,
}

impl Default for ConstraintSystem {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstraintSystem {
    pub fn new() -> Self {
        Self {
            values: vec![F::ONE],
            record_rows: true,
            num_public: 0,
            hologram_aligned: false,
            p2_perms: 0,
            p2_values: Vec::new(),
            p2_sbox: Rows::default(),
            sbox: Rows::default(),
            mul: Rows::default(),
            defs: None,
            tables: Vec::new(),
            range_tables: Vec::new(),
            lookup_tables: Vec::new(),
            lookup_columns: Vec::new(),
            num_lookups: 0,
        }
    }

    /// Store translated copies of recursive verifier rows once during shape synthesis.
    pub(super) fn with_row_templates() -> Self {
        let mut cs = Self::new();
        for group in [&mut cs.p2_sbox, &mut cs.sbox, &mut cs.mul] {
            for csr in group.matrices() {
                csr.templates = Some(RowTemplates::default());
            }
        }
        cs
    }

    /// A builder that records a [`Def`] for every variable; close it with
    /// [`Self::finish_recorded`] (produces a [`Closing::V2`] relation).
    pub fn new_recording() -> Self {
        let mut cs = Self::new();
        cs.defs = Some(Definitions {
            vars: vec![Def::One],
            sources: Vec::new(),
        });
        cs
    }

    /// Whether definitions are recorded.
    #[inline]
    pub fn is_recording(&self) -> bool {
        self.defs.is_some()
    }

    /// Register a [`Source`]. `make` runs only when recording; otherwise the returned
    /// index is a placeholder.
    pub fn source(&mut self, make: impl FnOnce() -> Source) -> SourceId {
        match &mut self.defs {
            Some(defs) => {
                defs.sources.push(make());
                SourceId(defs.sources.len() as u32 - 1)
            }
            None => SourceId(u32::MAX),
        }
    }

    /// Allocate a variable with the given assigned value and its definition. `def` runs
    /// only when recording.
    pub fn alloc_defined(&mut self, value: F, def: impl FnOnce() -> Def) -> Var {
        let var = self.alloc(value);
        if let Some(defs) = &mut self.defs {
            *defs.vars.last_mut().expect("just allocated") = def();
        }
        var
    }

    /// [`Self::finish_v2`] with the recorded definitions.
    pub fn finish_recorded(mut self) -> (Shape, Vec<F>, Definitions) {
        assert!(
            !self.hologram_aligned,
            "recording a hologram-aligned relation"
        );
        let mut defs = self.defs.take().expect("a recording builder");
        let (shape, z) = self.finish_v2();
        defs.vars.resize(shape.num_vars, Def::Mask);
        if let Some(lookups) = shape.lookups() {
            defs.vars[lookups.mult_var_base..shape.mask_var_base].fill(Def::Multiplicity);
        }
        (shape, z, defs)
    }

    /// Relation builder that places [`poseidon2_perm`] S-box rows and S-box output variables on
    /// 128-row / 128-variable boundaries for `ShapeHologram`.
    pub fn new_hologram_aligned() -> Self {
        let mut cs = Self::new();
        cs.hologram_aligned = true;
        cs
    }

    /// Re-evaluate a compiled relation's assignment without rebuilding its matrices.
    pub fn witness_only() -> Self {
        let mut cs = Self::new();
        cs.record_rows = false;
        cs
    }

    /// The assignment of a [`Self::witness_only`] builder, laid out for `shape` (masking
    /// variables zero).
    pub fn finish_assignment(mut self, shape: &Shape) -> Option<Vec<F>> {
        assert!(!self.record_rows && !self.hologram_aligned);
        self.push_multiplicities();
        if self.num_public != shape.num_public || self.values.len() != shape.mask_var_base {
            return None;
        }
        let masks = shape.num_vars - self.values.len();
        qsag_core::wipe::secret_vec_reserve(&mut self.values, masks);
        self.values.resize(shape.num_vars, F::ZERO);
        Some(core::mem::take(&mut self.values))
    }

    #[cfg(test)]
    pub(crate) fn fork_public_inputs(&self) -> Self {
        assert_eq!(self.values.len(), self.num_public + 1);
        assert!(self.p2_values.is_empty());
        assert!(self.defs.is_none(), "a recording builder is not forked");
        Self {
            values: self.values.clone(),
            record_rows: self.record_rows,
            num_public: self.num_public,
            hologram_aligned: self.hologram_aligned,
            p2_perms: 0,
            p2_values: Vec::new(),
            p2_sbox: Rows::default(),
            sbox: Rows::default(),
            mul: Rows::default(),
            defs: None,
            tables: self
                .tables
                .iter()
                .map(|t| LookupTable {
                    width: t.width,
                    rows: t.rows.clone(),
                    mult: vec![0; t.mult.len()],
                })
                .collect(),
            range_tables: self.range_tables.clone(),
            lookup_tables: Vec::new(),
            lookup_columns: Vec::new(),
            num_lookups: 0,
        }
    }

    /// Append a disjoint circuit with the same public prefix, relocating private variables.
    #[cfg(test)]
    pub(crate) fn append(&mut self, mut other: Self) {
        assert_eq!(self.num_public, other.num_public);
        assert_eq!(self.record_rows, other.record_rows);
        assert_eq!(self.hologram_aligned, other.hologram_aligned);
        assert_eq!(
            &self.values[..=self.num_public],
            &other.values[..=other.num_public]
        );
        let offset = u32::try_from(self.values.len() - self.num_public - 1)
            .expect("relation variable limit");
        let p2_offset = u32::try_from(self.p2_values.len()).expect("poseidon2 variable limit");
        let num_public = self.num_public;
        let relocate = |v: u32| -> u32 {
            if v & P2_VAR_TAG != 0 {
                let raw = (v & !P2_VAR_TAG)
                    .checked_add(p2_offset)
                    .expect("poseidon2 variable limit");
                assert!(raw < P2_VAR_TAG, "poseidon2 variable limit");
                P2_VAR_TAG | raw
            } else if v as usize > num_public {
                let next = v.checked_add(offset).expect("relation variable limit");
                assert!(next < P2_VAR_TAG, "relation variable limit");
                next
            } else {
                v
            }
        };
        for (mine, theirs) in [
            (&mut self.p2_sbox, &mut other.p2_sbox),
            (&mut self.sbox, &mut other.sbox),
            (&mut self.mul, &mut other.mul),
        ] {
            let mut theirs = core::mem::take(theirs);
            for matrix in theirs.matrices() {
                matrix.map_cols(relocate);
            }
            mine.append(theirs);
        }
        assert_eq!(
            self.tables.len(),
            other.tables.len(),
            "lookup tables are registered before a fork"
        );
        let width = self.lookup_columns.len().max(other.lookup_columns.len());
        self.widen_lookup_columns(width);
        other.widen_lookup_columns(width);
        self.lookup_tables.append(&mut other.lookup_tables);
        for (mine, theirs) in self
            .lookup_columns
            .iter_mut()
            .zip(core::mem::take(&mut other.lookup_columns))
        {
            let mut theirs = theirs;
            theirs.map_cols(relocate);
            mine.append(theirs);
        }
        self.num_lookups += other.num_lookups;
        for (mine, theirs) in self.tables.iter_mut().zip(&mut other.tables) {
            for (m, o) in mine.mult.iter_mut().zip(&theirs.mult) {
                *m += o;
            }
            qsag_asm::volatile_fill(&mut theirs.mult, 0u64);
        }
        self.p2_perms += other.p2_perms;
        qsag_core::wipe::secret_vec_extend_from_slice(&mut self.p2_values, &other.p2_values);
        qsag_asm::volatile_fill(&mut other.p2_values, F::ZERO);
        qsag_core::wipe::secret_vec_extend_from_slice(
            &mut self.values,
            &other.values[self.num_public + 1..],
        );
    }

    /// Allocate a public input (`1..=num_public`).
    pub fn public_input(&mut self, value: F) -> Var {
        assert_eq!(
            self.values.len(),
            1 + self.num_public,
            "public inputs are allocated first"
        );
        assert!(
            self.p2_values.is_empty(),
            "public inputs are allocated first"
        );
        self.num_public += 1;
        self.alloc_defined(value, || Def::Public)
    }

    /// Allocate a free variable with the given assigned value.
    pub fn alloc(&mut self, value: F) -> Var {
        qsag_core::wipe::secret_vec_push(&mut self.values, value);
        let idx = self.values.len() - 1;
        assert!(idx < P2_VAR_TAG as usize, "relation variable limit");
        if let Some(defs) = &mut self.defs {
            defs.vars.push(Def::Undefined);
        }
        Var(idx as u32)
    }

    pub fn eval(&self, lc: &Lc) -> F {
        lc.terms().iter().fold(F::ZERO, |acc, &(v, c)| {
            let val = if v & P2_VAR_TAG != 0 {
                self.p2_values[(v & !P2_VAR_TAG) as usize]
            } else {
                self.values[v as usize]
            };
            acc + c.const_mul(val)
        })
    }

    /// Fresh variable `y` with the row `a^7 = y`.
    pub fn sbox7(&mut self, a: &Lc) -> Var {
        let y = self.alloc_defined(poseidon2_sbox7(self.eval(a)), || Def::Power7(a.clone()));
        if self.record_rows {
            self.sbox.push(a.terms(), &[], &[(y.0, F::ONE)]);
        }
        y
    }

    fn p2_sbox7(&mut self, a: &Lc) -> Var {
        if !self.hologram_aligned {
            return self.sbox7(a);
        }
        let val = poseidon2_sbox7(self.eval(a));
        qsag_core::wipe::secret_vec_push(&mut self.p2_values, val);
        let idx = self.p2_values.len() - 1;
        assert!(idx < P2_VAR_TAG as usize, "poseidon2 variable limit");
        let y = Var(P2_VAR_TAG | (idx as u32));
        if self.record_rows {
            self.p2_sbox.push(a.terms(), &[], &[(y.0, F::ONE)]);
        }
        y
    }

    fn finish_p2_perm_block(&mut self) {
        if !self.hologram_aligned {
            return;
        }
        for _ in 0..10 {
            qsag_core::wipe::secret_vec_push(&mut self.p2_values, F::ZERO);
            if self.record_rows {
                self.p2_sbox.push(&[], &[], &[]);
            }
        }
        self.p2_perms += 1;
        debug_assert_eq!(self.p2_values.len(), 128 * self.p2_perms);
    }

    /// Fresh variable `y` with the row `a * b = y`.
    pub fn mul(&mut self, a: &Lc, b: &Lc) -> Var {
        let y = self.alloc_defined(self.eval(a).const_mul(self.eval(b)), || {
            Def::Product(a.clone(), b.clone())
        });
        if self.record_rows {
            self.mul.push(a.terms(), b.terms(), &[(y.0, F::ONE)]);
        }
        y
    }

    pub fn enforce_mul(&mut self, a: Lc, b: Lc, c: Lc) {
        if self.record_rows {
            self.mul.push(a.terms(), b.terms(), c.terms());
        }
    }

    /// Row `lc * 1 = 0`.
    pub fn enforce_zero(&mut self, lc: Lc) {
        if self.record_rows {
            self.mul.push(lc.terms(), &[(Var::ONE.0, F::ONE)], &[]);
        }
    }

    pub fn enforce_equal(&mut self, a: &Lc, b: &Lc) {
        self.enforce_zero(a.minus(b));
    }

    /// Row `v * (1 - v) = 0`.
    pub fn enforce_boolean(&mut self, v: &Lc) {
        if self.record_rows {
            self.mul
                .push(v.terms(), Lc::constant(F::ONE).minus(v).terms(), &[]);
        }
    }

    /// `if bit { on_one } else { on_zero }`, one multiplication row.
    pub fn select(&mut self, bit: &Lc, on_one: &Lc, on_zero: &Lc) -> Lc {
        let delta = self.mul(bit, &on_one.minus(on_zero));
        on_zero.plus(&delta.into())
    }

    /// Register a public table of `rows.len() / width` distinct rows of `width` columns.
    pub fn table(&mut self, width: usize, rows: Vec<F>) -> TableId {
        assert!(
            !self.hologram_aligned,
            "lookups are not supported in hologram-aligned relations"
        );
        assert!(width >= 1 && !rows.is_empty() && rows.len().is_multiple_of(width));
        let rows: Vec<u64> = rows.iter().map(|v| v.to_canonical_u64()).collect();
        let distinct: BTreeSet<&[u64]> = rows.chunks(width).collect();
        assert_eq!(
            distinct.len(),
            rows.len() / width,
            "table rows are distinct"
        );
        let id = u32::try_from(self.tables.len()).expect("lookup table limit");
        self.tables.push(LookupTable {
            width,
            mult: vec![0; rows.len() / width],
            rows,
        });
        TableId(id)
    }

    /// The one-column table `0..2^bits`, registered on first use.
    pub fn range_table(&mut self, bits: usize) -> TableId {
        if let Some(&(_, id)) = self.range_tables.iter().find(|(b, _)| *b == bits) {
            return id;
        }
        assert!((1..=16).contains(&bits), "range table of 1 to 16 bits");
        let rows: Vec<F> = (0..1u64 << bits).map(F::from_u64_reduced).collect();
        let id = self.table(1, rows);
        self.range_tables.push((bits, id));
        id
    }

    /// `(values_1, .., values_k)` is a row of `table`.
    pub fn enforce_in_table(&mut self, table: TableId, values: &[Lc]) {
        let mut tuple: Vec<u64> = values
            .iter()
            .map(|lc| self.eval(lc).to_canonical_u64())
            .collect();
        let t = &mut self.tables[table.0 as usize];
        assert_eq!(values.len(), t.width, "lookup tuple width");
        for (row, count) in t.rows.chunks(t.width).zip(&mut t.mult) {
            let diff = row.iter().zip(&tuple).fold(0u64, |d, (a, b)| d | (a ^ b));
            *count += ((diff | diff.wrapping_neg()) >> 63) ^ 1;
        }
        qsag_asm::volatile_fill(&mut tuple, 0u64);
        self.num_lookups += 1;
        if self.record_rows {
            self.widen_lookup_columns(values.len());
            self.lookup_tables.push(table.0);
            for (k, column) in self.lookup_columns.iter_mut().enumerate() {
                column.push_terms(values.get(k).map_or(&[], Lc::terms));
            }
        }
    }

    fn widen_lookup_columns(&mut self, width: usize) {
        while self.lookup_columns.len() < width {
            let mut column = Csr::new();
            column.push_empty_rows(self.lookup_tables.len());
            self.lookup_columns.push(column);
        }
    }

    /// `0 <= value < 256` via a lookup into [`Self::range_table`]`(8)`.
    pub fn enforce_byte(&mut self, value: &Lc) {
        let table = self.range_table(8);
        self.enforce_in_table(table, core::slice::from_ref(value));
    }

    /// Number of lookups recorded so far.
    #[inline]
    pub fn num_lookups(&self) -> usize {
        self.num_lookups
    }

    fn push_multiplicities(&mut self) -> usize {
        let base = self.values.len();
        for t in 0..self.tables.len() {
            for r in 0..self.tables[t].mult.len() {
                let count = F::from_u64_reduced(self.tables[t].mult[r]);
                self.alloc(count);
            }
        }
        base
    }

    fn take_lookups(&mut self, mult_var_base: usize, mask_base: usize) -> Lookups {
        let num_table_rows: usize = self.tables.iter().map(|t| t.mult.len()).sum();
        let width = 1 + self.tables.iter().map(|t| t.width).max().unwrap_or(0);
        self.widen_lookup_columns(width - 1);
        let lookups = core::mem::take(&mut self.lookup_tables);
        let used = lookups.len() + num_table_rows;
        let log_entries = (used + LOOKUP_CORNER_ENTRIES)
            .next_power_of_two()
            .trailing_zeros()
            .max(3) as usize;
        let empty = Lc::zero();
        let mut num = Csr::new();
        let mut den: Vec<Csr> = vec![Csr::new()];
        den.append(&mut self.lookup_columns);
        debug_assert_eq!(den.len(), width);
        let tag = |t: usize| Lc::constant(F::from_u64_reduced(t as u64));
        for &t in &lookups {
            num.push_row(&Lc::constant(F::ONE));
            den[0].push_row(&tag(t as usize));
        }
        let mut var = mult_var_base;
        for (t, table) in self.tables.iter().enumerate() {
            for row in table.rows.chunks(table.width) {
                num.push_row(&Lc::term(Var(var as u32), F::ZERO - F::ONE));
                var += 1;
                den[0].push_row(&tag(t));
                for (c, col) in den[1..].iter_mut().enumerate() {
                    let cell = row.get(c).map_or(F::ZERO, |&v| F::from_u64_reduced(v));
                    col.push_row(&Lc::constant(cell));
                }
            }
        }
        let total = 1usize << log_entries;
        for _ in used..total - LOOKUP_CORNER_ENTRIES {
            num.push_row(&empty);
            den.iter_mut().for_each(|col| col.push_row(&empty));
        }
        for k in 0..LOOKUP_CORNER_ENTRIES {
            if k < LOOKUP_MASK_ENTRIES {
                num.push_row(&Lc::term(Var((mask_base + k) as u32), F::ONE));
                den[0].push_row(&Lc::term(
                    Var((mask_base + LOOKUP_MASK_ENTRIES + k) as u32),
                    F::ONE,
                ));
                den[1..].iter_mut().for_each(|col| col.push_row(&empty));
            } else {
                num.push_row(&empty);
                den.iter_mut().for_each(|col| col.push_row(&empty));
            }
        }
        Lookups {
            log_entries,
            num_lookups: lookups.len(),
            num_table_rows,
            mult_var_base,
            num,
            den,
        }
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        self.p2_sbox.len() + self.sbox.len() + self.mul.len()
    }

    fn take_rows(&mut self, total: usize, pad_rows: usize) -> Rows {
        let used = self.num_rows();
        let mut rows = core::mem::take(&mut self.p2_sbox);
        rows.append(core::mem::take(&mut self.sbox));
        rows.append(core::mem::take(&mut self.mul));
        for matrix in rows.matrices() {
            matrix.push_empty_rows(total - pad_rows - used);
        }
        rows
    }

    /// Close for non-hiding public / hologram recursion (`Closing::Public`). Lookups are not
    /// supported on public relations; use [`Self::finish_v2`] for hiding zk-Hem v2 relations.
    pub fn finish(self) -> (Shape, Vec<F>) {
        assert!(
            self.tables.is_empty(),
            "relations with lookups must close with finish_v2 or finish_recorded"
        );
        self.finish_with(Closing::Public)
    }

    /// Close for zk-Hem v2 (`Closing::V2`): fifteen row-masking variables on three corners of
    /// eight rows, plus ten lookup-masking variables on an eight-entry corner when tables are
    /// registered.
    pub fn finish_v2(self) -> (Shape, Vec<F>) {
        self.finish_with(Closing::V2)
    }

    fn finish_with(mut self, closing: Closing) -> (Shape, Vec<F>) {
        assert!(self.record_rows);

        if !self.hologram_aligned {
            let mult_var_base = self.push_multiplicities();
            let mask_var_base = self.values.len();
            for _ in 0..closing.mask_vars() {
                self.alloc(F::ZERO);
            }
            let lookups = (!self.tables.is_empty()).then(|| {
                assert_eq!(closing, Closing::V2);
                for _ in 0..2 * LOOKUP_MASK_ENTRIES {
                    self.alloc(F::ZERO);
                }
                self.take_lookups(mult_var_base, mask_var_base + closing.mask_vars())
            });
            let log_rows = (self.num_rows() + closing.pad_rows())
                .next_power_of_two()
                .trailing_zeros()
                .max(closing.min_log_rows()) as usize;
            let total = 1usize << log_rows;

            let num_sbox = self.sbox.len();
            let Rows {
                mut a,
                mut b,
                mut c,
            } = self.take_rows(total, closing.pad_rows());
            closing.push_rows(mask_var_base, &mut a, &mut b, &mut c);
            for matrix in [&mut a, &mut b, &mut c] {
                if let Some(t) = &mut matrix.templates {
                    t.candidates.clear();
                }
            }
            let z = core::mem::take(&mut self.values);
            let mut shape = Shape {
                log_rows,
                num_sbox,
                num_vars: z.len(),
                num_public: self.num_public,
                mask_var_base,
                a,
                b,
                c,
                hologram_meta: HologramMeta::default(),
                closing,
                lookups,
                digest: [0; 32],
            };
            shape.digest = shape.compute_digest();
            return (shape, z);
        }

        assert!(self.tables.is_empty());
        let pub_prefix = 1 + self.num_public;
        let pub_var_blocks = pub_prefix.div_ceil(128);
        let p2_var_base = 128 * pub_var_blocks;
        let misc_var_base = p2_var_base + self.p2_values.len();
        let misc_len = self.values.len() - pub_prefix;
        let mask_var_base = misc_var_base + misc_len;
        let num_vars = mask_var_base + closing.mask_vars();

        let remap_var = |v: u32| -> u32 {
            if v & P2_VAR_TAG != 0 {
                (p2_var_base as u32) + (v & !P2_VAR_TAG)
            } else if (v as usize) < pub_prefix {
                v
            } else {
                (misc_var_base as u32) + (v - (pub_prefix as u32))
            }
        };

        let num_sbox = self.p2_sbox.len() + self.sbox.len();
        let log_rows = (self.num_rows() + closing.pad_rows())
            .next_power_of_two()
            .trailing_zeros()
            .max(closing.min_log_rows()) as usize;
        let total = 1usize << log_rows;

        let mut rows = self.take_rows(total, closing.pad_rows());
        for matrix in rows.matrices() {
            matrix.map_cols(remap_var);
            matrix.sort_rows();
        }
        let Rows {
            mut a,
            mut b,
            mut c,
        } = rows;
        closing.push_rows(mask_var_base, &mut a, &mut b, &mut c);

        let mut z = Vec::new();
        qsag_core::wipe::secret_vec_reserve(&mut z, num_vars);
        qsag_core::wipe::secret_vec_extend_from_slice(&mut z, &self.values[..pub_prefix]);
        z.resize(p2_var_base, F::ZERO);
        qsag_core::wipe::secret_vec_extend_from_slice(&mut z, &self.p2_values);
        qsag_asm::volatile_fill(&mut self.p2_values, F::ZERO);
        self.p2_values = Vec::new();
        qsag_core::wipe::secret_vec_extend_from_slice(&mut z, &self.values[pub_prefix..]);
        qsag_asm::volatile_fill(&mut self.values, F::ZERO);
        self.values = Vec::new();
        z.resize(num_vars, F::ZERO);

        let mut shape = Shape {
            log_rows,
            num_sbox,
            num_vars,
            num_public: self.num_public,
            mask_var_base,
            a,
            b,
            c,
            hologram_meta: HologramMeta {
                poseidon2_perms: self.p2_perms,
                pub_var_blocks,
            },
            closing,
            lookups: None,
            digest: [0; 32],
        };
        shape.digest = shape.compute_digest();
        (shape, z)
    }
}

impl Drop for ConstraintSystem {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.values, F::ZERO);
        qsag_asm::volatile_fill(&mut self.p2_values, F::ZERO);
        for table in &mut self.tables {
            qsag_asm::volatile_fill(&mut table.mult, 0u64);
        }
    }
}

// ============================================================================
// Width-12 Poseidon2 gadgets (canonical profile of `crate::sponge`)
// ============================================================================

fn layer_matrix(layer: fn(&mut [F; 12])) -> [[F; 12]; 12] {
    let mut m = [[F::ZERO; 12]; 12];
    for j in 0..12 {
        let mut e = [F::ZERO; 12];
        e[j] = F::ONE;
        layer(&mut e);
        for i in 0..12 {
            m[i][j] = e[i];
        }
    }
    m
}

/// The permutation `crate::sponge::poseidon2_perm12` on linear forms: 118 S-box rows.
pub fn poseidon2_perm(cs: &mut ConstraintSystem, st: &mut [Lc; 12]) {
    #[cfg(feature = "std")]
    let (me, mi) = {
        type Matrices = ([[F; 12]; 12], [[F; 12]; 12]);
        static MATRICES: std::sync::OnceLock<Matrices> = std::sync::OnceLock::new();
        MATRICES.get_or_init(|| {
            (
                layer_matrix(poseidon2_apply_me),
                layer_matrix(poseidon2_apply_mi),
            )
        })
    };
    #[cfg(not(feature = "std"))]
    let (me, mi) = (
        layer_matrix(poseidon2_apply_me),
        layer_matrix(poseidon2_apply_mi),
    );
    let external: Vec<Vec<F>> = me.iter().map(|row| row.to_vec()).collect();
    let form = |basis: &[Lc], coeffs: &[F], constant: F| -> Lc {
        let parts: Vec<(F, &Lc)> = coeffs.iter().copied().zip(basis).collect();
        Lc::combine(&parts).plus_const(constant)
    };

    let mut basis: Vec<Lc> = st.to_vec();
    let mut lanes = external.clone();
    for tag in [0u64, 1, 2] {
        if tag == 1 {
            for r in 0..POSEIDON2_INT_ROUNDS {
                let x = form(&basis, &lanes[0], poseidon2_const_at(1, r as u64, 0));
                basis.push(cs.p2_sbox7(&x).into());
                let n = basis.len();
                for lane in &mut lanes {
                    lane.resize(n, F::ZERO);
                }
                lanes[0].fill(F::ZERO);
                lanes[0][n - 1] = F::ONE;
                let mut sum = vec![F::ZERO; n];
                for lane in &lanes {
                    for (s, &c) in sum.iter_mut().zip(lane) {
                        *s += c;
                    }
                }
                for (j, lane) in lanes.iter_mut().enumerate() {
                    let d = mi[j][j] - F::ONE;
                    for (c, &s) in lane.iter_mut().zip(&sum) {
                        *c = c.const_mul(d) + s;
                    }
                }
            }
        } else {
            for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
                let outputs: Vec<Lc> = (0..12)
                    .map(|lane| {
                        let rc = poseidon2_const_at(tag, r as u64, lane as u64);
                        cs.p2_sbox7(&form(&basis, &lanes[lane], rc)).into()
                    })
                    .collect();
                basis = outputs;
                lanes = external.clone();
            }
        }
    }
    for (slot, lane) in st.iter_mut().zip(&lanes) {
        *slot = form(&basis, lane, F::ZERO);
    }
    cs.finish_p2_perm_block();
}

/// Rate-6, capacity-6 sponge over [`poseidon2_perm`] with canonical padding.
pub fn sponge12(cs: &mut ConstraintSystem, message: &[Lc]) -> [Lc; 12] {
    let mut state: [Lc; 12] = core::array::from_fn(|_| Lc::zero());
    for chunk in message.chunks(6) {
        for (lane, value) in state.iter_mut().zip(chunk) {
            *lane = lane.plus(value);
        }
        if chunk.len() < 6 {
            state[chunk.len()] = state[chunk.len()].plus_const(F::ONE);
        }
        poseidon2_perm(cs, &mut state);
    }
    if message.len().is_multiple_of(6) {
        state[0] = state[0].plus_const(F::ONE);
        poseidon2_perm(cs, &mut state);
    }
    state
}

/// [`sponge12`] on field values.
pub fn sponge12_native(message: &[F]) -> [F; 12] {
    let mut state = [F::ZERO; 12];
    for chunk in message.chunks(6) {
        for (lane, &value) in state.iter_mut().zip(chunk) {
            *lane += value;
        }
        if chunk.len() < 6 {
            state[chunk.len()] += F::ONE;
        }
        poseidon2_perm12(&mut state);
    }
    if message.len().is_multiple_of(6) {
        state[0] += F::ONE;
        poseidon2_perm12(&mut state);
    }
    state
}

// ============================================================================
// Width-24 `Poseidon2-GL-w24` gadgets (`SECURITY.md §V2.10` + `§V2.11` 708-row R1CS)
// ============================================================================

/// Exact degree-3 R1CS row count of one `Poseidon2-GL-w24` permutation or 2-to-1 Merkle node:
/// `236` $x^7$ S-boxes $\times$ `3` cubic product rows (`x2 = x * x * 1`, `x4 = x2 * x2 * 1`,
/// `x7 = x * x2 * x4`) = `708` rows (`0` rows for linear layers or Jive feed-forward).
pub const POSEIDON2_GL24_R1CS3_ROWS: usize = 3 * POSEIDON2_GL24_SBOX_COUNT;

/// Exact pure-quadratic (`A * B = C`) R1CS row count of one `Poseidon2-GL-w24` permutation:
/// `236` $x^7$ S-boxes $\times$ `4` bilinear rows (`x2, x3, x4, x7`) = `944` rows.
pub const POSEIDON2_GL24_QUAD_R1CS_ROWS: usize = 4 * POSEIDON2_GL24_SBOX_COUNT;

fn layer_matrix24(layer: fn(&mut [F; 24])) -> [[F; 24]; 24] {
    let mut m = [[F::ZERO; 24]; 24];
    for j in 0..24 {
        let mut e = [F::ZERO; 24];
        e[j] = F::ONE;
        layer(&mut e);
        for i in 0..24 {
            m[i][j] = e[i];
        }
    }
    m
}

fn synthesize_poseidon2_gl24_perm_with<S>(
    sys: &mut S,
    st: &mut [Lc; 24],
    mut apply_sbox7: impl FnMut(&mut S, &Lc) -> Lc,
) {
    #[cfg(feature = "std")]
    let (me, mi) = {
        type Matrices24 = ([[F; 24]; 24], [[F; 24]; 24]);
        static MATRICES24: std::sync::OnceLock<Matrices24> = std::sync::OnceLock::new();
        MATRICES24.get_or_init(|| {
            (
                layer_matrix24(poseidon2_gl24_apply_me),
                layer_matrix24(poseidon2_gl24_apply_mi),
            )
        })
    };
    #[cfg(not(feature = "std"))]
    let (me, mi) = (
        layer_matrix24(poseidon2_gl24_apply_me),
        layer_matrix24(poseidon2_gl24_apply_mi),
    );
    let external: Vec<Vec<F>> = me.iter().map(|row| row.to_vec()).collect();
    let form = |basis: &[Lc], coeffs: &[F], constant: F| -> Lc {
        let parts: Vec<(F, &Lc)> = coeffs.iter().copied().zip(basis).collect();
        Lc::combine(&parts).plus_const(constant)
    };

    let mut basis: Vec<Lc> = st.to_vec();
    let mut lanes = external.clone();

    for r in 0..POSEIDON2_GL24_HALF_EXTERNAL_ROUNDS {
        let base = 24 * r;
        let outputs: Vec<Lc> = (0..24)
            .map(|lane| {
                let rc = F::from_u64_reduced(POSEIDON2_GL24_RC[base + lane]);
                apply_sbox7(sys, &form(&basis, &lanes[lane], rc))
            })
            .collect();
        basis = outputs;
        lanes = external.clone();
    }

    for r in 0..POSEIDON2_GL24_INTERNAL_ROUNDS {
        let rc = F::from_u64_reduced(POSEIDON2_GL24_RC[96 + r]);
        let x = form(&basis, &lanes[0], rc);
        basis.push(apply_sbox7(sys, &x));
        let n = basis.len();
        for lane in &mut lanes {
            lane.resize(n, F::ZERO);
        }
        lanes[0].fill(F::ZERO);
        lanes[0][n - 1] = F::ONE;
        let mut sum = vec![F::ZERO; n];
        for lane in &lanes {
            for (s, &c) in sum.iter_mut().zip(lane) {
                *s += c;
            }
        }
        for (j, lane) in lanes.iter_mut().enumerate() {
            let d = mi[j][j] - F::ONE;
            for (c, &s) in lane.iter_mut().zip(&sum) {
                *c = c.const_mul(d) + s;
            }
        }
    }

    for r in 0..POSEIDON2_GL24_HALF_EXTERNAL_ROUNDS {
        let base = 140 + 24 * r;
        let outputs: Vec<Lc> = (0..24)
            .map(|lane| {
                let rc = F::from_u64_reduced(POSEIDON2_GL24_RC[base + lane]);
                apply_sbox7(sys, &form(&basis, &lanes[lane], rc))
            })
            .collect();
        basis = outputs;
        lanes = external.clone();
    }

    for (slot, lane) in st.iter_mut().zip(&lanes) {
        *slot = form(&basis, lane, F::ZERO);
    }
}

fn build_gl24_merkle_state(left: &[Lc; 7], right: &[Lc; 7], tweak: &[Lc; 2]) -> [Lc; 24] {
    let mut st: [Lc; 24] = core::array::from_fn(|_| Lc::zero());
    st[..7].clone_from_slice(left);
    st[7..14].clone_from_slice(right);
    st[14] = tweak[0].clone();
    st[15] = tweak[1].clone();
    st[16] = Lc::constant(F::from_u64_reduced(POSEIDON2_GL24_RATE as u64));
    st[17] = Lc::constant(F::from_u64_reduced(POSEIDON2_GL24_CAPACITY as u64));
    st[18] = Lc::constant(F::from_u64_reduced(POSEIDON2_GL24_DIGEST_LIMBS as u64));
    st[19] = Lc::constant(F::from_u64_reduced(POSEIDON2_GL24_MERKLE_TAG));
    st[23] = Lc::constant(F::from_u64_reduced(POSEIDON2_GL24_IV));
    st
}

fn apply_gl24_merkle_jive_ff(
    perm_out: &[Lc; 24],
    left: &[Lc; 7],
    right: &[Lc; 7],
    tweak: &[Lc; 2],
) -> [Lc; 7] {
    let four = F::from_u64_reduced(4);
    core::array::from_fn(|i| {
        let mut ff = left[i].plus(&right[i].scaled(F::TWO));
        if i < 2 {
            ff = ff.plus(&tweak[i].scaled(four));
        }
        perm_out[i].plus(&ff)
    })
}

/// Native `ConstraintSystem` Width-24 `Poseidon2-GL-w24` permutation gadget: `236` `sbox7` rows,
/// `0` multiplication rows.
pub fn poseidon2_gl24_perm_gadget(cs: &mut ConstraintSystem, st: &mut [Lc; 24]) {
    synthesize_poseidon2_gl24_perm_with(cs, st, |sys, x| sys.sbox7(x).into());
}

/// Native `ConstraintSystem` 1-call 2-to-1 `Poseidon2-GL-w24` Merkle compression gadget (`7 + 7 + 2 = 16`
/// rate limbs + Jive feed-forward): `236` `sbox7` rows, `0` multiplication rows.
pub fn poseidon2_gl24_merkle_compress(
    cs: &mut ConstraintSystem,
    left: &[Lc; 7],
    right: &[Lc; 7],
    tweak: &[Lc; 2],
) -> [Lc; 7] {
    let mut st = build_gl24_merkle_state(left, right, tweak);
    poseidon2_gl24_perm_gadget(cs, &mut st);
    apply_gl24_merkle_jive_ff(&st, left, right, tweak)
}

/// Width-24 permutation with four rank-one product rows per S-box.
pub fn poseidon2_gl24_perm_quadratic(cs: &mut ConstraintSystem, st: &mut [Lc; 24]) {
    synthesize_poseidon2_gl24_perm_with(cs, st, |sys, x| {
        let x2: Lc = sys.mul(x, x).into();
        let x3: Lc = sys.mul(&x2, x).into();
        let x4: Lc = sys.mul(&x2, &x2).into();
        sys.mul(&x3, &x4).into()
    });
}

/// Pure quadratic (`A * B = C`) R1CS 2-to-1 `Poseidon2-GL-w24` Merkle compression gadget:
/// `944` bilinear multiplication rows (`4` per $x^7$ S-box), `0` `sbox7` rows.
pub fn poseidon2_gl24_merkle_compress_quadratic(
    cs: &mut ConstraintSystem,
    left: &[Lc; 7],
    right: &[Lc; 7],
    tweak: &[Lc; 2],
) -> [Lc; 7] {
    let mut st = build_gl24_merkle_state(left, right, tweak);
    poseidon2_gl24_perm_quadratic(cs, &mut st);
    apply_gl24_merkle_jive_ff(&st, left, right, tweak)
}

/// Compiled degree-3 R1CS relation (`SECURITY.md §V2.11` virtual product rows at group size $2^0 = 1$):
/// every row enforces `<a_i, z> * <b_i, z> * <d_i, z> = <c_i, z>` with `z[0] = 1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CubicR1csShape {
    pub num_rows: usize,
    pub num_vars: usize,
    pub num_public: usize,
    pub a: Csr,
    pub b: Csr,
    pub d: Csr,
    pub c: Csr,
}

impl CubicR1csShape {
    /// Verify `z[0] == 1` and `<a_i, z> * <b_i, z> * <d_i, z> == <c_i, z>` on every row.
    pub fn is_satisfied(&self, z: &[F]) -> bool {
        z.len() == self.num_vars
            && z.first().copied() == Some(F::ONE)
            && (0..self.num_rows).all(|i| {
                let va = self.a.row_dot(i, z);
                let vb = self.b.row_dot(i, z);
                let vd = self.d.row_dot(i, z);
                let vc = self.c.row_dot(i, z);
                va.const_mul(vb).const_mul(vd) == vc
            })
    }
}

/// Builder for degree-3 R1CS (`<a, z> * <b, z> * <d, z> = <c, z>`, `SECURITY.md §V2.11`),
/// realizing each $x^7$ S-box in **3 rows** (`x2 = x*x*1`, `x4 = x2*x2*1`, `x7 = x*x2*x4`),
/// so one `Poseidon2-GL-w24` 2-to-1 Merkle compression uses **exactly `708` rows**.
pub struct CubicR1csSystem {
    values: Vec<F>,
    num_public: usize,
    rows: Vec<(Lc, Lc, Lc, Lc)>,
}

impl Default for CubicR1csSystem {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for CubicR1csSystem {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.values, F::ZERO);
    }
}

impl CubicR1csSystem {
    pub fn new() -> Self {
        Self {
            values: vec![F::ONE],
            num_public: 0,
            rows: Vec::new(),
        }
    }

    pub fn public_input(&mut self, value: F) -> Var {
        assert_eq!(
            self.values.len(),
            1 + self.num_public,
            "public inputs are allocated first"
        );
        self.num_public += 1;
        self.alloc(value)
    }

    pub fn alloc(&mut self, value: F) -> Var {
        qsag_core::wipe::secret_vec_push(&mut self.values, value);
        Var((self.values.len() - 1) as u32)
    }

    pub fn eval(&self, lc: &Lc) -> F {
        lc.terms().iter().fold(F::ZERO, |acc, &(v, c)| {
            acc + c.const_mul(self.values[v as usize])
        })
    }

    /// Allocate `y = a * b * d` and record one cubic R1CS row `<a, z> * <b, z> * <d, z> = y`.
    pub fn mul3(&mut self, a: &Lc, b: &Lc, d: &Lc) -> Var {
        let val = self.eval(a).const_mul(self.eval(b)).const_mul(self.eval(d));
        let y = self.alloc(val);
        self.rows.push((a.clone(), b.clone(), d.clone(), y.into()));
        y
    }

    /// Allocate `y = x^7` in **3 cubic rows**: `x2 = x*x*1`, `x4 = x2*x2*1`, `x7 = x*x2*x4`.
    pub fn sbox7_cubic(&mut self, x: &Lc) -> Var {
        let one = Lc::constant(F::ONE);
        let x2: Lc = self.mul3(x, x, &one).into();
        let x4: Lc = self.mul3(&x2, &x2, &one).into();
        self.mul3(x, &x2, &x4)
    }

    pub fn enforce_equal(&mut self, a: &Lc, b: &Lc) {
        let one = Lc::constant(F::ONE);
        self.rows.push((a.minus(b), one.clone(), one, Lc::zero()));
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        self.rows.len()
    }

    pub fn finish(mut self) -> (CubicR1csShape, Vec<F>) {
        let (mut a, mut b, mut d, mut c) = (Csr::new(), Csr::new(), Csr::new(), Csr::new());
        let rows = core::mem::take(&mut self.rows);
        let num_rows = rows.len();
        for (ra, rb, rd, rc) in rows {
            a.push_row(&ra);
            b.push_row(&rb);
            d.push_row(&rd);
            c.push_row(&rc);
        }
        let z = core::mem::take(&mut self.values);
        let shape = CubicR1csShape {
            num_rows,
            num_vars: z.len(),
            num_public: self.num_public,
            a,
            b,
            d,
            c,
        };
        (shape, z)
    }
}

/// 708-row degree-3 R1CS (`SECURITY.md §V2.11`) `Poseidon2-GL-w24` permutation gadget.
pub fn poseidon2_gl24_perm_r1cs3(cs: &mut CubicR1csSystem, st: &mut [Lc; 24]) {
    synthesize_poseidon2_gl24_perm_with(cs, st, |sys, x| sys.sbox7_cubic(x).into());
}

/// **708-row** degree-3 R1CS (`SECURITY.md §V2.11`) 1-call 2-to-1 `Poseidon2-GL-w24` Merkle
/// compression gadget (`7 + 7 + 2 = 16` rate limbs + Jive feed-forward, `0` linear-layer rows).
pub fn poseidon2_gl24_merkle_compress_r1cs3(
    cs: &mut CubicR1csSystem,
    left: &[Lc; 7],
    right: &[Lc; 7],
    tweak: &[Lc; 2],
) -> [Lc; 7] {
    let mut st = build_gl24_merkle_state(left, right, tweak);
    poseidon2_gl24_perm_r1cs3(cs, &mut st);
    apply_gl24_merkle_jive_ff(&st, left, right, tweak)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    fn hex32(bytes: [u8; 32]) -> alloc::string::String {
        bytes.iter().map(|b| alloc::format!("{b:02x}")).collect()
    }

    #[test]
    fn recursive_row_templates_preserve_shape_digest_and_assignment() {
        fn build(mut cs: ConstraintSystem) -> (Shape, Vec<F>) {
            for j in 0..4 {
                let mut state = core::array::from_fn(|i| cs.alloc(f(1 + i as u64 + j)).into());
                poseidon2_gl24_perm_gadget(&mut cs, &mut state);
                cs.mul(&state[2], &state[0]);
            }
            cs.finish()
        }
        let (plain, original) = build(ConstraintSystem::new());
        let (compact, witness) = build(ConstraintSystem::with_row_templates());
        assert_eq!(original, witness);
        assert_eq!(compact, plain);
        assert!(compact.a.col.len() < compact.a.nnz());
        assert!(compact.is_satisfied(&witness));
    }

    #[test]
    fn public_aligned_shape_digest_is_pinned() {
        let mut cs = ConstraintSystem::new_hologram_aligned();
        let p: Lc = cs.public_input(f(5)).into();
        let q: Lc = cs.public_input(f(9)).into();
        let part = |cs: &mut ConstraintSystem, k: u64| {
            let x: Lc = cs.alloc(f(k + 2)).into();
            let y: Lc = cs.mul(&x, &p).into();
            let s: Lc = cs.sbox7(&y.plus(&q)).into();
            cs.enforce_boolean(&Lc::constant(f(1)));
            cs.enforce_equal(&s.minus(&s), &Lc::zero());
            let out = sponge12(cs, &[x.clone(), y.clone(), s.scaled(f(3)).plus_const(f(k))]);
            cs.enforce_mul(out[0].clone(), x.clone(), out[0].scaled(f(k + 2)));
            let sel = cs.select(&Lc::constant(f(1)), &out[1], &y);
            cs.enforce_equal(&sel, &out[1]);
        };
        let mut forks: Vec<ConstraintSystem> = Vec::new();
        for k in 1..4 {
            let mut child = cs.fork_public_inputs();
            part(&mut child, k);
            forks.push(child);
        }
        for child in forks {
            cs.append(child);
        }
        part(&mut cs, 0);
        let last: Lc = cs.alloc(f(77)).into();
        cs.enforce_zero(last.plus_const(F::ZERO - f(77)));
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        assert_eq!(
            (
                shape.log_rows,
                shape.num_sbox,
                shape.num_vars,
                hex32(shape.digest()).as_str()
            ),
            (
                10,
                516,
                669,
                "8bb1b9cfa74638c39783b86973cf53faff986a166b45109f13ef8da04e492345"
            )
        );
    }

    #[test]
    fn canonical_rate6_sponge_matches_accelerator_at_boundaries() {
        for n in [0, 1, 5, 6, 7, 11, 12, 13, 32] {
            let words: Vec<u64> = (0..n).map(|i| i as u64 * 7919 + 17).collect();
            let message: Vec<F> = words.iter().copied().map(F::from_u64_reduced).collect();
            let native = sponge12_native(&message);
            assert_eq!(
                native.map(|x| x.to_canonical_u64()),
                qsag_accel::poseidon2::sponge12_rate6(&words)
            );
            let mut cs = ConstraintSystem::new();
            let inputs: Vec<Lc> = message.iter().map(|&v| cs.alloc(v).into()).collect();
            let out = sponge12(&mut cs, &inputs);
            assert_eq!(out.map(|v| cs.eval(&v)), native);
            let (shape, assignment) = cs.finish_v2();
            assert!(shape.is_satisfied(&assignment));
        }
    }

    #[test]
    fn recording_keeps_the_relation_and_names_every_definition() {
        let build = |mut cs: ConstraintSystem| {
            let public: Lc = cs.public_input(f(6)).into();
            let x: Lc = cs
                .alloc_defined(f(2), || Def::Bits {
                    source: SourceId(0),
                    lo: 0,
                    width: 2,
                })
                .into();
            let y: Lc = cs.mul(&x, &x.plus_const(f(1))).into();
            cs.enforce_equal(&y, &public);
            let loose = cs.alloc(f(9));
            (cs, loose)
        };
        let (plain, _) = build(ConstraintSystem::new());
        let (shape, z) = plain.finish_v2();
        let (mut recording, loose) = build(ConstraintSystem::new_recording());
        let source = recording.source(|| Source::Input { bits: 2 });
        assert_eq!(source.index(), 0);
        let (shape2, z2, defs) = recording.finish_recorded();
        assert_eq!((shape.digest(), &z), (shape2.digest(), &z2));
        assert_eq!(defs.vars.len(), shape.num_vars);
        assert_eq!(defs.vars[0], Def::One);
        assert_eq!(defs.vars[1], Def::Public);
        assert!(matches!(defs.vars[2], Def::Bits { width: 2, .. }));
        assert!(matches!(defs.vars[3], Def::Product(..)));
        assert_eq!(defs.undefined(), vec![loose.index()]);
        assert!(
            defs.vars[shape.mask_var_base..]
                .iter()
                .all(|d| *d == Def::Mask)
        );
        let mut cs = ConstraintSystem::new();
        cs.alloc_defined(f(1), || unreachable!());
        cs.source(|| unreachable!());
    }

    #[test]
    fn lookups_add_no_rows_and_their_shape_is_value_independent() {
        let build = |x: [u64; 3]| {
            let mut cs = ConstraintSystem::new();
            let pairs: Vec<F> = (0..5u64).flat_map(|t| [f(t), f(10 * t)]).collect();
            let table = cs.table(2, pairs);
            let a: Lc = cs.alloc(f(x[0])).into();
            let b: Lc = cs.alloc(f(x[1])).into();
            let c: Lc = cs.alloc(f(x[2])).into();
            cs.enforce_byte(&a);
            cs.enforce_byte(&a.plus(&b));
            cs.enforce_in_table(table, &[b.clone(), c]);
            assert_eq!((cs.num_rows(), cs.num_lookups()), (0, 3));
            cs.finish_v2()
        };
        let (shape, z) = build([200, 3, 30]);
        let (shape2, z2) = build([0, 4, 40]);
        assert_eq!(shape, shape2);
        assert_eq!(shape.digest(), shape2.digest());
        assert!(shape.is_satisfied(&z) && shape.is_satisfied(&z2));
        let lookups = shape.lookups().unwrap();
        assert_eq!(lookups.num_lookups, 3);
        assert_eq!(lookups.num_table_rows, 5 + 256);
        assert_eq!(lookups.width(), 3);
        assert_eq!(
            shape.num_vars,
            1 + 3 + 261 + Closing::V2.mask_vars() + 2 * LOOKUP_MASK_ENTRIES
        );
        let mut masked = z.clone();
        for slot in &mut masked[shape.mask_var_base..] {
            *slot = f(0xBEEF);
        }
        assert!(shape.is_satisfied(&masked));
        for bad in [[200, 56, 0], [256, 0, 0], [1, 5, 50], [1, 3, 40]] {
            let (_, z) = build(bad);
            assert!(!shape.is_satisfied(&z), "{bad:?}");
        }
    }

    #[test]
    fn witness_only_and_forked_synthesis_reproduce_the_multiplicities() {
        let synth = |cs: &mut ConstraintSystem, x: u64| {
            let v: Lc = cs.alloc(f(x)).into();
            cs.enforce_byte(&v);
            cs.enforce_byte(&v.plus_const(f(1)));
        };
        let serial = {
            let mut cs = ConstraintSystem::new();
            cs.range_table(8);
            synth(&mut cs, 5);
            synth(&mut cs, 6);
            cs.finish_v2()
        };
        let forked = {
            let mut cs = ConstraintSystem::new();
            cs.range_table(8);
            let mut left = cs.fork_public_inputs();
            let mut right = cs.fork_public_inputs();
            synth(&mut left, 5);
            synth(&mut right, 6);
            cs.append(left);
            cs.append(right);
            cs.finish_v2()
        };
        assert_eq!(serial, forked);
        assert!(serial.0.is_satisfied(&serial.1));
        let mut cs = ConstraintSystem::witness_only();
        cs.range_table(8);
        synth(&mut cs, 5);
        synth(&mut cs, 6);
        assert_eq!(cs.finish_assignment(&serial.0), Some(serial.1.clone()));
    }

    #[test]
    fn poseidon2_gl24_merkle_gadgets_match_native_and_hit_708_r1cs3_rows() {
        use crate::sponge::poseidon2_gl24_compress_merkle;

        let left_vals: [F; 7] = core::array::from_fn(|i| f((i + 1) as u64));
        let right_vals: [F; 7] = core::array::from_fn(|i| f((i + 8) as u64));
        let tweak_vals: [F; 2] = [f(100), f(200)];
        let want = poseidon2_gl24_compress_merkle(&left_vals, &right_vals, &tweak_vals);

        // 1. Exact 708-row degree-3 R1CS (`§V2.11`) Merkle-compression gadget (including zero wires!).
        let mut cs3 = CubicR1csSystem::new();
        let l3: [Lc; 7] = core::array::from_fn(|i| cs3.alloc(left_vals[i]).into());
        let r3: [Lc; 7] = core::array::from_fn(|i| cs3.alloc(right_vals[i]).into());
        let tw3: [Lc; 2] = core::array::from_fn(|i| cs3.alloc(tweak_vals[i]).into());
        let out3 = poseidon2_gl24_merkle_compress_r1cs3(&mut cs3, &l3, &r3, &tw3);
        assert_eq!(cs3.num_rows(), POSEIDON2_GL24_R1CS3_ROWS);
        assert_eq!(cs3.num_rows(), 708);
        assert_eq!(out3.map(|lc| cs3.eval(&lc)), want);
        let (shape3, z3) = cs3.finish();
        assert_eq!(shape3.num_rows, 708);
        assert!(shape3.is_satisfied(&z3));
        let mut bad3 = z3.clone();
        bad3[25] += F::ONE;
        assert!(!shape3.is_satisfied(&bad3));

        // 2. Native `ConstraintSystem` (`236` `sbox7` rows, `v2` closing).
        let mut cs = ConstraintSystem::new();
        let l_lc: [Lc; 7] = core::array::from_fn(|i| cs.alloc(left_vals[i]).into());
        let r_lc: [Lc; 7] = core::array::from_fn(|i| cs.alloc(right_vals[i]).into());
        let tw_lc: [Lc; 2] = core::array::from_fn(|i| cs.alloc(tweak_vals[i]).into());
        let out_lc = poseidon2_gl24_merkle_compress(&mut cs, &l_lc, &r_lc, &tw_lc);
        assert_eq!(cs.num_rows(), 236);
        assert_eq!(out_lc.map(|lc| cs.eval(&lc)), want);
        let (shape_v2, z_v2) = cs.finish_v2();
        assert_eq!(shape_v2.num_sbox, 236);
        assert!(shape_v2.is_satisfied(&z_v2));

        // 3. Pure quadratic (`944` `mul` rows, `0` `sbox7` rows).
        let mut cs_q = ConstraintSystem::new();
        let lq: [Lc; 7] = core::array::from_fn(|i| cs_q.alloc(left_vals[i]).into());
        let rq: [Lc; 7] = core::array::from_fn(|i| cs_q.alloc(right_vals[i]).into());
        let twq: [Lc; 2] = core::array::from_fn(|i| cs_q.alloc(tweak_vals[i]).into());
        let out_q = poseidon2_gl24_merkle_compress_quadratic(&mut cs_q, &lq, &rq, &twq);
        assert_eq!(cs_q.num_rows(), POSEIDON2_GL24_QUAD_R1CS_ROWS);
        assert_eq!(cs_q.num_rows(), 944);
        assert_eq!(out_q.map(|lc| cs_q.eval(&lc)), want);
        let (shape_q, z_q) = cs_q.finish_v2();
        assert_eq!(shape_q.num_sbox, 0);
        assert!(shape_q.is_satisfied(&z_q));
    }
}
