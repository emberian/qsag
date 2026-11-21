//! zk-Hem v2 for a [`Shape`] closed by `ConstraintSystem::finish_v2` (SECURITY.md, V2.1).
//!
//! One Stage-0 commitment holds the assignment table `Z` (`params::Layout`) and the mask
//! polynomial `R`. The front end is that of v1 over `F_{p^5}` with five limbs: a masked row
//! sumcheck, the row values, a masked column sumcheck over the variable cube, and one linear
//! functional `K` with value `V` for everything that remains. `K` reads the variable cells
//! below `var_cells` and the two sumcheck masks, nothing else; [`super::pcs`] opens it.
//!
//! The prover refuses ([`ZkHemV2Error::MaskRankDeficient`]) when the verifier's coins fall
//! outside the event Good, a predicate of those coins only: (G1) is [`row_challenge_good`],
//! (G2) and (G3) are tested inside [`super::pcs::open`].

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use super::field5::Fp5;
use super::hash::{Digest, Transcript};
use super::params::{
    COL_DEGREE, COL_MASK_BITS, DIGEST_BYTES, LIMBS, Layout, PAD_VARS, Profile, ROW_DEGREE,
    ROW_MASK_BITS, ShapeSize,
};
use super::pcs::{self, Opening, TensorTerm, par_chunk, par_chunks_mut, par_sum};
use crate::field::{Goldilocks, GoldilocksOps as _};
use crate::pcs::hypercube_to_monomial_coeffs;
use crate::sponge::cshake256_32;
use crate::zk_hem::SeedStream;
use crate::zk_hem::relation::{Closing, Shape};

type E = Fp5;
type F = Goldilocks;

/// First bytes of every serialized v2 proof.
pub const MAGIC: [u8; 8] = *b"QSAGZKH2";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkHemV2Error {
    /// The assignment does not satisfy the relation.
    Unsatisfied,
    /// The relation was not closed by `finish_v2`, or it does not fit a v2 table.
    UnsupportedRelation,
    /// The verifier's coins fell outside the event Good; the proof would not be zero
    /// knowledge. This happens with probability below `2^-59`. Retry with a new seed.
    MaskRankDeficient,
}

/// The table layout of a v2 relation, or `None` if it has none.
pub fn layout_of(shape: &Shape) -> Option<Layout> {
    if shape.closing() != Closing::V2 || shape.log_rows < 5 {
        return None;
    }
    let layout = Layout::new(ShapeSize {
        log_rows: shape.log_rows,
        num_vars: shape.num_vars,
        num_public: shape.num_public,
    })?;
    pcs::stage_dims(layout.log_cells, &layout.schedule)?;
    Some(layout)
}

/// A zk-Hem v2 proof. Wire format ([`Self::to_bytes`]): the magic `QSAGZKH2`, the profile
/// tag, `log_cells`, the Stage-0 root, then the prover messages in round order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkHemV2Proof {
    pub profile: Profile,
    pub log_cells: u8,
    /// Root of the Stage-0 tree over `(Z^, R^)`.
    pub root: Digest,
    /// `sum_x g1(x)`.
    pub row_mask_sum: E,
    /// Coefficients of the masked row rounds.
    pub row_rounds: Vec<Vec<E>>,
    /// `(Az, Bz, Cz)(rx)`.
    pub row_values: [E; 3],
    /// `sum_y g2(y)`.
    pub col_mask_sum: E,
    /// Coefficients of the masked column rounds.
    pub col_rounds: Vec<Vec<E>>,
    pub opening: Opening,
}

impl ZkHemV2Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&MAGIC);
        out.push(self.profile.wire_tag());
        out.push(self.log_cells);
        out.extend_from_slice(&self.root);
        let push = |out: &mut Vec<u8>, v: &E| out.extend_from_slice(&v.to_le_bytes());
        push(&mut out, &self.row_mask_sum);
        self.row_rounds
            .iter()
            .flatten()
            .for_each(|v| push(&mut out, v));
        self.row_values.iter().for_each(|v| push(&mut out, v));
        push(&mut out, &self.col_mask_sum);
        self.col_rounds
            .iter()
            .flatten()
            .for_each(|v| push(&mut out, v));
        self.opening.push_bytes(&mut out);
        out
    }

    /// Canonical decoding for the relation: rejects another magic (a v1 proof has none), an
    /// unknown profile tag, a table size other than the relation's, non-reduced field
    /// elements, wrong lengths and trailing bytes.
    pub fn from_bytes(bytes: &[u8], shape: &Shape) -> Option<Self> {
        let layout = layout_of(shape)?;
        if bytes.get(..8)? != MAGIC {
            return None;
        }
        let profile = Profile::from_wire_tag(*bytes.get(8)?)?;
        let log_cells = *bytes.get(9)?;
        if usize::from(log_cells) != layout.log_cells {
            return None;
        }
        let mut pos = 10usize;
        let root: Digest = bytes.get(pos..pos + DIGEST_BYTES)?.try_into().ok()?;
        pos += DIGEST_BYTES;
        let take = |pos: &mut usize| -> Option<E> {
            let chunk: [u8; 40] = bytes.get(*pos..*pos + 40)?.try_into().ok()?;
            *pos += 40;
            E::from_le_bytes_canonical(chunk)
        };
        let rounds = |pos: &mut usize, n: usize, d: usize| -> Option<Vec<Vec<E>>> {
            (0..n)
                .map(|_| (0..=d).map(|_| take(pos)).collect())
                .collect()
        };
        let row_mask_sum = take(&mut pos)?;
        let row_rounds = rounds(&mut pos, shape.log_rows, ROW_DEGREE)?;
        let row_values = [take(&mut pos)?, take(&mut pos)?, take(&mut pos)?];
        let col_mask_sum = take(&mut pos)?;
        let col_rounds = rounds(&mut pos, layout.var_bits, COL_DEGREE)?;
        let opening = Opening::read(bytes, &mut pos, layout.log_cells, &layout.schedule)?;
        (pos == bytes.len()).then_some(Self {
            profile,
            log_cells,
            root,
            row_mask_sum,
            row_rounds,
            row_values,
            col_mask_sum,
            col_rounds,
            opening,
        })
    }
}

// ============================================================================
// Shared algebra
// ============================================================================

/// The `F_p`-basis `1, X, .., X^4` of the challenge field, dual to [`Fp5::to_limbs`].
fn limb_basis() -> [E; LIMBS] {
    core::array::from_fn(|j| {
        let mut limbs = [F::ZERO; LIMBS];
        limbs[j] = F::ONE;
        E::from_limbs(limbs)
    })
}

#[inline]
fn eval_poly(coeffs: &[E], x: E) -> E {
    coeffs.iter().rev().fold(E::ZERO, |acc, &c| acc * x + c)
}

fn eq_eval(a: &[E], b: &[E]) -> E {
    a.iter().zip(b).fold(E::ONE, |acc, (&x, &y)| {
        let xy = x * y;
        acc * (xy + xy + E::ONE - x - y)
    })
}

/// `eq(point, x)` for every `x`, with `point[0]` on the lowest index bit.
fn eq_table(point: &[E]) -> Vec<E> {
    let serial = |point: &[E]| {
        let mut table = vec![E::ZERO; 1 << point.len()];
        table[0] = E::ONE;
        for (j, &r) in point.iter().enumerate() {
            let (lo, hi) = table[..2 << j].split_at_mut(1 << j);
            for (l, h) in lo.iter_mut().zip(hi) {
                *h = *l * r;
                *l -= *h;
            }
        }
        table
    };
    let mut table = vec![E::ZERO; 1 << point.len()];
    let rows = par_chunk(table.len());
    if rows >= table.len() {
        return serial(point);
    }
    // The table is the product of the tables of the two halves of the point.
    let split = point.len() / 2;
    let (low, high) = (serial(&point[..split]), serial(&point[split..]));
    let per_job = rows.div_ceil(low.len()) * low.len();
    par_chunks_of(&mut table, per_job, |off, part| {
        for (block, &h) in part.chunks_mut(low.len()).zip(&high[off / low.len()..]) {
            for (slot, &l) in block.iter_mut().zip(&low) {
                *slot = h * l;
            }
        }
    });
    table
}

/// `f(offset, chunk)` over consecutive chunks of `chunk` elements of `data`.
fn par_chunks_of(data: &mut [E], chunk: usize, f: impl Fn(usize, &mut [E]) + Sync) {
    #[cfg(feature = "std")]
    {
        std::thread::scope(|scope| {
            for (k, part) in data.chunks_mut(chunk).enumerate() {
                let f = &f;
                crate::spawn_bounded(scope, move || f(k * chunk, part));
            }
        });
    }
    #[cfg(not(feature = "std"))]
    for (k, part) in data.chunks_mut(chunk).enumerate() {
        f(k * chunk, part);
    }
}

/// `eq(point, bits of index)` for one index.
fn eq_index(point: &[E], index: usize) -> E {
    point.iter().enumerate().fold(E::ONE, |acc, (j, &r)| {
        acc * if (index >> j) & 1 == 1 { r } else { E::ONE - r }
    })
}

/// Multilinear extension of the indicator of `{0, .., count - 1}` at `point`.
fn prefix_indicator(point: &[E], count: usize) -> E {
    if count >> point.len() != 0 {
        return E::ONE;
    }
    let mut acc = E::ZERO;
    let mut prefix = E::ONE;
    for (j, &r) in point.iter().enumerate().rev() {
        if (count >> j) & 1 == 1 {
            acc += prefix * (E::ONE - r);
            prefix *= r;
        } else {
            prefix *= E::ONE - r;
        }
    }
    acc
}

/// The row constraint `s (a^7 - c) + (1 - s)(a b - c)`.
#[inline]
fn row_gate(s: E, a: E, b: E, c: E) -> E {
    let a2 = a.square();
    let a7 = a2.square() * a2 * a;
    let ab = a * b;
    s * (a7 - ab) + ab - c
}

fn pow2(n: usize) -> E {
    (0..n).fold(E::ONE, |acc, _| acc + acc)
}

fn pow2_coords(x: E, bits: usize) -> Vec<E> {
    let mut out = Vec::with_capacity(bits);
    let mut cur = x;
    for _ in 0..bits {
        out.push(cur);
        cur = cur.square();
    }
    out
}

/// Coefficients of the polynomial of degree below `evals.len()` with the given values at
/// `0, 1, 2, ..`: divided differences, then expansion of the Newton form.
fn evals_to_coeffs(evals: &[E]) -> Vec<E> {
    let n = evals.len();
    let mut dd = evals.to_vec();
    for j in 1..n {
        let inv = F::from_u64_reduced(j as u64).inv();
        for i in (j..n).rev() {
            dd[i] = (dd[i] - dd[i - 1]).mul_base(inv);
        }
    }
    let mut out = vec![E::ZERO; n];
    for i in (0..n).rev() {
        // out <- out * (X - i) + dd[i]
        let node = F::from_u64_reduced(i as u64);
        for k in (1..n).rev() {
            out[k] = out[k - 1] - out[k].mul_base(node);
        }
        out[0] = dd[i] - out[0].mul_base(node);
    }
    qsag_asm::volatile_fill(&mut dd, E::ZERO);
    out
}

// ============================================================================
// The event Good, condition (G1)
// ============================================================================

/// Determinant of the five by five base-field matrix whose columns are the limbs of the
/// corner weights `eq((rx_0, rx_1, rx_2), c)`, `c = 0..4`.
pub fn pad_basis_det(rx: &[E]) -> F {
    let weights: [E; LIMBS] = core::array::from_fn(|c| eq_index(&rx[..3], c));
    let mut m: [[F; LIMBS]; LIMBS] =
        core::array::from_fn(|row| core::array::from_fn(|col| weights[col].to_limbs()[row]));
    let mut det = F::ONE;
    for col in 0..LIMBS {
        let Some(pivot) = (col..LIMBS).find(|&row| !m[row][col].is_zero()) else {
            return F::ZERO;
        };
        if pivot != col {
            m.swap(col, pivot);
            det = -det;
        }
        det *= m[col][col];
        let inv = m[col][col].inv();
        let pivot_row = m[col];
        for row in m.iter_mut().skip(col + 1) {
            let factor = row[col] * inv;
            for (cell, p) in row.iter_mut().zip(pivot_row) {
                *cell -= factor * p;
            }
        }
    }
    det
}

/// Whether the five corner weights are an `F_p`-basis of the challenge field.
pub fn pad_basis_exists(rx: &[E]) -> bool {
    !pad_basis_det(rx).is_zero()
}

/// Common weight of the eight rows `base..base + 8` at `rx`, without the three low variables.
fn corner_factor(rx: &[E], base: usize) -> E {
    rx.iter().enumerate().skip(3).fold(E::ONE, |acc, (j, &r)| {
        acc * if (base >> j) & 1 == 1 { r } else { E::ONE - r }
    })
}

/// Condition (G1): the masking rows make `(Az, Bz, Cz)(rx)` uniform.
pub fn row_challenge_good(shape: &Shape, rx: &[E]) -> bool {
    pad_basis_exists(rx) && (0..3).all(|g| !corner_factor(rx, shape.mask_row_base(g)).is_zero())
}

// ============================================================================
// Coins and masks
// ============================================================================

/// The prover's coins (SECURITY.md V2.5): uniform base-field elements from
/// `cSHAKE256("QSAG.ZKHEM2.COINS/v1")` keyed by a hash of the seed, the profile tag, the
/// relation digest, the layout, the statement and the witness.
struct Coins(SeedStream);

impl Coins {
    fn new(
        profile: Profile,
        shape: &Shape,
        layout: &Layout,
        statement: &[u8],
        assignment: &[F],
        seed: &[u8; 32],
    ) -> Self {
        let mut input = seed.to_vec();
        input.push(profile.wire_tag());
        input.extend_from_slice(&shape.digest());
        input.extend_from_slice(&layout_bytes(shape, layout));
        input.extend_from_slice(&cshake256_32(b"QSAG.ZKHEM2.COINS.STMT/v1", statement));
        let mut witness: Vec<u8> = assignment.iter().flat_map(|v| v.to_le_bytes()).collect();
        input.extend_from_slice(&cshake256_32(b"QSAG.ZKHEM2.COINS.WIT/v1", &witness));
        qsag_asm::volatile_fill(&mut witness, 0u8);
        let mut coin_seed = cshake256_32(b"QSAG.ZKHEM2.COINS.SEED/v1", &input);
        qsag_asm::volatile_fill(&mut input, 0u8);
        let stream = SeedStream::new(b"QSAG.ZKHEM2.COINS/v1", &coin_seed);
        qsag_asm::volatile_fill(&mut coin_seed, 0u8);
        Self(stream)
    }

    fn next_base(&mut self) -> F {
        self.0.next_base()
    }

    fn next_fp5(&mut self) -> E {
        E::from_limbs(core::array::from_fn(|_| self.0.next_base()))
    }
}

/// A separable mask `g(x) = sum_i u_i(x_i)`, `u_i(X) = sum_k coef[i][k] X^k`.
struct Mask {
    coef: Vec<Vec<E>>,
}

impl Mask {
    fn sample(coins: &mut Coins, rounds: usize, degree: usize) -> Self {
        let coef = (0..rounds)
            .map(|_| (0..=degree).map(|_| coins.next_fp5()).collect())
            .collect();
        Self { coef }
    }

    /// `u_i(0) + u_i(1)`.
    fn unit_sum(&self, i: usize) -> E {
        self.coef[i].iter().fold(self.coef[i][0], |acc, &c| acc + c)
    }

    /// `sum_x g(x)` over the cube.
    fn sum(&self) -> E {
        let n = self.coef.len();
        pow2(n - 1) * (0..n).fold(E::ZERO, |acc, i| acc + self.unit_sum(i))
    }

    /// `g` at a full point.
    fn eval(&self, point: &[E]) -> E {
        self.coef
            .iter()
            .zip(point)
            .fold(E::ZERO, |acc, (u, &c)| acc + eval_poly(u, c))
    }

    /// Coefficients of `X -> sum_x g(c_0, .., c_{i-1}, X, x)`.
    fn round_poly(&self, prefix: &[E]) -> Vec<E> {
        let (i, n) = (prefix.len(), self.coef.len());
        let free = n - i - 1;
        let scale = pow2(free);
        let mut out: Vec<E> = self.coef[i].iter().map(|&c| scale * c).collect();
        out[0] += scale * self.eval(prefix);
        if free > 0 {
            out[0] += pow2(free - 1) * (i + 1..n).fold(E::ZERO, |acc, j| acc + self.unit_sum(j));
        }
        out
    }

    /// Store limb `j` of round `i` as the hypercube values of the multilinear polynomial
    /// whose monomial coefficient `k` is that limb of `coef[i][k]`. Its evaluation at
    /// `(x, x^2, x^4, ..)` is then the limb of `u_i(x)`.
    fn write(&self, cells: &mut [F], bits: usize, block: impl Fn(usize, usize) -> usize) {
        for (i, row) in self.coef.iter().enumerate() {
            for j in 0..LIMBS {
                let mut m = vec![F::ZERO; 1 << bits];
                for (slot, c) in m.iter_mut().zip(row) {
                    *slot = c.to_limbs()[j];
                }
                for b in 0..bits {
                    for idx in 0..m.len() {
                        if (idx >> b) & 1 == 1 {
                            let lower = m[idx ^ (1 << b)];
                            m[idx] += lower;
                        }
                    }
                }
                let off = block(i, j);
                cells[off..off + m.len()].copy_from_slice(&m);
                qsag_asm::volatile_fill(&mut m, F::ZERO);
            }
        }
    }
}

impl Drop for Mask {
    fn drop(&mut self) {
        for row in &mut self.coef {
            qsag_asm::volatile_fill(row, E::ZERO);
        }
    }
}

/// Everything the prover draws, placed: the table with masking variables, sumcheck masks and
/// blinders, the mask polynomial and the salt seed.
struct Secrets {
    table: Vec<F>,
    row_mask: Mask,
    col_mask: Mask,
    mask_poly: Vec<E>,
    salt_seed: [u8; 32],
}

impl Drop for Secrets {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.table, F::ZERO);
        qsag_asm::volatile_fill(&mut self.mask_poly, E::ZERO);
        qsag_asm::volatile_fill(&mut self.salt_seed, 0u8);
    }
}

/// Draw the coins in a fixed order and build the table. `assignment` gets its masking
/// variables.
fn sample_secrets(
    coins: &mut Coins,
    shape: &Shape,
    layout: &Layout,
    assignment: &mut [F],
) -> Secrets {
    for slot in &mut assignment[shape.mask_var_base..] {
        *slot = coins.next_base();
    }
    let cells = 1usize << layout.log_cells;
    let row_mask = Mask::sample(coins, shape.log_rows, ROW_DEGREE);
    let col_mask = Mask::sample(coins, layout.var_bits, COL_DEGREE);
    let mut table = vec![F::ZERO; cells];
    row_mask.write(&mut table, ROW_MASK_BITS, |i, j| {
        layout.row_mask_block(i, j)
    });
    col_mask.write(&mut table, COL_MASK_BITS, |i, j| {
        layout.col_mask_block(shape.log_rows, i, j)
    });
    table[..shape.num_vars].copy_from_slice(assignment);
    for slot in &mut table[cells - layout.blind_cells..] {
        *slot = coins.next_base();
    }
    let step_vars = layout.schedule.stages[0].step_vars;
    let mask_poly = (0..pcs::mask_len(layout.log_cells, step_vars))
        .map(|_| coins.next_fp5())
        .collect();
    let mut salt_seed = [0u8; 32];
    for chunk in salt_seed.chunks_mut(8) {
        chunk.copy_from_slice(&coins.next_base().to_le_bytes());
    }
    Secrets {
        table,
        row_mask,
        col_mask,
        mask_poly,
        salt_seed,
    }
}

// ============================================================================
// The linear functional of step 4
// ============================================================================

struct ClaimInputs<'a> {
    layout: &'a Layout,
    log_rows: usize,
    num_public: usize,
    rx: &'a [E],
    ry: &'a [E],
    lambda: E,
    rho2: E,
    matrix_at_point: E,
}

impl ClaimInputs<'_> {
    /// `lambda^0, lambda^1, ..`: the two mask sums, `g1(rx)`, the column terminal value, the
    /// constant cell and the public inputs.
    fn powers(&self) -> Vec<E> {
        (0..5 + self.num_public)
            .scan(E::ONE, |acc, _| {
                let cur = *acc;
                *acc *= self.lambda;
                Some(cur)
            })
            .collect()
    }

    /// Cells of the variable region the column sumcheck sums over.
    fn var_cells(&self) -> usize {
        self.layout.var_cells.min(1 << self.layout.var_bits)
    }
}

/// The point selecting the block at cell offset `block` with `low` on its own variables,
/// without trailing zero coordinates.
fn block_point(block: usize, low: &[E]) -> Vec<E> {
    let mut point = low.to_vec();
    let mut b = low.len();
    while block >> b != 0 {
        point.push(if (block >> b) & 1 == 1 {
            E::ONE
        } else {
            E::ZERO
        });
        b += 1;
    }
    point
}

/// `K` as tensor terms, for the verifier: weighted evaluations of the multilinear table.
fn claim_terms(inp: &ClaimInputs<'_>) -> Vec<TensorTerm> {
    let basis = limb_basis();
    let lam = inp.powers();
    let k = inp.layout.var_bits;
    let mut terms = Vec::new();
    let mut push = |weight: E, point: Vec<E>| terms.push(TensorTerm { weight, point });
    let row_half = pow2(inp.log_rows - 1);
    let col_half = pow2(k - 1);
    for (j, &limb) in basis.iter().enumerate() {
        for i in 0..inp.log_rows {
            let block = inp.layout.row_mask_block(i, j);
            // sum g1 = 2^(n-1) sum_i (u_i(0) + u_i(1)).
            push(
                lam[0] * row_half * limb,
                block_point(block, &[E::ZERO; ROW_MASK_BITS]),
            );
            push(
                lam[0] * row_half * limb,
                block_point(block, &[E::ONE; ROW_MASK_BITS]),
            );
            // g1(rx) = sum_i u_i(rx_i).
            push(
                lam[2] * limb,
                block_point(block, &pow2_coords(inp.rx[i], ROW_MASK_BITS)),
            );
        }
        for i in 0..k {
            let block = inp.layout.col_mask_block(inp.log_rows, i, j);
            push(
                lam[1] * col_half * limb,
                block_point(block, &[E::ZERO; COL_MASK_BITS]),
            );
            push(
                lam[1] * col_half * limb,
                block_point(block, &[E::ONE; COL_MASK_BITS]),
            );
            push(
                lam[3] * inp.rho2 * limb,
                block_point(block, &pow2_coords(inp.ry[i], COL_MASK_BITS)),
            );
        }
    }
    // M(rx, ry) * Z_var~(ry): one term per dyadic block of [0, var_cells).
    let count = inp.var_cells();
    let mut start = 0usize;
    for a in (0..=k).rev() {
        if (count >> a) & 1 == 1 {
            let weight = lam[3] * inp.matrix_at_point * eq_index(&inp.ry[a..], start >> a);
            push(weight, block_point(start, &inp.ry[..a]));
            start += 1 << a;
        }
    }
    // Variable 0 holds the constant 1; variables 1..=num_public hold the public inputs.
    for i in 0..=inp.num_public {
        push(lam[4 + i], block_point(i, &[]));
    }
    terms
}

/// `K` as weights on the cells of the table, for the prover: `sum_y out[y] Z[y]` is the value
/// of the functional. The length is a power of two covering every cell `K` reads.
fn claim_cell_weights(inp: &ClaimInputs<'_>) -> Vec<E> {
    let basis = limb_basis();
    let lam = inp.powers();
    let k = inp.layout.var_bits;
    let end = inp.layout.col_mask_block(inp.log_rows, k, 0);
    let mut out = vec![E::ZERO; end.next_power_of_two()];
    let row_half = pow2(inp.log_rows - 1);
    let col_half = pow2(k - 1);
    for i in 0..inp.log_rows {
        let eq = eq_table(&pow2_coords(inp.rx[i], ROW_MASK_BITS));
        for (j, &limb) in basis.iter().enumerate() {
            let block = inp.layout.row_mask_block(i, j);
            out[block] += lam[0] * row_half * limb;
            out[block + eq.len() - 1] += lam[0] * row_half * limb;
            for (slot, &e) in out[block..].iter_mut().zip(&eq) {
                *slot += lam[2] * limb * e;
            }
        }
    }
    for i in 0..k {
        let eq = eq_table(&pow2_coords(inp.ry[i], COL_MASK_BITS));
        for (j, &limb) in basis.iter().enumerate() {
            let block = inp.layout.col_mask_block(inp.log_rows, i, j);
            out[block] += lam[1] * col_half * limb;
            out[block + eq.len() - 1] += lam[1] * col_half * limb;
            for (slot, &e) in out[block..].iter_mut().zip(&eq) {
                *slot += lam[3] * inp.rho2 * limb * e;
            }
        }
    }
    let eq = eq_table(inp.ry);
    let scale = lam[3] * inp.matrix_at_point;
    let count = inp.var_cells();
    par_chunks_mut(&mut out[..count], |off, part| {
        for (slot, &e) in part.iter_mut().zip(&eq[off..]) {
            *slot += scale * e;
        }
    });
    for i in 0..=inp.num_public {
        out[i] += lam[4 + i];
    }
    out
}

/// Turn weights on cells into the kernel on monomial coefficients: a cell is the sum of the
/// coefficients whose index is a subset of its own, so coefficient `i` gets the sum of the
/// weights of the cells containing `i`.
fn cell_weights_to_kernel(mut weights: Vec<E>, cells: usize) -> Vec<E> {
    let bits = weights.len().trailing_zeros() as usize;
    let low = bits.min(16);
    let within = |block: &mut [E]| {
        for b in 0..low {
            for idx in 0..block.len() {
                if (idx >> b) & 1 == 0 {
                    let upper = block[idx | (1 << b)];
                    block[idx] += upper;
                }
            }
        }
    };
    let add = |lo: &mut [E], hi: &[E]| {
        for (l, h) in lo.iter_mut().zip(hi) {
            *l += *h;
        }
    };
    #[cfg(feature = "std")]
    {
        let per_job = (par_chunk(weights.len()) >> low).max(1) << low;
        std::thread::scope(|scope| {
            for part in weights.chunks_mut(per_job) {
                let within = &within;
                crate::spawn_bounded(scope, move || part.chunks_mut(1 << low).for_each(within));
            }
        });
        for b in low..bits {
            for chunk in weights.chunks_mut(2 << b) {
                let (lo, hi) = chunk.split_at_mut(1 << b);
                let step = par_chunk(lo.len());
                std::thread::scope(|scope| {
                    for (l, h) in lo.chunks_mut(step).zip(hi.chunks(step)) {
                        let add = &add;
                        crate::spawn_bounded(scope, move || add(l, h));
                    }
                });
            }
        }
    }
    #[cfg(not(feature = "std"))]
    {
        let _ = par_chunk;
        weights.chunks_mut(1 << low).for_each(within);
        for b in low..bits {
            for chunk in weights.chunks_mut(2 << b) {
                let (lo, hi) = chunk.split_at_mut(1 << b);
                add(lo, hi);
            }
        }
    }
    weights.resize(cells, E::ZERO);
    weights
}

fn batched_value(lambda: E, values: &[E]) -> E {
    values
        .iter()
        .rev()
        .fold(E::ZERO, |acc, &v| acc * lambda + v)
}

/// The layout and the schedule as bytes, for the transcript and the coins.
fn layout_bytes(shape: &Shape, layout: &Layout) -> Vec<u8> {
    let mut out = Vec::new();
    let mut put = |n: usize| out.extend_from_slice(&(n as u64).to_le_bytes());
    for n in [
        shape.log_rows,
        shape.num_vars,
        shape.num_public,
        layout.log_cells,
        layout.var_bits,
        layout.var_cells,
        layout.var_align,
        layout.mask_base,
        layout.blind_cells,
        layout.schedule.early_stop_vars,
        layout.schedule.stages.len(),
    ] {
        put(n);
    }
    for st in &layout.schedule.stages {
        put(st.blowup);
        put(st.step_vars);
        put(st.num_queries);
    }
    out
}

/// Round 0: the transcript bound to the magic, the profile, the relation, the layout with its
/// schedule, the statement and the public inputs, with the Stage-0 root absorbed.
fn start_transcript(
    profile: Profile,
    shape: &Shape,
    layout: &Layout,
    statement: &[u8],
    public_inputs: &[F],
    root: &Digest,
) -> Transcript {
    let public_bytes: Vec<u8> = public_inputs.iter().flat_map(|v| v.to_le_bytes()).collect();
    let mut tr = Transcript::new(
        profile,
        &[
            &MAGIC,
            &shape.digest(),
            &layout_bytes(shape, layout),
            statement,
            &public_bytes,
        ],
    );
    tr.absorb(b"STAGE0_ROOT", root);
    tr
}

fn squeeze_point(tr: &mut Transcript, label: &[u8], n: usize) -> Vec<E> {
    (0..n).map(|_| tr.squeeze_fp5(label)).collect()
}

// ============================================================================
// Prover
// ============================================================================

/// Replace every pair `(table[2i], table[2i + 1])` by `f` of it. `secret` erases the old
/// table.
fn fold_pairs(table: &mut Vec<E>, secret: bool, f: impl Fn(E, E) -> E + Sync) {
    let mut out = vec![E::ZERO; table.len() / 2];
    let src = &*table;
    par_chunks_mut(&mut out, |off, part| {
        for (i, slot) in part.iter_mut().enumerate() {
            *slot = f(src[2 * (off + i)], src[2 * (off + i) + 1]);
        }
    });
    if secret {
        qsag_asm::volatile_fill(table, E::ZERO);
    }
    *table = out;
}

/// Bind the lowest variable of a multilinear table to `r`.
fn fold_in_place(table: &mut Vec<E>, r: E, secret: bool) {
    fold_pairs(table, secret, |lo, hi| lo + r * (hi - lo));
}

/// [`fold_in_place`] for a table that is still over the base field.
fn fold_base(table: &[F], r: E) -> Vec<E> {
    let mut out = vec![E::ZERO; table.len() / 2];
    par_chunks_mut(&mut out, |off, part| {
        for (i, slot) in part.iter_mut().enumerate() {
            let (lo, hi) = (table[2 * (off + i)], table[2 * (off + i) + 1]);
            *slot = E::from_base(lo) + r.mul_base(hi - lo);
        }
    });
    out
}

/// Sum of `per_item` over `range`.
fn round_evals<const N: usize>(
    range: core::ops::Range<usize>,
    per_item: impl Fn(usize) -> [E; N] + Sync,
) -> [E; N] {
    let start = range.start;
    par_sum(range.len(), |sub| {
        let mut acc = [E::ZERO; N];
        for i in sub {
            for (a, p) in acc.iter_mut().zip(per_item(start + i)) {
                *a += p;
            }
        }
        acc
    })
}

/// The multilinear selector of rows `0..count`, folded lowest variable first without a
/// table: after `k` folds entry `j` is one below `count >> k`, zero above it and
/// `boundary` at it.
struct PrefixSelector {
    count: usize,
    boundary: E,
}

impl PrefixSelector {
    fn at(&self, j: usize) -> E {
        match j.cmp(&self.count) {
            core::cmp::Ordering::Less => E::ONE,
            core::cmp::Ordering::Equal => self.boundary,
            core::cmp::Ordering::Greater => E::ZERO,
        }
    }

    fn fold(&mut self, r: E) {
        self.boundary = if self.count & 1 == 1 {
            E::ONE + r * (self.boundary - E::ONE)
        } else {
            self.boundary - r * self.boundary
        };
        self.count >>= 1;
    }
}

/// Field in which one row round evaluates its gate: the base field before the first
/// challenge, the challenge field after it.
trait GateField:
    Copy + core::ops::Add<Output = Self> + core::ops::Sub<Output = Self> + Send + Sync
{
    fn times(self, rhs: Self) -> Self;
    /// `weight * self`.
    fn weigh(self, weight: E) -> E;
    fn lift(self) -> E;
}

impl GateField for F {
    #[inline(always)]
    fn times(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
    #[inline(always)]
    fn weigh(self, weight: E) -> E {
        weight.mul_base(self)
    }
    #[inline(always)]
    fn lift(self) -> E {
        E::from_base(self)
    }
}

impl GateField for E {
    #[inline(always)]
    fn times(self, rhs: Self) -> Self {
        self * rhs
    }
    #[inline(always)]
    fn weigh(self, weight: E) -> E {
        weight * self
    }
    #[inline(always)]
    fn lift(self) -> E {
        self
    }
}

/// `h(X) = sum_x eq_rest(x) gate(X, x)` for one row round, as `ROW_DEGREE` coefficients.
/// Rows below the selector boundary are S-box rows (degree 7 in `X`), rows above it are
/// multiplication rows (degree 2); only the pair holding the boundary needs the general gate.
fn row_round<T: GateField>(
    [ta, tb, tc]: [&[T]; 3],
    eq_rest: &[E],
    selector: &PrefixSelector,
) -> Vec<E> {
    let pairs = eq_rest.len();
    let mixed = (selector.count / 2).min(pairs);
    let line = |t: &[T], i: usize| (t[2 * i], t[2 * i + 1] - t[2 * i]);
    let mut sbox = round_evals::<{ ROW_DEGREE - 1 }>(0..mixed, |i| {
        let (mut a, da) = line(ta, i);
        let (mut c, dc) = line(tc, i);
        core::array::from_fn(|_| {
            let a2 = a.times(a);
            let v = (a2.times(a2).times(a2).times(a) - c).weigh(eq_rest[i]);
            a = a + da;
            c = c + dc;
            v
        })
    });
    let mut mul = round_evals::<3>((mixed + 1).min(pairs)..pairs, |i| {
        let (mut a, da) = line(ta, i);
        let (mut b, db) = line(tb, i);
        let (mut c, dc) = line(tc, i);
        core::array::from_fn(|_| {
            let v = (a.times(b) - c).weigh(eq_rest[i]);
            a = a + da;
            b = b + db;
            c = c + dc;
            v
        })
    });
    let mut coeffs = vec![E::ZERO; ROW_DEGREE];
    let mut add = |evals: &mut [E]| {
        let mut part = evals_to_coeffs(evals);
        for (c, &p) in coeffs.iter_mut().zip(&part) {
            *c += p;
        }
        qsag_asm::volatile_fill(&mut part, E::ZERO);
        qsag_asm::volatile_fill(evals, E::ZERO);
    };
    add(&mut sbox);
    add(&mut mul);
    if mixed < pairs {
        let lift = |t: &[T]| {
            let (lo, hi) = (t[2 * mixed].lift(), t[2 * mixed + 1].lift());
            (lo, hi - lo)
        };
        let (mut a, da) = lift(ta);
        let (mut b, db) = lift(tb);
        let (mut c, dc) = lift(tc);
        let mut s = selector.at(2 * mixed);
        let ds = selector.at(2 * mixed + 1) - s;
        let mut evals: [E; ROW_DEGREE] = core::array::from_fn(|_| {
            let v = eq_rest[mixed] * row_gate(s, a, b, c);
            a += da;
            b += db;
            c += dc;
            s += ds;
            v
        });
        add(&mut evals);
    }
    coeffs
}

/// Masked row sumcheck of `eq(tau, x) gate(x) + rho g1(x)` over the row tables. Returns the
/// round polynomials, the point and the three tables' values at it.
fn row_sumcheck(
    tr: &mut Transcript,
    tau: &[E],
    num_sbox: usize,
    mut base: [Vec<F>; 3],
    mask: &Mask,
    rho: E,
) -> (Vec<Vec<E>>, Vec<E>, [E; 3]) {
    let _phase = crate::profile::span("zkhem2_row_sumcheck");
    let n = tau.len();
    let mut ext: [Vec<E>; 3] = core::array::from_fn(|_| Vec::new());
    let mut selector = PrefixSelector {
        count: num_sbox,
        boundary: E::ZERO,
    };
    let mut eq_rest = eq_table(&tau[1..]);
    let mut eq_bound = E::ONE;
    let mut rounds = Vec::with_capacity(n);
    let mut rx: Vec<E> = Vec::with_capacity(n);
    for (round, &t) in tau.iter().enumerate() {
        let mut h = if round == 0 {
            row_round(base.each_ref().map(Vec::as_slice), &eq_rest, &selector)
        } else {
            row_round(ext.each_ref().map(Vec::as_slice), &eq_rest, &selector)
        };
        // Times `eq_bound * eq(t, X)`, plus the mask round.
        let l1 = eq_bound * (t + t - E::ONE);
        let l0 = eq_bound * (E::ONE - t);
        let mut coeffs = vec![E::ZERO; ROW_DEGREE + 1];
        for (k, &hk) in h.iter().enumerate() {
            coeffs[k] += l0 * hk;
            coeffs[k + 1] += l1 * hk;
        }
        qsag_asm::volatile_fill(&mut h, E::ZERO);
        let mut g = mask.round_poly(&rx);
        for (c, &g) in coeffs.iter_mut().zip(&g) {
            *c += rho * g;
        }
        qsag_asm::volatile_fill(&mut g, E::ZERO);
        tr.absorb_fp5_slice(b"ROW_ROUND", &coeffs);
        let c = tr.squeeze_fp5(b"ROW_ROUND");
        rounds.push(coeffs);
        rx.push(c);

        if round == 0 {
            for (e, b) in ext.iter_mut().zip(base.iter_mut()) {
                *e = fold_base(b, c);
                qsag_asm::volatile_fill(b, F::ZERO);
                *b = Vec::new();
            }
        } else {
            for e in ext.iter_mut() {
                fold_in_place(e, c, true);
            }
        }
        selector.fold(c);
        if round + 1 < n {
            let tc = t * c;
            eq_bound *= E::ONE - t - c + tc + tc;
            fold_pairs(&mut eq_rest, false, |lo, hi| lo + hi);
        }
    }
    let values = [ext[0][0], ext[1][0], ext[2][0]];
    for e in &mut ext {
        qsag_asm::volatile_fill(e, E::ZERO);
    }
    (rounds, rx, values)
}

/// Masked column sumcheck of `M(y) Z_var(y) + rho g2(y)`. Returns the round polynomials, the
/// point and `M` at it.
fn column_sumcheck(
    tr: &mut Transcript,
    mut tm: Vec<E>,
    z: &[F],
    mask: &Mask,
    rho: E,
) -> (Vec<Vec<E>>, Vec<E>, E) {
    let _phase = crate::profile::span("zkhem2_column_sumcheck");
    let n = tm.len().trailing_zeros() as usize;
    let mut tz: Vec<E> = Vec::new();
    let mut rounds = Vec::with_capacity(n);
    let mut ry: Vec<E> = Vec::with_capacity(n);
    for round in 0..n {
        let tm_ref = &tm;
        let mut evals: [E; COL_DEGREE + 1] = if round == 0 {
            round_evals(0..tm.len() / 2, |i| {
                let (m0, m1) = (tm_ref[2 * i], tm_ref[2 * i + 1]);
                let (z0, z1) = (z[2 * i], z[2 * i + 1]);
                [
                    m0.mul_base(z0),
                    m1.mul_base(z1),
                    (m1 + m1 - m0).mul_base(z1 + z1 - z0),
                ]
            })
        } else {
            let tz_ref = &tz;
            round_evals(0..tm.len() / 2, |i| {
                let (m0, m1) = (tm_ref[2 * i], tm_ref[2 * i + 1]);
                let (z0, z1) = (tz_ref[2 * i], tz_ref[2 * i + 1]);
                [m0 * z0, m1 * z1, (m1 + m1 - m0) * (z1 + z1 - z0)]
            })
        };
        let mut coeffs = evals_to_coeffs(&evals);
        qsag_asm::volatile_fill(&mut evals, E::ZERO);
        let mut g = mask.round_poly(&ry);
        for (c, &g) in coeffs.iter_mut().zip(&g) {
            *c += rho * g;
        }
        qsag_asm::volatile_fill(&mut g, E::ZERO);
        tr.absorb_fp5_slice(b"COL_ROUND", &coeffs);
        let c = tr.squeeze_fp5(b"COL_ROUND");
        rounds.push(coeffs);
        ry.push(c);
        if round == 0 {
            tz = fold_base(z, c);
        } else {
            fold_in_place(&mut tz, c, true);
        }
        fold_in_place(&mut tm, c, false);
    }
    qsag_asm::volatile_fill(&mut tz, E::ZERO);
    (rounds, ry, tm[0])
}

/// `(Az, Bz, Cz)` as row tables. With `check`, `None` unless every row is satisfied; the
/// scan does not stop at the first failing row.
fn row_tables(shape: &Shape, assignment: &[F], check: bool) -> Option<[Vec<F>; 3]> {
    let _phase = crate::profile::span("zkhem2_row_tables");
    let rows = shape.num_rows();
    let fill = |m: &crate::zk_hem::relation::Csr| {
        let mut t = vec![F::ZERO; rows];
        par_chunks_mut(&mut t, |off, part| {
            for (j, slot) in part.iter_mut().enumerate() {
                *slot = m.row_dot(off + j, assignment);
            }
        });
        t
    };
    let (ta, tb) = (fill(&shape.a), fill(&shape.b));
    let valid = core::sync::atomic::AtomicBool::new(true);
    let mut tc = vec![F::ZERO; rows];
    par_chunks_mut(&mut tc, |off, part| {
        let mut ok = true;
        for (j, slot) in part.iter_mut().enumerate() {
            let i = off + j;
            *slot = shape.c.row_dot(i, assignment);
            let expected = if i < shape.num_sbox {
                crate::sponge::poseidon2_sbox7(ta[i])
            } else {
                ta[i].const_mul(tb[i])
            };
            ok &= expected == *slot;
        }
        if !ok {
            valid.store(false, core::sync::atomic::Ordering::Relaxed);
        }
    });
    let mut tables = [ta, tb, tc];
    if check && !valid.load(core::sync::atomic::Ordering::Relaxed) {
        for t in &mut tables {
            qsag_asm::volatile_fill(t, F::ZERO);
        }
        return None;
    }
    Some(tables)
}

/// `sum_i eq_rx[i] (r_a A + r_b B + r_c C)[i, .]` on `cells` columns.
///
/// Rows of one kind allocate their variables in row order, so a run of rows mostly touches
/// one window of columns. Each worker owns such a window of the table and writes it
/// directly; what it has for other columns (the constant, the public inputs, old variables)
/// it sums per column and that is added afterwards. The result is the exact sparse
/// contraction whatever the windows are.
fn column_table(shape: &Shape, eq_rx: &[E], combine: &[E], cells: usize) -> Vec<E> {
    let _phase = crate::profile::span("zkhem2_column_table");
    let mut table = vec![E::ZERO; cells];
    let matrices = [&shape.a, &shape.b, &shape.c];
    // Rows `rows` into `window`, the table's columns from `home` on; other columns to `far`.
    let scatter = |rows: core::ops::Range<usize>,
                   home: usize,
                   window: &mut [E],
                   far: &mut BTreeMap<usize, E>| {
        for i in rows {
            for (matrix, &r) in matrices.into_iter().zip(combine) {
                let mut entries = matrix.row(i).peekable();
                if entries.peek().is_none() {
                    continue;
                }
                let weight = r * eq_rx[i];
                for (col, val) in entries {
                    let term = weight.mul_base(val);
                    match col.checked_sub(home).and_then(|c| window.get_mut(c)) {
                        Some(slot) => *slot += term,
                        None => *far.entry(col).or_insert(E::ZERO) += term,
                    }
                }
            }
        }
    };
    #[cfg(feature = "std")]
    if eq_rx.len() > par_chunk(eq_rx.len()) {
        // The newest variable among the first rows of a run marks where its window starts.
        let newest = |rows: core::ops::Range<usize>| {
            rows.take(64)
                .flat_map(|i| matrices.into_iter().flat_map(move |m| m.row(i)))
                .map(|(col, _)| col)
                .max()
        };
        for block in [0..shape.num_sbox, shape.num_sbox..eq_rx.len()] {
            let chunk = par_chunk(block.len());
            let runs: Vec<_> = block
                .clone()
                .step_by(chunk)
                .map(|start| start..(start + chunk).min(block.end))
                .collect();
            // Run `k` owns the columns `homes[k]..homes[k + 1]`: nondecreasing bounds that
            // cover the table.
            let mut homes = vec![0; runs.len() + 1];
            for (k, run) in runs.iter().enumerate().skip(1) {
                homes[k] = newest(run.clone()).unwrap_or(0).clamp(homes[k - 1], cells);
            }
            homes[runs.len()] = cells;
            let deferred = std::thread::scope(|scope| {
                let mut rest = table.as_mut_slice();
                let workers: Vec<_> = runs
                    .iter()
                    .zip(homes.windows(2))
                    .map(|(run, home)| {
                        let (window, tail) =
                            core::mem::take(&mut rest).split_at_mut(home[1] - home[0]);
                        rest = tail;
                        let (scatter, run, home) = (&scatter, run.clone(), home[0]);
                        crate::spawn_bounded(scope, move || {
                            let mut far = BTreeMap::new();
                            scatter(run, home, window, &mut far);
                            far
                        })
                    })
                    .collect();
                workers
                    .into_iter()
                    .map(crate::join_worker)
                    .collect::<Vec<_>>()
            });
            for (col, term) in deferred.into_iter().flatten() {
                table[col] += term;
            }
        }
        return table;
    }
    let mut far = BTreeMap::new();
    scatter(0..eq_rx.len(), 0, &mut table, &mut far);
    debug_assert!(far.is_empty());
    table
}

/// Prove that `assignment` satisfies `shape`, bound to `statement`.
///
/// `shape` and `assignment` come from `ConstraintSystem::finish_v2`; the masking variables of
/// the assignment are overwritten here. `seed` must be uniform and secret: it determines the
/// masks, the blinders, the mask polynomial and the leaf salts. What the proof guarantees is
/// SECURITY.md section V2; the numbers are [`super::bounds::report`].
pub fn prove(
    shape: &Shape,
    assignment: Vec<F>,
    statement: &[u8],
    profile: Profile,
    seed: &[u8; 32],
) -> Result<ZkHemV2Proof, ZkHemV2Error> {
    prove_inner(shape, assignment, statement, profile, seed, true, None)
}

/// `claimed` replaces the public inputs bound into the transcript and `check` can be turned
/// off (tests only: a prover whose committed cells differ from what it claims).
fn prove_inner(
    shape: &Shape,
    mut assignment: Vec<F>,
    statement: &[u8],
    profile: Profile,
    seed: &[u8; 32],
    check: bool,
    claimed: Option<&[F]>,
) -> Result<ZkHemV2Proof, ZkHemV2Error> {
    let Some(layout) = layout_of(shape) else {
        qsag_asm::volatile_fill(&mut assignment, F::ZERO);
        return Err(ZkHemV2Error::UnsupportedRelation);
    };
    if assignment.len() != shape.num_vars {
        qsag_asm::volatile_fill(&mut assignment, F::ZERO);
        return Err(ZkHemV2Error::Unsatisfied);
    }
    let phase = crate::profile::span("zkhem2_coins");
    let mut coins = Coins::new(profile, shape, &layout, statement, &assignment, seed);
    let mut secrets = sample_secrets(&mut coins, shape, &layout, &mut assignment);
    drop(coins);
    drop(phase);
    let row_base = if check && assignment[0] != F::ONE {
        None
    } else {
        row_tables(shape, &assignment, check)
    };
    let public_inputs =
        claimed.map_or_else(|| assignment[1..=shape.num_public].to_vec(), <[F]>::to_vec);
    qsag_asm::volatile_fill(&mut assignment, F::ZERO);
    let Some(row_base) = row_base else {
        return Err(ZkHemV2Error::Unsatisfied);
    };

    // The variable cells the column sumcheck runs over, zero above `var_cells`.
    let phase = crate::profile::span("zkhem2_monomial");
    let var_cube = 1usize << layout.var_bits;
    let mut z_var = vec![F::ZERO; var_cube];
    let live = layout.var_cells.min(var_cube);
    z_var[..live].copy_from_slice(&secrets.table[..live]);

    let coeffs = hypercube_to_monomial_coeffs(&secrets.table);
    qsag_asm::volatile_fill(&mut secrets.table, F::ZERO);
    secrets.table = Vec::new();
    drop(phase);
    let committed = pcs::commit(
        profile,
        layout.log_cells,
        &layout.schedule,
        coeffs,
        core::mem::take(&mut secrets.mask_poly),
        &secrets.salt_seed,
    );
    let root = committed.root();
    let mut tr = start_transcript(profile, shape, &layout, statement, &public_inputs, &root);

    // Rounds 1 and 2: masked row sumcheck.
    let tau = squeeze_point(&mut tr, b"TAU", shape.log_rows);
    let row_mask_sum = secrets.row_mask.sum();
    tr.absorb_fp5_slice(b"ROW_MASK_SUM", &[row_mask_sum]);
    let rho1 = tr.squeeze_fp5_nonzero(b"RHO1");
    let (row_rounds, rx, mut row_values) = row_sumcheck(
        &mut tr,
        &tau,
        shape.num_sbox,
        row_base,
        &secrets.row_mask,
        rho1,
    );
    // (G1), before the row values exist outside the prover.
    if !row_challenge_good(shape, &rx) {
        qsag_asm::volatile_fill(&mut row_values, E::ZERO);
        qsag_asm::volatile_fill(&mut z_var, F::ZERO);
        return Err(ZkHemV2Error::MaskRankDeficient);
    }

    // Round 3: row values. Rounds 4 and 5: masked column sumcheck of `M(rx, y) Z_var(y)`.
    tr.absorb_fp5_slice(b"ROW_VALUES", &row_values);
    let combine = squeeze_point(&mut tr, b"COMBINE", 3);
    let col_mask_sum = secrets.col_mask.sum();
    tr.absorb_fp5_slice(b"COL_MASK_SUM", &[col_mask_sum]);
    let rho2 = tr.squeeze_fp5_nonzero(b"RHO2");
    let tm = column_table(shape, &eq_table(&rx), &combine, var_cube);
    let (col_rounds, ry, matrix_at_point) =
        column_sumcheck(&mut tr, tm, &z_var, &secrets.col_mask, rho2);
    qsag_asm::volatile_fill(&mut z_var, F::ZERO);

    // Round 6: one linear functional for everything that remains.
    let lambda = tr.squeeze_fp5(b"LAMBDA");
    let phase = crate::profile::span("zkhem2_kernel");
    let weights = claim_cell_weights(&ClaimInputs {
        layout: &layout,
        log_rows: shape.log_rows,
        num_public: shape.num_public,
        rx: &rx,
        ry: &ry,
        lambda,
        rho2,
        matrix_at_point,
    });
    let kernel = cell_weights_to_kernel(weights, 1 << layout.log_cells);
    let table_coeffs = committed.coeffs();
    let [value] = par_sum(kernel.len(), |range| {
        [range.fold(E::ZERO, |acc, i| acc + kernel[i].mul_base(table_coeffs[i]))]
    });
    drop(phase);

    // Rounds 7 on.
    let opening = pcs::open(&committed, kernel, value, &mut tr)
        .map_err(|pcs::MaskRankDeficient| ZkHemV2Error::MaskRankDeficient)?;
    Ok(ZkHemV2Proof {
        profile,
        log_cells: layout.log_cells as u8,
        root,
        row_mask_sum,
        row_rounds,
        row_values,
        col_mask_sum,
        col_rounds,
        opening,
    })
}

// ============================================================================
// Verifier
// ============================================================================

/// Replays one masked sumcheck; returns the final claim and the challenge point.
fn verify_sumcheck(
    tr: &mut Transcript,
    label: &[u8],
    rounds: &[Vec<E>],
    degree: usize,
    mut claim: E,
) -> Option<(E, Vec<E>)> {
    let mut point = Vec::with_capacity(rounds.len());
    for round in rounds {
        if round.len() != degree + 1 {
            return None;
        }
        let at_one = round.iter().fold(E::ZERO, |acc, &c| acc + c);
        if round[0] + at_one != claim {
            return None;
        }
        tr.absorb_fp5_slice(label, round);
        let c = tr.squeeze_fp5(label);
        claim = eval_poly(round, c);
        point.push(c);
    }
    Some((claim, point))
}

/// `sum_i eq(rx, i) (r_a A + r_b B + r_c C)[i, .]` evaluated at `ry` on the variable cells.
fn matrix_at(shape: &Shape, rx: &[E], ry: &[E], combine: &[E]) -> E {
    let eq_rx = eq_table(rx);
    let eq_ry = eq_table(ry);
    let cols = &eq_ry[..shape.num_vars];
    let [total] = par_sum(eq_rx.len(), |range| {
        let mut acc = E::ZERO;
        for i in range {
            let mut row = E::ZERO;
            for (m, &r) in [&shape.a, &shape.b, &shape.c].into_iter().zip(combine) {
                let inner = m
                    .row(i)
                    .fold(E::ZERO, |acc, (col, val)| acc + cols[col].mul_base(val));
                row += r * inner;
            }
            acc += eq_rx[i] * row;
        }
        [acc]
    });
    total
}

/// Verify a zk-Hem v2 proof for `shape` with the given public inputs, bound to `statement`,
/// under `profile`.
pub fn verify(
    shape: &Shape,
    public_inputs: &[F],
    statement: &[u8],
    profile: Profile,
    proof: &ZkHemV2Proof,
) -> bool {
    let Some(layout) = layout_of(shape) else {
        return false;
    };
    if proof.profile != profile
        || usize::from(proof.log_cells) != layout.log_cells
        || proof.row_rounds.len() != shape.log_rows
        || proof.col_rounds.len() != layout.var_bits
        || public_inputs.len() != shape.num_public
    {
        return false;
    }
    let mut tr = start_transcript(
        profile,
        shape,
        &layout,
        statement,
        public_inputs,
        &proof.root,
    );

    let tau = squeeze_point(&mut tr, b"TAU", shape.log_rows);
    tr.absorb_fp5_slice(b"ROW_MASK_SUM", &[proof.row_mask_sum]);
    let rho1 = tr.squeeze_fp5_nonzero(b"RHO1");
    let Some((row_final, rx)) = verify_sumcheck(
        &mut tr,
        b"ROW_ROUND",
        &proof.row_rounds,
        ROW_DEGREE,
        rho1 * proof.row_mask_sum,
    ) else {
        return false;
    };
    let [va, vb, vc] = proof.row_values;
    tr.absorb_fp5_slice(b"ROW_VALUES", &proof.row_values);
    let gate = eq_eval(&tau, &rx) * row_gate(prefix_indicator(&rx, shape.num_sbox), va, vb, vc);
    // The value the committed row mask must take at `rx`.
    let row_mask_at_point = (row_final - gate) * rho1.inv();

    let combine = squeeze_point(&mut tr, b"COMBINE", 3);
    tr.absorb_fp5_slice(b"COL_MASK_SUM", &[proof.col_mask_sum]);
    let rho2 = tr.squeeze_fp5_nonzero(b"RHO2");
    let col_claim = combine[0] * va + combine[1] * vb + combine[2] * vc;
    let Some((col_final, ry)) = verify_sumcheck(
        &mut tr,
        b"COL_ROUND",
        &proof.col_rounds,
        COL_DEGREE,
        col_claim + rho2 * proof.col_mask_sum,
    ) else {
        return false;
    };

    let lambda = tr.squeeze_fp5(b"LAMBDA");
    let phase = crate::profile::span("zkhem2_verify_matrix");
    let matrix_at_point = matrix_at(shape, &rx, &ry, &combine);
    drop(phase);
    let terms = claim_terms(&ClaimInputs {
        layout: &layout,
        log_rows: shape.log_rows,
        num_public: shape.num_public,
        rx: &rx,
        ry: &ry,
        lambda,
        rho2,
        matrix_at_point,
    });
    let mut values = vec![
        proof.row_mask_sum,
        proof.col_mask_sum,
        row_mask_at_point,
        col_final,
        E::ONE,
    ];
    values.extend(public_inputs.iter().map(|&v| E::from_base(v)));
    let value = batched_value(lambda, &values);
    let _phase = crate::profile::span("zkhem2_verify_opening");
    pcs::verify(
        profile,
        &proof.root,
        layout.log_cells,
        &layout.schedule,
        &terms,
        value,
        &proof.opening,
        &mut tr,
    )
}

const _: () = assert!(PAD_VARS == LIMBS);
const _: () = assert!(ROW_DEGREE < 1 << ROW_MASK_BITS && COL_DEGREE < 1 << COL_MASK_BITS);

#[cfg(test)]
mod tests {
    use super::super::bounds;
    use super::super::params::{MAX_LOG_CELLS, MIN_LOG_CELLS, schedule};
    use super::*;
    use crate::pcs::WhirSecurityRegime;
    use crate::zk_hem::protocol as v1;
    use crate::zk_hem::relation::{ConstraintSystem, Lc};

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    struct Rng(u64);

    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }
        fn fp5(&mut self) -> E {
            Fp5(core::array::from_fn(|_| f(self.next_u64())))
        }
    }

    /// `y = x^7 * w`, `w` boolean-free witness, plus a few rows of each kind; `x`, `y`
    /// public. `extra` adds witness-only rows and variables.
    fn relation(x: u64, w: u64, constant: u64, extra: usize) -> ConstraintSystem {
        let mut cs = ConstraintSystem::new();
        let xv = cs.public_input(f(x));
        let x7 = f(x).pow(7);
        let yv = cs.public_input(x7 * f(w) + f(constant));
        let wv = cs.alloc(f(w));
        let s = cs.sbox7(&xv.into());
        let prod = cs.mul(&s.into(), &wv.into());
        cs.enforce_equal(&Lc::from(prod).plus_const(f(constant)), &yv.into());
        let mut acc: Lc = wv.into();
        for i in 0..extra {
            let t = cs.sbox7(&acc);
            let u = cs.mul(&t.into(), &acc);
            acc = Lc::from(u).plus_const(f(i as u64 + 1));
        }
        cs
    }

    fn fixture(extra: usize) -> (Shape, Vec<F>) {
        relation(3, 5, 11, extra).finish_v2()
    }

    const SEED: [u8; 32] = [7u8; 32];
    const STATEMENT: &[u8] = b"v2 statement";

    fn publics(shape: &Shape, z: &[F]) -> Vec<F> {
        z[1..=shape.num_public].to_vec()
    }

    #[test]
    fn honest_roundtrip_both_profiles_and_serialization() {
        let (shape, z) = fixture(40);
        assert!(shape.is_satisfied(&z));
        let layout = layout_of(&shape).unwrap();
        for profile in Profile::ALL {
            let proof = prove(&shape, z.clone(), STATEMENT, profile, &SEED).unwrap();
            assert!(verify(
                &shape,
                &publics(&shape, &z),
                STATEMENT,
                profile,
                &proof
            ));
            let bytes = proof.to_bytes();
            assert_eq!(&bytes[..8], b"QSAGZKH2");
            assert_eq!(bytes[8], profile.wire_tag());
            assert_eq!(
                ZkHemV2Proof::from_bytes(&bytes, &shape),
                Some(proof.clone())
            );
            // The calculator's bound covers the serialized proof.
            let report = bounds::report(
                profile,
                ShapeSize {
                    log_rows: shape.log_rows,
                    num_vars: shape.num_vars,
                    num_public: shape.num_public,
                },
            )
            .unwrap();
            assert_eq!(report.log_cells, layout.log_cells);
            assert!(
                bytes.len() <= report.proof_bytes,
                "{} bytes, bound {}",
                bytes.len(),
                report.proof_bytes
            );
            // Canonical decoding.
            assert!(ZkHemV2Proof::from_bytes(&bytes[..bytes.len() - 1], &shape).is_none());
            let mut longer = bytes.clone();
            longer.push(0);
            assert!(ZkHemV2Proof::from_bytes(&longer, &shape).is_none());
            for (at, value) in [(0usize, b'X'), (8, 4), (8, 18), (9, 17)] {
                let mut bad = bytes.clone();
                bad[at] = value;
                assert!(
                    ZkHemV2Proof::from_bytes(&bad, &shape).is_none(),
                    "byte {at}"
                );
            }
            let mut bad = bytes.clone();
            bad[60..68].copy_from_slice(&crate::field::GOLDILOCKS_PRIME.to_le_bytes());
            assert!(ZkHemV2Proof::from_bytes(&bad, &shape).is_none());
        }
        // A wrong witness is refused, and a proof made without the check does not verify.
        let mut bad = z.clone();
        bad[3] += F::ONE;
        assert_eq!(
            prove(
                &shape,
                bad.clone(),
                STATEMENT,
                Profile::CshakeJohnson400,
                &SEED
            ),
            Err(ZkHemV2Error::Unsatisfied)
        );
        let forged = prove_inner(
            &shape,
            bad,
            STATEMENT,
            Profile::CshakeJohnson400,
            &SEED,
            false,
            None,
        )
        .unwrap();
        assert!(!verify(
            &shape,
            &publics(&shape, &z),
            STATEMENT,
            Profile::CshakeJohnson400,
            &forged
        ));
    }

    #[test]
    fn every_proof_field_is_bound() {
        let (shape, z) = fixture(40);
        let profile = Profile::TurboShakeJohnson400;
        let proof = prove(&shape, z.clone(), STATEMENT, profile, &SEED).unwrap();
        let public = publics(&shape, &z);
        assert!(verify(&shape, &public, STATEMENT, profile, &proof));
        let bump = Fp5::X.pow(2);
        let last_stage = proof.opening.stages.len() - 1;
        type Edit = alloc::boxed::Box<dyn Fn(&mut ZkHemV2Proof)>;
        let edits: Vec<(&str, Edit)> = vec![
            ("root", alloc::boxed::Box::new(|p| p.root[10] ^= 1)),
            (
                "row mask sum",
                alloc::boxed::Box::new(move |p| p.row_mask_sum += bump),
            ),
            (
                "row round 0",
                alloc::boxed::Box::new(move |p| p.row_rounds[0][9] += bump),
            ),
            (
                "row round last",
                alloc::boxed::Box::new(move |p| {
                    let n = p.row_rounds.len();
                    p.row_rounds[n - 1][0] += bump
                }),
            ),
            (
                "row value a",
                alloc::boxed::Box::new(move |p| p.row_values[0] += bump),
            ),
            (
                "row value b",
                alloc::boxed::Box::new(move |p| p.row_values[1] += bump),
            ),
            (
                "row value c",
                alloc::boxed::Box::new(move |p| p.row_values[2] += bump),
            ),
            (
                "col mask sum",
                alloc::boxed::Box::new(move |p| p.col_mask_sum += bump),
            ),
            (
                "col round",
                alloc::boxed::Box::new(move |p| p.col_rounds[1][2] += bump),
            ),
            (
                "a_0",
                alloc::boxed::Box::new(move |p| p.opening.mask_evals[0] += bump),
            ),
            (
                "a_4",
                alloc::boxed::Box::new(move |p| p.opening.mask_evals[4] += bump),
            ),
            (
                "sigma_even",
                alloc::boxed::Box::new(move |p| p.opening.stage0_folds[0][0] += bump),
            ),
            (
                "tau_01",
                alloc::boxed::Box::new(move |p| p.opening.stage0_folds[0][1] += bump),
            ),
            (
                "tau_10",
                alloc::boxed::Box::new(move |p| p.opening.stage0_folds[0][2] += bump),
            ),
            (
                "c_F",
                alloc::boxed::Box::new(move |p| p.opening.stage0_folds[0][3] += bump),
            ),
            (
                "c_G",
                alloc::boxed::Box::new(move |p| p.opening.stage0_folds[0][4] += bump),
            ),
            (
                "mu",
                alloc::boxed::Box::new(move |p| p.opening.mask_claim += bump),
            ),
            (
                "stage-1 root",
                alloc::boxed::Box::new(|p| p.opening.stages[0].root[0] ^= 1),
            ),
            (
                "ood value",
                alloc::boxed::Box::new(move |p| p.opening.stages[0].ood[0] += bump),
            ),
            (
                "Z symbol",
                alloc::boxed::Box::new(|p| p.opening.stage0_query.leaves[5].z[1] += F::ONE),
            ),
            (
                "R symbol",
                alloc::boxed::Box::new(move |p| p.opening.stage0_query.leaves[5].r += bump),
            ),
            (
                "salt",
                alloc::boxed::Box::new(|p| p.opening.stage0_query.leaves[0].salt[0] ^= 1),
            ),
            (
                "sibling",
                alloc::boxed::Box::new(|p| p.opening.stage0_query.siblings[3][1] ^= 1),
            ),
            (
                "later symbol",
                alloc::boxed::Box::new(move |p| {
                    p.opening.stages[last_stage].query.leaves[0][0] += bump
                }),
            ),
            (
                "terminal coefficient",
                alloc::boxed::Box::new(move |p| p.opening.final_coeffs[1] += bump),
            ),
        ];
        for (name, edit) in &edits {
            let mut bad = proof.clone();
            edit(&mut bad);
            assert_ne!(bad, proof, "{name}: the edit changed nothing");
            assert!(
                !verify(&shape, &public, STATEMENT, profile, &bad),
                "accepted a proof with a changed {name}"
            );
        }
        // One flipped bit anywhere in a sample of byte positions of the serialized proof.
        let bytes = proof.to_bytes();
        for at in (10..bytes.len()).step_by(bytes.len() / 97) {
            let mut bad = bytes.clone();
            bad[at] ^= 0x10;
            let accepted = ZkHemV2Proof::from_bytes(&bad, &shape)
                .is_some_and(|p| verify(&shape, &public, STATEMENT, profile, &p));
            assert!(!accepted, "byte {at}");
        }
    }

    #[test]
    fn statement_relation_public_input_and_profile_are_bound() {
        let (shape, z) = fixture(40);
        let profile = Profile::CshakeJohnson400;
        let proof = prove(&shape, z.clone(), STATEMENT, profile, &SEED).unwrap();
        let public = publics(&shape, &z);
        assert!(verify(&shape, &public, STATEMENT, profile, &proof));
        assert!(!verify(&shape, &public, b"v2 statemenu", profile, &proof));
        assert!(!verify(
            &shape,
            &public,
            STATEMENT,
            Profile::TurboShakeJohnson400,
            &proof
        ));
        let mut retagged = proof.clone();
        retagged.profile = Profile::TurboShakeJohnson400;
        assert!(!verify(
            &shape,
            &public,
            STATEMENT,
            Profile::TurboShakeJohnson400,
            &retagged
        ));
        for i in 0..public.len() {
            let mut other = public.clone();
            other[i] += F::ONE;
            assert!(!verify(&shape, &other, STATEMENT, profile, &proof));
        }
        assert!(!verify(&shape, &public[..1], STATEMENT, profile, &proof));
        // The same sizes, another constant in one row.
        let (other, _) = relation(3, 5, 12, 40).finish_v2();
        assert_eq!(
            (other.log_rows, other.num_vars, other.num_public),
            (shape.log_rows, shape.num_vars, shape.num_public)
        );
        assert_ne!(other.digest(), shape.digest());
        assert!(!verify(&other, &public, STATEMENT, profile, &proof));
        // A prover that commits to one public value and claims another.
        let mut claimed = public.clone();
        claimed[1] += F::ONE;
        let lying = prove_inner(
            &shape,
            z.clone(),
            STATEMENT,
            profile,
            &SEED,
            true,
            Some(&claimed),
        )
        .unwrap();
        assert!(!verify(&shape, &claimed, STATEMENT, profile, &lying));
        assert!(!verify(&shape, &public, STATEMENT, profile, &lying));
    }

    #[test]
    fn coins_do_not_repeat_across_profiles() {
        let (shape, z) = fixture(40);
        let a = prove(
            &shape,
            z.clone(),
            STATEMENT,
            Profile::CshakeJohnson400,
            &SEED,
        )
        .unwrap();
        let b = prove(
            &shape,
            z.clone(),
            STATEMENT,
            Profile::TurboShakeJohnson400,
            &SEED,
        )
        .unwrap();
        assert_ne!(a.row_mask_sum, b.row_mask_sum);
        assert_ne!(a.col_mask_sum, b.col_mask_sum);
        assert_ne!(a.root, b.root);
        // Deterministic for a fixed seed; a new seed, statement or witness changes the coins.
        let again = prove(
            &shape,
            z.clone(),
            STATEMENT,
            Profile::CshakeJohnson400,
            &SEED,
        )
        .unwrap();
        assert_eq!(a, again);
        let c = prove(
            &shape,
            z.clone(),
            STATEMENT,
            Profile::CshakeJohnson400,
            &[8u8; 32],
        )
        .unwrap();
        assert_ne!(a.row_mask_sum, c.row_mask_sum);
        let d = prove(
            &shape,
            z.clone(),
            b"other",
            Profile::CshakeJohnson400,
            &SEED,
        )
        .unwrap();
        assert_ne!(a.row_mask_sum, d.row_mask_sum);
        let (shape_w, z_w) = relation(3, 6, 11, 40).finish_v2();
        let (shape_w0, _) = relation(3, 5, 11, 40).finish_v2();
        assert_eq!(shape_w0.digest(), shape.digest());
        let e = prove(&shape_w, z_w, STATEMENT, Profile::CshakeJohnson400, &SEED).unwrap();
        assert_ne!(a.row_mask_sum, e.row_mask_sum);
        // Two layouts.
        let (big, z_big) = fixture(300);
        assert_ne!(layout_of(&big).unwrap(), layout_of(&shape).unwrap());
        let g = prove(&big, z_big, STATEMENT, Profile::CshakeJohnson400, &SEED).unwrap();
        assert_ne!(a.row_mask_sum, g.row_mask_sum);
        assert_ne!(a.root, g.root);
        // v1 with the same seed, statement and synthesis.
        let (shape1, z1) = relation(3, 5, 11, 40).finish();
        let regime = WhirSecurityRegime::BciksJohnsonQrom128;
        let p1 = v1::prove(&shape1, z1, STATEMENT, regime, &SEED).unwrap();
        assert_ne!(
            p1.row_mask_sum.to_limbs()[..],
            a.row_mask_sum.to_limbs()[..4]
        );
        assert_ne!(p1.commitment.root[..], a.root[..32]);
    }

    #[test]
    fn blinders_match_the_opened_view_and_are_fresh_per_seed() {
        // b = opened symbols + 25 * 2^s at every accepted size.
        for log_cells in MIN_LOG_CELLS..=MAX_LOG_CELLS {
            let sched = schedule(log_cells).unwrap();
            let dims = pcs::stage_dims(log_cells, &sched).unwrap();
            let d0 = dims[0];
            let layout = Layout::new(ShapeSize {
                log_rows: log_cells - 1,
                num_vars: 1 << (log_cells - 2),
                num_public: 1,
            })
            .unwrap();
            if layout.log_cells == log_cells {
                assert_eq!(
                    layout.blind_cells,
                    d0.queries * d0.arity() + 25 * d0.arity(),
                    "2^{log_cells} cells"
                );
                assert_eq!(layout.blind_cells % d0.arity(), 0);
                assert_eq!(((1usize << log_cells) - layout.blind_cells) % d0.arity(), 0);
            }
        }
        let (shape, z) = fixture(40);
        let layout = layout_of(&shape).unwrap();
        let d0 = pcs::stage_dims(layout.log_cells, &layout.schedule).unwrap()[0];
        assert_eq!(layout.blind_cells, (d0.queries + 25) * d0.arity());
        let draw = |seed: &[u8; 32]| {
            let mut a = z.clone();
            let mut coins = Coins::new(
                Profile::CshakeJohnson400,
                &shape,
                &layout,
                STATEMENT,
                &a,
                seed,
            );
            let s = sample_secrets(&mut coins, &shape, &layout, &mut a);
            let cells = s.table.len();
            (
                s.table[cells - layout.blind_cells..].to_vec(),
                s.mask_poly.clone(),
                s.salt_seed,
                a[shape.mask_var_base..].to_vec(),
                s.table[layout.mask_base..cells - layout.blind_cells].to_vec(),
            )
        };
        let (b1, r1, s1, m1, masks1) = draw(&SEED);
        let (b2, r2, s2, m2, masks2) = draw(&[9u8; 32]);
        assert_eq!(draw(&SEED).0, b1);
        assert_eq!(b1.len(), layout.blind_cells);
        assert_eq!(r1.len(), (1 << (layout.log_cells - d0.step_vars)) + 2);
        assert_eq!(m1.len(), 15);
        // No coordinate repeats between the two seeds.
        assert!(b1.iter().zip(&b2).all(|(x, y)| x != y));
        assert!(r1.iter().zip(&r2).all(|(x, y)| x != y));
        assert!(m1.iter().zip(&m2).all(|(x, y)| x != y));
        assert_ne!(s1, s2);
        assert_ne!(masks1, masks2);
        // The blinders are not constant and the cells between the masks and the blinders are
        // zero.
        assert!(b1.windows(2).all(|w| w[0] != w[1]));
        let mask_end = layout.col_mask_block(shape.log_rows, layout.var_bits, 0) - layout.mask_base;
        assert!(masks1[mask_end..].iter().all(|v| v.is_zero()));
        assert!(masks1[..mask_end].iter().filter(|v| v.is_zero()).count() < 8);
    }

    #[test]
    fn pad_basis_exists() {
        // The witness of SECURITY.md V2.1: (X, X^2, X^4).
        let x = Fp5::X;
        let det = pad_basis_det(&[x, x.pow(2), x.pow(4)]);
        assert!(det == f(16) || det == -f(16), "{det:?}");
        let mut rng = Rng(3);
        for _ in 0..50 {
            let rx: Vec<E> = (0..5).map(|_| rng.fp5()).collect();
            assert!(super::pad_basis_exists(&rx));
        }
        // Degenerate challenges: base-field coordinates, or a repeated weight.
        let base: Vec<E> = (0..5).map(|i| E::from_u64(i + 2)).collect();
        assert!(!super::pad_basis_exists(&base));
        let mut rx: Vec<E> = (0..5).map(|_| rng.fp5()).collect();
        rx[0] = E::ZERO;
        assert!(!super::pad_basis_exists(&rx));
        rx[0] = rng.fp5();
        rx[2] = E::ONE;
        assert!(!super::pad_basis_exists(&rx));
    }

    #[test]
    fn row_challenge_good_rejects_zero_corner_factors() {
        let (shape, _) = fixture(40);
        assert_eq!(shape.mask_row_base(2) + 8, shape.num_rows());
        let mut rng = Rng(4);
        let rx: Vec<E> = (0..shape.log_rows).map(|_| rng.fp5()).collect();
        assert!(row_challenge_good(&shape, &rx));
        // The corners sit at the top of the row cube: every high coordinate is 1 there, except
        // the two bits that number the corners.
        for j in 3..shape.log_rows {
            let mut bad = rx.clone();
            bad[j] = E::ZERO;
            assert!(!row_challenge_good(&shape, &bad), "coordinate {j}");
        }
        let mut bad = rx.clone();
        bad[3] = E::ONE;
        assert!(!row_challenge_good(&shape, &bad));
        let mut bad = rx.clone();
        bad[1] = bad[0];
        bad[2] = bad[0];
        assert_eq!(
            super::pad_basis_exists(&bad),
            row_challenge_good(&shape, &bad)
        );
    }

    #[test]
    fn cell_weights_and_tensor_terms_are_the_same_functional() {
        let (shape, _) = fixture(300);
        let layout = layout_of(&shape).unwrap();
        let mut rng = Rng(5);
        let rx: Vec<E> = (0..shape.log_rows).map(|_| rng.fp5()).collect();
        let ry: Vec<E> = (0..layout.var_bits).map(|_| rng.fp5()).collect();
        let inp = ClaimInputs {
            layout: &layout,
            log_rows: shape.log_rows,
            num_public: shape.num_public,
            rx: &rx,
            ry: &ry,
            lambda: rng.fp5(),
            rho2: rng.fp5(),
            matrix_at_point: rng.fp5(),
        };
        let weights = claim_cell_weights(&inp);
        let terms = claim_terms(&inp);
        assert!(terms.len() <= 15 * (shape.log_rows + layout.var_bits) + 16);
        // A random table over the cells the functional may read.
        let cells = 1usize << layout.log_cells;
        let table: Vec<F> = (0..cells).map(|_| f(rng.next_u64())).collect();
        let by_cells = weights
            .iter()
            .zip(&table)
            .fold(E::ZERO, |acc, (&w, &z)| acc + w.mul_base(z));
        // Each tensor term is a multilinear evaluation of the table.
        let eval = |point: &[E]| {
            let eq = eq_table(point);
            eq.iter()
                .zip(&table)
                .fold(E::ZERO, |acc, (&e, &z)| acc + e.mul_base(z))
        };
        let by_terms = terms
            .iter()
            .fold(E::ZERO, |acc, t| acc + t.weight * eval(&t.point));
        assert_eq!(by_cells, by_terms);
        // The kernel on monomial coefficients gives the same value and reads no blinder.
        let kernel = cell_weights_to_kernel(weights.clone(), cells);
        let coeffs = hypercube_to_monomial_coeffs(&table);
        let by_kernel = kernel
            .iter()
            .zip(&coeffs)
            .fold(E::ZERO, |acc, (&k, &c)| acc + k.mul_base(c));
        assert_eq!(by_kernel, by_cells);
        let mask_end = layout.col_mask_block(shape.log_rows, layout.var_bits, 0);
        assert!(kernel[mask_end..].iter().all(|k| k.is_zero()));
        assert!(mask_end <= cells - layout.blind_cells);
        // It reads the variables below `var_cells` and the masks: a cell between the
        // variables and `var_cells` has weight from the terminal term only when inside the cube.
        assert!(!weights[0].is_zero() && !weights[layout.mask_base].is_zero());
        // Changing one mask cell or one variable cell changes the value.
        for cell in [
            1usize,
            shape.num_vars - 1,
            layout.mask_base + 3,
            mask_end - 1,
        ] {
            assert!(!weights[cell].is_zero(), "cell {cell}");
        }
    }

    #[test]
    fn sumcheck_mask_sums_and_rounds_are_consistent() {
        let (shape, z) = fixture(40);
        let layout = layout_of(&shape).unwrap();
        let mut coins = Coins::new(
            Profile::CshakeJohnson400,
            &shape,
            &layout,
            STATEMENT,
            &z,
            &SEED,
        );
        let mask = Mask::sample(&mut coins, 4, 3);
        // Brute force over the cube.
        let brute: E = (0..16usize)
            .map(|x| {
                let point: Vec<E> = (0..4).map(|j| E::from_u64(((x >> j) & 1) as u64)).collect();
                mask.eval(&point)
            })
            .fold(E::ZERO, |a, b| a + b);
        assert_eq!(mask.sum(), brute);
        let mut rng = Rng(6);
        let mut prefix = Vec::new();
        let mut claim = mask.sum();
        for _ in 0..4 {
            let round = mask.round_poly(&prefix);
            let at_one = round.iter().fold(E::ZERO, |a, &c| a + c);
            assert_eq!(round[0] + at_one, claim);
            let c = rng.fp5();
            claim = eval_poly(&round, c);
            prefix.push(c);
        }
        assert_eq!(claim, mask.eval(&prefix));
        // Interpolation on 0..d.
        let poly: Vec<E> = (0..9).map(|_| rng.fp5()).collect();
        let evals: Vec<E> = (0..9).map(|i| eval_poly(&poly, E::from_u64(i))).collect();
        assert_eq!(evals_to_coeffs(&evals), poly);
    }

    #[test]
    fn v1_and_v2_reject_each_other() {
        let (shape2, z2) = fixture(40);
        let (shape1, z1) = relation(3, 5, 11, 40).finish();
        let regime = WhirSecurityRegime::BciksJohnsonQrom128;
        let profile = Profile::CshakeJohnson400;
        assert_eq!(shape1.closing(), Closing::V1);
        assert_eq!(shape2.closing(), Closing::V2);
        assert_ne!(shape1.digest(), shape2.digest());
        assert_eq!(shape2.num_vars, shape1.num_vars + 3);

        let p1 = v1::prove(&shape1, z1.clone(), STATEMENT, regime, &SEED).unwrap();
        let public1 = z1[1..=shape1.num_public].to_vec();
        assert!(v1::verify(&shape1, &public1, STATEMENT, regime, &p1));
        let bytes1 = p1.to_bytes();
        let p2 = prove(&shape2, z2.clone(), STATEMENT, profile, &SEED).unwrap();
        let bytes2 = p2.to_bytes();

        // v1 bytes are not a v2 proof, for either shape.
        assert!(ZkHemV2Proof::from_bytes(&bytes1, &shape2).is_none());
        assert!(ZkHemV2Proof::from_bytes(&bytes1, &shape1).is_none());
        // v2 bytes are not a v1 proof, for either shape.
        assert!(v1::ZkHemProof::from_bytes(&bytes2, &shape1, regime).is_none());
        assert!(v1::ZkHemProof::from_bytes(&bytes2, &shape2, regime).is_none());
        // v2 refuses a v1 relation.
        assert!(layout_of(&shape1).is_none());
        assert_eq!(
            prove(&shape1, z1, STATEMENT, profile, &SEED),
            Err(ZkHemV2Error::UnsupportedRelation)
        );
        assert!(!verify(&shape1, &public1, STATEMENT, profile, &p2));
        // A v1 proof of the v1 relation does not verify against the v2 relation.
        assert!(!v1::verify(&shape2, &public1, STATEMENT, regime, &p1));
    }
}
