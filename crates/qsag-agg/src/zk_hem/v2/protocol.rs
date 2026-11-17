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
    let mut table = vec![E::ZERO; 1 << point.len()];
    table[0] = E::ONE;
    for (j, &r) in point.iter().enumerate() {
        let (lo, hi) = table[..2 << j].split_at_mut(1 << j);
        let step = |lo: &mut [E], hi: &mut [E]| {
            for (l, h) in lo.iter_mut().zip(hi) {
                *h = *l * r;
                *l -= *h;
            }
        };
        #[cfg(feature = "std")]
        {
            let chunk = par_chunk(lo.len());
            if lo.len() > chunk {
                std::thread::scope(|scope| {
                    for (l, h) in lo.chunks_mut(chunk).zip(hi.chunks_mut(chunk)) {
                        let step = &step;
                        crate::spawn_bounded(scope, move || step(l, h));
                    }
                });
                continue;
            }
        }
        step(lo, hi);
    }
    table
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
