//! Committed zk-Hem: a zero-knowledge argument for a [`Shape`] over the Hem WHIR commitment.
//!
//! One batch commitment holds five base-field tables of `2^l` cells: the masked assignment
//! table `Z` and four uniform companion tables `C_0..C_3`. `Z` is laid out as
//!
//! ```text
//! [ 1, variables, masking variables, zeros | sumcheck masks | zeros | opening blinders ]
//!   `2^k` cells: the variable subcube
//! ```
//!
//! The column sumcheck runs over the variable subcube only, so its summand does not involve
//! the masks or the blinders.
//!
//! ```text
//! ```
//!
//! Everything below is committed before any challenge exists.
//!
//! 1. Row sumcheck of `eq(tau, x) * F(Az, Bz, Cz)(x)`, masked by the committed separable
//!    polynomial `g1` (`libra_sumcheck_perfectly_simulated`): the prover sends
//!    `G1 = sum g1`, then `rho1` is drawn and the rounds run on `f + rho1 g1`.
//! 2. The prover reveals `(Az, Bz, Cz)(rx)`. The twelve masking rows of the relation make
//!    this triple uniform ([`super::relation::MASK_ROWS`]).
//! 3. Column sumcheck of `M(rx, y) * Z(y)`, masked by `g2`, down to a point `ry`. Neither
//!    `Z(ry)` nor `g2(ry)` is sent.
//! 4. All remaining checks are linear in `Z`: the two mask sums, `g1(rx)`, the value
//!    `M(rx, ry) Z(ry) + rho2 g2(ry)`, the cell holding the constant `1` and the cells of
//!    the public inputs. They are batched with `lambda` into one functional `K` with a
//!    known value `V`.
//! 5. The prover sends `sigma_j = <C_j, K>`, then a challenge `beta` outside the quadratic
//!    subfield is drawn and WHIR opens the single word
//!    `U = Z + beta C_0 + beta^2 C_1 + beta^3 C_2 + beta^4 C_3` at `K` with value
//!    `V + sum beta^(j+1) sigma_j` (`batched_base_companion_perfectly_simulated`). Every
//!    out-of-domain value, fold and terminal polynomial WHIR reveals is a function of `U`.
//! 6. The only raw symbols of `Z` that are opened are the queried Stage-0 symbols. The top
//!    cells of `Z` are uniform blinders, at least as many as opened symbols, so those
//!    symbols are uniform (`opened_symbols_perfectly_simulated`). Unopened Stage-0 leaves
//!    are salted.
//!
//! What this file does not establish is listed on [`prove`].

use alloc::vec;
use alloc::vec::Vec;

use super::relation::Shape;
use super::{CornerPadBasis, LibraMask, NonzeroChallenge, PrimitiveChallenge, SeedStream, interp};
use crate::field::{Goldilocks, GoldilocksExt4, build_eq_table_ext4};
use crate::pcs::{
    CanopyCommitment, HemWhirOpeningProof, MAX_PCS_NUM_VARS, WeightedPoint, WhirSchedule,
    WhirSecurityRegime, add_point_kernel, hypercube_to_monomial_coeffs,
    whir_commit_batch_secret_with_schedule, whir_open_blend, whir_verify_blend,
};
use crate::sponge::{FiatShamirTranscript, InstanceBound, cshake256_32};

type E = GoldilocksExt4;
type F = Goldilocks;

/// Individual degree of the row sumcheck: `eq * selector * a^7`.
pub const ROW_DEGREE: usize = 9;
/// Individual degree of the column sumcheck: `M * Z`.
pub const COL_DEGREE: usize = 2;
const ROW_MASK_BITS: usize = 4;
const COL_MASK_BITS: usize = 2;
const COMPANIONS: usize = 4;
const _: () = assert!(ROW_DEGREE < 1 << ROW_MASK_BITS && COL_DEGREE < 1 << COL_MASK_BITS);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkHemError {
    /// The assignment does not satisfy the relation.
    Unsatisfied,
    /// The relation does not fit the largest supported commitment.
    RelationTooLarge,
    /// The row challenge left the masking rows without full rank. This happens with
    /// negligible probability; the prover refuses instead of emitting a proof whose
    /// revealed row values are not uniform. Retry with a different `seed`.
    MaskRankDeficient,
}

/// Cell layout of the assignment table for one relation and regime.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// `log2` of the table size.
    pub log_cells: usize,
    /// `log2` of the variable subcube; variable `v` lives in cell `v`.
    pub var_bits: usize,
    /// Uniform cells at the top of the table, one per opened Stage-0 symbol.
    pub blind_cells: usize,
    pub schedule: WhirSchedule,
}

impl Layout {
    /// Smallest table that holds the variable subcube, the masks and the opening blinders.
    pub fn new(shape: &Shape, regime: WhirSecurityRegime) -> Option<Self> {
        if !regime.meets_qrom_128_floor() {
            return None;
        }
        let var_bits = shape.num_vars.next_power_of_two().trailing_zeros().max(1) as usize;
        let masks = ((shape.log_rows * 4) << ROW_MASK_BITS) + ((var_bits * 4) << COL_MASK_BITS);
        (var_bits + 1..=MAX_PCS_NUM_VARS).find_map(|log_cells| {
            let cells = 1usize << log_cells;
            let schedule = regime.schedule(log_cells);
            let st0 = schedule.stages[0];
            let arity = 1usize << st0.step_vars;
            let fibers = cells * st0.blowup / arity;
            let blind_cells = st0.num_queries.min(fibers) * arity;
            ((1usize << var_bits) + masks + blind_cells <= cells).then_some(Self {
                log_cells,
                var_bits,
                blind_cells,
                schedule,
            })
        })
    }

    #[inline]
    fn row_mask_block(&self, round: usize, limb: usize) -> usize {
        (1usize << self.var_bits) + ((round * 4 + limb) << ROW_MASK_BITS)
    }

    #[inline]
    fn col_mask_block(&self, log_rows: usize, round: usize, limb: usize) -> usize {
        self.row_mask_block(log_rows, 0) + ((round * 4 + limb) << COL_MASK_BITS)
    }
}

/// A zk-Hem proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkHemProof {
    pub commitment: CanopyCommitment,
    /// `sum_x g1(x)`, sent before `rho1`.
    pub row_mask_sum: E,
    /// Coefficients of the masked row-sumcheck rounds.
    pub row_rounds: Vec<Vec<E>>,
    /// `(Az, Bz, Cz)(rx)`.
    pub row_values: [E; 3],
    /// `sum_y g2(y)`, sent before `rho2`.
    pub col_mask_sum: E,
    /// Coefficients of the masked column-sumcheck rounds.
    pub col_rounds: Vec<Vec<E>>,
    /// `<C_j, K>`, sent before `beta`.
    pub companion_claims: [E; COMPANIONS],
    pub opening: HemWhirOpeningProof,
}

impl ZkHemProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.commitment.to_bytes());
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
        self.companion_claims.iter().for_each(|v| push(&mut out, v));
        self.opening.push_bytes(&mut out);
        out
    }

    /// Canonical decoding for the given relation and regime; rejects trailing bytes.
    pub fn from_bytes(bytes: &[u8], shape: &Shape, regime: WhirSecurityRegime) -> Option<Self> {
        let layout = Layout::new(shape, regime)?;
        let (commitment, mut pos) = CanopyCommitment::from_bytes_canonical(bytes)?;
        let take = |pos: &mut usize| -> Option<E> {
            let chunk: [u8; 32] = bytes.get(*pos..*pos + 32)?.try_into().ok()?;
            *pos += 32;
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
        let companion_claims = [
            take(&mut pos)?,
            take(&mut pos)?,
            take(&mut pos)?,
            take(&mut pos)?,
        ];
        let (opening, used) = HemWhirOpeningProof::from_bytes_canonical(&bytes[pos..])?;
        (pos + used == bytes.len()).then_some(Self {
            commitment,
            row_mask_sum,
            row_rounds,
            row_values,
            col_mask_sum,
            col_rounds,
            companion_claims,
            opening,
        })
    }
}

// ============================================================================
// Shared algebra
// ============================================================================

/// The `F_p`-basis of `Ext4` dual to [`GoldilocksExt4::to_limbs`].
fn limb_basis() -> [E; 4] {
    core::array::from_fn(|j| {
        let mut limbs = [F::ZERO; 4];
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

/// Common weight of the four rows `base..base + 4` at `rx`, excluding the two low variables.
fn corner_factor(rx: &[E], base: usize) -> E {
    rx.iter().enumerate().skip(2).fold(E::ONE, |acc, (j, &r)| {
        acc * if (base >> j) & 1 == 1 { r } else { E::ONE - r }
    })
}

/// Whether the masking rows make `(Az, Bz, Cz)(rx)` uniform.
fn mask_rows_full_rank(shape: &Shape, rx: &[E]) -> bool {
    CornerPadBasis::new(rx[0], rx[1]).is_some()
        && (0..3).all(|g| !corner_factor(rx, shape.mask_row_base(g)).is_zero())
}

/// Coefficients of one separable mask: `g(x) = sum_i sum_k coef[i][k] x_i^k`.
struct Mask {
    coef: Vec<Vec<E>>,
}

impl Mask {
    fn sample(stream: &mut SeedStream, rounds: usize, degree: usize) -> Self {
        let coef = (0..rounds)
            .map(|_| (0..=degree).map(|_| stream.next_ext4()).collect())
            .collect();
        Self { coef }
    }

    fn libra(&self) -> LibraMask {
        LibraMask {
            a0: self.coef.iter().fold(E::ZERO, |acc, row| acc + row[0]),
            a: self.coef.iter().map(|row| row[1..].to_vec()).collect(),
        }
    }

    /// Store limb `j` of round `i` as the hypercube values of the multilinear polynomial
    /// whose monomial coefficient `k` is that limb of `coef[i][k]`. Its evaluation at
    /// `(x, x^2, x^4, ..)` is then the limb of the round's univariate at `x`.
    fn write(&self, cells: &mut [F], bits: usize, block: impl Fn(usize, usize) -> usize) {
        for (i, row) in self.coef.iter().enumerate() {
            for j in 0..4 {
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

/// The point selecting the block at cell offset `block` with `low` on its own variables.
fn block_point(log_cells: usize, block: usize, low: &[E]) -> Vec<E> {
    let mut point = low.to_vec();
    point.extend((low.len()..log_cells).map(|b| {
        if (block >> b) & 1 == 1 {
            E::ONE
        } else {
            E::ZERO
        }
    }));
    point
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

fn pow2(n: usize) -> E {
    (0..n).fold(E::ONE, |acc, _| acc + acc)
}

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

/// The batched linear functional of step 4, as weighted evaluation points of `Z`.
fn claim_terms(inp: &ClaimInputs<'_>) -> Vec<WeightedPoint> {
    let l = inp.layout.log_cells;
    let basis = limb_basis();
    let lam: Vec<E> = (0..5 + inp.num_public)
        .scan(E::ONE, |acc, _| {
            let cur = *acc;
            *acc *= inp.lambda;
            Some(cur)
        })
        .collect();
    let mut terms = Vec::with_capacity(12 * (inp.log_rows + l) + 2);
    let mut push = |weight: E, point: Vec<E>| terms.push(WeightedPoint { weight, point });

    let zeros = |bits: usize| vec![E::ZERO; bits];
    let ones = |bits: usize| vec![E::ONE; bits];
    let row_half = pow2(inp.log_rows - 1);
    let k = inp.layout.var_bits;
    let col_half = pow2(k - 1);
    for (j, &limb) in basis.iter().enumerate() {
        for i in 0..inp.log_rows {
            let block = inp.layout.row_mask_block(i, j);
            // sum g1 = 2^(n-1) sum_i (g1_i(0) + g1_i(1)).
            push(
                lam[0] * row_half * limb,
                block_point(l, block, &zeros(ROW_MASK_BITS)),
            );
            push(
                lam[0] * row_half * limb,
                block_point(l, block, &ones(ROW_MASK_BITS)),
            );
            // g1(rx) = sum_i g1_i(rx_i).
            push(
                lam[2] * limb,
                block_point(l, block, &pow2_coords(inp.rx[i], ROW_MASK_BITS)),
            );
        }
        for i in 0..k {
            let block = inp.layout.col_mask_block(inp.log_rows, i, j);
            push(
                lam[1] * col_half * limb,
                block_point(l, block, &zeros(COL_MASK_BITS)),
            );
            push(
                lam[1] * col_half * limb,
                block_point(l, block, &ones(COL_MASK_BITS)),
            );
            push(
                lam[3] * inp.rho2 * limb,
                block_point(l, block, &pow2_coords(inp.ry[i], COL_MASK_BITS)),
            );
        }
    }
    push(lam[3] * inp.matrix_at_point, block_point(l, 0, inp.ry));
    // Variable 0 holds the constant 1; variables 1..=num_public hold the public inputs.
    for i in 0..=inp.num_public {
        push(lam[4 + i], block_point(l, i, &[]));
    }
    terms
}

/// `kernel[i] += weight * prod_j point[j]^(bit_j(i))`, visiting only indices whose bits lie on
/// nonzero coordinates of `point`.
fn add_sparse_point_kernel(kernel: &mut [E], weight: E, point: &[E]) {
    let live: Vec<(usize, E)> = point
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.is_zero())
        .map(|(j, &c)| (1usize << j, c))
        .collect();
    let mut entries: Vec<(usize, E)> = Vec::with_capacity(1 << live.len());
    entries.push((0, weight));
    for &(bit, c) in &live {
        for n in 0..entries.len() {
            let (idx, v) = entries[n];
            entries.push((idx | bit, v * c));
        }
    }
    for (idx, v) in entries {
        kernel[idx] += v;
    }
}

fn batched_value(lambda: E, values: &[E]) -> E {
    values
        .iter()
        .rev()
        .fold(E::ZERO, |acc, &v| acc * lambda + v)
}

fn start_transcript(
    shape: &Shape,
    layout: &Layout,
    statement: &[u8],
    public_inputs: &[F],
    commitment: &CanopyCommitment,
) -> FiatShamirTranscript<InstanceBound> {
    let public_bytes: Vec<u8> = public_inputs.iter().flat_map(|v| v.to_le_bytes()).collect();
    let mut params = shape.digest().to_vec();
    for n in [layout.log_cells, layout.var_bits, layout.blind_cells] {
        params.extend_from_slice(&(n as u64).to_le_bytes());
    }
    FiatShamirTranscript::new()
        .bind_relation(b"QSAG.ZKHEM.COMMITTED/v1", &params, &layout.schedule)
        .bind_instance(&[statement, &public_bytes, &commitment.to_bytes()])
}

fn squeeze_point(tr: &mut FiatShamirTranscript<InstanceBound>, label: &[u8], n: usize) -> Vec<E> {
    (0..n).map(|_| tr.squeeze_ext4(label)).collect()
}

// ============================================================================
// Prover
// ============================================================================

/// Smallest table worth splitting across workers.
const PAR_MIN: usize = 1 << 12;

/// Chunk length that spreads `len` items over the worker budget.
fn par_chunk(len: usize) -> usize {
    #[cfg(feature = "std")]
    let workers = crate::parallel_workers();
    #[cfg(not(feature = "std"))]
    let workers = 1;
    len.div_ceil(workers).max(PAR_MIN)
}

/// `f(k, chunk_k)` over `data.chunks_mut(chunk)`, on the worker pool when there are several.
fn for_each_chunk_mut<T: Send>(data: &mut [T], chunk: usize, f: impl Fn(usize, &mut [T]) + Sync) {
    #[cfg(feature = "std")]
    if data.len() > chunk {
        std::thread::scope(|scope| {
            for (k, part) in data.chunks_mut(chunk).enumerate() {
                let f = &f;
                crate::spawn_bounded(scope, move || f(k, part));
            }
        });
        return;
    }
    for (k, part) in data.chunks_mut(chunk).enumerate() {
        f(k, part);
    }
}

/// Replace every pair `(table[2i], table[2i + 1])` by `f` of it, halving the table.
/// `secret` erases the vacated half, which may hold witness-dependent values.
fn fold_pairs(table: &mut Vec<E>, secret: bool, f: impl Fn(E, E) -> E + Sync) {
    let half = table.len() / 2;
    let chunk = 2 * par_chunk(half);
    // Each chunk folds into its own first half; the halves are then packed in order.
    for_each_chunk_mut(table, chunk, |_, part| {
        for i in 0..part.len() / 2 {
            part[i] = f(part[2 * i], part[2 * i + 1]);
        }
    });
    for start in (chunk..table.len()).step_by(chunk) {
        let len = (table.len() - start).min(chunk) / 2;
        table.copy_within(start..start + len, start / 2);
    }
    if secret {
        qsag_asm::volatile_fill(&mut table[half..], E::ZERO);
    }
    table.truncate(half);
}

/// Bind the lowest variable of a multilinear table to `r`.
fn fold_in_place(table: &mut Vec<E>, r: E, secret: bool) {
    fold_pairs(table, secret, |lo, hi| lo + r * (hi - lo));
}

/// [`fold_in_place`] for a table that is still over the base field.
fn fold_base(table: &[F], r: E) -> Vec<E> {
    let mut out = vec![E::ZERO; table.len() / 2];
    let chunk = par_chunk(out.len());
    for_each_chunk_mut(&mut out, chunk, |k, part| {
        let pairs = table[2 * k * chunk..].as_chunks::<2>().0;
        for (slot, &[lo, hi]) in part.iter_mut().zip(pairs) {
            *slot = E::from_base(lo) + r.mul_base(hi - lo);
        }
    });
    out
}

/// `eq(point, x)` for every `x`, with `point[0]` on the lowest index bit.
fn eq_table(point: &[E]) -> Vec<E> {
    let split = point.len() / 2;
    if 1usize << point.len() <= PAR_MIN {
        return build_eq_table_ext4(point);
    }
    let low = build_eq_table_ext4(&point[..split]);
    let high = build_eq_table_ext4(&point[split..]);
    let mut table = vec![E::ZERO; 1 << point.len()];
    let rows = par_chunk(table.len()).div_ceil(low.len());
    for_each_chunk_mut(&mut table, rows * low.len(), |k, part| {
        for (block, &h) in part.chunks_mut(low.len()).zip(&high[k * rows..]) {
            for (slot, &l) in block.iter_mut().zip(&low) {
                *slot = h * l;
            }
        }
    });
    table
}

/// Sum of `per_item` over `range`. Partial sums are erased: in the hiding mode they are
/// unmasked witness polynomials.
fn round_evals<const N: usize>(
    range: core::ops::Range<usize>,
    per_item: impl Fn(usize) -> [E; N] + Sync,
) -> [E; N] {
    let add = |mut acc: [E; N], part: [E; N]| {
        for (a, p) in acc.iter_mut().zip(part) {
            *a += p;
        }
        acc
    };
    let sum =
        |range: core::ops::Range<usize>| range.fold([E::ZERO; N], |acc, i| add(acc, per_item(i)));
    #[cfg(feature = "std")]
    if range.len() > PAR_MIN && crate::parallel_workers() > 1 {
        let chunk = par_chunk(range.len());
        let mut parts: Vec<[E; N]> = std::thread::scope(|scope| {
            let workers: Vec<_> = range
                .clone()
                .step_by(chunk)
                .map(|start| {
                    let (sum, end) = (&sum, (start + chunk).min(range.end));
                    crate::spawn_bounded(scope, move || sum(start..end))
                })
                .collect();
            workers.into_iter().map(crate::join_worker).collect()
        });
        let total = parts.iter().fold([E::ZERO; N], |acc, &part| add(acc, part));
        for part in &mut parts {
            qsag_asm::volatile_fill(part, E::ZERO);
        }
        return total;
    }
    sum(range)
}

fn evals_to_coeffs(evals: &[E]) -> Vec<E> {
    let xs: Vec<E> = (0..evals.len() as u64).map(E::from_u64).collect();
    match interp(&xs, evals) {
        Some(coeffs) => coeffs,
        None => unreachable!("the points 0..=d are distinct"),
    }
}

/// Runs one sumcheck, masked when `mask` is given; returns the round coefficient lists and
/// the challenge point.
fn sumcheck(
    tr: &mut FiatShamirTranscript<InstanceBound>,
    label: &[u8],
    n: usize,
    mask: Option<(&LibraMask, E)>,
    mut witness_round: impl FnMut(Option<E>) -> Vec<E>,
) -> (Vec<Vec<E>>, Vec<E>) {
    let mut rounds = Vec::with_capacity(n);
    let mut point = Vec::with_capacity(n);
    let mut last = None;
    for _ in 0..n {
        let mut f = witness_round(last);
        if let Some((mask, rho)) = mask {
            let mut g = mask.round_poly(&point);
            for (v, &g) in f.iter_mut().zip(&g) {
                *v += rho * g;
            }
            qsag_asm::volatile_fill(&mut g, E::ZERO);
        }
        tr.absorb_ext4_slice(label, &f);
        let c = tr.squeeze_ext4(label);
        rounds.push(f);
        point.push(c);
        last = Some(c);
    }
    (rounds, point)
}

/// The multilinear selector of rows `0..count`, folded lowest variable first without a
/// table: after `k` folds entry `j` is one below `count >> k`, zero above it and
/// `boundary` at it.
struct PrefixSelector {
    count: usize,
    boundary: E,
}

impl PrefixSelector {
    fn new(count: usize) -> Self {
        Self {
            count,
            boundary: E::ZERO,
        }
    }

    fn at(&self, j: usize) -> E {
        match j.cmp(&self.count) {
            core::cmp::Ordering::Less => E::ONE,
            core::cmp::Ordering::Equal => self.boundary,
            core::cmp::Ordering::Greater => E::ZERO,
        }
    }

    fn fold(&mut self, r: E) {
        // The new boundary entry covers the old one and one neighbour: an all-one entry
        // below it when the folded bit of `count` is set, an all-zero entry above otherwise.
        self.boundary = if self.count & 1 == 1 {
            E::ONE + r * (self.boundary - E::ONE)
        } else {
            self.boundary - r * self.boundary
        };
        self.count >>= 1;
    }
}

/// Field in which one row round evaluates its gate: the base field before the first
/// challenge, the extension after it. Both use the same branchless software arithmetic.
trait GateField:
    Copy + core::ops::Add<Output = Self> + core::ops::Sub<Output = Self> + Send + Sync
{
    fn is_zero(self) -> bool;
    fn times(self, rhs: Self) -> Self;
    /// `weight * self`.
    fn weigh(self, weight: E) -> E;
    fn lift(self) -> E;
}

impl GateField for F {
    #[inline(always)]
    fn is_zero(self) -> bool {
        self == F::ZERO
    }
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
    fn is_zero(self) -> bool {
        E::is_zero(self)
    }
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

/// `h(X) = sum_x eq_rest(x) gate(X, x)` for one row round, as `ROW_DEGREE` coefficients:
/// the round polynomial without the factor `eq` contributes for the current variable.
///
/// Rows below the selector boundary are S-box rows (degree 7 in `X`), rows above it are
/// multiplication rows (degree 2); only the pair holding the boundary needs the general
/// degree-8 gate. Each part is evaluated at as many points as its degree requires.
fn row_round<T: GateField>(
    [ta, tb, tc]: [&[T]; 3],
    eq_rest: &[E],
    selector: &PrefixSelector,
    secret: bool,
) -> Vec<E> {
    let pairs = eq_rest.len();
    let mixed = (selector.count / 2).min(pairs);
    let line = |t: &[T], i: usize| (t[2 * i], t[2 * i + 1] - t[2 * i]);
    // A zero A/C pair gives the zero gate at every X, whatever B is. This covers padding
    // and satisfied linear rows. It reads witness values, so only the public mode uses it.
    let vanishes = |i: usize| {
        !secret
            && ta[2 * i].is_zero()
            && ta[2 * i + 1].is_zero()
            && tc[2 * i].is_zero()
            && tc[2 * i + 1].is_zero()
    };
    let mut sbox = round_evals::<{ ROW_DEGREE - 1 }>(0..mixed, |i| {
        if vanishes(i) {
            return [E::ZERO; ROW_DEGREE - 1];
        }
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
        if vanishes(i) {
            return [E::ZERO; 3];
        }
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

/// Row sumcheck of `eq(tau, x) gate(x)` over the row tables `(Az, Bz, Cz)`. Returns the
/// round polynomials, the point and the three tables' values at it.
fn row_sumcheck(
    tr: &mut FiatShamirTranscript<InstanceBound>,
    tau: &[E],
    num_sbox: usize,
    mut base: [Vec<F>; 3],
    mask: Option<(&LibraMask, E)>,
) -> (Vec<Vec<E>>, Vec<E>, [E; 3]) {
    let _phase = crate::profile::span("hem_row_sumcheck");
    let secret = mask.is_some();
    let mut ext: [Vec<E>; 3] = core::array::from_fn(|_| Vec::new());
    let mut selector = PrefixSelector::new(num_sbox);
    // `eq` splits into the bound prefix, the current variable and the rest. Summing the
    // rest table over its lowest variable removes that variable.
    let mut eq_rest = eq_table(&tau[1..]);
    let mut eq_bound = E::ONE;
    let bind = |c: E,
                round: usize,
                base: &mut [Vec<F>; 3],
                ext: &mut [Vec<E>; 3],
                selector: &mut PrefixSelector| {
        if round == 1 {
            for (e, b) in ext.iter_mut().zip(base.iter_mut()) {
                *e = fold_base(b, c);
                if secret {
                    qsag_asm::volatile_fill(b, F::ZERO);
                }
                *b = Vec::new();
            }
        } else {
            for e in ext.iter_mut() {
                fold_in_place(e, c, secret);
            }
        }
        selector.fold(c);
    };
    let mut round = 0;
    let (rounds, rx) = sumcheck(tr, b"ZKHEM_ROW_ROUND", tau.len(), mask, |c| {
        if let Some(c) = c {
            bind(c, round, &mut base, &mut ext, &mut selector);
            let t = tau[round - 1];
            let tc = t * c;
            eq_bound *= E::ONE - t - c + tc + tc;
            fold_pairs(&mut eq_rest, false, |lo, hi| lo + hi);
        }
        let mut h = if round == 0 {
            row_round(
                base.each_ref().map(Vec::as_slice),
                &eq_rest,
                &selector,
                secret,
            )
        } else {
            row_round(
                ext.each_ref().map(Vec::as_slice),
                &eq_rest,
                &selector,
                secret,
            )
        };
        // Times `eq_bound * eq(tau[round], X)`.
        let l1 = eq_bound * (tau[round] + tau[round] - E::ONE);
        let l0 = eq_bound * (E::ONE - tau[round]);
        let mut coeffs = vec![E::ZERO; ROW_DEGREE + 1];
        for (k, &hk) in h.iter().enumerate() {
            coeffs[k] += l0 * hk;
            coeffs[k + 1] += l1 * hk;
        }
        qsag_asm::volatile_fill(&mut h, E::ZERO);
        round += 1;
        coeffs
    });
    bind(rx[tau.len() - 1], round, &mut base, &mut ext, &mut selector);
    let values = [ext[0][0], ext[1][0], ext[2][0]];
    (rounds, rx, values)
}

/// Column sumcheck of `M(y) Z(y)` over the variable cells. Returns the round polynomials,
/// the point, `M` at it and `Z` at it.
fn column_sumcheck(
    tr: &mut FiatShamirTranscript<InstanceBound>,
    mut tm: Vec<E>,
    z: &[F],
    mask: Option<(&LibraMask, E)>,
) -> (Vec<Vec<E>>, Vec<E>, E, E) {
    let _phase = crate::profile::span("hem_column_sumcheck");
    let secret = mask.is_some();
    let rounds = tm.len().trailing_zeros() as usize;
    let mut tz: Vec<E> = Vec::new();
    let finish = |mut evals: [E; COL_DEGREE + 1]| {
        let coeffs = evals_to_coeffs(&evals);
        qsag_asm::volatile_fill(&mut evals, E::ZERO);
        coeffs
    };
    let mut round = 0;
    let bind = |c: E, round: usize, tm: &mut Vec<E>, tz: &mut Vec<E>| {
        if round == 1 {
            *tz = fold_base(z, c);
        } else {
            fold_in_place(tz, c, secret);
        }
        fold_in_place(tm, c, false);
    };
    let (col_rounds, ry) = sumcheck(tr, b"ZKHEM_COL_ROUND", rounds, mask, |c| {
        if let Some(c) = c {
            bind(c, round, &mut tm, &mut tz);
        }
        round += 1;
        let tm = &tm;
        if round == 1 {
            return finish(round_evals(0..tm.len() / 2, |i| {
                let (m0, m1) = (tm[2 * i], tm[2 * i + 1]);
                let (z0, z1) = (z[2 * i], z[2 * i + 1]);
                [
                    m0.mul_base(z0),
                    m1.mul_base(z1),
                    (m1 + m1 - m0).mul_base(z1 + z1 - z0),
                ]
            }));
        }
        let tz = &tz;
        finish(round_evals(0..tm.len() / 2, |i| {
            let (m0, m1) = (tm[2 * i], tm[2 * i + 1]);
            let (z0, z1) = (tz[2 * i], tz[2 * i + 1]);
            [m0 * z0, m1 * z1, (m1 + m1 - m0) * (z1 + z1 - z0)]
        }))
    });
    bind(ry[rounds - 1], round, &mut tm, &mut tz);
    let (matrix, value) = (tm[0], tz[0]);
    if secret {
        qsag_asm::volatile_fill(&mut tz, E::ZERO);
    }
    (col_rounds, ry, matrix, value)
}

/// `(Az, Bz, Cz)` as row tables. With `check`, `None` unless every row is satisfied; the
/// scan does not stop at the first failing row.
fn row_tables(shape: &Shape, assignment: &[F], check: bool) -> Option<[Vec<F>; 3]> {
    let _phase = crate::profile::span("hem_row_tables");
    let mut tables: [Vec<F>; 3] = core::array::from_fn(|_| vec![F::ZERO; shape.num_rows()]);
    let valid = core::sync::atomic::AtomicBool::new(true);
    let chunk = par_chunk(shape.num_rows());
    {
        let [a, b, c] = &mut tables;
        let mut rows: Vec<_> = a
            .chunks_mut(chunk)
            .zip(b.chunks_mut(chunk))
            .zip(c.chunks_mut(chunk))
            .collect();
        for_each_chunk_mut(&mut rows, 1, |k, part| {
            let ((a, b), c) = &mut part[0];
            let mut ok = true;
            for (j, ((ta, tb), tc)) in a.iter_mut().zip(b.iter_mut()).zip(c.iter_mut()).enumerate()
            {
                let i = k * chunk + j;
                let va = shape.a.row_dot(i, assignment);
                let vb = shape.b.row_dot(i, assignment);
                let vc = shape.c.row_dot(i, assignment);
                let expected = if i < shape.num_sbox {
                    crate::sponge::poseidon2_sbox7(va)
                } else {
                    va.const_mul(vb)
                };
                ok &= expected == vc;
                (*ta, *tb, *tc) = (va, vb, vc);
            }
            if !ok {
                valid.store(false, core::sync::atomic::Ordering::Relaxed);
            }
        });
    }
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
/// directly; its remaining entries are deferred and added afterwards. The result is the
/// exact sparse contraction whatever the windows are.
fn column_table(shape: &Shape, eq_rx: &[E], combine: &[E], cells: usize) -> Vec<E> {
    let _phase = crate::profile::span("hem_column_table");
    let mut table = vec![E::ZERO; cells];
    let matrices = [&shape.a, &shape.b, &shape.c];
    // Rows `rows` into `window`, the table's columns from `home` on; other columns to `far`.
    let scatter = |rows: core::ops::Range<usize>,
                   home: usize,
                   window: &mut [E],
                   far: &mut Vec<(usize, E)>| {
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
                        None => far.push((col, term)),
                    }
                }
            }
        }
    };
    let mut far = Vec::new();
    #[cfg(feature = "std")]
    if eq_rx.len() > PAR_MIN && crate::parallel_workers() > 1 {
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
                            let mut far = Vec::new();
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
            far.extend(deferred.into_iter().flatten());
        }
        for (col, term) in far {
            table[col] += term;
        }
        return table;
    }
    scatter(0..eq_rx.len(), 0, &mut table, &mut far);
    debug_assert!(far.is_empty());
    table
}

/// Prove that `assignment` satisfies `shape`, bound to `statement`.
///
/// `assignment` is the vector returned by [`super::relation::ConstraintSystem::finish`];
/// its masking variables are overwritten here. `seed` must be uniform and secret: it
/// determines the masks, the companions, the blinders and the leaf salts.
///
/// Not established by this implementation:
/// * a mechanized proof of the composed simulator for this exact layout. The ingredients
///   are the theorems of `ZkHemSoundnessAndPrivacy.lean` named in the module comment; their
///   composition over the cell layout is argued in comments only: the row masks do not
///   enter the row summand, the column masks and blinders lie outside the variable subcube
///   the column sumcheck runs over, the masking rows have determinant `k1 k2 k3`, and the
///   blinders are sampled last, conditioned on everything else;
/// * hiding of unopened Stage-0 leaves beyond the salted-leaf coupling of that file (no
///   bound on the bad event is mechanized there);
/// * the batching step uses scalar weights `beta^j`. Its proximity loss is the standard one
///   for random linear combinations and is not re-derived for the regime's query schedule,
///   which was accounted for the affine cascade of the non-hiding opening;
/// * knowledge soundness of the composition (masked sumchecks, linear batching, companion
///   challenge, WHIR) has no concrete bound stated or proved here.
pub fn prove(
    shape: &Shape,
    assignment: Vec<F>,
    statement: &[u8],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
) -> Result<ZkHemProof, ZkHemError> {
    prove_inner(shape, assignment, statement, regime, seed, true)
}

fn prove_inner(
    shape: &Shape,
    assignment: Vec<F>,
    statement: &[u8],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
    check: bool,
) -> Result<ZkHemProof, ZkHemError> {
    prove_with_claimed_publics(shape, assignment, statement, regime, seed, check, None)
}

/// `claimed` replaces the public inputs bound into the transcript (tests only: a prover whose
/// committed cells differ from the values it claims).
fn prove_with_claimed_publics(
    shape: &Shape,
    mut assignment: Vec<F>,
    statement: &[u8],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
    check: bool,
    claimed: Option<&[F]>,
) -> Result<ZkHemProof, ZkHemError> {
    let Some(layout) = Layout::new(shape, regime) else {
        qsag_asm::volatile_fill(&mut assignment, F::ZERO);
        return Err(ZkHemError::RelationTooLarge);
    };
    if assignment.len() != shape.num_vars {
        qsag_asm::volatile_fill(&mut assignment, F::ZERO);
        return Err(ZkHemError::Unsatisfied);
    }
    // Coins are bound to the relation, the statement and the witness, so a repeated `seed`
    // does not repeat masks across different proofs.
    let mut coin_input = seed.to_vec();
    coin_input.extend_from_slice(&shape.digest());
    coin_input.extend_from_slice(&cshake256_32(b"QSAG.ZKHEM.COINS.STMT/v1", statement));
    let mut witness_bytes: Vec<u8> = assignment.iter().flat_map(|v| v.to_le_bytes()).collect();
    coin_input.extend_from_slice(&cshake256_32(b"QSAG.ZKHEM.COINS.WIT/v1", &witness_bytes));
    qsag_asm::volatile_fill(&mut witness_bytes, 0u8);
    let mut coin_seed = cshake256_32(b"QSAG.ZKHEM.COINS.SEED/v1", &coin_input);
    qsag_asm::volatile_fill(&mut coin_input, 0u8);
    let mut stream = SeedStream::new(b"QSAG.ZKHEM.COINS/v1", &coin_seed);
    qsag_asm::volatile_fill(&mut coin_seed, 0u8);
    for slot in &mut assignment[shape.mask_var_base..] {
        *slot = stream.next_base();
    }
    // Row values `(Az, Bz, Cz)`, taken before the table moves into the commitment.
    let row_base = if check && assignment[0] != F::ONE {
        None
    } else {
        row_tables(shape, &assignment, check)
    };
    let Some(row_base) = row_base else {
        qsag_asm::volatile_fill(&mut assignment, F::ZERO);
        return Err(ZkHemError::Unsatisfied);
    };

    let cells = 1usize << layout.log_cells;
    let row_mask = Mask::sample(&mut stream, shape.log_rows, ROW_DEGREE);
    let col_mask = Mask::sample(&mut stream, layout.var_bits, COL_DEGREE);
    let mut table = vec![F::ZERO; cells];
    row_mask.write(&mut table, ROW_MASK_BITS, |i, j| {
        layout.row_mask_block(i, j)
    });
    col_mask.write(&mut table, COL_MASK_BITS, |i, j| {
        layout.col_mask_block(shape.log_rows, i, j)
    });
    table[..shape.num_vars].copy_from_slice(&assignment);
    let public_inputs =
        claimed.map_or_else(|| assignment[1..=shape.num_public].to_vec(), <[F]>::to_vec);
    for slot in &mut table[cells - layout.blind_cells..] {
        *slot = stream.next_base();
    }

    qsag_asm::volatile_fill(&mut assignment, F::ZERO);

    let mut polys = Vec::with_capacity(1 + COMPANIONS);
    polys.push(table);
    for _ in 0..COMPANIONS {
        polys.push((0..cells).map(|_| stream.next_base()).collect());
    }
    let mut salt_seed = [0u8; 32];
    for chunk in salt_seed.chunks_mut(8) {
        chunk.copy_from_slice(&stream.next_base().to_le_bytes());
    }
    let (commitment, mut state) =
        whir_commit_batch_secret_with_schedule(polys, &salt_seed, &layout.schedule);
    qsag_asm::volatile_fill(&mut salt_seed, 0u8);

    let mut tr = start_transcript(shape, &layout, statement, &public_inputs, &commitment);

    // 1. Masked row sumcheck.
    let tau = squeeze_point(&mut tr, b"ZKHEM_TAU", shape.log_rows);
    let row_libra = row_mask.libra();
    let row_mask_sum = row_libra.sum();
    tr.absorb_ext4(b"ZKHEM_ROW_MASK_SUM", row_mask_sum);
    let rho1 = NonzeroChallenge::squeeze(&mut tr, b"ZKHEM_RHO1").get();
    let (row_rounds, rx, row_values) = row_sumcheck(
        &mut tr,
        &tau,
        shape.num_sbox,
        row_base,
        Some((&row_libra, rho1)),
    );
    if !mask_rows_full_rank(shape, &rx) {
        qsag_asm::volatile_fill(&mut state.salt_seed, 0u8);
        for secret in state
            .hypercube_evals
            .iter_mut()
            .chain(&mut state.codewords_0)
        {
            qsag_asm::volatile_fill(secret, F::ZERO);
        }
        return Err(ZkHemError::MaskRankDeficient);
    }

    // 2. Row values.
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &row_values);

    // 3. Masked column sumcheck of `M(rx, y) Z(y)`.
    let combine = squeeze_point(&mut tr, b"ZKHEM_COMBINE", 3);
    let col_libra = col_mask.libra();
    let col_mask_sum = col_libra.sum();
    tr.absorb_ext4(b"ZKHEM_COL_MASK_SUM", col_mask_sum);
    let rho2 = NonzeroChallenge::squeeze(&mut tr, b"ZKHEM_RHO2").get();
    let tm = column_table(shape, &eq_table(&rx), &combine, 1 << layout.var_bits);
    // Neither `Z(ry)` nor the mask value there is sent.
    let (col_rounds, ry, matrix_at_point, _) = column_sumcheck(
        &mut tr,
        tm,
        &state.hypercube_evals[0][..1 << layout.var_bits],
        Some((&col_libra, rho2)),
    );

    // 4. One linear functional for everything that remains.
    let lambda = tr.squeeze_ext4(b"ZKHEM_LAMBDA");
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
    let mut kernel = vec![E::ZERO; cells + 2];
    for term in &terms {
        if term.point.iter().filter(|c| !c.is_zero()).count() <= 16 {
            add_sparse_point_kernel(&mut kernel, term.weight, &term.point);
        } else {
            let live = term
                .point
                .iter()
                .rposition(|c| !c.is_zero())
                .map_or(0, |p| p + 1);
            add_point_kernel(&mut kernel, term.weight, &term.point[..live]);
        }
    }
    drop(terms);

    // 5. Companion claims, then the blend challenge.
    let monos: Vec<Vec<F>> = state
        .hypercube_evals
        .iter()
        .map(|t| hypercube_to_monomial_coeffs(t))
        .collect();
    let functional = |mono: &[F]| {
        mono.iter()
            .zip(&kernel)
            .fold(E::ZERO, |acc, (&c, &k)| acc + k.mul_base(c))
    };
    let value = functional(&monos[0]);
    let companion_claims: [E; COMPANIONS] = core::array::from_fn(|j| functional(&monos[1 + j]));
    tr.absorb_ext4_slice(b"ZKHEM_COMPANION_CLAIMS", &companion_claims);
    let beta = PrimitiveChallenge::squeeze(&mut tr, b"ZKHEM_BETA").get();
    let mut scalars = vec![E::ONE];
    let mut claim = value;
    for &sigma in &companion_claims {
        let s = scalars[scalars.len() - 1] * beta;
        claim += s * sigma;
        scalars.push(s);
    }
    let opening = whir_open_blend(&state, &scalars, &monos, kernel, claim, &mut tr);
    let mut monos = monos;
    qsag_asm::volatile_fill(&mut state.salt_seed, 0u8);
    for secret in monos
        .iter_mut()
        .chain(&mut state.hypercube_evals)
        .chain(&mut state.codewords_0)
    {
        qsag_asm::volatile_fill(secret, F::ZERO);
    }

    Ok(ZkHemProof {
        commitment,
        row_mask_sum,
        row_rounds,
        row_values,
        col_mask_sum,
        col_rounds,
        companion_claims,
        opening,
    })
}

// ============================================================================
// Verifier
// ============================================================================

/// Replays one masked sumcheck; returns the final claim and the challenge point.
fn verify_sumcheck(
    tr: &mut FiatShamirTranscript<InstanceBound>,
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
        tr.absorb_ext4_slice(label, round);
        let c = tr.squeeze_ext4(label);
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
    let row_term = |i: usize| {
        let mut row = E::ZERO;
        for (m, &r) in [&shape.a, &shape.b, &shape.c].into_iter().zip(combine) {
            let inner = m
                .row(i)
                .fold(E::ZERO, |acc, (col, val)| acc + cols[col].mul_base(val));
            row += r * inner;
        }
        eq_rx[i] * row
    };
    #[cfg(feature = "std")]
    if eq_rx.len() >= 1 << 14 && crate::parallel_workers() > 1 {
        let idx: Vec<usize> = (0..eq_rx.len()).collect();
        return crate::map_chunks_bounded_with_limit(&idx, crate::parallel_workers(), |chunk| {
            chunk.iter().fold(E::ZERO, |acc, &i| acc + row_term(i))
        })
        .into_iter()
        .fold(E::ZERO, |acc, part| acc + part);
    }
    (0..eq_rx.len()).fold(E::ZERO, |acc, i| acc + row_term(i))
}

/// Verify a zk-Hem proof for `shape` with the given public inputs, bound to `statement`.
pub fn verify(
    shape: &Shape,
    public_inputs: &[F],
    statement: &[u8],
    regime: WhirSecurityRegime,
    proof: &ZkHemProof,
) -> bool {
    let Some(layout) = Layout::new(shape, regime) else {
        return false;
    };
    if proof.row_rounds.len() != shape.log_rows
        || proof.col_rounds.len() != layout.var_bits
        || public_inputs.len() != shape.num_public
    {
        return false;
    }
    let mut tr = start_transcript(shape, &layout, statement, public_inputs, &proof.commitment);

    let tau = squeeze_point(&mut tr, b"ZKHEM_TAU", shape.log_rows);
    tr.absorb_ext4(b"ZKHEM_ROW_MASK_SUM", proof.row_mask_sum);
    let rho1 = NonzeroChallenge::squeeze(&mut tr, b"ZKHEM_RHO1").get();
    let Some((row_final, rx)) = verify_sumcheck(
        &mut tr,
        b"ZKHEM_ROW_ROUND",
        &proof.row_rounds,
        ROW_DEGREE,
        rho1 * proof.row_mask_sum,
    ) else {
        return false;
    };
    let [va, vb, vc] = proof.row_values;
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &proof.row_values);
    let gate = eq_eval(&tau, &rx) * row_gate(prefix_indicator(&rx, shape.num_sbox), va, vb, vc);
    // The value the committed row mask must take at `rx`.
    let row_mask_at_point = (row_final - gate) * rho1.inv();

    let combine = squeeze_point(&mut tr, b"ZKHEM_COMBINE", 3);
    tr.absorb_ext4(b"ZKHEM_COL_MASK_SUM", proof.col_mask_sum);
    let rho2 = NonzeroChallenge::squeeze(&mut tr, b"ZKHEM_RHO2").get();
    let col_claim = combine[0] * va + combine[1] * vb + combine[2] * vc;
    let Some((col_final, ry)) = verify_sumcheck(
        &mut tr,
        b"ZKHEM_COL_ROUND",
        &proof.col_rounds,
        COL_DEGREE,
        col_claim + rho2 * proof.col_mask_sum,
    ) else {
        return false;
    };

    let lambda = tr.squeeze_ext4(b"ZKHEM_LAMBDA");
    let terms = claim_terms(&ClaimInputs {
        layout: &layout,
        log_rows: shape.log_rows,
        num_public: shape.num_public,
        rx: &rx,
        ry: &ry,
        lambda,
        rho2,
        matrix_at_point: matrix_at(shape, &rx, &ry, &combine),
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

    tr.absorb_ext4_slice(b"ZKHEM_COMPANION_CLAIMS", &proof.companion_claims);
    let beta = PrimitiveChallenge::squeeze(&mut tr, b"ZKHEM_BETA").get();
    let mut scalars = vec![E::ONE];
    let mut claim = value;
    for &sigma in &proof.companion_claims {
        let s = scalars[scalars.len() - 1] * beta;
        claim += s * sigma;
        scalars.push(s);
    }
    whir_verify_blend(
        &proof.commitment,
        layout.log_cells,
        &scalars,
        &terms,
        claim,
        &proof.opening,
        &mut tr,
        &layout.schedule,
    )
}

/// Non-hiding Hem proof. Use only when revealing the assignment is acceptable.
/// Public inputs are checked in the column sumcheck before the single-point opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicHemProof {
    pub commitment: CanopyCommitment,
    pub row_rounds: Vec<Vec<E>>,
    pub row_values: [E; 3],
    pub col_rounds: Vec<Vec<E>>,
    pub evaluation: E,
    pub opening: HemWhirOpeningProof,
}

fn public_layout(shape: &Shape, regime: WhirSecurityRegime) -> Option<Layout> {
    let var_bits = shape
        .num_vars
        .checked_next_power_of_two()?
        .trailing_zeros()
        .max(2) as usize;
    (regime.meets_qrom_128_floor() && var_bits <= MAX_PCS_NUM_VARS).then(|| Layout {
        log_cells: var_bits,
        var_bits,
        blind_cells: 0,
        schedule: regime.schedule(var_bits),
    })
}

impl PublicHemProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = self.commitment.to_bytes().to_vec();
        for v in self
            .row_rounds
            .iter()
            .flatten()
            .chain(&self.row_values)
            .chain(self.col_rounds.iter().flatten())
            .chain(core::iter::once(&self.evaluation))
        {
            out.extend_from_slice(&v.to_le_bytes());
        }
        self.opening.push_bytes(&mut out);
        out
    }
    /// Canonical decoding for a public relation; rejects trailing bytes.
    pub fn from_bytes(bytes: &[u8], shape: &Shape, regime: WhirSecurityRegime) -> Option<Self> {
        let layout = public_layout(shape, regime)?;
        let (commitment, mut pos) = CanopyCommitment::from_bytes_canonical(bytes)?;
        let mut take = || -> Option<E> {
            let chunk = bytes.get(pos..pos + 32)?.try_into().ok()?;
            pos += 32;
            E::from_le_bytes_canonical(chunk)
        };
        let row_rounds = (0..shape.log_rows)
            .map(|_| (0..=ROW_DEGREE).map(|_| take()).collect())
            .collect::<Option<_>>()?;
        let row_values = [take()?, take()?, take()?];
        let col_rounds = (0..layout.var_bits)
            .map(|_| (0..=COL_DEGREE).map(|_| take()).collect())
            .collect::<Option<_>>()?;
        let evaluation = take()?;
        let (opening, used) = HemWhirOpeningProof::from_bytes_canonical(&bytes[pos..])?;
        (pos + used == bytes.len()).then_some(Self {
            commitment,
            row_rounds,
            row_values,
            col_rounds,
            evaluation,
            opening,
        })
    }
}

fn public_transcript(
    shape: &Shape,
    layout: &Layout,
    statement: &[u8],
    public: &[F],
    commitment: &CanopyCommitment,
) -> FiatShamirTranscript<InstanceBound> {
    let bytes: Vec<u8> = public.iter().flat_map(|v| v.to_le_bytes()).collect();
    FiatShamirTranscript::new()
        .bind_relation(b"QSAG.HEM.PUBLIC/v1", &shape.digest(), &layout.schedule)
        .bind_instance(&[statement, &bytes, &commitment.to_bytes()])
}

/// Commit one assignment table on its tight hypercube, without hiding masks, companions,
/// or opening blinders. This intentionally reveals witness information. Private callers
/// must use [`prove`]. `seed` supplies leaf salts; secrecy is not required in this mode.
pub fn prove_public(
    shape: &Shape,
    assignment: Vec<F>,
    statement: &[u8],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
) -> Result<PublicHemProof, ZkHemError> {
    prove_public_inner(shape, assignment, statement, regime, seed, true, None)
}

fn prove_public_inner(
    shape: &Shape,
    mut assignment: Vec<F>,
    statement: &[u8],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
    check: bool,
    claimed: Option<&[F]>,
) -> Result<PublicHemProof, ZkHemError> {
    let layout = public_layout(shape, regime).ok_or(ZkHemError::RelationTooLarge)?;
    if assignment.len() != shape.num_vars || (check && assignment.first() != Some(&F::ONE)) {
        return Err(ZkHemError::Unsatisfied);
    }
    let public = claimed.map_or_else(|| assignment[1..=shape.num_public].to_vec(), <[F]>::to_vec);
    let row_base = row_tables(shape, &assignment, check).ok_or(ZkHemError::Unsatisfied)?;
    assignment.resize(1 << layout.var_bits, F::ZERO);
    let (commitment, state) =
        crate::pcs::whir_commit_owned_with_schedule(assignment, seed, &layout.schedule);
    let mut tr = public_transcript(shape, &layout, statement, &public, &commitment);
    let tau = squeeze_point(&mut tr, b"ZKHEM_TAU", shape.log_rows);
    let (row_rounds, rx, row_values) = row_sumcheck(&mut tr, &tau, shape.num_sbox, row_base, None);
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &row_values);
    let combine = squeeze_point(&mut tr, b"ZKHEM_COMBINE", 3);
    // Bind the constant/public cells in the same degree-two column sumcheck. The
    // assignment was committed before lambda, so erroneous cells cannot cancel at will.
    let lambda = tr.squeeze_ext4(b"HEM_PUBLIC_CELLS");
    let mut tm = column_table(shape, &eq_table(&rx), &combine, 1 << layout.var_bits);
    let mut weight = lambda;
    for slot in tm.iter_mut().take(shape.num_public + 1) {
        *slot += weight;
        weight *= lambda;
    }
    let (col_rounds, ry, _, evaluation) =
        column_sumcheck(&mut tr, tm, &state.hypercube_evals[0], None);
    let opening = crate::pcs::whir_open(&state, &ry, evaluation, &mut tr);
    Ok(PublicHemProof {
        commitment,
        row_rounds,
        row_values,
        col_rounds,
        evaluation,
        opening,
    })
}

/// Verify the explicitly non-hiding proof, with a domain distinct from private zk-Hem.
pub fn verify_public(
    shape: &Shape,
    public: &[F],
    statement: &[u8],
    regime: WhirSecurityRegime,
    proof: &PublicHemProof,
) -> bool {
    let Some(layout) = public_layout(shape, regime) else {
        return false;
    };
    if public.len() != shape.num_public
        || proof.row_rounds.len() != shape.log_rows
        || proof.col_rounds.len() != layout.var_bits
    {
        return false;
    }
    let mut tr = public_transcript(shape, &layout, statement, public, &proof.commitment);
    let tau = squeeze_point(&mut tr, b"ZKHEM_TAU", shape.log_rows);
    let Some((row_final, rx)) = verify_sumcheck(
        &mut tr,
        b"ZKHEM_ROW_ROUND",
        &proof.row_rounds,
        ROW_DEGREE,
        E::ZERO,
    ) else {
        return false;
    };
    let [a, b, c] = proof.row_values;
    if row_final != eq_eval(&tau, &rx) * row_gate(prefix_indicator(&rx, shape.num_sbox), a, b, c) {
        return false;
    }
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &proof.row_values);
    let combine = squeeze_point(&mut tr, b"ZKHEM_COMBINE", 3);
    let lambda = tr.squeeze_ext4(b"HEM_PUBLIC_CELLS");
    let mut claim = combine[0] * a + combine[1] * b + combine[2] * c;
    let mut weight = lambda;
    for v in core::iter::once(&F::ONE).chain(public) {
        claim += weight.mul_base(*v);
        weight *= lambda;
    }
    let Some((col_final, ry)) = verify_sumcheck(
        &mut tr,
        b"ZKHEM_COL_ROUND",
        &proof.col_rounds,
        COL_DEGREE,
        claim,
    ) else {
        return false;
    };
    let mut matrix = matrix_at(shape, &rx, &ry, &combine);
    let mut weight = lambda;
    for cell in 0..=shape.num_public {
        // `eq(ry, cell)`: the constant and public-input cells of the column sumcheck.
        let eq = ry.iter().enumerate().fold(E::ONE, |acc, (bit, &r)| {
            acc * if (cell >> bit) & 1 == 1 {
                r
            } else {
                E::ONE - r
            }
        });
        matrix += weight * eq;
        weight *= lambda;
    }
    if col_final != matrix * proof.evaluation {
        return false;
    }
    crate::pcs::whir_verify_with_schedule(
        &proof.commitment,
        layout.var_bits,
        &ry,
        proof.evaluation,
        &proof.opening,
        &mut tr,
        &layout.schedule,
    )
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::super::relation::{ConstraintSystem, Lc, MASK_ROWS, sponge12, sponge12_native};
    use super::super::{Pad, pad_map};
    use super::*;

    const REGIMES: [WhirSecurityRegime; 2] = [
        WhirSecurityRegime::BciksJohnsonQrom128,
        WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
    ];

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    /// Knowledge of a sponge preimage `(x0, x1)` of a public digest lane, with `x0` Boolean
    /// and a public product `x0 * x1`.
    fn preimage_relation(x: [u64; 2]) -> (Shape, Vec<F>) {
        let honest = [f(1), f(77)];
        let digest = sponge12_native(&honest)[0];
        let mut cs = ConstraintSystem::new();
        let v: [Lc; 2] = core::array::from_fn(|i| cs.alloc(f(x[i])).into());
        cs.enforce_boolean(&v[0]);
        let prod = cs.mul(&v[0], &v[1]);
        cs.enforce_zero(Lc::from(prod).plus_const(F::ZERO - honest[0] * honest[1]));
        let out = sponge12(&mut cs, &v);
        cs.enforce_zero(out[0].plus_const(F::ZERO - digest));
        cs.finish()
    }

    fn test_transcript(tag: &[u8]) -> FiatShamirTranscript<InstanceBound> {
        let schedule = WhirSecurityRegime::BciksJohnsonQrom128.schedule(4);
        FiatShamirTranscript::new()
            .bind_relation(b"QSAG.ZKHEM.TEST/v1", &[0; 32], &schedule)
            .bind_instance(&[tag])
    }

    /// Row round polynomials straight from the definition: `eq` and the selector as
    /// tables, every table folded explicitly, ten evaluation points per pair.
    fn reference_row_rounds(
        tau: &[E],
        num_sbox: usize,
        base: &[Vec<F>; 3],
        rx: &[E],
    ) -> (Vec<Vec<E>>, [E; 3]) {
        let lift = |t: &Vec<F>| t.iter().map(|&v| E::from_base(v)).collect::<Vec<E>>();
        let selector = (0..1usize << tau.len())
            .map(|i| if i < num_sbox { E::ONE } else { E::ZERO })
            .collect();
        let mut tables = [
            build_eq_table_ext4(tau),
            selector,
            lift(&base[0]),
            lift(&base[1]),
            lift(&base[2]),
        ];
        let mut rounds = Vec::new();
        for &r in rx {
            let mut evals = [E::ZERO; ROW_DEGREE + 1];
            for i in 0..tables[0].len() / 2 {
                for (k, slot) in evals.iter_mut().enumerate() {
                    let at =
                        |t: &Vec<E>| t[2 * i] + E::from_u64(k as u64) * (t[2 * i + 1] - t[2 * i]);
                    *slot += at(&tables[0])
                        * row_gate(
                            at(&tables[1]),
                            at(&tables[2]),
                            at(&tables[3]),
                            at(&tables[4]),
                        );
                }
            }
            rounds.push(evals_to_coeffs(&evals));
            for t in &mut tables {
                *t = t
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|&[lo, hi]| lo + r * (hi - lo))
                    .collect();
            }
        }
        (rounds, [tables[2][0], tables[3][0], tables[4][0]])
    }

    #[test]
    fn row_sumcheck_matches_the_direct_definition() {
        let mut stream = SeedStream::new(b"QSAG.ZKHEM.TEST.ROWS/v1", &[3; 32]);
        // Boundaries: none, odd, even, every row, and a table large enough for the workers.
        for (log_rows, num_sbox) in [(4, 0), (4, 5), (4, 6), (4, 16), (6, 37), (14, 9001)] {
            let rows = 1usize << log_rows;
            let mut base: [Vec<F>; 3] =
                core::array::from_fn(|_| (0..rows).map(|_| stream.next_base()).collect());
            // Pairs with zero A and C, at several fold depths, on both sides of the boundary.
            for i in (0..rows).filter(|i| (i / 4) % 3 == 0) {
                base[0][i] = F::ZERO;
                base[2][i] = F::ZERO;
            }
            let tau: Vec<E> = (0..log_rows).map(|_| stream.next_ext4()).collect();
            let libra = LibraMask::from_stream(&mut stream, log_rows, ROW_DEGREE);
            let rho = stream.next_ext4();
            for mask in [None, Some((&libra, rho))] {
                let mut tr = test_transcript(b"rows");
                let (rounds, rx, values) =
                    row_sumcheck(&mut tr, &tau, num_sbox, base.clone(), mask);
                let (mut expected, expected_values) =
                    reference_row_rounds(&tau, num_sbox, &base, &rx);
                if let Some((libra, rho)) = mask {
                    for (i, round) in expected.iter_mut().enumerate() {
                        for (c, g) in round.iter_mut().zip(libra.round_poly(&rx[..i])) {
                            *c += rho * g;
                        }
                    }
                }
                assert_eq!(
                    rounds, expected,
                    "log_rows {log_rows}, {num_sbox} S-box rows"
                );
                assert_eq!(values, expected_values);
            }
        }
    }

    #[test]
    fn column_sumcheck_matches_the_direct_definition() {
        let mut stream = SeedStream::new(b"QSAG.ZKHEM.TEST.COLS/v1", &[4; 32]);
        for bits in [1usize, 2, 5, 14] {
            let matrix: Vec<E> = (0..1 << bits).map(|_| stream.next_ext4()).collect();
            let z: Vec<F> = (0..1 << bits).map(|_| stream.next_base()).collect();
            let libra = LibraMask::from_stream(&mut stream, bits, COL_DEGREE);
            let rho = stream.next_ext4();
            for mask in [None, Some((&libra, rho))] {
                let mut tr = test_transcript(b"columns");
                let (rounds, ry, matrix_at_point, value) =
                    column_sumcheck(&mut tr, matrix.clone(), &z, mask);
                let mut tm = matrix.clone();
                let mut tz: Vec<E> = z.iter().map(|&v| E::from_base(v)).collect();
                for (i, (round, &r)) in rounds.iter().zip(&ry).enumerate() {
                    let mut evals = [E::ZERO; COL_DEGREE + 1];
                    for (m, z) in tm.as_chunks::<2>().0.iter().zip(tz.as_chunks::<2>().0) {
                        for (k, slot) in evals.iter_mut().enumerate() {
                            let k = E::from_u64(k as u64);
                            *slot += (m[0] + k * (m[1] - m[0])) * (z[0] + k * (z[1] - z[0]));
                        }
                    }
                    let mut expected = evals_to_coeffs(&evals);
                    if let Some((libra, rho)) = mask {
                        for (c, g) in expected.iter_mut().zip(libra.round_poly(&ry[..i])) {
                            *c += rho * g;
                        }
                    }
                    assert_eq!(round, &expected, "{bits} variables, round {i}");
                    for t in [&mut tm, &mut tz] {
                        *t = t
                            .as_chunks::<2>()
                            .0
                            .iter()
                            .map(|&[lo, hi]| lo + r * (hi - lo))
                            .collect();
                    }
                }
                assert_eq!((matrix_at_point, value), (tm[0], tz[0]));
            }
        }
    }

    #[test]
    fn parallel_tables_match_their_serial_definitions() {
        let mut stream = SeedStream::new(b"QSAG.ZKHEM.TEST.TABLES/v1", &[5; 32]);
        let point: Vec<E> = (0..15).map(|_| stream.next_ext4()).collect();
        for n in [0, 1, 11, 12, 13, 15] {
            assert_eq!(eq_table(&point[..n]), build_eq_table_ext4(&point[..n]));
        }
        // S-box and multiplication rows that reach back to an early variable and to a
        // public input, enough of them for several workers.
        let mut cs = ConstraintSystem::new();
        let public: Lc = cs.public_input(f(5)).into();
        let first: Lc = cs.alloc(f(3)).into();
        let mut prev = first.clone();
        for _ in 0..6000 {
            let y: Lc = cs.sbox7(&prev.plus(&public)).into();
            prev = cs.mul(&y, &first).into();
            cs.enforce_boolean(&Lc::constant(F::ONE));
        }
        let (shape, z) = cs.finish();
        assert!(shape.num_rows() > PAR_MIN && shape.is_satisfied(&z));
        let eq = eq_table(&point[..shape.log_rows]);
        let combine = &point[..3];
        let cells = shape.num_vars.next_power_of_two();
        let mut expected = vec![E::ZERO; cells];
        for (i, &e) in eq.iter().enumerate() {
            for (m, &r) in [&shape.a, &shape.b, &shape.c].into_iter().zip(combine) {
                for (col, val) in m.row(i) {
                    expected[col] += (r * e).mul_base(val);
                }
            }
        }
        assert_eq!(column_table(&shape, &eq, combine, cells), expected);
        let tables = row_tables(&shape, &z, true).unwrap();
        for (table, m) in tables.iter().zip([&shape.a, &shape.b, &shape.c]) {
            let expected: Vec<F> = (0..shape.num_rows()).map(|i| m.row_dot(i, &z)).collect();
            assert_eq!(table, &expected);
        }
        let mut bad = z;
        bad[2] += F::ONE;
        assert!(row_tables(&shape, &bad, true).is_none());
        assert!(row_tables(&shape, &bad, false).is_some());
    }

    #[test]
    fn public_mode_checks_public_inputs_and_the_relation() {
        let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let mut cs = ConstraintSystem::new();
        let x: Lc = cs.public_input(f(9)).into();
        let y: Lc = cs.public_input(f(81)).into();
        let w: Lc = cs.alloc(f(3)).into();
        cs.enforce_mul(w.clone(), w, x.clone());
        cs.enforce_mul(x.clone(), x, y);
        let (shape, z) = cs.finish();
        let proof = prove_public(&shape, z, b"public", regime, &[5; 32]).unwrap();
        assert!(verify_public(
            &shape,
            &[f(9), f(81)],
            b"public",
            regime,
            &proof
        ));
        for public in [
            &[f(9), f(82)][..],
            &[f(10), f(81)],
            &[f(81), f(9)],
            &[f(9)],
            &[f(9), f(81), f(0)],
        ] {
            assert!(!verify_public(&shape, public, b"public", regime, &proof));
        }
        // The same proof under another regime, another relation, or the hiding verifier's
        // transcript domain.
        assert!(!verify_public(
            &shape,
            &[f(9), f(81)],
            b"public",
            WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
            &proof
        ));
        let (other, _) = preimage_relation([1, 77]);
        assert!(!verify_public(
            &other,
            &[f(9), f(81)],
            b"public",
            regime,
            &proof
        ));
        assert!(!verify_public(&other, &[], b"public", regime, &proof));
    }

    /// Flip one bit in every 8-byte word of a serialized public proof: commitment, each
    /// sumcheck coefficient, the claimed values, and everything the opening carries
    /// (out-of-domain values, fold polynomials, nonces, leaf values, salts, Merkle siblings).
    #[test]
    fn every_serialized_word_of_a_public_proof_is_bound() {
        for regime in [
            WhirSecurityRegime::BciksJohnsonQrom128,
            WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
        ] {
            let mut cs = ConstraintSystem::new();
            let public: Lc = cs.public_input(f(11)).into();
            let mut prev: Lc = cs.alloc(f(2)).into();
            for _ in 0..40 {
                prev = cs.sbox7(&prev.plus(&public)).into();
                prev = cs.mul(&prev, &public).into();
            }
            // Enough cells that the opening does not query every leaf.
            for i in 0..4000 {
                cs.alloc(f(i));
            }
            let (shape, z) = cs.finish();
            let proof = prove_public(&shape, z, b"sweep", regime, &[6; 32]).unwrap();
            assert!(!proof.opening.round0_multiproof.auth_siblings.is_empty());
            let bytes = proof.to_bytes();
            assert!(verify_public(&shape, &[f(11)], b"sweep", regime, &proof));
            let mut decoded = 0usize;
            for pos in (0..bytes.len()).step_by(8) {
                let mut bad = bytes.clone();
                bad[pos] ^= 1;
                if let Some(bad) = PublicHemProof::from_bytes(&bad, &shape, regime) {
                    decoded += 1;
                    assert!(
                        !verify_public(&shape, &[f(11)], b"sweep", regime, &bad),
                        "{regime:?}: byte {pos} of {} is not bound",
                        bytes.len()
                    );
                }
            }
            // Most single-bit changes are still canonical encodings and reach the verifier.
            assert!(
                decoded * 2 > bytes.len() / 8,
                "{decoded} of {}",
                bytes.len() / 8
            );
            std::println!(
                "PUBLIC_SWEEP {regime:?} bytes={} verified_tampers={decoded}",
                bytes.len()
            );
        }
    }

    #[test]
    fn public_mode_rejects_a_corrupt_authentication_path() {
        let mut cs = ConstraintSystem::new();
        for i in 0..4096 {
            cs.alloc(f(i));
        }
        let (shape, z) = cs.finish();
        let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let mut proof = prove_public(&shape, z, b"merkle", regime, &[7; 32]).unwrap();
        assert!(verify_public(&shape, &[], b"merkle", regime, &proof));
        assert!(!proof.opening.round0_multiproof.auth_siblings.is_empty());
        proof.opening.round0_multiproof.auth_siblings[0][0] ^= 1;
        assert!(!verify_public(&shape, &[], b"merkle", regime, &proof));
    }

    #[test]
    fn public_mode_binds_witness_statement_cells_and_openings() {
        for regime in REGIMES
            .into_iter()
            .chain([WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128])
        {
            let (shape, z) = preimage_relation([1, 77]);
            let proof = prove_public(&shape, z, b"public", regime, &[1; 32]).unwrap();
            assert!(verify_public(&shape, &[], b"public", regime, &proof));
            assert!(!verify_public(&shape, &[], b"changed", regime, &proof));
            let bytes = proof.to_bytes();
            assert_eq!(
                PublicHemProof::from_bytes(&bytes, &shape, regime),
                Some(proof.clone())
            );
            assert!(
                PublicHemProof::from_bytes(&bytes[..bytes.len() - 1], &shape, regime).is_none()
            );
            let mut trailing = bytes;
            trailing.push(0);
            assert!(PublicHemProof::from_bytes(&trailing, &shape, regime).is_none());
            let (_, bad) = preimage_relation([1, 78]);
            assert_eq!(
                prove_public(&shape, bad.clone(), b"public", regime, &[1; 32]),
                Err(ZkHemError::Unsatisfied)
            );
            let forged =
                prove_public_inner(&shape, bad, b"public", regime, &[1; 32], false, None).unwrap();
            assert!(!verify_public(&shape, &[], b"public", regime, &forged));
            let changes: &[fn(&mut PublicHemProof)] = &[
                |p| p.row_rounds[0][1] += E::ONE,
                |p| p.row_values[0] += E::ONE,
                |p| p.col_rounds[0][1] += E::ONE,
                |p| p.evaluation += E::ONE,
                |p| p.opening.stage0_ood_evals[0] += E::ONE,
                |p| p.opening.round0_vals[0] += F::ONE,
                |p| p.opening.round0_salts[0][0] ^= 1,
                |p| p.commitment.root[0] ^= 1,
            ];
            for change in changes {
                let mut bad = proof.clone();
                change(&mut bad);
                assert!(!verify_public(&shape, &[], b"public", regime, &bad));
            }
            let mut cs = ConstraintSystem::new();
            let public: Lc = cs.public_input(f(9)).into();
            let private: Lc = cs.alloc(f(3)).into();
            cs.enforce_mul(private.clone(), private, public);
            let (shape, z) = cs.finish();
            let claimed = [f(10)];
            let forged =
                prove_public_inner(&shape, z, b"public", regime, &[2; 32], true, Some(&claimed))
                    .unwrap();
            assert!(!verify_public(&shape, &claimed, b"public", regime, &forged));
        }
    }

    #[test]
    fn honest_proofs_verify_and_roundtrip_in_both_hash_regimes() {
        let (shape, z) = preimage_relation([1, 77]);
        for regime in REGIMES {
            let proof = prove(&shape, z.clone(), b"stmt", regime, &[7; 32]).unwrap();
            assert!(verify(&shape, &[], b"stmt", regime, &proof));
            let bytes = proof.to_bytes();
            let decoded = ZkHemProof::from_bytes(&bytes, &shape, regime).unwrap();
            assert_eq!(decoded, proof);
            assert!(ZkHemProof::from_bytes(&bytes[..bytes.len() - 1], &shape, regime).is_none());
            let mut longer = bytes.clone();
            longer.push(0);
            assert!(ZkHemProof::from_bytes(&longer, &shape, regime).is_none());
            assert!(!verify(&shape, &[], b"other", regime, &proof));
        }
    }

    #[test]
    fn prover_refuses_and_verifier_rejects_a_false_witness() {
        let (shape, bad) = preimage_relation([1, 78]);
        let regime = REGIMES[0];
        assert_eq!(
            prove(&shape, bad.clone(), b"s", regime, &[1; 32]),
            Err(ZkHemError::Unsatisfied)
        );
        let forged = prove_inner(&shape, bad, b"s", regime, &[1; 32], false).unwrap();
        assert!(!verify(&shape, &[], b"s", regime, &forged));
    }

    #[test]
    fn every_proof_field_is_bound() {
        let (shape, z) = preimage_relation([1, 77]);
        let regime = REGIMES[0];
        let proof = prove(&shape, z, b"s", regime, &[3; 32]).unwrap();
        assert!(verify(&shape, &[], b"s", regime, &proof));
        type Mutation = fn(&mut ZkHemProof, &dyn Fn(&mut E));
        let bump = |x: &mut E| *x += E::ONE;
        let mutations: Vec<Mutation> = vec![
            |p, b| b(&mut p.row_mask_sum),
            |p, b| b(&mut p.row_rounds[0][3]),
            |p, b| b(&mut p.row_rounds.last_mut().unwrap()[9]),
            |p, b| b(&mut p.row_values[0]),
            |p, b| b(&mut p.row_values[1]),
            |p, b| b(&mut p.row_values[2]),
            |p, b| b(&mut p.col_mask_sum),
            |p, b| b(&mut p.col_rounds[1][2]),
            |p, b| b(&mut p.companion_claims[0]),
            |p, b| b(&mut p.companion_claims[3]),
            |p, b| b(&mut p.opening.stage0_ood_evals[0]),
            |p, b| b(p.opening.final_coeffs.last_mut().unwrap()),
            |p, _| p.opening.round0_vals[0] += F::ONE,
            |p, _| p.opening.round0_salts[0][0] ^= 1,
            |p, _| p.commitment.root[0] ^= 1,
        ];
        for (k, mutate) in mutations.iter().enumerate() {
            let mut bad = proof.clone();
            mutate(&mut bad, &bump);
            assert!(
                !verify(&shape, &[], b"s", regime, &bad),
                "mutation {k} accepted"
            );
        }
        // A balanced change of a round polynomial keeps `p(0) + p(1)` but moves `p(c)`.
        let mut bad = proof.clone();
        bad.row_rounds[2][1] += E::ONE;
        bad.row_rounds[2][2] -= E::ONE;
        assert!(!verify(&shape, &[], b"s", regime, &bad));
    }

    #[test]
    fn proofs_for_one_relation_do_not_verify_for_another() {
        let (shape, z) = preimage_relation([1, 77]);
        let mut cs = ConstraintSystem::new();
        let v: [Lc; 2] = core::array::from_fn(|i| cs.alloc(f([1, 77][i])).into());
        cs.enforce_boolean(&v[0]);
        let _ = cs.mul(&v[0], &v[1]);
        let out = sponge12(&mut cs, &v);
        cs.enforce_zero(out[1].plus_const(F::ZERO - sponge12_native(&[f(1), f(77)])[1]));
        let (other, _) = cs.finish();
        let regime = REGIMES[0];
        let proof = prove(&shape, z, b"s", regime, &[9; 32]).unwrap();
        assert_eq!(Layout::new(&shape, regime), Layout::new(&other, regime));
        assert!(!verify(&other, &[], b"s", regime, &proof));
    }

    #[test]
    fn public_inputs_are_checked_against_the_committed_cells() {
        let build = |x: u64, y: u64| {
            let mut cs = ConstraintSystem::new();
            let out = cs.public_input(f(y));
            let tag = cs.public_input(f(4));
            let w: Lc = cs.alloc(f(x)).into();
            let seventh = cs.sbox7(&w.plus(&tag.into()));
            cs.enforce_equal(&seventh.into(), &out.into());
            cs.finish()
        };
        let y = crate::sponge::poseidon2_sbox7(f(3 + 4)).to_canonical_u64();
        let (shape, z) = build(3, y);
        assert_eq!(shape.num_public, 2);
        let regime = REGIMES[1];
        let publics = [f(y), f(4)];
        let proof = prove(&shape, z, b"s", regime, &[17; 32]).unwrap();
        assert!(verify(&shape, &publics, b"s", regime, &proof));
        assert!(!verify(&shape, &[f(y + 1), f(4)], b"s", regime, &proof));
        assert!(!verify(&shape, &[f(y), f(5)], b"s", regime, &proof));
        assert!(!verify(&shape, &[f(y)], b"s", regime, &proof));
        // A prover whose committed public cells differ from the claimed values is rejected
        // even when its own assignment is consistent.
        let y5 = crate::sponge::poseidon2_sbox7(f(5 + 4)).to_canonical_u64();
        let (shape5, z5) = build(5, y5);
        assert_eq!(shape5, shape);
        let other = prove(&shape, z5, b"s", regime, &[18; 32]).unwrap();
        assert!(verify(&shape, &[f(y5), f(4)], b"s", regime, &other));
        assert!(!verify(&shape, &publics, b"s", regime, &other));
        // Bind the claimed values into the transcript while committing different cells: only
        // the cell terms of the batched functional can reject this.
        let (_, z5) = build(5, y5);
        let lying =
            prove_with_claimed_publics(&shape, z5, b"s", regime, &[19; 32], true, Some(&publics))
                .unwrap();
        assert!(!verify(&shape, &publics, b"s", regime, &lying));
        assert!(!verify(&shape, &[f(y5), f(4)], b"s", regime, &lying));
    }

    #[test]
    fn layout_reserves_a_blinder_for_every_opened_stage0_symbol() {
        let (shape, _) = preimage_relation([1, 77]);
        for regime in REGIMES {
            let layout = Layout::new(&shape, regime).unwrap();
            let st0 = layout.schedule.stages[0];
            let proof =
                prove(&shape, preimage_relation([1, 77]).1, b"s", regime, &[5; 32]).unwrap();
            let opened_per_table = proof.opening.round0_vals.len() / (1 + COMPANIONS);
            assert!(opened_per_table <= layout.blind_cells);
            assert_eq!(layout.blind_cells, st0.num_queries << st0.step_vars);
            assert!(shape.num_vars <= 1 << layout.var_bits);
            assert!(
                layout.col_mask_block(shape.log_rows, layout.var_bits, 0) + layout.blind_cells
                    <= 1 << layout.log_cells
            );
        }
    }

    /// The masking rows are a bijection onto the revealed triple: for two different
    /// witnesses of one relation there are masking values giving the same `(Az, Bz, Cz)(rx)`.
    #[test]
    fn masking_rows_make_the_revealed_row_values_witness_independent() {
        let build = |x: u64| {
            let mut cs = ConstraintSystem::new();
            let v: Lc = cs.alloc(f(x)).into();
            let y = cs.sbox7(&v);
            let _ = cs.mul(&v, &y.into());
            cs.finish()
        };
        let (shape, mut z1) = build(3);
        let (shape2, mut z2) = build(5);
        assert_eq!(shape, shape2);
        let mut s = SeedStream::new(b"QSAG.TEST.ZKHEM", &[11; 32]);
        let rx: Vec<E> = (0..shape.log_rows).map(|_| s.next_ext4()).collect();
        assert!(mask_rows_full_rank(&shape, &rx));
        for slot in &mut z1[shape.mask_var_base..] {
            *slot = s.next_base();
        }
        let triple = |z: &[F]| -> [E; 3] {
            let eq = build_eq_table_ext4(&rx);
            [&shape.a, &shape.b, &shape.c].map(|m| {
                (0..shape.num_rows()).fold(E::ZERO, |acc, i| acc + eq[i].mul_base(m.row_dot(i, z)))
            })
        };
        let want = triple(&z1);
        let have = triple(&z2);
        let d: [E; 3] = core::array::from_fn(|i| want[i] - have[i]);
        let k: [E; 3] = core::array::from_fn(|g| corner_factor(&rx, shape.mask_row_base(g)));
        let e2 = d[1] * k[1].inv();
        let e3 = (d[2] - d[1] - d[0]) * k[2].inv();
        let e1 = (d[0] - k[2] * e3) * k[0].inv();
        let basis = CornerPadBasis::new(rx[0], rx[1]).unwrap();
        for (g, e) in [e1, e2, e3].into_iter().enumerate() {
            let Pad(cells) = basis.invert(e);
            z2[shape.mask_var_base + 4 * g..shape.mask_var_base + 4 * g + 4]
                .copy_from_slice(&cells);
        }
        assert!(shape.is_satisfied(&z1) && shape.is_satisfied(&z2));
        assert_ne!(z1[1], z2[1]);
        assert_eq!(triple(&z2), want);
        assert_eq!(MASK_ROWS, 12);
    }

    /// The blend of a base-field table with four companions is a bijection of the
    /// companions for a challenge outside the quadratic subfield: any target word is hit.
    #[test]
    fn four_companions_reach_every_blended_word() {
        let mut s = SeedStream::new(b"QSAG.TEST.ZKHEM", &[12; 32]);
        let beta = loop {
            if let Some(b) = PrimitiveChallenge::new(s.next_ext4()) {
                break b;
            }
        };
        for _ in 0..64 {
            let z = s.next_base();
            let target = s.next_ext4();
            let pad = super::super::pad_inv(beta, (target - E::from_base(z)) * beta.get().inv());
            assert_eq!(
                E::from_base(z) + beta.get() * pad_map(beta.get(), &pad),
                target
            );
        }
    }

    #[test]
    fn prefix_indicator_matches_the_table() {
        let mut s = SeedStream::new(b"QSAG.TEST.ZKHEM", &[13; 32]);
        let point: Vec<E> = (0..5).map(|_| s.next_ext4()).collect();
        let eq = build_eq_table_ext4(&point);
        for count in 0..=32 {
            let want = eq[..count].iter().fold(E::ZERO, |a, &b| a + b);
            assert_eq!(prefix_indicator(&point, count), want, "count {count}");
        }
    }
}
