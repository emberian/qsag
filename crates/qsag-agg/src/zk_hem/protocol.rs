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

use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use super::recursive_whir::{
    Backend as RecBackend, Base as RecBase, Correlated3WhirProof, Digest as RecDigest,
    Ext as RecExt, FixedPathWhirParams, FoldedEdgeSpec, FoldedLevelWhirProof,
    Native as RecNative, PublicRecursionCommitment, Transcript as RecTranscript,
    commit_for_recursion, commit_levels_for_recursion, f as rec_f, open_correlated3_for_recursion,
    prove_folded_level_for_recursion, verify_correlated3_gadget, verify_folded_level,
};
use super::relation::{HologramMeta, Poseidon2InteriorTemplate, Shape};
use super::{CornerPadBasis, LibraMask, NonzeroChallenge, PrimitiveChallenge, SeedStream, interp};
use crate::field::{Goldilocks, GoldilocksExt4, build_eq_table_ext4};
use crate::pcs::{
    CanopyCommitment, HemWhirOpeningProof, MAX_PCS_NUM_VARS, WeightedPoint, WhirSchedule,
    WhirSecurityRegime, add_point_kernel, hypercube_to_monomial_coeffs,
    whir_commit_batch_secret_with_schedule, whir_open_blend, whir_open_blend_from_state,
    whir_verify_blend,
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
    let (commitment, state) =
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
    for secret in &mut monos {
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

// ============================================================================
// Spark Matrix Hologram + LogUp-GKR (native and in-circuit verification)
// ============================================================================

/// Wire magic for [`HologramPublicProof`].
pub const HOLOGRAM_PUBLIC_WIRE_MAGIC: &[u8; 8] = b"QSAGHGP1";
/// Wire magic for [`ShapeVerifierKey`].
pub const SHAPE_VK_WIRE_MAGIC: &[u8; 8] = b"QSAGSVK1";

/// Degree of the Spark sparse-matrix evaluation sumcheck (`e_x * e_y * V`).
const SPARK_MAT_DEGREE: usize = 3;
/// Degree of each LogUp-GKR fractional-tree layer sumcheck (`eq * (p_0 q_1 + p_1 q_0 + beta q_0 q_1)`).
const GKR_LAYER_DEGREE: usize = 3;

/// Compact (`< 256` bytes) sublinear verifier key for a compiled [`ShapeHologram`].
///
/// Replaces the multi-megabyte [`Shape`] CSR during native and recursive verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShapeVerifierKey {
    pub shape_digest: [u8; 32],
    pub log_rows: usize,
    pub num_sbox: usize,
    pub num_vars: usize,
    pub num_public: usize,
    pub var_bits: usize,
    pub ell_nz: usize,
    pub hologram_meta: HologramMeta,
    pub regime: WhirSecurityRegime,
    pub hologram_comm: CanopyCommitment,
    pub rec_hologram_root: Option<RecDigest>,
}

impl ShapeVerifierKey {
    /// Variable count of each 4-slice half in the 2-poly native hologram commitment (`ell_nz + 2`).
    #[inline]
    pub fn native_pack_vars(&self) -> usize {
        self.ell_nz + 2
    }

    /// Variable count of the 8-slice single-poly recursive hologram commitment (`ell_nz + 3`).
    #[inline]
    pub fn pack_vars(&self) -> usize {
        self.ell_nz + 3
    }

    /// Check bounded geometry before decoding proofs or evaluating structured matrices.
    pub fn is_well_formed(&self) -> bool {
        if !self.regime.meets_qrom_128_floor()
            || !(4..=MAX_PCS_NUM_VARS).contains(&self.log_rows)
            || !(2..=MAX_PCS_NUM_VARS).contains(&self.var_bits)
            || self.ell_nz < self.log_rows.max(self.var_bits)
            || self.ell_nz > MAX_PCS_NUM_VARS - 2
            || self.num_vars == 0
            || self.num_vars > (1usize << self.var_bits)
            || self.num_public >= self.num_vars
            || self.num_sbox >= (1usize << self.log_rows)
            || (self.rec_hologram_root.is_some()
                && (!self.regime.uses_poseidon2_canopy() || self.ell_nz > MAX_PCS_NUM_VARS - 3))
        {
            return false;
        }
        let p = self.hologram_meta.poseidon2_perms;
        let blocks = self.hologram_meta.pub_var_blocks;
        if p > 0
            && (self.log_rows < 7
                || self.var_bits < 7
                || p > self.num_sbox / 128
                || blocks != (self.num_public + 1).div_ceil(128)
                || blocks
                    .checked_add(p)
                    .is_none_or(|n| n > self.num_vars / 128))
        {
            return false;
        }
        let stage = self.regime.schedule(self.native_pack_vars()).stages[0];
        usize::from(self.hologram_comm.log_leaves)
            == self.native_pack_vars() + stage.blowup.trailing_zeros() as usize - stage.step_vars
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(160);
        out.extend_from_slice(SHAPE_VK_WIRE_MAGIC);
        out.extend_from_slice(&self.shape_digest);
        out.push(self.log_rows as u8);
        out.extend_from_slice(&(self.num_sbox as u64).to_le_bytes());
        out.extend_from_slice(&(self.num_vars as u64).to_le_bytes());
        out.extend_from_slice(&(self.num_public as u64).to_le_bytes());
        out.push(self.var_bits as u8);
        out.push(self.ell_nz as u8);
        out.extend_from_slice(&(self.hologram_meta.poseidon2_perms as u64).to_le_bytes());
        out.extend_from_slice(&(self.hologram_meta.pub_var_blocks as u64).to_le_bytes());
        out.push(self.regime as u8);
        out.extend_from_slice(&self.hologram_comm.to_bytes());
        match self.rec_hologram_root {
            Some(r) => {
                out.push(1);
                for limb in r {
                    out.extend_from_slice(&limb.to_le_bytes());
                }
            }
            None => out.push(0),
        }
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.get(..8)? != SHAPE_VK_WIRE_MAGIC {
            return None;
        }
        let shape_digest: [u8; 32] = bytes.get(8..40)?.try_into().ok()?;
        let log_rows = *bytes.get(40)? as usize;
        let num_sbox =
            usize::try_from(u64::from_le_bytes(bytes.get(41..49)?.try_into().ok()?)).ok()?;
        let num_vars =
            usize::try_from(u64::from_le_bytes(bytes.get(49..57)?.try_into().ok()?)).ok()?;
        let num_public =
            usize::try_from(u64::from_le_bytes(bytes.get(57..65)?.try_into().ok()?)).ok()?;
        let var_bits = *bytes.get(65)? as usize;
        let ell_nz = *bytes.get(66)? as usize;
        let poseidon2_perms =
            usize::try_from(u64::from_le_bytes(bytes.get(67..75)?.try_into().ok()?)).ok()?;
        let pub_var_blocks =
            usize::try_from(u64::from_le_bytes(bytes.get(75..83)?.try_into().ok()?)).ok()?;
        let regime = WhirSecurityRegime::from_u8(*bytes.get(83)?)?;
        if !regime.meets_qrom_128_floor()
            || !(4..=MAX_PCS_NUM_VARS).contains(&log_rows)
            || !(2..=MAX_PCS_NUM_VARS).contains(&var_bits)
            || ell_nz < log_rows.max(var_bits)
            || ell_nz + 2 > MAX_PCS_NUM_VARS
        {
            return None;
        }
        let (hologram_comm, used) = CanopyCommitment::from_bytes_canonical(bytes.get(84..)?)?;
        let mut pos = 84 + used;
        let rec_tag = *bytes.get(pos)?;
        pos += 1;
        let rec_hologram_root = match rec_tag {
            0 => None,
            1 => {
                let mut root = [F::ZERO; 4];
                for slot in &mut root {
                    let chunk: [u8; 8] = bytes.get(pos..pos + 8)?.try_into().ok()?;
                    pos += 8;
                    *slot = F::from_le_bytes_canonical(chunk).ok()?;
                }
                Some(root)
            }
            _ => return None,
        };
        if pos != bytes.len() {
            return None;
        }
        let vk = Self {
            shape_digest,
            log_rows,
            num_sbox,
            num_vars,
            num_public,
            var_bits,
            ell_nz,
            hologram_meta: HologramMeta {
                poseidon2_perms,
                pub_var_blocks,
            },
            regime,
            hologram_comm,
            rec_hologram_root,
        };
        vk.is_well_formed().then_some(vk)
    }
}

/// Largest native hologram commitment (`ell_nz + 2` variables per polynomial) whose Stage-0
/// Reed-Solomon codewords stay cached between proofs: 256 MiB at this size. Above it each
/// opening re-encodes them, trading seconds per proof for gigabytes of resident memory.
const HOLOGRAM_ROUND0_CACHE_MAX_VARS: usize = 22;

/// Offline-compiled Spark matrix hologram for a fixed public [`Shape`].
pub struct ShapeHologram {
    vk: ShapeVerifierKey,
    row_idx: Arc<Vec<u32>>,
    col_idx: Arc<Vec<u32>>,
    val_a: Arc<Vec<F>>,
    val_b: Arc<Vec<F>>,
    val_c: Arc<Vec<F>>,
    count_x: Arc<Vec<F>>,
    count_y: Arc<Vec<F>>,
    h_state: crate::pcs::HemWhirProverState,
    rec_h: Option<Arc<PublicRecursionCommitment>>,
}

impl Clone for ShapeHologram {
    fn clone(&self) -> Self {
        let schedule = self.vk.regime.schedule(self.vk.native_pack_vars());
        let mut h0 = self.h_super_evals();
        let h1 = h0.split_off(h0.len() / 2);
        let (comm, mut h_state) =
            crate::pcs::whir_commit_batch_owned_with_schedule(vec![h0, h1], &[0u8; 32], &schedule);
        debug_assert_eq!(comm, self.vk.hologram_comm);
        if self.h_state.codewords_0.is_empty() {
            crate::pcs::release_round0_cache(&mut h_state);
        }
        Self {
            vk: self.vk.clone(),
            row_idx: Arc::clone(&self.row_idx),
            col_idx: Arc::clone(&self.col_idx),
            val_a: Arc::clone(&self.val_a),
            val_b: Arc::clone(&self.val_b),
            val_c: Arc::clone(&self.val_c),
            count_x: Arc::clone(&self.count_x),
            count_y: Arc::clone(&self.count_y),
            h_state,
            rec_h: self.rec_h.as_ref().map(Arc::clone),
        }
    }
}

impl core::fmt::Debug for ShapeHologram {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_struct("ShapeHologram")
            .field("vk", &self.vk)
            .finish()
    }
}

impl ShapeHologram {
    /// Deterministically compile the residual sparse hologram of `shape` under `regime`,
    /// including the Poseidon2 recursive hologram commitment when `regime.uses_poseidon2_canopy()`.
    pub fn compile(shape: &Shape, regime: WhirSecurityRegime) -> Result<Self, ZkHemError> {
        Self::compile_with_options(shape, regime, true)
    }

    /// Deterministically compile only the native 2-poly hologram commitment (`rec_h = None`),
    /// avoiding the `ell_nz + 3` recursive commitment for root/leaf-only native relations.
    pub fn compile_native(shape: &Shape, regime: WhirSecurityRegime) -> Result<Self, ZkHemError> {
        Self::compile_with_options(shape, regime, false)
    }

    fn compile_with_options(
        shape: &Shape,
        regime: WhirSecurityRegime,
        include_recursive: bool,
    ) -> Result<Self, ZkHemError> {
        let layout = public_layout(shape, regime).ok_or(ZkHemError::RelationTooLarge)?;
        let var_bits = layout.var_bits;
        let num_rows = shape.num_rows();

        // Merge sorted `(col, val)` iterators across `(A, B, C)` on residual rows so each
        // distinct `(row, col)` coordinate uses a single hologram slot.
        let mut row_idx = Vec::new();
        let mut col_idx = Vec::new();
        let mut val_a = Vec::new();
        let mut val_b = Vec::new();
        let mut val_c = Vec::new();

        for r in 0..num_rows {
            if !shape.is_residual_row(r) {
                continue;
            }
            let mut ia = shape.a.row(r).peekable();
            let mut ib = shape.b.row(r).peekable();
            let mut ic = shape.c.row(r).peekable();
            loop {
                let min_col = [
                    ia.peek().map(|&(c, _)| c),
                    ib.peek().map(|&(c, _)| c),
                    ic.peek().map(|&(c, _)| c),
                ]
                .into_iter()
                .flatten()
                .min();
                let Some(col) = min_col else {
                    break;
                };
                let take_if = |it: &mut core::iter::Peekable<_>| -> F {
                    if let Some(&(c, v)) = it.peek()
                        && c == col
                    {
                        let _ = it.next();
                        return v;
                    }
                    F::ZERO
                };
                let va = take_if(&mut ia);
                let vb = take_if(&mut ib);
                let vc = take_if(&mut ic);
                if !(va.is_zero() && vb.is_zero() && vc.is_zero()) {
                    row_idx.push(r as u32);
                    col_idx.push(col as u32);
                    val_a.push(va);
                    val_b.push(vb);
                    val_c.push(vc);
                }
            }
        }

        let min_entries = 1usize << shape.log_rows.max(var_bits).max(2);
        let nz_cap = row_idx.len().max(min_entries).next_power_of_two();
        let ell_nz = nz_cap.trailing_zeros() as usize;
        let pack_vars = ell_nz + 3;
        #[cfg(feature = "std")]
        if std::env::var_os("QSAG_PROFILE").is_some() {
            let sbox_slots = row_idx
                .iter()
                .filter(|&&r| (r as usize) < shape.num_sbox)
                .count();
            // Slots held by multiplication rows, by row width.
            let mut by_width = alloc::collections::BTreeMap::<usize, (usize, usize)>::new();
            let mut start = sbox_slots;
            while start < row_idx.len() {
                let end = start
                    + row_idx[start..]
                        .iter()
                        .take_while(|&&r| r == row_idx[start])
                        .count();
                let width = end - start;
                let bucket = if width <= 12 {
                    width
                } else {
                    13 + (width - 13) / 8 * 8
                };
                let entry = by_width.entry(bucket).or_default();
                entry.0 += 1;
                entry.1 += width;
                start = end;
            }
            std::eprintln!("hologram_mul_row_widths (width -> rows, slots) {by_width:?}");
            std::eprintln!(
                "hologram_geometry rows={} sbox_rows={} vars={} slots={} sbox_slots={} mul_slots={} csr_nnz={} nz_cap={} pack_vars={} recursive={}",
                num_rows,
                shape.num_sbox,
                shape.num_vars,
                row_idx.len(),
                sbox_slots,
                row_idx.len() - sbox_slots,
                shape.a.nnz() + shape.b.nnz() + shape.c.nnz(),
                nz_cap,
                pack_vars,
                include_recursive
            );
        }

        let required_vars = if include_recursive && regime.uses_poseidon2_canopy() {
            pack_vars
        } else {
            ell_nz + 2
        };
        if required_vars > MAX_PCS_NUM_VARS {
            return Err(ZkHemError::RelationTooLarge);
        }

        // Pad unused slots with `(row = 0, col = 0, vals = 0)` and account their reads in `c_x[0], c_y[0]`.
        row_idx.resize(nz_cap, 0);
        col_idx.resize(nz_cap, 0);
        val_a.resize(nz_cap, F::ZERO);
        val_b.resize(nz_cap, F::ZERO);
        val_c.resize(nz_cap, F::ZERO);

        let mut cx_u64 = vec![0u64; nz_cap];
        let mut cy_u64 = vec![0u64; nz_cap];
        for k in 0..nz_cap {
            cx_u64[row_idx[k] as usize] += 1;
            cy_u64[col_idx[k] as usize] += 1;
        }
        let count_x: Vec<F> = cx_u64.into_iter().map(F::from_u64_reduced).collect();
        let count_y: Vec<F> = cy_u64.into_iter().map(F::from_u64_reduced).collect();

        let mut h_super = vec![F::ZERO; 8 * nz_cap];
        for k in 0..nz_cap {
            h_super[k] = F::from_u64_reduced(u64::from(row_idx[k]));
            h_super[nz_cap + k] = F::from_u64_reduced(u64::from(col_idx[k]));
        }
        h_super[2 * nz_cap..3 * nz_cap].copy_from_slice(&val_a);
        h_super[3 * nz_cap..4 * nz_cap].copy_from_slice(&val_b);
        h_super[4 * nz_cap..5 * nz_cap].copy_from_slice(&val_c);
        h_super[5 * nz_cap..6 * nz_cap].copy_from_slice(&count_x);
        h_super[6 * nz_cap..7 * nz_cap].copy_from_slice(&count_y);

        let half_h = 4 * nz_cap;
        let h1 = h_super.split_off(half_h);
        let h0 = h_super;
        let h_schedule = regime.schedule(ell_nz + 2);
        let (hologram_comm, mut h_state) = crate::pcs::whir_commit_batch_owned_with_schedule(
            vec![h0, h1],
            &[0u8; 32],
            &h_schedule,
        );

        // Recursive parents need the recursive oracle, not duplicate native RS caches, and
        // a large native hologram would hold gigabytes of them between proofs. The retained
        // evaluations let an opening regenerate the cache.
        if (include_recursive && regime.uses_poseidon2_canopy())
            || ell_nz + 2 > HOLOGRAM_ROUND0_CACHE_MAX_VARS
        {
            crate::pcs::release_round0_cache(&mut h_state);
        }
        let h_super = if include_recursive && regime.uses_poseidon2_canopy() {
            h_state.hypercube_evals.concat()
        } else {
            Vec::new()
        };
        let rec_h = if include_recursive && regime.uses_poseidon2_canopy() {
            let rec_params = FixedPathWhirParams::new(regime, pack_vars)
                .map_err(|_| ZkHemError::RelationTooLarge)?;
            Some(Arc::new(
                PublicRecursionCommitment::commit(&rec_params, &h_super)
                    .map_err(|_| ZkHemError::RelationTooLarge)?,
            ))
        } else {
            None
        };
        let rec_hologram_root = rec_h.as_deref().map(PublicRecursionCommitment::root);

        drop(h_super);

        let vk = ShapeVerifierKey {
            shape_digest: shape.digest(),
            log_rows: shape.log_rows,
            num_sbox: shape.num_sbox,
            num_vars: shape.num_vars,
            num_public: shape.num_public,
            var_bits,
            ell_nz,
            hologram_meta: shape.hologram_meta(),
            regime,
            hologram_comm,
            rec_hologram_root,
        };
        Ok(Self {
            vk,
            row_idx: Arc::new(row_idx),
            col_idx: Arc::new(col_idx),
            val_a: Arc::new(val_a),
            val_b: Arc::new(val_b),
            val_c: Arc::new(val_c),
            count_x: Arc::new(count_x),
            count_y: Arc::new(count_y),
            h_state,
            rec_h,
        })
    }

    #[inline]
    pub fn verifier_key(&self) -> &ShapeVerifierKey {
        &self.vk
    }

    pub(crate) fn split_ref(&self) -> Option<SplitHologramRef> {
        let rec_h = self.rec_h.as_ref().map(Arc::clone)?;
        Some(SplitHologramRef {
            ell_nz: self.vk.ell_nz,
            pack_vars: self.vk.pack_vars(),
            row_idx: Arc::clone(&self.row_idx),
            col_idx: Arc::clone(&self.col_idx),
            val_a: Arc::clone(&self.val_a),
            val_b: Arc::clone(&self.val_b),
            val_c: Arc::clone(&self.val_c),
            count_x: Arc::clone(&self.count_x),
            count_y: Arc::clone(&self.count_y),
            rec_h,
        })
    }

    /// Give up the Reed-Solomon cache as a large hologram does, whatever this one's size.
    #[cfg(test)]
    fn without_round0_cache(mut self) -> Self {
        crate::pcs::release_round0_cache(&mut self.h_state);
        self
    }

    fn h_super_evals(&self) -> Vec<F> {
        let nz_cap = 1usize << self.vk.ell_nz;
        let mut h_super = vec![F::ZERO; 8 * nz_cap];
        for k in 0..nz_cap {
            h_super[k] = F::from_u64_reduced(u64::from(self.row_idx[k]));
            h_super[nz_cap + k] = F::from_u64_reduced(u64::from(self.col_idx[k]));
        }
        h_super[2 * nz_cap..3 * nz_cap].copy_from_slice(&self.val_a);
        h_super[3 * nz_cap..4 * nz_cap].copy_from_slice(&self.val_b);
        h_super[4 * nz_cap..5 * nz_cap].copy_from_slice(&self.val_c);
        h_super[5 * nz_cap..6 * nz_cap].copy_from_slice(&self.count_x);
        h_super[6 * nz_cap..7 * nz_cap].copy_from_slice(&self.count_y);
        h_super
    }
}

// ----------------------------------------------------------------------------
// Generic closed-form Poseidon2 `106 x 118` interior evaluator (`Native` & `ConstraintSystem`)
// ----------------------------------------------------------------------------

fn eq_table_gadget<B: RecBackend>(b: &mut B, point: &[RecExt<B::W>]) -> Vec<RecExt<B::W>> {
    let one = RecExt::<B::W>::one();
    let mut table = vec![one];
    for r in point {
        let mut lo = Vec::with_capacity(table.len());
        let mut hi = Vec::with_capacity(table.len());
        for v in &table {
            let vh = v.mul(b, r);
            lo.push(v.sub(&vh));
            hi.push(vh);
        }
        lo.extend(hi);
        table = lo;
    }
    table
}

fn eq_eval_gadget<B: RecBackend>(
    b: &mut B,
    x: &[RecExt<B::W>],
    y: &[RecExt<B::W>],
) -> RecExt<B::W> {
    assert_eq!(x.len(), y.len());
    let one = RecExt::<B::W>::one();
    let mut acc = one.clone();
    for (xi, yi) in x.iter().zip(y) {
        let xy = xi.mul(b, yi);
        let factor = xy.add(&xy).add(&one).sub(xi).sub(yi);
        acc = acc.mul(b, &factor);
    }
    acc
}

fn prefix_indicator_gadget<B: RecBackend>(
    b: &mut B,
    point: &[RecExt<B::W>],
    count: usize,
) -> RecExt<B::W> {
    let one = RecExt::<B::W>::one();
    if count == 0 {
        return RecExt::zero();
    }
    if count >> point.len() != 0 {
        return one;
    }
    let mut acc = RecExt::zero();
    let mut prefix = one.clone();
    for (j, r) in point.iter().enumerate().rev() {
        if (count >> j) & 1 == 1 {
            let term = prefix.mul(b, &one.sub(r));
            acc = acc.add(&term);
            prefix = prefix.mul(b, r);
        } else {
            prefix = prefix.mul(b, &one.sub(r));
        }
    }
    acc
}

/// $\sum_{p=0}^{P-1} \text{eq}(u_x, p) \cdot \text{eq}(u_y, B_{\text{pub}} + p)$ in $O(\log P)$
/// via a 4-state LSB-to-MSB `(carry_in, lt_P)` automaton with zero witness-dependent branches.
fn prefix_diag_gadget<B: RecBackend>(
    b: &mut B,
    ux: &[RecExt<B::W>],
    uy: &[RecExt<B::W>],
    perms: usize,
    pub_blocks: usize,
) -> RecExt<B::W> {
    if perms == 0 {
        return RecExt::zero();
    }
    let mx = ux.len();
    let my = uy.len();
    let m = mx.max(my);
    assert!(perms < (1usize << mx) && pub_blocks + perms <= (1usize << my));
    let one = RecExt::<B::W>::one();
    let mut dp = [
        [one.clone(), RecExt::zero()],
        [RecExt::zero(), RecExt::zero()],
    ];
    let mut live = [[true, false], [false, false]];

    for k in 0..m {
        let bk = (pub_blocks >> k) & 1;
        let pk = (perms >> k) & 1;
        let mut next_dp = [
            [RecExt::zero(), RecExt::zero()],
            [RecExt::zero(), RecExt::zero()],
        ];
        let mut next_live = [[false; 2]; 2];

        for bp in 0..=1usize {
            if k >= mx && bp == 1 {
                continue;
            }
            for carry in 0..=1usize {
                if !live[carry][0] && !live[carry][1] {
                    continue;
                }
                let sum = bp + bk + carry;
                let bq = sum & 1;
                let nc = sum >> 1;
                if k >= my && bq == 1 {
                    continue;
                }
                let wx = if k < mx {
                    if bp == 1 {
                        Some(ux[k].clone())
                    } else {
                        Some(one.sub(&ux[k]))
                    }
                } else {
                    None
                };
                let wy = if k < my {
                    if bq == 1 {
                        Some(uy[k].clone())
                    } else {
                        Some(one.sub(&uy[k]))
                    }
                } else {
                    None
                };
                let w_step = match (wx, wy) {
                    (Some(x), Some(y)) => Some(x.mul(b, &y)),
                    (Some(x), None) => Some(x),
                    (None, Some(y)) => Some(y),
                    (None, None) => None,
                };
                for lt in 0..=1usize {
                    if !live[carry][lt] {
                        continue;
                    }
                    let nlt = if bp < pk {
                        1
                    } else if bp > pk {
                        0
                    } else {
                        lt
                    };
                    let contrib = match &w_step {
                        Some(w) => dp[carry][lt].mul(b, w),
                        None => dp[carry][lt].clone(),
                    };
                    next_dp[nc][nlt] = if next_live[nc][nlt] {
                        next_dp[nc][nlt].add(&contrib)
                    } else {
                        contrib
                    };
                    next_live[nc][nlt] = true;
                }
            }
        }
        dp = next_dp;
        live = next_live;
    }
    if live[0][1] {
        dp[0][1].clone()
    } else {
        RecExt::zero()
    }
}

pub(crate) fn eval_poseidon2_interior_gadget<B: RecBackend>(
    b: &mut B,
    meta: HologramMeta,
    rx: &[RecExt<B::W>],
    ry: &[RecExt<B::W>],
    combine: &[RecExt<B::W>; 3],
) -> RecExt<B::W> {
    if meta.poseidon2_perms == 0 {
        return RecExt::zero();
    }
    assert!(rx.len() >= 7 && ry.len() >= 7);
    let eq_rx_lo = eq_table_gadget(b, &rx[..7]);
    let eq_ry_lo = eq_table_gadget(b, &ry[..7]);
    let (sa, sc, ca) = Poseidon2InteriorTemplate::with(|tpl| {
        let mut sa = RecExt::zero();
        let mut sc = RecExt::zero();
        let mut ca = RecExt::zero();
        for r_off in 0..106 {
            let r = 12 + r_off;
            let mut row_lc = RecExt::zero();
            for &(w, coeff) in &tpl.rows_a[r_off] {
                row_lc = row_lc.add(&eq_ry_lo[w as usize].scale(coeff));
            }
            let term_a = eq_rx_lo[r].mul(b, &row_lc);
            sa = sa.add(&term_a);
            let term_c = eq_rx_lo[r].mul(b, &eq_ry_lo[r]);
            sc = sc.add(&term_c);
            if !tpl.const_a[r_off].is_zero() {
                ca = ca.add(&eq_rx_lo[r].scale(tpl.const_a[r_off]));
            }
        }
        (sa, sc, ca)
    });
    let u_wires = combine[0].mul(b, &sa).add(&combine[2].mul(b, &sc));
    let u_const = combine[0].mul(b, &ca);
    let diag = prefix_diag_gadget(
        b,
        &rx[7..],
        &ry[7..],
        meta.poseidon2_perms,
        meta.pub_var_blocks,
    );
    let pref_p = prefix_indicator_gadget(b, &rx[7..], meta.poseidon2_perms);
    let one = RecExt::<B::W>::one();
    let mut eq_ry_zero = one.clone();
    for r in ry {
        eq_ry_zero = eq_ry_zero.mul(b, &one.sub(r));
    }
    let wire_part = diag.mul(b, &u_wires);
    let const_factor = pref_p.mul(b, &eq_ry_zero);
    let const_part = const_factor.mul(b, &u_const);
    wire_part.add(&const_part)
}

pub(crate) fn eval_poseidon2_interior_native(
    meta: HologramMeta,
    rx: &[E],
    ry: &[E],
    combine: &[E; 3],
) -> E {
    if meta.poseidon2_perms == 0 {
        return E::ZERO;
    }
    let mut b = RecNative::default();
    let rx_c: Vec<_> = rx.iter().copied().map(RecExt::constant).collect();
    let ry_c: Vec<_> = ry.iter().copied().map(RecExt::constant).collect();
    let comb_c = combine.map(RecExt::constant);
    eval_poseidon2_interior_gadget(&mut b, meta, &rx_c, &ry_c, &comb_c).value(&b)
}

// ----------------------------------------------------------------------------
// LogUp-GKR Layer Prover & Verifier Helpers
// ----------------------------------------------------------------------------

/// One layer of the binary LogUp-GKR fractional sumcheck from root (`m = 0`) down to leaves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogUpGkrLayer {
    /// `m` degree-3 sumcheck round polynomials (each of length `GKR_LAYER_DEGREE + 1 = 4`).
    pub rounds: Vec<[E; GKR_LAYER_DEGREE + 1]>,
    /// `[p_L, p_R, q_L, q_R]` at `(0, u*)` and `(1, u*)`.
    pub split: [E; 4],
}

/// Evaluate leaf `idx in 0..4*2^ell_nz` of the 4-way LogUp-GKR fractional tree on the fly
/// without materializing the leaf arrays.
#[inline]
#[allow(clippy::too_many_arguments)]
fn eval_gkr_leaf(
    holo: &ShapeHologram,
    ex: &[E],
    ey: &[E],
    eq_rx: &[E],
    eq_ry: &[E],
    alpha_mem: E,
    gamma_x: E,
    gamma_y: E,
    delta: E,
    idx: usize,
) -> (E, E) {
    let ell = holo.vk.ell_nz;
    let m = 1usize << ell;
    let k = idx & (m - 1);
    match idx >> ell {
        0 => {
            let row_f = F::from_u64_reduced(u64::from(holo.row_idx[k]));
            (E::ONE, gamma_x - (E::from_base(row_f) + alpha_mem * ex[k]))
        }
        1 => {
            let id_f = F::from_u64_reduced(k as u64);
            let tbl_ex = eq_rx[k & (eq_rx.len() - 1)];
            (
                E::ZERO - E::from_base(holo.count_x[k]),
                gamma_x - (E::from_base(id_f) + alpha_mem * tbl_ex),
            )
        }
        2 => {
            let col_f = F::from_u64_reduced(u64::from(holo.col_idx[k]));
            (delta, gamma_y - (E::from_base(col_f) + alpha_mem * ey[k]))
        }
        _ => {
            let id_f = F::from_u64_reduced(k as u64);
            let tbl_ey = eq_ry[k & (eq_ry.len() - 1)];
            (
                E::ZERO - delta.mul_base(holo.count_y[k]),
                gamma_y - (E::from_base(id_f) + alpha_mem * tbl_ey),
            )
        }
    }
}

/// Fraction `(p, q)` of node `u` of the layer above the leaves: the sum of leaves `2u` and
/// `2u + 1` as fractions.
#[inline]
fn gkr_layer1_node(leaf: &(impl Fn(usize) -> (E, E) + Sync), u: usize) -> (E, E) {
    let (pl, ql) = leaf(2 * u);
    let (pr, qr) = leaf(2 * u + 1);
    (pl * qr + pr * ql, ql * qr)
}

/// GKR layers `2..=ell_nz + 2` above `4 * 2^ell_nz` leaves, bottom first. Layer `d` holds one
/// fraction per node, node `u` summing nodes `2u` and `2u + 1` of layer `d - 1`. The leaf
/// layer and layer `1` are never stored: the prover recomputes their nodes from `leaf`.
fn build_gkr_upper_tree(
    leaf: &(impl Fn(usize) -> (E, E) + Sync),
    ell_nz: usize,
) -> Vec<(Vec<E>, Vec<E>)> {
    let _phase = crate::profile::span("hologram_gkr_tree");
    let gkr_depth = ell_nz + 2;
    let len2 = 1usize << ell_nz;
    let mut p2 = vec![E::ZERO; len2];
    let mut q2 = vec![E::ZERO; len2];
    let chunk0 = par_chunk(len2);
    let mut pairs0: Vec<_> = p2.chunks_mut(chunk0).zip(q2.chunks_mut(chunk0)).collect();
    for_each_chunk_mut(&mut pairs0, 1, |c_idx, part| {
        let (pn, qn) = &mut part[0];
        let base = c_idx * chunk0;
        for (off, (ps, qs)) in pn.iter_mut().zip(qn.iter_mut()).enumerate() {
            let u = base + off;
            let (pl, ql) = gkr_layer1_node(leaf, 2 * u);
            let (pr, qr) = gkr_layer1_node(leaf, 2 * u + 1);
            *ps = pl * qr + pr * ql;
            *qs = ql * qr;
        }
    });

    let mut upper = Vec::with_capacity(gkr_depth - 1);
    upper.push((p2, q2));
    for idx in 0..(gkr_depth - 2) {
        let (p_prev, q_prev) = &upper[idx];
        let half = p_prev.len() / 2;
        let mut p_next = vec![E::ZERO; half];
        let mut q_next = vec![E::ZERO; half];
        let chunk = par_chunk(half);
        let mut pairs: Vec<_> = p_next
            .chunks_mut(chunk)
            .zip(q_next.chunks_mut(chunk))
            .collect();
        for_each_chunk_mut(&mut pairs, 1, |c_idx, part| {
            let (pn, qn) = &mut part[0];
            let base = c_idx * chunk;
            for (off, (ps, qs)) in pn.iter_mut().zip(qn.iter_mut()).enumerate() {
                let u = base + off;
                let (pl, pr) = (p_prev[2 * u], p_prev[2 * u + 1]);
                let (ql, qr) = (q_prev[2 * u], q_prev[2 * u + 1]);
                *ps = pl * qr + pr * ql;
                *qs = ql * qr;
            }
        });
        upper.push((p_next, q_next));
    }
    upper
}

/// Degree-3 sumcheck over `k in {0,1}^ell_nz` of `ex(k) * ey(k) * v(k)` without cloning
/// `ex` and `ey` (round 0 reads slices directly and folds into `half`-length buffers).
fn run_cubic_triple_sumcheck_slices(
    sa: &[E],
    sb: &[E],
    sc: &[E],
    mut absorb_and_squeeze: impl FnMut([E; 4]) -> E,
) -> (Vec<[E; 4]>, Vec<E>, [E; 3]) {
    let n = sa.len().trailing_zeros() as usize;
    let mut rounds = Vec::with_capacity(n);
    let mut point = Vec::with_capacity(n);
    let half0 = sa.len() / 2;
    let evals0 = round_evals::<4>(0..half0, |i| {
        let (a0, da) = (sa[2 * i], sa[2 * i + 1] - sa[2 * i]);
        let (b0, db) = (sb[2 * i], sb[2 * i + 1] - sb[2 * i]);
        let (c0, dc) = (sc[2 * i], sc[2 * i + 1] - sc[2 * i]);
        let (mut a, mut b, mut c) = (a0, b0, c0);
        core::array::from_fn(|_| {
            let val = a * b * c;
            a += da;
            b += db;
            c += dc;
            val
        })
    });
    let coeffs0: [E; 4] = evals_to_coeffs(&evals0).try_into().unwrap();
    let chal0 = absorb_and_squeeze(coeffs0);
    rounds.push(coeffs0);
    point.push(chal0);

    let mut ta = vec![E::ZERO; half0];
    let mut tb = vec![E::ZERO; half0];
    let mut tc = vec![E::ZERO; half0];
    let chunk0 = par_chunk(half0);
    let mut triples: Vec<_> = ta
        .chunks_mut(chunk0)
        .zip(tb.chunks_mut(chunk0))
        .zip(tc.chunks_mut(chunk0))
        .collect();
    for_each_chunk_mut(&mut triples, 1, |c_idx, part| {
        let ((fa, fb), fc) = &mut part[0];
        let base = c_idx * chunk0;
        for j in 0..fa.len() {
            let i = base + j;
            fa[j] = sa[2 * i] + chal0 * (sa[2 * i + 1] - sa[2 * i]);
            fb[j] = sb[2 * i] + chal0 * (sb[2 * i + 1] - sb[2 * i]);
            fc[j] = sc[2 * i] + chal0 * (sc[2 * i + 1] - sc[2 * i]);
        }
    });

    for _ in 1..n {
        let half = ta.len() / 2;
        let evals = round_evals::<4>(0..half, |i| {
            let (a0, da) = (ta[2 * i], ta[2 * i + 1] - ta[2 * i]);
            let (b0, db) = (tb[2 * i], tb[2 * i + 1] - tb[2 * i]);
            let (c0, dc) = (tc[2 * i], tc[2 * i + 1] - tc[2 * i]);
            let (mut a, mut b, mut c) = (a0, b0, c0);
            core::array::from_fn(|_| {
                let val = a * b * c;
                a += da;
                b += db;
                c += dc;
                val
            })
        });
        let coeffs: [E; 4] = evals_to_coeffs(&evals).try_into().unwrap();
        let chal = absorb_and_squeeze(coeffs);
        rounds.push(coeffs);
        point.push(chal);
        fold_in_place(&mut ta, chal, false);
        fold_in_place(&mut tb, chal, false);
        fold_in_place(&mut tc, chal, false);
    }
    (rounds, point, [ta[0], tb[0], tc[0]])
}

#[allow(clippy::too_many_arguments)]
fn finish_gkr_folded_rounds(
    mut eq_t: Vec<E>,
    mut p0: Vec<E>,
    mut p1: Vec<E>,
    mut q0: Vec<E>,
    mut q1: Vec<E>,
    beta: E,
    mut rounds: Vec<[E; 4]>,
    mut u_star: Vec<E>,
    mut absorb_and_squeeze: impl FnMut([E; 4]) -> E,
) -> (Vec<[E; 4]>, Vec<E>, [E; 4]) {
    while eq_t.len() > 1 {
        let half = eq_t.len() / 2;
        let evals = round_evals::<4>(0..half, |i| {
            let (e0, de) = (eq_t[2 * i], eq_t[2 * i + 1] - eq_t[2 * i]);
            let (pl0, dpl) = (p0[2 * i], p0[2 * i + 1] - p0[2 * i]);
            let (pr0, dpr) = (p1[2 * i], p1[2 * i + 1] - p1[2 * i]);
            let (ql0, dql) = (q0[2 * i], q0[2 * i + 1] - q0[2 * i]);
            let (qr0, dqr) = (q1[2 * i], q1[2 * i + 1] - q1[2 * i]);
            let (mut e, mut pl, mut pr, mut ql, mut qr) = (e0, pl0, pr0, ql0, qr0);
            core::array::from_fn(|_| {
                let v = e * (pl * qr + pr * ql + beta * ql * qr);
                e += de;
                pl += dpl;
                pr += dpr;
                ql += dql;
                qr += dqr;
                v
            })
        });
        let coeffs: [E; 4] = evals_to_coeffs(&evals).try_into().unwrap();
        let chal = absorb_and_squeeze(coeffs);
        rounds.push(coeffs);
        u_star.push(chal);
        fold_in_place(&mut eq_t, chal, false);
        fold_in_place(&mut p0, chal, false);
        fold_in_place(&mut p1, chal, false);
        fold_in_place(&mut q0, chal, false);
        fold_in_place(&mut q1, chal, false);
    }
    (rounds, u_star, [p0[0], p1[0], q0[0], q1[0]])
}

/// Degree-3 sumcheck reducing the claims on one GKR layer to claims on the layer below,
/// whose fraction at node `u` is `node(u)`. Round 0 reads the nodes and folds them into
/// half-length tables, so the layer below is never needed as a whole.
fn run_gkr_layer_sumcheck(
    node: impl Fn(usize) -> (E, E) + Sync,
    r_hi: &[E],
    beta: E,
    mut absorb_and_squeeze: impl FnMut([E; 4]) -> E,
) -> (Vec<[E; 4]>, Vec<E>, [E; 4]) {
    let m = r_hi.len();
    assert!(m >= 1);
    let half0 = 1usize << (m - 1);
    let eq_hi = eq_table(&r_hi[1..]);
    let r0 = r_hi[0];
    let w0 = E::ONE - r0;
    let w1 = r0;

    let evals0 = round_evals::<4>(0..half0, |i| {
        let eh = eq_hi[i];
        let (e0, de) = (eh * w0, eh * (w1 - w0));
        let (pl_a, ql_a) = node(4 * i);
        let (pr_a, qr_a) = node(4 * i + 1);
        let (pl_b, ql_b) = node(4 * i + 2);
        let (pr_b, qr_b) = node(4 * i + 3);
        let (dpl, dpr, dql, dqr) = (pl_b - pl_a, pr_b - pr_a, ql_b - ql_a, qr_b - qr_a);
        let (mut e, mut pl, mut pr, mut ql, mut qr) = (e0, pl_a, pr_a, ql_a, qr_a);
        core::array::from_fn(|_| {
            let v = e * (pl * qr + pr * ql + beta * ql * qr);
            e += de;
            pl += dpl;
            pr += dpr;
            ql += dql;
            qr += dqr;
            v
        })
    });
    let coeffs0: [E; 4] = evals_to_coeffs(&evals0).try_into().unwrap();
    let chal0 = absorb_and_squeeze(coeffs0);
    let mut rounds = Vec::with_capacity(m);
    let mut u_star = Vec::with_capacity(m);
    rounds.push(coeffs0);
    u_star.push(chal0);

    let eq_fold_factor = w0 + chal0 * (w1 - w0);
    let mut eq_t = eq_hi;
    for_each_chunk_mut(&mut eq_t, par_chunk(half0), |_, part| {
        for eh in part {
            *eh *= eq_fold_factor;
        }
    });
    let mut p0 = vec![E::ZERO; half0];
    let mut p1 = vec![E::ZERO; half0];
    let mut q0 = vec![E::ZERO; half0];
    let mut q1 = vec![E::ZERO; half0];
    let chunk = par_chunk(half0);
    let mut quads: Vec<_> = p0
        .chunks_mut(chunk)
        .zip(p1.chunks_mut(chunk))
        .zip(q0.chunks_mut(chunk))
        .zip(q1.chunks_mut(chunk))
        .collect();
    for_each_chunk_mut(&mut quads, 1, |c_idx, part| {
        let (((fp0, fp1), fq0), fq1) = &mut part[0];
        let base = c_idx * chunk;
        for j in 0..fp0.len() {
            let i = base + j;
            let (pl_a, ql_a) = node(4 * i);
            let (pr_a, qr_a) = node(4 * i + 1);
            let (pl_b, ql_b) = node(4 * i + 2);
            let (pr_b, qr_b) = node(4 * i + 3);
            fp0[j] = pl_a + chal0 * (pl_b - pl_a);
            fp1[j] = pr_a + chal0 * (pr_b - pr_a);
            fq0[j] = ql_a + chal0 * (ql_b - ql_a);
            fq1[j] = qr_a + chal0 * (qr_b - qr_a);
        }
    });
    drop(quads);

    finish_gkr_folded_rounds(
        eq_t,
        p0,
        p1,
        q0,
        q1,
        beta,
        rounds,
        u_star,
        absorb_and_squeeze,
    )
}

/// The whole LogUp-GKR reduction, root to leaves, over fractions given by `leaf`. Returns
/// `q_root`, the per-layer messages and the final point, or `None` when `q_root` is zero.
///
/// `on_root` absorbs `q_root`; `beta` squeezes a layer's batching challenge; `round` absorbs
/// a round polynomial and squeezes its challenge; `split` absorbs a layer's four end values
/// and squeezes the bit that selects between them.
fn prove_logup_gkr(
    leaf: impl Fn(usize) -> (E, E) + Sync,
    ell_nz: usize,
    mut on_root: impl FnMut(E),
    mut beta: impl FnMut() -> E,
    mut round: impl FnMut([E; 4]) -> E,
    mut split: impl FnMut([E; 4]) -> E,
) -> Option<(E, Vec<LogUpGkrLayer>, Vec<E>)> {
    let mut upper = build_gkr_upper_tree(&leaf, ell_nz);
    let gkr_depth = ell_nz + 2;
    let (p_root, q_root) = {
        let (pr, qr) = upper.pop().expect("nonempty GKR root");
        (pr[0], qr[0])
    };
    debug_assert_eq!(p_root, E::ZERO);
    if q_root.is_zero() {
        return None;
    }
    on_root(q_root);

    let _phase = crate::profile::span("hologram_gkr_rounds");
    let mut r_cur: Vec<E> = Vec::new();
    let mut gkr_layers = Vec::with_capacity(gkr_depth);
    for d in (0..gkr_depth).rev() {
        let m_vars = gkr_depth - 1 - d;
        let (rounds, u_star, ends) = if m_vars == 0 {
            let (p_top, q_top) = upper.pop().expect("GKR top split");
            (
                Vec::new(),
                Vec::new(),
                [p_top[0], p_top[1], q_top[0], q_top[1]],
            )
        } else {
            let beta = beta();
            match d {
                0 => run_gkr_layer_sumcheck(&leaf, &r_cur, beta, &mut round),
                1 => {
                    debug_assert!(upper.is_empty());
                    run_gkr_layer_sumcheck(|u| gkr_layer1_node(&leaf, u), &r_cur, beta, &mut round)
                }
                _ => {
                    let (p_d, q_d) = upper.pop().expect("GKR internal layer");
                    run_gkr_layer_sumcheck(|u| (p_d[u], q_d[u]), &r_cur, beta, &mut round)
                }
            }
        };
        let c_bit = split(ends);
        let mut next_r = Vec::with_capacity(m_vars + 1);
        next_r.push(c_bit);
        next_r.extend_from_slice(&u_star);
        r_cur = next_r;
        gkr_layers.push(LogUpGkrLayer {
            rounds,
            split: ends,
        });
    }
    Some((q_root, gkr_layers, r_cur))
}

/// `(eq(rx, row[k]), eq(ry, col[k]))` over the hologram's slots `k`.
fn spark_read_tables(hologram: &ShapeHologram, eq_rx: &[E], eq_ry: &[E]) -> (Vec<E>, Vec<E>) {
    let m_nz = 1usize << hologram.vk.ell_nz;
    let mut ex = vec![E::ZERO; m_nz];
    let mut ey = vec![E::ZERO; m_nz];
    let chunk = par_chunk(m_nz);
    for_each_chunk_mut(&mut ex, chunk, |c_idx, part| {
        let base = c_idx * chunk;
        for (off, slot) in part.iter_mut().enumerate() {
            *slot = eq_rx[hologram.row_idx[base + off] as usize];
        }
    });
    for_each_chunk_mut(&mut ey, chunk, |c_idx, part| {
        let base = c_idx * chunk;
        for (off, slot) in part.iter_mut().enumerate() {
            *slot = eq_ry[hologram.col_idx[base + off] as usize];
        }
    });
    (ex, ey)
}

/// `combine[0] A + combine[1] B + combine[2] C` over the hologram's slots.
fn spark_value_table(hologram: &ShapeHologram, combine: &[E; 3]) -> Vec<E> {
    let m_nz = 1usize << hologram.vk.ell_nz;
    let mut val_comb = vec![E::ZERO; m_nz];
    let chunk = par_chunk(m_nz);
    for_each_chunk_mut(&mut val_comb, chunk, |c_idx, part| {
        let base = c_idx * chunk;
        for (off, slot) in part.iter_mut().enumerate() {
            let k = base + off;
            *slot = combine[0].mul_base(hologram.val_a[k])
                + combine[1].mul_base(hologram.val_b[k])
                + combine[2].mul_base(hologram.val_c[k]);
        }
    });
    val_comb
}

fn pack_e_super(ex: &[E], ey: &[E]) -> Vec<F> {
    let m = ex.len();
    debug_assert_eq!(ey.len(), m);
    let mut out = vec![F::ZERO; 8 * m];
    for k in 0..m {
        let lx = ex[k].to_limbs();
        let ly = ey[k].to_limbs();
        for j in 0..4 {
            out[j * m + k] = lx[j];
            out[(4 + j) * m + k] = ly[j];
        }
    }
    out
}

fn super8_blend2_claim(slices: &[E; 8], sel2: &[E; 2], eta: E) -> E {
    let eq2 = build_eq_table_ext4(sel2);
    let c0 = slices[..4]
        .iter()
        .zip(&eq2)
        .fold(E::ZERO, |acc, (&v, &w)| acc + v * w);
    let c1 = slices[4..]
        .iter()
        .zip(&eq2)
        .fold(E::ZERO, |acc, (&v, &w)| acc + v * w);
    c0 + eta * c1
}

// ----------------------------------------------------------------------------
// Native Sublinear Hologram Proof (`HologramPublicProof`)
// ----------------------------------------------------------------------------

/// Non-hiding Hem proof verified in sublinear time against [`ShapeVerifierKey`]
/// without scanning the relation's CSR matrices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HologramPublicProof {
    pub comm_z: CanopyCommitment,
    pub row_rounds: Vec<Vec<E>>,
    pub row_values: [E; 3],
    pub col_rounds: Vec<Vec<E>>,
    pub eval_z: E,
    pub comm_e: CanopyCommitment,
    pub m_sparse_claim: E,
    pub mat_rounds: Vec<[E; SPARK_MAT_DEGREE + 1]>,
    pub h_at_mat: [E; 7],
    pub e_limbs_at_mat: [E; 8],
    pub q_root: E,
    pub gkr_layers: Vec<LogUpGkrLayer>,
    pub h_at_gkr: [E; 7],
    pub e_limbs_at_gkr: [E; 8],
    pub open_z: HemWhirOpeningProof,
    pub open_h: HemWhirOpeningProof,
    pub open_e: HemWhirOpeningProof,
}

impl HologramPublicProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = HOLOGRAM_PUBLIC_WIRE_MAGIC.to_vec();
        out.extend_from_slice(&self.comm_z.to_bytes());
        let push_e = |out: &mut Vec<u8>, v: &E| out.extend_from_slice(&v.to_le_bytes());
        for v in self
            .row_rounds
            .iter()
            .flatten()
            .chain(&self.row_values)
            .chain(self.col_rounds.iter().flatten())
            .chain(core::iter::once(&self.eval_z))
        {
            push_e(&mut out, v);
        }
        out.extend_from_slice(&self.comm_e.to_bytes());
        push_e(&mut out, &self.m_sparse_claim);
        for v in self
            .mat_rounds
            .iter()
            .flatten()
            .chain(&self.h_at_mat)
            .chain(&self.e_limbs_at_mat)
            .chain(core::iter::once(&self.q_root))
        {
            push_e(&mut out, v);
        }
        for layer in &self.gkr_layers {
            for v in layer.rounds.iter().flatten().chain(&layer.split) {
                push_e(&mut out, v);
            }
        }
        for v in self.h_at_gkr.iter().chain(&self.e_limbs_at_gkr) {
            push_e(&mut out, v);
        }
        self.open_z.push_bytes(&mut out);
        self.open_h.push_bytes(&mut out);
        self.open_e.push_bytes(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8], vk: &ShapeVerifierKey) -> Option<Self> {
        if bytes.get(..8)? != HOLOGRAM_PUBLIC_WIRE_MAGIC || !vk.is_well_formed() {
            return None;
        }
        let mut pos = 8usize;
        let (comm_z, used_z) = CanopyCommitment::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += used_z;
        fn take_e(bytes: &[u8], pos: &mut usize) -> Option<E> {
            let chunk: [u8; 32] = bytes.get(*pos..*pos + 32)?.try_into().ok()?;
            *pos += 32;
            E::from_le_bytes_canonical(chunk)
        }
        let row_rounds = (0..vk.log_rows)
            .map(|_| (0..=ROW_DEGREE).map(|_| take_e(bytes, &mut pos)).collect())
            .collect::<Option<Vec<Vec<E>>>>()?;
        let row_values = [
            take_e(bytes, &mut pos)?,
            take_e(bytes, &mut pos)?,
            take_e(bytes, &mut pos)?,
        ];
        let col_rounds = (0..vk.var_bits)
            .map(|_| (0..=COL_DEGREE).map(|_| take_e(bytes, &mut pos)).collect())
            .collect::<Option<Vec<Vec<E>>>>()?;
        let eval_z = take_e(bytes, &mut pos)?;
        let (comm_e, used_e) = CanopyCommitment::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += used_e;
        let m_sparse_claim = take_e(bytes, &mut pos)?;
        let mut mat_rounds = Vec::with_capacity(vk.ell_nz);
        for _ in 0..vk.ell_nz {
            mat_rounds.push([
                take_e(bytes, &mut pos)?,
                take_e(bytes, &mut pos)?,
                take_e(bytes, &mut pos)?,
                take_e(bytes, &mut pos)?,
            ]);
        }
        let mut h_at_mat = [E::ZERO; 7];
        for s in &mut h_at_mat {
            *s = take_e(bytes, &mut pos)?;
        }
        let mut e_limbs_at_mat = [E::ZERO; 8];
        for s in &mut e_limbs_at_mat {
            *s = take_e(bytes, &mut pos)?;
        }
        let q_root = take_e(bytes, &mut pos)?;
        let gkr_depth = vk.ell_nz + 2;
        let mut gkr_layers = Vec::with_capacity(gkr_depth);
        for m in 0..gkr_depth {
            let mut rounds = Vec::with_capacity(m);
            for _ in 0..m {
                rounds.push([
                    take_e(bytes, &mut pos)?,
                    take_e(bytes, &mut pos)?,
                    take_e(bytes, &mut pos)?,
                    take_e(bytes, &mut pos)?,
                ]);
            }
            let split = [
                take_e(bytes, &mut pos)?,
                take_e(bytes, &mut pos)?,
                take_e(bytes, &mut pos)?,
                take_e(bytes, &mut pos)?,
            ];
            gkr_layers.push(LogUpGkrLayer { rounds, split });
        }
        let mut h_at_gkr = [E::ZERO; 7];
        for s in &mut h_at_gkr {
            *s = take_e(bytes, &mut pos)?;
        }
        let mut e_limbs_at_gkr = [E::ZERO; 8];
        for s in &mut e_limbs_at_gkr {
            *s = take_e(bytes, &mut pos)?;
        }
        let (open_z, u1) = HemWhirOpeningProof::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += u1;
        let (open_h, u2) = HemWhirOpeningProof::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += u2;
        let (open_e, u3) = HemWhirOpeningProof::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += u3;
        (pos == bytes.len()).then_some(Self {
            comm_z,
            row_rounds,
            row_values,
            col_rounds,
            eval_z,
            comm_e,
            m_sparse_claim,
            mat_rounds,
            h_at_mat,
            e_limbs_at_mat,
            q_root,
            gkr_layers,
            h_at_gkr,
            e_limbs_at_gkr,
            open_z,
            open_h,
            open_e,
        })
    }
}

fn eval_h_and_e_limbs_at_point(
    holo: &ShapeHologram,
    e0: &[F],
    e1: &[F],
    pt: &[E],
) -> ([E; 7], [E; 8]) {
    let eq_pt = eq_table(pt);
    let m = eq_pt.len();
    let evals = round_evals::<15>(0..m, |k| {
        let w = eq_pt[k];
        [
            w.mul_base(F::from_u64_reduced(u64::from(holo.row_idx[k]))),
            w.mul_base(F::from_u64_reduced(u64::from(holo.col_idx[k]))),
            w.mul_base(holo.val_a[k]),
            w.mul_base(holo.val_b[k]),
            w.mul_base(holo.val_c[k]),
            w.mul_base(holo.count_x[k]),
            w.mul_base(holo.count_y[k]),
            w.mul_base(e0[k]),
            w.mul_base(e0[m + k]),
            w.mul_base(e0[2 * m + k]),
            w.mul_base(e0[3 * m + k]),
            w.mul_base(e1[k]),
            w.mul_base(e1[m + k]),
            w.mul_base(e1[2 * m + k]),
            w.mul_base(e1[3 * m + k]),
        ]
    });
    let h: [E; 7] = evals[..7].try_into().unwrap();
    let e_limbs: [E; 8] = evals[7..].try_into().unwrap();
    (h, e_limbs)
}

fn recompose_ext4_from_limb_evals(limbs: &[E; 4]) -> E {
    let basis = limb_basis();
    limbs
        .iter()
        .zip(&basis)
        .fold(E::ZERO, |acc, (&l, &b)| acc + l * b)
}

fn start_hologram_transcript(
    vk: &ShapeVerifierKey,
    statement: &[u8],
    public: &[F],
    comm_z: &CanopyCommitment,
) -> FiatShamirTranscript<InstanceBound> {
    let pub_bytes: Vec<u8> = public.iter().flat_map(|v| v.to_le_bytes()).collect();
    let vk_bytes = vk.to_bytes();
    let z_schedule = vk.regime.schedule(vk.var_bits);
    FiatShamirTranscript::new()
        .bind_relation(b"QSAG.HEM.HOLOGRAM/v1", &vk_bytes, &z_schedule)
        .bind_instance(&[statement, &pub_bytes, &comm_z.to_bytes()])
}

/// Prove a public relation using a precompiled [`ShapeHologram`] so native verification runs
/// against [`ShapeVerifierKey`] alone; timing depends on shape and security regime.
pub fn prove_public_hologram(
    shape: &Shape,
    hologram: &ShapeHologram,
    mut assignment: Vec<F>,
    statement: &[u8],
    seed: &[u8; 32],
) -> Result<HologramPublicProof, ZkHemError> {
    let vk = &hologram.vk;
    if vk.shape_digest != shape.digest() || !vk.regime.meets_qrom_128_floor() {
        return Err(ZkHemError::Unsatisfied);
    }
    if assignment.len() != shape.num_vars || assignment.first() != Some(&F::ONE) {
        return Err(ZkHemError::Unsatisfied);
    }
    // A hologram compiled without its Reed-Solomon cache marks a relation large enough that
    // this proof's own `E` commitment gives its cache up as well.
    let release_caches = hologram.h_state.codewords_0.is_empty();
    let public = assignment[1..=shape.num_public].to_vec();
    let row_base = row_tables(shape, &assignment, true).ok_or(ZkHemError::Unsatisfied)?;
    assignment.resize(1 << vk.var_bits, F::ZERO);
    let z_schedule = vk.regime.schedule(vk.var_bits);
    let (comm_z, state_z) =
        crate::pcs::whir_commit_owned_with_schedule(assignment, seed, &z_schedule);

    let mut tr = start_hologram_transcript(vk, statement, &public, &comm_z);
    let tau = squeeze_point(&mut tr, b"ZKHEM_TAU", vk.log_rows);
    let (row_rounds, rx, row_values) = row_sumcheck(&mut tr, &tau, vk.num_sbox, row_base, None);
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &row_values);
    let combine_vec = squeeze_point(&mut tr, b"ZKHEM_COMBINE", 3);
    let combine: [E; 3] = combine_vec.clone().try_into().unwrap();
    let lambda = tr.squeeze_ext4(b"HEM_PUBLIC_CELLS");

    let eq_rx = eq_table(&rx);
    let mut tm = column_table(shape, &eq_rx, &combine_vec, 1 << vk.var_bits);
    let mut weight = lambda;
    for slot in tm.iter_mut().take(vk.num_public + 1) {
        *slot += weight;
        weight *= lambda;
    }
    let (col_rounds, ry, _, eval_z) =
        column_sumcheck(&mut tr, tm, &state_z.hypercube_evals[0], None);

    // `ex[k] = eq(rx, row[k])`, `ey[k] = eq(ry, col[k])` and `V[k]` are gathers from small
    // tables: they are released across the commitment to `E` and rebuilt after it.
    let eq_ry = eq_table(&ry);
    let m_nz = 1usize << vk.ell_nz;
    let (comm_e, state_e, m_sparse_claim) = {
        let (ex, ey) = spark_read_tables(hologram, &eq_rx, &eq_ry);
        let val_comb = spark_value_table(hologram, &combine);
        let [m_sparse_claim] = round_evals::<1>(0..m_nz, |k| [ex[k] * ey[k] * val_comb[k]]);
        drop(val_comb);
        let mut e0 = pack_e_super(&ex, &ey);
        drop(ex);
        drop(ey);
        let e1 = e0.split_off(4 * m_nz);
        let pack_schedule = vk.regime.schedule(vk.native_pack_vars());
        let mut e_salt = [0u8; 32];
        e_salt.copy_from_slice(&cshake256_32(b"QSAG.HEM.HOLOGRAM.ESALT/v1", seed));
        let _phase = crate::profile::span("hologram_commit_e");
        let (comm_e, mut state_e) = crate::pcs::whir_commit_batch_owned_with_schedule(
            vec![e0, e1],
            &e_salt,
            &pack_schedule,
        );
        if release_caches {
            crate::pcs::release_round0_cache(&mut state_e);
        }
        (comm_e, state_e, m_sparse_claim)
    };

    tr.absorb(b"HOLO_COMM_E", &comm_e.to_bytes());
    tr.absorb_ext4(b"HOLO_M_SPARSE", m_sparse_claim);
    let alpha_mem = tr.squeeze_ext4(b"HOLO_ALPHA_MEM");
    let gamma_x = tr.squeeze_ext4(b"HOLO_GAMMA_X");
    let gamma_y = tr.squeeze_ext4(b"HOLO_GAMMA_Y");
    let delta = tr.squeeze_ext4(b"HOLO_DELTA");

    // 1. Spark cubic matrix sumcheck -> `r_mat`.
    let (ex, ey) = spark_read_tables(hologram, &eq_rx, &eq_ry);
    let (mat_rounds, r_mat) = {
        let val_comb = spark_value_table(hologram, &combine);
        let _phase = crate::profile::span("hologram_mat_sumcheck");
        let (mat_rounds, r_mat, _) =
            run_cubic_triple_sumcheck_slices(&ex, &ey, &val_comb, |coeffs| {
                tr.absorb_ext4_slice(b"HOLO_MAT_ROUND", &coeffs);
                tr.squeeze_ext4(b"HOLO_MAT_ROUND")
            });
        (mat_rounds, r_mat)
    };
    let (h_at_mat, e_limbs_at_mat) = eval_h_and_e_limbs_at_point(
        hologram,
        &state_e.hypercube_evals[0],
        &state_e.hypercube_evals[1],
        &r_mat,
    );
    tr.absorb_ext4_slice(b"HOLO_AT_MAT_H", &h_at_mat);
    tr.absorb_ext4_slice(b"HOLO_AT_MAT_E", &e_limbs_at_mat);

    // 2. LogUp-GKR fractional binary tree -> `(r_gkr, b_gkr)`.
    let (q_root, gkr_layers, r_cur) = {
        // The four closures take turns on the one transcript.
        let tr = core::cell::RefCell::new(&mut tr);
        prove_logup_gkr(
            |idx| {
                eval_gkr_leaf(
                    hologram, &ex, &ey, &eq_rx, &eq_ry, alpha_mem, gamma_x, gamma_y, delta, idx,
                )
            },
            vk.ell_nz,
            |q_root| tr.borrow_mut().absorb_ext4(b"HOLO_Q_ROOT", q_root),
            || tr.borrow_mut().squeeze_ext4(b"HOLO_GKR_BETA"),
            |coeffs| {
                let mut tr = tr.borrow_mut();
                tr.absorb_ext4_slice(b"HOLO_GKR_ROUND", &coeffs);
                tr.squeeze_ext4(b"HOLO_GKR_ROUND")
            },
            |ends| {
                let mut tr = tr.borrow_mut();
                tr.absorb_ext4_slice(b"HOLO_GKR_SPLIT", &ends);
                tr.squeeze_ext4(b"HOLO_GKR_BIT")
            },
        )
        .ok_or(ZkHemError::MaskRankDeficient)?
    };
    drop(ex);
    drop(ey);
    drop(eq_rx);
    drop(eq_ry);

    let r_gkr = &r_cur[..vk.ell_nz];
    let (h_at_gkr, e_limbs_at_gkr) = eval_h_and_e_limbs_at_point(
        hologram,
        &state_e.hypercube_evals[0],
        &state_e.hypercube_evals[1],
        r_gkr,
    );
    tr.absorb_ext4_slice(b"HOLO_AT_GKR_H", &h_at_gkr);
    tr.absorb_ext4_slice(b"HOLO_AT_GKR_E", &e_limbs_at_gkr);

    // 3. 2-poly 4-slice selector reduction + WHIR openings of `Z`, `H_pair`, `E_pair`.
    let sel2_mat: [E; 2] = squeeze_point(&mut tr, b"HOLO_SEL_MAT", 2)
        .try_into()
        .unwrap();
    let sel2_gkr: [E; 2] = squeeze_point(&mut tr, b"HOLO_SEL_GKR", 2)
        .try_into()
        .unwrap();
    let eta_slice = tr.squeeze_ext4(b"HOLO_SLICE_ETA");
    let lambda_open = tr.squeeze_ext4(b"HOLO_OPEN_COMB");

    let open_z = crate::pcs::whir_open(&state_z, &ry, eval_z, &mut tr);
    drop(state_z);

    let mut pt_mat = r_mat;
    pt_mat.extend_from_slice(&sel2_mat);
    let mut pt_gkr = r_gkr.to_vec();
    pt_gkr.extend_from_slice(&sel2_gkr);

    let build_kernel_he = || {
        let mut k = vec![E::ZERO; (1usize << vk.native_pack_vars()) + 2];
        add_point_kernel(&mut k, E::ONE, &pt_mat);
        add_point_kernel(&mut k, lambda_open, &pt_gkr);
        k
    };

    let mut h_mat8 = [E::ZERO; 8];
    h_mat8[..7].copy_from_slice(&h_at_mat);
    let mut h_gkr8 = [E::ZERO; 8];
    h_gkr8[..7].copy_from_slice(&h_at_gkr);
    let claim_h = super8_blend2_claim(&h_mat8, &sel2_mat, eta_slice)
        + lambda_open * super8_blend2_claim(&h_gkr8, &sel2_gkr, eta_slice);
    let claim_e = super8_blend2_claim(&e_limbs_at_mat, &sel2_mat, eta_slice)
        + lambda_open * super8_blend2_claim(&e_limbs_at_gkr, &sel2_gkr, eta_slice);

    let scalars = [E::ONE, eta_slice];
    let open_h = {
        let _phase = crate::profile::span("hologram_open_h");
        whir_open_blend_from_state(
            &hologram.h_state,
            &scalars,
            build_kernel_he(),
            claim_h,
            &mut tr,
        )
    };
    let open_e = {
        let _phase = crate::profile::span("hologram_open_e");
        whir_open_blend_from_state(&state_e, &scalars, build_kernel_he(), claim_e, &mut tr)
    };

    Ok(HologramPublicProof {
        comm_z,
        row_rounds,
        row_values,
        col_rounds,
        eval_z,
        comm_e,
        m_sparse_claim,
        mat_rounds,
        h_at_mat,
        e_limbs_at_mat,
        q_root,
        gkr_layers,
        h_at_gkr,
        e_limbs_at_gkr,
        open_z,
        open_h,
        open_e,
    })
}

/// Sublinear native verifier requiring only the compact [`ShapeVerifierKey`].
pub fn verify_public_hologram(
    vk: &ShapeVerifierKey,
    public: &[F],
    statement: &[u8],
    proof: &HologramPublicProof,
) -> bool {
    if !vk.is_well_formed()
        || public.len() != vk.num_public
        || proof.row_rounds.len() != vk.log_rows
        || proof.col_rounds.len() != vk.var_bits
        || proof.mat_rounds.len() != vk.ell_nz
        || proof.gkr_layers.len() != vk.ell_nz + 2
        || proof.q_root.is_zero()
    {
        return false;
    }

    let mut tr = start_hologram_transcript(vk, statement, public, &proof.comm_z);
    let tau = squeeze_point(&mut tr, b"ZKHEM_TAU", vk.log_rows);
    let Some((row_final, rx)) = verify_sumcheck(
        &mut tr,
        b"ZKHEM_ROW_ROUND",
        &proof.row_rounds,
        ROW_DEGREE,
        E::ZERO,
    ) else {
        return false;
    };
    let [va, vb, vc] = proof.row_values;
    if row_final != eq_eval(&tau, &rx) * row_gate(prefix_indicator(&rx, vk.num_sbox), va, vb, vc) {
        return false;
    }
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &proof.row_values);
    let combine_vec = squeeze_point(&mut tr, b"ZKHEM_COMBINE", 3);
    let combine: [E; 3] = combine_vec.try_into().unwrap();
    let lambda = tr.squeeze_ext4(b"HEM_PUBLIC_CELLS");

    let mut col_claim = combine[0] * va + combine[1] * vb + combine[2] * vc;
    let mut weight = lambda;
    for v in core::iter::once(&F::ONE).chain(public) {
        col_claim += weight.mul_base(*v);
        weight *= lambda;
    }
    let Some((col_final, ry)) = verify_sumcheck(
        &mut tr,
        b"ZKHEM_COL_ROUND",
        &proof.col_rounds,
        COL_DEGREE,
        col_claim,
    ) else {
        return false;
    };

    // Sublinear matrix check: O(log P) closed-form Poseidon2 interior + Spark claim.
    let m_p2 = eval_poseidon2_interior_native(vk.hologram_meta, &rx, &ry, &combine);
    let mut m_total = m_p2 + proof.m_sparse_claim;
    let mut weight = lambda;
    for cell in 0..=vk.num_public {
        let eq = ry.iter().enumerate().fold(E::ONE, |acc, (bit, &r)| {
            acc * if (cell >> bit) & 1 == 1 {
                r
            } else {
                E::ONE - r
            }
        });
        m_total += weight * eq;
        weight *= lambda;
    }
    if col_final != m_total * proof.eval_z {
        return false;
    }

    tr.absorb(b"HOLO_COMM_E", &proof.comm_e.to_bytes());
    tr.absorb_ext4(b"HOLO_M_SPARSE", proof.m_sparse_claim);
    let alpha_mem = tr.squeeze_ext4(b"HOLO_ALPHA_MEM");
    let gamma_x = tr.squeeze_ext4(b"HOLO_GAMMA_X");
    let gamma_y = tr.squeeze_ext4(b"HOLO_GAMMA_Y");
    let delta = tr.squeeze_ext4(b"HOLO_DELTA");

    // 1. Verify Spark cubic matrix sumcheck.
    let mut mat_claim = proof.m_sparse_claim;
    let mut r_mat = Vec::with_capacity(vk.ell_nz);
    for round in &proof.mat_rounds {
        let at_one = round.iter().fold(E::ZERO, |acc, &c| acc + c);
        if round[0] + at_one != mat_claim {
            return false;
        }
        tr.absorb_ext4_slice(b"HOLO_MAT_ROUND", round);
        let c = tr.squeeze_ext4(b"HOLO_MAT_ROUND");
        mat_claim = eval_poly(round, c);
        r_mat.push(c);
    }
    tr.absorb_ext4_slice(b"HOLO_AT_MAT_H", &proof.h_at_mat);
    tr.absorb_ext4_slice(b"HOLO_AT_MAT_E", &proof.e_limbs_at_mat);
    let ex_mat = recompose_ext4_from_limb_evals(proof.e_limbs_at_mat[..4].try_into().unwrap());
    let ey_mat = recompose_ext4_from_limb_evals(proof.e_limbs_at_mat[4..].try_into().unwrap());
    let v_mat = combine[0] * proof.h_at_mat[2]
        + combine[1] * proof.h_at_mat[3]
        + combine[2] * proof.h_at_mat[4];
    if mat_claim != ex_mat * ey_mat * v_mat {
        return false;
    }

    // 2. Verify LogUp-GKR fractional binary tree.
    tr.absorb_ext4(b"HOLO_Q_ROOT", proof.q_root);
    let gkr_depth = vk.ell_nz + 2;
    let mut p_claim = E::ZERO;
    let mut q_claim = proof.q_root;
    let mut r_cur: Vec<E> = Vec::new();
    for (m_vars, layer) in proof.gkr_layers.iter().enumerate() {
        if layer.rounds.len() != m_vars {
            return false;
        }
        let [pl, pr, ql, qr] = layer.split;
        if m_vars == 0 {
            if pl * qr + pr * ql != p_claim || ql * qr != q_claim {
                return false;
            }
        } else {
            let beta = tr.squeeze_ext4(b"HOLO_GKR_BETA");
            let mut sc_claim = p_claim + beta * q_claim;
            let mut u_star = Vec::with_capacity(m_vars);
            for round in &layer.rounds {
                let at_one = round.iter().fold(E::ZERO, |acc, &c| acc + c);
                if round[0] + at_one != sc_claim {
                    return false;
                }
                tr.absorb_ext4_slice(b"HOLO_GKR_ROUND", round);
                let c = tr.squeeze_ext4(b"HOLO_GKR_ROUND");
                sc_claim = eval_poly(round, c);
                u_star.push(c);
            }
            if sc_claim != eq_eval(&r_cur, &u_star) * (pl * qr + pr * ql + beta * ql * qr) {
                return false;
            }
            r_cur = u_star;
        }
        tr.absorb_ext4_slice(b"HOLO_GKR_SPLIT", &layer.split);
        let c_bit = tr.squeeze_ext4(b"HOLO_GKR_BIT");
        p_claim = pl + c_bit * (pr - pl);
        q_claim = ql + c_bit * (qr - ql);
        let mut next_r = Vec::with_capacity(m_vars + 1);
        next_r.push(c_bit);
        next_r.extend_from_slice(&r_cur);
        r_cur = next_r;
    }
    if r_cur.len() != gkr_depth {
        return false;
    }
    let r_gkr = &r_cur[..vk.ell_nz];
    let (b0, b1) = (r_cur[vk.ell_nz], r_cur[vk.ell_nz + 1]);
    tr.absorb_ext4_slice(b"HOLO_AT_GKR_H", &proof.h_at_gkr);
    tr.absorb_ext4_slice(b"HOLO_AT_GKR_E", &proof.e_limbs_at_gkr);

    let ex_gkr = recompose_ext4_from_limb_evals(proof.e_limbs_at_gkr[..4].try_into().unwrap());
    let ey_gkr = recompose_ext4_from_limb_evals(proof.e_limbs_at_gkr[4..].try_into().unwrap());
    let id_eval = r_gkr.iter().enumerate().fold(E::ZERO, |acc, (j, &rj)| {
        acc + rj.mul_base(F::from_u64_reduced(1u64 << j))
    });
    let tbl_ex = eq_eval(&rx, &r_gkr[..vk.log_rows]);
    let tbl_ey = eq_eval(&ry, &r_gkr[..vk.var_bits]);

    let w0 = (E::ONE - b0) * (E::ONE - b1);
    let w1 = b0 * (E::ONE - b1);
    let w2 = (E::ONE - b0) * b1;
    let w3 = b0 * b1;
    let p_exp = w0 - w1 * proof.h_at_gkr[5] + w2 * delta - w3 * delta * proof.h_at_gkr[6];
    let q_exp = w0 * (gamma_x - proof.h_at_gkr[0] - alpha_mem * ex_gkr)
        + w1 * (gamma_x - id_eval - alpha_mem * tbl_ex)
        + w2 * (gamma_y - proof.h_at_gkr[1] - alpha_mem * ey_gkr)
        + w3 * (gamma_y - id_eval - alpha_mem * tbl_ey);
    if p_claim != p_exp || q_claim != q_exp {
        return false;
    }

    // 3. Verify WHIR openings of `Z`, `H_pair`, `E_pair`.
    let sel2_mat: [E; 2] = squeeze_point(&mut tr, b"HOLO_SEL_MAT", 2)
        .try_into()
        .unwrap();
    let sel2_gkr: [E; 2] = squeeze_point(&mut tr, b"HOLO_SEL_GKR", 2)
        .try_into()
        .unwrap();
    let eta_slice = tr.squeeze_ext4(b"HOLO_SLICE_ETA");
    let lambda_open = tr.squeeze_ext4(b"HOLO_OPEN_COMB");

    let z_schedule = vk.regime.schedule(vk.var_bits);
    if !crate::pcs::whir_verify_with_schedule(
        &proof.comm_z,
        vk.var_bits,
        &ry,
        proof.eval_z,
        &proof.open_z,
        &mut tr,
        &z_schedule,
    ) {
        return false;
    }

    let mut pt_mat = r_mat;
    pt_mat.extend_from_slice(&sel2_mat);
    let mut pt_gkr = r_gkr.to_vec();
    pt_gkr.extend_from_slice(&sel2_gkr);
    let terms_he = [
        WeightedPoint {
            weight: E::ONE,
            point: pt_mat,
        },
        WeightedPoint {
            weight: lambda_open,
            point: pt_gkr,
        },
    ];
    let mut h_mat8 = [E::ZERO; 8];
    h_mat8[..7].copy_from_slice(&proof.h_at_mat);
    let mut h_gkr8 = [E::ZERO; 8];
    h_gkr8[..7].copy_from_slice(&proof.h_at_gkr);
    let claim_h = super8_blend2_claim(&h_mat8, &sel2_mat, eta_slice)
        + lambda_open * super8_blend2_claim(&h_gkr8, &sel2_gkr, eta_slice);
    let claim_e = super8_blend2_claim(&proof.e_limbs_at_mat, &sel2_mat, eta_slice)
        + lambda_open * super8_blend2_claim(&proof.e_limbs_at_gkr, &sel2_gkr, eta_slice);

    let scalars = [E::ONE, eta_slice];
    let pack_schedule = vk.regime.schedule(vk.native_pack_vars());
    whir_verify_blend(
        &vk.hologram_comm,
        vk.native_pack_vars(),
        &scalars,
        &terms_he,
        claim_h,
        &proof.open_h,
        &mut tr,
        &pack_schedule,
    ) && whir_verify_blend(
        &proof.comm_e,
        vk.native_pack_vars(),
        &scalars,
        &terms_he,
        claim_e,
        &proof.open_e,
        &mut tr,
        &pack_schedule,
    )
}

// ----------------------------------------------------------------------------
// In-Circuit Recursive Hologram Proof (`RecursivePublicHemProof` for `Merge -> Merge`)
// ----------------------------------------------------------------------------

const REC_HOLO_VERSION: u64 = 0x5248_4F4C_0000_0001;

#[derive(Clone)]
pub(crate) struct SplitHologramRef {
    pub(crate) ell_nz: usize,
    pub(crate) pack_vars: usize,
    pub(crate) row_idx: Arc<Vec<u32>>,
    pub(crate) col_idx: Arc<Vec<u32>>,
    pub(crate) val_a: Arc<Vec<F>>,
    pub(crate) val_b: Arc<Vec<F>>,
    pub(crate) val_c: Arc<Vec<F>>,
    pub(crate) count_x: Arc<Vec<F>>,
    pub(crate) count_y: Arc<Vec<F>>,
    pub(crate) rec_h: Arc<PublicRecursionCommitment>,
}

impl SplitHologramRef {
    fn fill_h_super(&self, dst: &mut Vec<F>) {
        let nz_cap = 1usize << self.ell_nz;
        let eval_n = 1usize << self.pack_vars;
        dst.clear();
        dst.resize(eval_n, F::ZERO);
        for k in 0..nz_cap {
            dst[k] = F::from_u64_reduced(u64::from(self.row_idx[k]));
            dst[nz_cap + k] = F::from_u64_reduced(u64::from(self.col_idx[k]));
        }
        dst[2 * nz_cap..3 * nz_cap].copy_from_slice(&self.val_a);
        dst[3 * nz_cap..4 * nz_cap].copy_from_slice(&self.val_b);
        dst[4 * nz_cap..5 * nz_cap].copy_from_slice(&self.val_c);
        dst[5 * nz_cap..6 * nz_cap].copy_from_slice(&self.count_x);
        dst[6 * nz_cap..7 * nz_cap].copy_from_slice(&self.count_y);
    }
}

pub(crate) struct SecretAssignment(Vec<F>);
impl Drop for SecretAssignment {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.0, F::ZERO);
    }
}

/// Compact prover-side witness retained by split subtree nodes so `prove_root` can fold all
/// homogeneous siblings at a level into ONE `[CWYZ26]` `FoldedLevelWhirProof` without retaining
/// multi-GiB RS codewords across siblings.
pub(crate) struct SplitDeferredWitness {
    pub(crate) holo: SplitHologramRef,
    pub(crate) z_unpadded: SecretAssignment,
    pub(crate) rx: Vec<E>,
    pub(crate) ry: Vec<E>,
    pub(crate) z_levels: Vec<Vec<RecDigest>>,
    pub(crate) e_levels: Vec<Vec<RecDigest>>,
}

impl SplitDeferredWitness {
    fn fill_z_padded(&self, dst: &mut Vec<F>) {
        let eval_n = 1usize << self.holo.pack_vars;
        dst.clear();
        dst.reserve_exact(eval_n);
        dst.extend_from_slice(&self.z_unpadded.0);
        dst.resize(eval_n, F::ZERO);
    }

    fn fill_e_super(&self, dst: &mut Vec<F>) {
        let eq_rx = eq_table(&self.rx);
        let eq_ry = eq_table(&self.ry);
        let m = 1usize << self.holo.ell_nz;
        let eval_n = 1usize << self.holo.pack_vars;
        dst.clear();
        dst.resize(eval_n, F::ZERO);
        for k in 0..m {
            let lx = eq_rx[self.holo.row_idx[k] as usize].to_limbs();
            let ly = eq_ry[self.holo.col_idx[k] as usize].to_limbs();
            for j in 0..4 {
                dst[j * m + k] = lx[j];
                dst[(4 + j) * m + k] = ly[j];
            }
        }
    }
}

#[derive(Clone, Default)]
pub struct OptionalSplitWitness(pub(crate) Option<Arc<SplitDeferredWitness>>);

impl core::fmt::Debug for OptionalSplitWitness {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.write_str("..")
    }
}
impl PartialEq for OptionalSplitWitness {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl Eq for OptionalSplitWitness {}

/// Field-native Poseidon2 recursive public proof of a relation, for a parent relation to
/// verify. Verified both natively ([`verify_public_for_recursion`]) and inside a parent
/// [`super::relation::ConstraintSystem`] ([`verify_public_gadget`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursivePublicHemProof {
    pub comm_z: RecDigest,
    pub row_rounds: Vec<[E; ROW_DEGREE + 1]>,
    pub row_values: [E; 3],
    pub col_rounds: Vec<[E; COL_DEGREE + 1]>,
    pub eval_z: E,
    pub comm_e: RecDigest,
    pub m_sparse_claim: E,
    pub mat_rounds: Vec<[E; SPARK_MAT_DEGREE + 1]>,
    pub h_at_mat: [E; 7],
    pub e_limbs_at_mat: [E; 8],
    pub q_root: E,
    pub gkr_layers: Vec<LogUpGkrLayer>,
    pub h_at_gkr: [E; 7],
    pub e_limbs_at_gkr: [E; 8],
    pub opening: Correlated3WhirProof,
    #[doc(hidden)]
    pub split_witness: OptionalSplitWitness,
}

impl RecursivePublicHemProof {
    pub fn placeholder(vk: &ShapeVerifierKey) -> Option<Self> {
        if !vk.is_well_formed() {
            return None;
        }
        let params = FixedPathWhirParams::new(vk.regime, vk.pack_vars()).ok()?;
        let gkr_depth = vk.ell_nz + 2;
        Some(Self {
            comm_z: [F::ZERO; 4],
            row_rounds: vec![[E::ZERO; ROW_DEGREE + 1]; vk.log_rows],
            row_values: [E::ZERO; 3],
            col_rounds: vec![[E::ZERO; COL_DEGREE + 1]; vk.var_bits],
            eval_z: E::ZERO,
            comm_e: [F::ZERO; 4],
            m_sparse_claim: E::ONE,
            mat_rounds: vec![[E::ZERO; SPARK_MAT_DEGREE + 1]; vk.ell_nz],
            h_at_mat: [E::ZERO; 7],
            e_limbs_at_mat: [E::ZERO; 8],
            q_root: E::ONE,
            gkr_layers: (0..gkr_depth)
                .map(|m| LogUpGkrLayer {
                    rounds: vec![[E::ZERO; GKR_LAYER_DEGREE + 1]; m],
                    split: [E::ZERO, E::ZERO, E::ONE, E::ONE],
                })
                .collect(),
            h_at_gkr: [E::ZERO; 7],
            e_limbs_at_gkr: [E::ZERO; 8],
            opening: params.placeholder_correlated3(),
            split_witness: OptionalSplitWitness::default(),
        })
    }

    pub fn well_formed(&self, vk: &ShapeVerifierKey) -> bool {
        if !vk.is_well_formed() {
            return false;
        }
        let Ok(params) = FixedPathWhirParams::new(vk.regime, vk.pack_vars()) else {
            return false;
        };
        let gkr_depth = vk.ell_nz + 2;
        vk.rec_hologram_root.is_some()
            && self.row_rounds.len() == vk.log_rows
            && self.col_rounds.len() == vk.var_bits
            && self.mat_rounds.len() == vk.ell_nz
            && self.gkr_layers.len() == gkr_depth
            && self
                .gkr_layers
                .iter()
                .enumerate()
                .all(|(m, l)| l.rounds.len() == m)
            && params.well_formed_correlated3(&self.opening)
    }
}

fn start_rec_hologram_transcript<B: RecBackend>(
    b: &mut B,
    vk: &ShapeVerifierKey,
    statement_tag: [u8; 32],
    public: &[B::W],
    comm_z: &[B::W; 4],
) -> RecTranscript<B::W> {
    let rec_root = vk
        .rec_hologram_root
        .expect("Poseidon2 recursion verifier key");
    let mut header = vec![
        rec_f(REC_HOLO_VERSION),
        rec_f(vk.log_rows as u64),
        rec_f(vk.num_sbox as u64),
        rec_f(vk.num_vars as u64),
        rec_f(vk.num_public as u64),
        rec_f(vk.var_bits as u64),
        rec_f(vk.ell_nz as u64),
        rec_f(vk.hologram_meta.poseidon2_perms as u64),
        rec_f(vk.hologram_meta.pub_var_blocks as u64),
        rec_f(vk.regime as u64),
    ];
    for chunk in vk.shape_digest.as_chunks::<4>().0 {
        header.push(rec_f(u64::from(u32::from_le_bytes(*chunk))));
    }
    for chunk in statement_tag.as_chunks::<4>().0 {
        header.push(rec_f(u64::from(u32::from_le_bytes(*chunk))));
    }
    header.extend_from_slice(&rec_root);
    let mut tr = RecTranscript::new();
    let header_w: Vec<B::W> = header.into_iter().map(B::W::constant).collect();
    tr.absorb(b, 200, &header_w);
    tr.absorb(b, 201, public);
    tr.absorb(b, 202, comm_z);
    tr
}

fn row_sumcheck_rec(
    tr: &mut RecTranscript<F>,
    b: &mut RecNative,
    tau: &[E],
    num_sbox: usize,
    mut base: [Vec<F>; 3],
) -> (Vec<[E; ROW_DEGREE + 1]>, Vec<E>, [E; 3]) {
    let mut ext: [Vec<E>; 3] = core::array::from_fn(|_| Vec::new());
    let mut selector = PrefixSelector::new(num_sbox);
    let mut eq_rest = eq_table(&tau[1..]);
    let mut eq_bound = E::ONE;
    let bind = |c: E,
                round: usize,
                base: &mut [Vec<F>; 3],
                ext: &mut [Vec<E>; 3],
                selector: &mut PrefixSelector| {
        if round == 1 {
            for (e, bm) in ext.iter_mut().zip(base.iter_mut()) {
                *e = fold_base(bm, c);
                *bm = Vec::new();
            }
        } else {
            for e in ext.iter_mut() {
                fold_in_place(e, c, false);
            }
        }
        selector.fold(c);
    };
    let mut rounds = Vec::with_capacity(tau.len());
    let mut rx = Vec::with_capacity(tau.len());
    for round in 0..tau.len() {
        let h = if round == 0 {
            row_round(
                base.each_ref().map(Vec::as_slice),
                &eq_rest,
                &selector,
                false,
            )
        } else {
            row_round(
                ext.each_ref().map(Vec::as_slice),
                &eq_rest,
                &selector,
                false,
            )
        };
        let l1 = eq_bound * (tau[round] + tau[round] - E::ONE);
        let l0 = eq_bound * (E::ONE - tau[round]);
        let mut coeffs = [E::ZERO; ROW_DEGREE + 1];
        for (k, &hk) in h.iter().enumerate() {
            coeffs[k] += l0 * hk;
            coeffs[k + 1] += l1 * hk;
        }
        tr.absorb_exts(b, 204, &coeffs.map(RecExt::constant));
        let c = tr.ext(b, 205).value(b);
        rounds.push(coeffs);
        rx.push(c);
        bind(c, round + 1, &mut base, &mut ext, &mut selector);
        if round + 1 < tau.len() {
            let t = tau[round];
            let tc = t * c;
            eq_bound *= E::ONE - t - c + tc + tc;
            fold_pairs(&mut eq_rest, false, |lo, hi| lo + hi);
        }
    }
    (rounds, rx, [ext[0][0], ext[1][0], ext[2][0]])
}

fn col_sumcheck_rec(
    tr: &mut RecTranscript<F>,
    b: &mut RecNative,
    mut tm: Vec<E>,
    z: &[F],
) -> (Vec<[E; COL_DEGREE + 1]>, Vec<E>, E) {
    let n = tm.len().trailing_zeros() as usize;
    let mut tz: Vec<E> = Vec::new();
    let mut rounds = Vec::with_capacity(n);
    let mut ry = Vec::with_capacity(n);
    for round in 0..n {
        let evals = if round == 0 {
            round_evals(0..tm.len() / 2, |i| {
                let (m0, m1) = (tm[2 * i], tm[2 * i + 1]);
                let (z0, z1) = (z[2 * i], z[2 * i + 1]);
                [
                    m0.mul_base(z0),
                    m1.mul_base(z1),
                    (m1 + m1 - m0).mul_base(z1 + z1 - z0),
                ]
            })
        } else {
            let tz = &tz;
            round_evals(0..tm.len() / 2, |i| {
                let (m0, m1) = (tm[2 * i], tm[2 * i + 1]);
                let (z0, z1) = (tz[2 * i], tz[2 * i + 1]);
                [m0 * z0, m1 * z1, (m1 + m1 - m0) * (z1 + z1 - z0)]
            })
        };
        let coeffs: [E; COL_DEGREE + 1] = evals_to_coeffs(&evals).try_into().unwrap();
        tr.absorb_exts(b, 209, &coeffs.map(RecExt::constant));
        let c = tr.ext(b, 210).value(b);
        rounds.push(coeffs);
        ry.push(c);
        if round == 0 {
            tz = fold_base(z, c);
        } else {
            fold_in_place(&mut tz, c, false);
        }
        fold_in_place(&mut tm, c, false);
    }
    (rounds, ry, tz[0])
}

/// Emit a recursive Poseidon2 public proof suitable for verification inside a parent
/// [`ConstraintSystem`] via [`verify_public_gadget`].
pub fn prove_public_for_recursion(
    shape: &Shape,
    hologram: &ShapeHologram,
    assignment: Vec<F>,
    statement_tag: [u8; 32],
) -> Result<RecursivePublicHemProof, ZkHemError> {
    prove_public_for_recursion_inner(shape, hologram, assignment, statement_tag, true)
}

/// Emit the algebraic recursive proof + compact [`SplitDeferredWitness`] for split subtree
/// recursion, skipping redundant per-child WHIR cascades that `prove_root` folds per level!
pub(crate) fn prove_public_for_split(
    shape: &Shape,
    hologram: &ShapeHologram,
    assignment: Vec<F>,
    statement_tag: [u8; 32],
) -> Result<RecursivePublicHemProof, ZkHemError> {
    prove_public_for_recursion_inner(shape, hologram, assignment, statement_tag, false)
}

fn prove_public_for_recursion_inner(
    shape: &Shape,
    hologram: &ShapeHologram,
    mut assignment: Vec<F>,
    statement_tag: [u8; 32],
    with_individual_opening: bool,
) -> Result<RecursivePublicHemProof, ZkHemError> {
    let vk = &hologram.vk;
    let rec_h = hologram
        .rec_h
        .as_deref()
        .ok_or(ZkHemError::RelationTooLarge)?;
    let split_holo = hologram.split_ref().ok_or(ZkHemError::RelationTooLarge)?;
    if vk.shape_digest != shape.digest() || !vk.regime.uses_poseidon2_canopy() {
        return Err(ZkHemError::Unsatisfied);
    }
    if assignment.len() != shape.num_vars || assignment.first() != Some(&F::ONE) {
        return Err(ZkHemError::Unsatisfied);
    }
    let public = assignment[1..=shape.num_public].to_vec();
    let row_base = row_tables(shape, &assignment, true).ok_or(ZkHemError::Unsatisfied)?;
    let z_unpadded = SecretAssignment(assignment.clone());

    let pack_vars = vk.pack_vars();
    let rec_params =
        FixedPathWhirParams::new(vk.regime, pack_vars).map_err(|_| ZkHemError::RelationTooLarge)?;
    assignment.resize(1 << pack_vars, F::ZERO);
    let (comm_z, z_comm_opt, z_levels_opt) = if with_individual_opening {
        let zc = commit_for_recursion(&rec_params, &assignment)
            .map_err(|_| ZkHemError::RelationTooLarge)?;
        (zc.root(), Some(zc), None)
    } else {
        let (r, lvls) = commit_levels_for_recursion(&rec_params, &assignment)
            .map_err(|_| ZkHemError::RelationTooLarge)?;
        (r, None, Some(lvls))
    };

    let mut b = RecNative::default();
    let mut tr = start_rec_hologram_transcript(&mut b, vk, statement_tag, &public, &comm_z);
    let tau: Vec<E> = (0..vk.log_rows)
        .map(|_| tr.ext(&mut b, 203).value(&b))
        .collect();
    let (row_rounds, rx, row_values) =
        row_sumcheck_rec(&mut tr, &mut b, &tau, vk.num_sbox, row_base);
    tr.absorb_exts(&mut b, 206, &row_values.map(RecExt::constant));
    let combine: [E; 3] = core::array::from_fn(|_| tr.ext(&mut b, 207).value(&b));
    let lambda = tr.ext(&mut b, 208).value(&b);

    let eq_rx = eq_table(&rx);
    let mut tm = column_table(shape, &eq_rx, &combine, 1 << vk.var_bits);
    let mut weight = lambda;
    for slot in tm.iter_mut().take(vk.num_public + 1) {
        *slot += weight;
        weight *= lambda;
    }
    let (col_rounds, ry, eval_z) =
        col_sumcheck_rec(&mut tr, &mut b, tm, &assignment[..1 << vk.var_bits]);
    qsag_asm::volatile_fill(&mut assignment, F::ZERO);
    drop(assignment);
    tr.absorb_exts(&mut b, 211, &[RecExt::constant(eval_z)]);

    let eq_ry = eq_table(&ry);
    let m_nz = 1usize << vk.ell_nz;
    let (ex, ey) = spark_read_tables(hologram, &eq_rx, &eq_ry);
    let val_comb = spark_value_table(hologram, &combine);
    let [m_sparse_claim] = round_evals::<1>(0..m_nz, |k| [ex[k] * ey[k] * val_comb[k]]);

    let mut e_super = pack_e_super(&ex, &ey);
    let (comm_e, e_comm_opt, e_levels_opt) = if with_individual_opening {
        let ec = commit_for_recursion(&rec_params, &e_super)
            .map_err(|_| ZkHemError::RelationTooLarge)?;
        (ec.root(), Some(ec), None)
    } else {
        let (r, lvls) = commit_levels_for_recursion(&rec_params, &e_super)
            .map_err(|_| ZkHemError::RelationTooLarge)?;
        (r, None, Some(lvls))
    };

    tr.absorb(&mut b, 212, &comm_e);
    tr.absorb_exts(&mut b, 213, &[RecExt::constant(m_sparse_claim)]);
    let alpha_mem = tr.ext(&mut b, 214).value(&b);
    let gamma_x = tr.ext(&mut b, 215).value(&b);
    let gamma_y = tr.ext(&mut b, 216).value(&b);
    let delta = tr.ext(&mut b, 217).value(&b);

    let (mat_rounds, r_mat, _) = run_cubic_triple_sumcheck_slices(&ex, &ey, &val_comb, |coeffs| {
        tr.absorb_exts(&mut b, 218, &coeffs.map(RecExt::constant));
        tr.ext(&mut b, 219).value(&b)
    });
    drop(val_comb);
    let half_e = 4 * m_nz;
    let (h_at_mat, e_limbs_at_mat) =
        eval_h_and_e_limbs_at_point(hologram, &e_super[..half_e], &e_super[half_e..], &r_mat);
    tr.absorb_exts(&mut b, 220, &h_at_mat.map(RecExt::constant));
    tr.absorb_exts(&mut b, 221, &e_limbs_at_mat.map(RecExt::constant));

    let (q_root, gkr_layers, r_cur) = {
        // The four closures take turns on the one transcript.
        let shared = core::cell::RefCell::new((&mut tr, &mut b));
        prove_logup_gkr(
            |idx| {
                eval_gkr_leaf(
                    hologram, &ex, &ey, &eq_rx, &eq_ry, alpha_mem, gamma_x, gamma_y, delta, idx,
                )
            },
            vk.ell_nz,
            |q_root| {
                let (tr, b) = &mut *shared.borrow_mut();
                let (tr, b) = (&mut **tr, &mut **b);
                tr.absorb_exts(b, 222, &[RecExt::constant(q_root)]);
            },
            || {
                let (tr, b) = &mut *shared.borrow_mut();
                let (tr, b) = (&mut **tr, &mut **b);
                tr.ext(b, 223).value(&*b)
            },
            |coeffs| {
                let (tr, b) = &mut *shared.borrow_mut();
                let (tr, b) = (&mut **tr, &mut **b);
                tr.absorb_exts(b, 224, &coeffs.map(RecExt::constant));
                tr.ext(b, 225).value(&*b)
            },
            |ends| {
                let (tr, b) = &mut *shared.borrow_mut();
                let (tr, b) = (&mut **tr, &mut **b);
                tr.absorb_exts(b, 226, &ends.map(RecExt::constant));
                tr.ext(b, 227).value(&*b)
            },
        )
        .ok_or(ZkHemError::MaskRankDeficient)?
    };
    drop(ex);
    drop(ey);
    drop(eq_rx);
    drop(eq_ry);

    let r_gkr = &r_cur[..vk.ell_nz];
    let (h_at_gkr, e_limbs_at_gkr) =
        eval_h_and_e_limbs_at_point(hologram, &e_super[..half_e], &e_super[half_e..], r_gkr);
    qsag_asm::volatile_fill(&mut e_super, F::ZERO);
    drop(e_super);
    tr.absorb_exts(&mut b, 228, &h_at_gkr.map(RecExt::constant));
    tr.absorb_exts(&mut b, 229, &e_limbs_at_gkr.map(RecExt::constant));

    let sel_mat: [E; 3] = core::array::from_fn(|_| tr.ext(&mut b, 230).value(&b));
    let sel_gkr: [E; 3] = core::array::from_fn(|_| tr.ext(&mut b, 231).value(&b));

    let (opening, z_levels, e_levels) = if with_individual_opening {
        let z_comm = z_comm_opt.expect("z_comm");
        let e_comm = e_comm_opt.expect("e_comm");
        let z_lvls = z_comm.levels().to_vec();
        let e_lvls = e_comm.levels().to_vec();
        let mut p_z = ry.clone();
        p_z.resize(pack_vars, E::ZERO);
        let mut p_mat = r_mat;
        p_mat.extend_from_slice(&sel_mat);
        let mut p_gkr = r_gkr.to_vec();
        p_gkr.extend_from_slice(&sel_gkr);
        let op = open_correlated3_for_recursion(
            &rec_params,
            &mut tr,
            z_comm,
            rec_h,
            e_comm,
            &[p_z, p_mat, p_gkr],
        )
        .map_err(|_| ZkHemError::RelationTooLarge)?;
        (op, z_lvls, e_lvls)
    } else {
        (
            rec_params.placeholder_correlated3(),
            z_levels_opt.expect("z_levels"),
            e_levels_opt.expect("e_levels"),
        )
    };
    debug_assert!(!b.failed);

    let split_witness = OptionalSplitWitness(Some(Arc::new(SplitDeferredWitness {
        holo: split_holo,
        z_unpadded,
        rx,
        ry,
        z_levels,
        e_levels,
    })));

    Ok(RecursivePublicHemProof {
        comm_z,
        row_rounds,
        row_values,
        col_rounds,
        eval_z,
        comm_e,
        m_sparse_claim,
        mat_rounds,
        h_at_mat,
        e_limbs_at_mat,
        q_root,
        gkr_layers,
        h_at_gkr,
        e_limbs_at_gkr,
        opening,
        split_witness,
    })
}

fn eval_poly_gadget<B: RecBackend>(
    b: &mut B,
    coeffs: &[RecExt<B::W>],
    x: &RecExt<B::W>,
) -> RecExt<B::W> {
    let (last, rest) = coeffs.split_last().expect("nonempty polynomial");
    rest.iter()
        .rev()
        .fold(last.clone(), |acc, c| acc.mul(b, x).add(c))
}

fn verify_sumcheck_gadget<B: RecBackend>(
    b: &mut B,
    tr: &mut RecTranscript<B::W>,
    absorb_tag: u64,
    squeeze_tag: u64,
    rounds: &[Vec<E>],
    mut claim: RecExt<B::W>,
) -> (RecExt<B::W>, Vec<RecExt<B::W>>) {
    let mut point = Vec::with_capacity(rounds.len());
    for round in rounds {
        let rw: Vec<RecExt<B::W>> = round.iter().map(|&v| RecExt::alloc(b, v)).collect();
        let at_one = rw.iter().fold(RecExt::zero(), |acc, c| acc.add(c));
        rw[0].add(&at_one).equal(b, &claim);
        tr.absorb_exts(b, absorb_tag, &rw);
        let c = tr.ext(b, squeeze_tag);
        claim = eval_poly_gadget(b, &rw, &c);
        point.push(c);
    }
    (claim, point)
}

fn recompose_ext4_gadget<W: RecBase>(limbs: &[RecExt<W>; 4]) -> RecExt<W> {
    let basis = limb_basis();
    let mut acc = RecExt::zero();
    for (j, limb_ext) in limbs.iter().enumerate() {
        let b_limbs = basis[j].to_limbs();
        // `basis[j]` is the unit vector `e_j`, so multiplying `limb_ext` by `e_j` in the tower
        // is a pure constant linear combination over `limb_ext.0` with ZERO multiplications!
        // Specifically, in `E`, `x * e_j`: evaluate on unit vectors via native `E`!
        let mut cols = [[F::ZERO; 4]; 4];
        for i in 0..4 {
            let mut u = [F::ZERO; 4];
            u[i] = F::ONE;
            cols[i] = (E::from_limbs(u) * E::from_limbs(b_limbs)).to_limbs();
        }
        let prod = RecExt(core::array::from_fn(|out_l| {
            (0..4).fold(W::constant(F::ZERO), |s, in_l| {
                s.plus(&limb_ext.0[in_l].scale(cols[in_l][out_l]))
            })
        }));
        acc = acc.add(&prod);
    }
    acc
}

fn super8_claim_gadget<B: RecBackend>(
    b: &mut B,
    slices: &[RecExt<B::W>; 8],
    sel: &[RecExt<B::W>; 3],
) -> RecExt<B::W> {
    let eq_s = eq_table_gadget(b, sel);
    let mut acc = RecExt::zero();
    for (v, w) in slices.iter().zip(&eq_s) {
        let prod = v.mul(b, w);
        acc = acc.add(&prod);
    }
    acc
}

/// The exact boundary between the algebraic IOP and correlated WHIR verification.
/// All transcript lanes, roots, points, claim presence bits and values are committed.
/// In particular, a digest of roots alone would not bind the IOP's evaluation claims.
#[derive(Clone)]
pub(crate) struct DeferredPcsClaim<W: RecBase> {
    pub(crate) regime: WhirSecurityRegime,
    pub(crate) num_vars: usize,
    pub(crate) transcript: [W; 12],
    pub(crate) roots: [[W; 4]; 3],
    pub(crate) points: [Vec<RecExt<W>>; 3],
    pub(crate) claims: [[Option<RecExt<W>>; 3]; 3],
}

impl<W: RecBase> DeferredPcsClaim<W> {
    pub(crate) fn digest<B: RecBackend<W = W>>(&self, b: &mut B) -> [W; 4] {
        let mut words = vec![
            W::constant(rec_f(self.regime as u64)),
            W::constant(rec_f(self.num_vars as u64)),
        ];
        words.extend_from_slice(&self.transcript);
        words.extend(self.roots.iter().flatten().cloned());
        for point in &self.points {
            words.push(W::constant(rec_f(point.len() as u64)));
            words.extend(point.iter().flat_map(|v| v.0.clone()));
        }
        for claim in self.claims.iter().flatten() {
            words.push(W::constant(rec_f(u64::from(claim.is_some()))));
            words.extend(claim.clone().unwrap_or_else(RecExt::zero).0);
        }
        let mut tr = RecTranscript::new();
        tr.absorb(b, 0x4450_4353_0001, &words);
        core::array::from_fn(|i| b.pin(tr.state[i].clone()))
    }
}

impl DeferredPcsClaim<F> {
    pub(crate) fn to_folded_edge_spec(&self) -> FoldedEdgeSpec {
        let mut nb = RecNative::default();
        let claim_digest = self.digest(&mut nb);
        let points = core::array::from_fn(|j| {
            self.points[j]
                .iter()
                .map(|ext| E::from_limbs(ext.0))
                .collect()
        });
        let claims = core::array::from_fn(|m| {
            core::array::from_fn(|j| self.claims[m][j].as_ref().map(|ext| E::from_limbs(ext.0)))
        });
        FoldedEdgeSpec {
            regime: self.regime,
            num_vars: self.num_vars,
            claim_digest,
            roots: self.roots,
            points,
            claims,
        }
    }
}

pub(crate) fn prove_folded_level_from_split(
    level: usize,
    top_accumulator_root: RecDigest,
    items: &[(&DeferredPcsClaim<F>, &SplitDeferredWitness)],
) -> Result<FoldedLevelWhirProof, ZkHemError> {
    if items.is_empty() {
        return Err(ZkHemError::Unsatisfied);
    }
    let specs: Vec<FoldedEdgeSpec> = items.iter().map(|(c, _)| c.to_folded_edge_spec()).collect();
    let holo0 = &items[0].1.holo;
    prove_folded_level_for_recursion(
        level,
        top_accumulator_root,
        &specs,
        |k, dst| {
            if k == 0 {
                holo0.fill_h_super(dst);
            } else {
                let u = (k - 1) / 2;
                if (k - 1) % 2 == 0 {
                    items[u].1.fill_z_padded(dst);
                } else {
                    items[u].1.fill_e_super(dst);
                }
            }
        },
        |k| {
            if k == 0 {
                holo0.rec_h.levels()
            } else {
                let u = (k - 1) / 2;
                if (k - 1) % 2 == 0 {
                    &items[u].1.z_levels
                } else {
                    &items[u].1.e_levels
                }
            }
        },
    )
    .map_err(|_| ZkHemError::RelationTooLarge)
}

pub(crate) fn verify_folded_level_claims(
    level: usize,
    top_accumulator_root: RecDigest,
    claims: &[&DeferredPcsClaim<F>],
    proof: &FoldedLevelWhirProof,
) -> bool {
    let specs: Vec<FoldedEdgeSpec> = claims.iter().map(|c| c.to_folded_edge_spec()).collect();
    verify_folded_level(level, top_accumulator_root, &specs, proof)
}

/// Complete fixed-topology verifier. Existing callers still discharge the PCS in-circuit.
pub(crate) fn verify_public_gadget<B: RecBackend>(
    b: &mut B,
    vk: &ShapeVerifierKey,
    statement_tag: [u8; 32],
    public: &[B::W],
    proof: &RecursivePublicHemProof,
) {
    let obligation = verify_public_algebraic_gadget(b, vk, statement_tag, public, proof);
    let params =
        FixedPathWhirParams::new(vk.regime, vk.pack_vars()).expect("validated recursion params");
    let mut tr = RecTranscript {
        state: obligation.transcript,
    };
    verify_correlated3_gadget(
        b,
        &params,
        &mut tr,
        &obligation.roots,
        &obligation.points,
        &obligation.claims,
        &proof.opening,
    );
}

/// Verify the algebraic IOP and return its remaining PCS obligation. This is NOT an
/// acceptance predicate: a caller must bind this obligation into its public output and
/// discharge it with the full WHIR verifier before accepting the enclosing proof.
pub(crate) fn verify_public_algebraic_gadget<B: RecBackend>(
    b: &mut B,
    vk: &ShapeVerifierKey,
    statement_tag: [u8; 32],
    public: &[B::W],
    proof: &RecursivePublicHemProof,
) -> DeferredPcsClaim<B::W> {
    assert_eq!(public.len(), vk.num_public);
    let rec_root = vk
        .rec_hologram_root
        .expect("Poseidon2 recursion verifier key")
        .map(B::W::constant);

    super::recursive_whir::census("sumchecks");
    let comm_z: [B::W; 4] = proof.comm_z.map(|x| b.alloc(x));
    let mut tr = start_rec_hologram_transcript(b, vk, statement_tag, public, &comm_z);
    let tau: Vec<RecExt<B::W>> = (0..vk.log_rows).map(|_| tr.ext(b, 203)).collect();

    let row_vecs: Vec<Vec<E>> = proof.row_rounds.iter().map(|r| r.to_vec()).collect();
    let (row_final, rx) = verify_sumcheck_gadget(b, &mut tr, 204, 205, &row_vecs, RecExt::zero());
    let row_vals: [RecExt<B::W>; 3] = proof.row_values.map(|v| RecExt::alloc(b, v));
    let [va, vb, vc] = &row_vals;

    // `row_final == eq(tau, rx) * (s * (va^7 - va*vb) + va*vb - vc)`.
    let eq_tau_rx = eq_eval_gadget(b, &tau, &rx);
    let sel_sbox = prefix_indicator_gadget(b, &rx, vk.num_sbox);
    let va2 = va.mul(b, va);
    let va4 = va2.mul(b, &va2);
    let va6 = va4.mul(b, &va2);
    let va7 = va6.mul(b, va);
    let vab = va.mul(b, vb);
    let gate_inner = sel_sbox.mul(b, &va7.sub(&vab)).add(&vab).sub(vc);
    let expected_row = eq_tau_rx.mul(b, &gate_inner);
    row_final.equal(b, &expected_row);

    tr.absorb_exts(b, 206, &row_vals);
    let combine: [RecExt<B::W>; 3] = core::array::from_fn(|_| tr.ext(b, 207));
    let lambda = tr.ext(b, 208);

    let mut col_claim = combine[0]
        .mul(b, va)
        .add(&combine[1].mul(b, vb))
        .add(&combine[2].mul(b, vc));
    let mut weight = lambda.clone();
    col_claim = col_claim.add(&weight);
    for pub_w in public {
        weight = weight.mul(b, &lambda);
        let term = weight.mul_base(b, pub_w);
        col_claim = col_claim.add(&term);
    }

    let col_vecs: Vec<Vec<E>> = proof.col_rounds.iter().map(|r| r.to_vec()).collect();
    let (col_final, ry) = verify_sumcheck_gadget(b, &mut tr, 209, 210, &col_vecs, col_claim);
    let eval_z = RecExt::alloc(b, proof.eval_z);
    tr.absorb_exts(b, 211, core::slice::from_ref(&eval_z));

    let comm_e: [B::W; 4] = proof.comm_e.map(|x| b.alloc(x));
    let m_sparse = RecExt::alloc(b, proof.m_sparse_claim);
    tr.absorb(b, 212, &comm_e);
    tr.absorb_exts(b, 213, core::slice::from_ref(&m_sparse));

    // Closed-form Poseidon2 interior + public-input column weights + Spark sparse claim.
    let m_p2 = eval_poseidon2_interior_gadget(b, vk.hologram_meta, &rx, &ry, &combine);
    let mut m_total = m_p2.add(&m_sparse);
    let one = RecExt::<B::W>::one();
    let mut weight = lambda.clone();
    for cell in 0..=vk.num_public {
        let mut eq_cell = one.clone();
        for (bit, r) in ry.iter().enumerate() {
            let factor = if (cell >> bit) & 1 == 1 {
                r.clone()
            } else {
                one.sub(r)
            };
            eq_cell = eq_cell.mul(b, &factor);
        }
        let term = weight.mul(b, &eq_cell);
        m_total = m_total.add(&term);
        if cell < vk.num_public {
            weight = weight.mul(b, &lambda);
        }
    }
    let expected_col = m_total.mul(b, &eval_z);
    col_final.equal(b, &expected_col);

    let alpha_mem = tr.ext(b, 214);
    let gamma_x = tr.ext(b, 215);
    let gamma_y = tr.ext(b, 216);
    let delta = tr.ext(b, 217);

    // 1. Spark cubic matrix sumcheck.
    let mat_vecs: Vec<Vec<E>> = proof.mat_rounds.iter().map(|r| r.to_vec()).collect();
    let (mat_final, r_mat) =
        verify_sumcheck_gadget(b, &mut tr, 218, 219, &mat_vecs, m_sparse.clone());
    let h_mat: [RecExt<B::W>; 7] = proof.h_at_mat.map(|v| RecExt::alloc(b, v));
    let e_limbs_mat: [RecExt<B::W>; 8] = proof.e_limbs_at_mat.map(|v| RecExt::alloc(b, v));
    tr.absorb_exts(b, 220, &h_mat);
    tr.absorb_exts(b, 221, &e_limbs_mat);
    let ex_mat = recompose_ext4_gadget(&core::array::from_fn(|j| e_limbs_mat[j].clone()));
    let ey_mat = recompose_ext4_gadget(&core::array::from_fn(|j| e_limbs_mat[4 + j].clone()));
    let v_mat = combine[0]
        .mul(b, &h_mat[2])
        .add(&combine[1].mul(b, &h_mat[3]))
        .add(&combine[2].mul(b, &h_mat[4]));
    let ex_ey_mat = ex_mat.mul(b, &ey_mat);
    let expected_mat = ex_ey_mat.mul(b, &v_mat);
    mat_final.equal(b, &expected_mat);

    // 2. LogUp-GKR fractional binary tree + nonzero root check (`q_root * q_root_inv == 1`).
    super::recursive_whir::census("gkr");
    let q_root = RecExt::alloc(b, proof.q_root);
    let q_root_inv = RecExt::alloc(b, q_root.value(b).inv());
    q_root.mul(b, &q_root_inv).equal(b, &one);
    tr.absorb_exts(b, 222, core::slice::from_ref(&q_root));

    let gkr_depth = vk.ell_nz + 2;
    let mut p_claim = RecExt::zero();
    let mut q_claim = q_root;
    let mut r_cur: Vec<RecExt<B::W>> = Vec::new();
    for (m_vars, layer) in proof.gkr_layers.iter().enumerate() {
        let split_w: [RecExt<B::W>; 4] = layer.split.map(|v| RecExt::alloc(b, v));
        let [pl, pr, ql, qr] = &split_w;
        let pl_qr = pl.mul(b, qr);
        let pr_ql = pr.mul(b, ql);
        let p_comb = pl_qr.add(&pr_ql);
        let q_comb = ql.mul(b, qr);
        if m_vars == 0 {
            p_comb.equal(b, &p_claim);
            q_comb.equal(b, &q_claim);
        } else {
            let beta = tr.ext(b, 223);
            let sc_init = p_claim.add(&beta.mul(b, &q_claim));
            let l_vecs: Vec<Vec<E>> = layer.rounds.iter().map(|r| r.to_vec()).collect();
            let (sc_final, u_star) = verify_sumcheck_gadget(b, &mut tr, 224, 225, &l_vecs, sc_init);
            let eq_u = eq_eval_gadget(b, &r_cur, &u_star);
            let inner = p_comb.add(&beta.mul(b, &q_comb));
            let expected_sc = eq_u.mul(b, &inner);
            sc_final.equal(b, &expected_sc);
            r_cur = u_star;
        }
        tr.absorb_exts(b, 226, &split_w);
        let c_bit = tr.ext(b, 227);
        p_claim = pl.add(&c_bit.mul(b, &pr.sub(pl)));
        q_claim = ql.add(&c_bit.mul(b, &qr.sub(ql)));
        let mut next_r = Vec::with_capacity(m_vars + 1);
        next_r.push(c_bit);
        next_r.extend_from_slice(&r_cur);
        r_cur = next_r;
    }
    assert_eq!(r_cur.len(), gkr_depth);
    let r_gkr = &r_cur[..vk.ell_nz];
    let b0 = &r_cur[vk.ell_nz];
    let b1 = &r_cur[vk.ell_nz + 1];

    let h_gkr: [RecExt<B::W>; 7] = proof.h_at_gkr.map(|v| RecExt::alloc(b, v));
    let e_limbs_gkr: [RecExt<B::W>; 8] = proof.e_limbs_at_gkr.map(|v| RecExt::alloc(b, v));
    tr.absorb_exts(b, 228, &h_gkr);
    tr.absorb_exts(b, 229, &e_limbs_gkr);

    let ex_gkr = recompose_ext4_gadget(&core::array::from_fn(|j| e_limbs_gkr[j].clone()));
    let ey_gkr = recompose_ext4_gadget(&core::array::from_fn(|j| e_limbs_gkr[4 + j].clone()));
    let id_eval = r_gkr
        .iter()
        .enumerate()
        .fold(RecExt::zero(), |acc, (j, rj)| {
            acc.add(&rj.scale(rec_f(1u64 << j)))
        });
    let tbl_ex = eq_eval_gadget(b, &rx, &r_gkr[..vk.log_rows]);
    let tbl_ey = eq_eval_gadget(b, &ry, &r_gkr[..vk.var_bits]);

    let one_m_b0 = one.sub(b0);
    let one_m_b1 = one.sub(b1);
    let w0 = one_m_b0.mul(b, &one_m_b1);
    let w1 = b0.mul(b, &one_m_b1);
    let w2 = one_m_b0.mul(b, b1);
    let w3 = b0.mul(b, b1);

    let t1_p = w1.mul(b, &h_gkr[5]);
    let t2_p = w2.mul(b, &delta);
    let w3_d = w3.mul(b, &delta);
    let t3_p = w3_d.mul(b, &h_gkr[6]);
    let p_exp = w0.sub(&t1_p).add(&t2_p).sub(&t3_p);
    p_claim.equal(b, &p_exp);

    let d0 = gamma_x.sub(&h_gkr[0]).sub(&alpha_mem.mul(b, &ex_gkr));
    let d1 = gamma_x.sub(&id_eval).sub(&alpha_mem.mul(b, &tbl_ex));
    let d2 = gamma_y.sub(&h_gkr[1]).sub(&alpha_mem.mul(b, &ey_gkr));
    let d3 = gamma_y.sub(&id_eval).sub(&alpha_mem.mul(b, &tbl_ey));
    let q_exp = w0
        .mul(b, &d0)
        .add(&w1.mul(b, &d1))
        .add(&w2.mul(b, &d2))
        .add(&w3.mul(b, &d3));
    q_claim.equal(b, &q_exp);

    // 3. Correlated 3-oracle WHIR opening of `(Z_pad, H_super, E_super)`.
    let sel_mat: [RecExt<B::W>; 3] = core::array::from_fn(|_| tr.ext(b, 230));
    let sel_gkr: [RecExt<B::W>; 3] = core::array::from_fn(|_| tr.ext(b, 231));

    let zero_ext = RecExt::<B::W>::zero();
    let mut p_z = ry;
    p_z.resize(vk.pack_vars(), zero_ext.clone());
    let mut p_mat = r_mat;
    p_mat.extend_from_slice(&sel_mat);
    let mut p_gkr = r_gkr.to_vec();
    p_gkr.extend_from_slice(&sel_gkr);

    let h_mat8: [RecExt<B::W>; 8] = core::array::from_fn(|i| {
        if i < 7 {
            h_mat[i].clone()
        } else {
            zero_ext.clone()
        }
    });
    let h_gkr8: [RecExt<B::W>; 8] = core::array::from_fn(|i| {
        if i < 7 {
            h_gkr[i].clone()
        } else {
            zero_ext.clone()
        }
    });
    let claim_h_mat = super8_claim_gadget(b, &h_mat8, &sel_mat);
    let claim_h_gkr = super8_claim_gadget(b, &h_gkr8, &sel_gkr);
    let claim_e_mat = super8_claim_gadget(b, &e_limbs_mat, &sel_mat);
    let claim_e_gkr = super8_claim_gadget(b, &e_limbs_gkr, &sel_gkr);

    let expected_claims = [
        [Some(eval_z), None, None],
        [None, Some(claim_h_mat), Some(claim_h_gkr)],
        [None, Some(claim_e_mat), Some(claim_e_gkr)],
    ];
    DeferredPcsClaim {
        regime: vk.regime,
        num_vars: vk.pack_vars(),
        transcript: tr.state,
        roots: [comm_z, rec_root, comm_e],
        points: [p_z, p_mat, p_gkr],
        claims: expected_claims,
    }
}

/// Native verification of a [`RecursivePublicHemProof`].
pub fn verify_public_for_recursion(
    vk: &ShapeVerifierKey,
    public: &[F],
    statement_tag: [u8; 32],
    proof: &RecursivePublicHemProof,
) -> bool {
    if !vk.regime.uses_poseidon2_canopy()
        || public.len() != vk.num_public
        || !proof.well_formed(vk)
        || proof.q_root.is_zero()
    {
        return false;
    }
    let mut b = RecNative::default();
    verify_public_gadget(&mut b, vk, statement_tag, public, proof);
    !b.failed
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

    /// Releasing the Reed-Solomon caches (the large-relation path) changes no proof byte.
    #[test]
    fn hologram_proof_is_identical_without_round0_caches() {
        for regime in [
            WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128,
            WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
        ] {
            let mut cs = ConstraintSystem::new_hologram_aligned();
            let claim = cs.public_input(f(0));
            let mut st: [Lc; 12] = core::array::from_fn(|i| cs.alloc(f(3 + i as u64)).into());
            for _ in 0..9 {
                super::super::relation::poseidon2_perm(&mut cs, &mut st);
            }
            let prod = cs.mul(&st[0], &st[5]);
            cs.enforce_equal(&prod.into(), &Lc::constant(cs.eval(&prod.into())));
            cs.enforce_equal(&claim.into(), &Lc::zero());
            let (shape, z) = cs.finish();
            let cached = ShapeHologram::compile_native(&shape, regime).unwrap();
            assert!(!cached.h_state.codewords_0.is_empty());
            let lean = cached.clone().without_round0_cache();
            let with_cache =
                prove_public_hologram(&shape, &cached, z.clone(), b"cache", &[5; 32]).unwrap();
            let without =
                prove_public_hologram(&shape, &lean, z.clone(), b"cache", &[5; 32]).unwrap();
            assert_eq!(with_cache.to_bytes(), without.to_bytes());
            assert!(verify_public_hologram(
                lean.verifier_key(),
                &z[1..=shape.num_public],
                b"cache",
                &without
            ));
            // A clone keeps the choice its source made.
            assert!(lean.clone().h_state.codewords_0.is_empty());
        }
    }

    /// Verifier key with the geometry of a relation that was never compiled: enough for a
    /// row census of [`verify_public_gadget`] on a placeholder proof.
    fn census_vk(
        regime: WhirSecurityRegime,
        log_rows: usize,
        var_bits: usize,
        ell_nz: usize,
    ) -> ShapeVerifierKey {
        let stage = regime.schedule(ell_nz + 2).stages[0];
        let vk = ShapeVerifierKey {
            shape_digest: [0; 32],
            log_rows,
            num_sbox: 1 << (log_rows - 1),
            num_vars: 1 << var_bits,
            num_public: 14,
            var_bits,
            ell_nz,
            hologram_meta: HologramMeta {
                poseidon2_perms: 1 << (log_rows - 8),
                pub_var_blocks: 1,
            },
            regime,
            hologram_comm: CanopyCommitment {
                root: [0; 32],
                log_leaves: (ell_nz + 2 + stage.blowup.trailing_zeros() as usize - stage.step_vars)
                    as u8,
            },
            rec_hologram_root: Some([F::ZERO; 4]),
        };
        assert!(vk.is_well_formed());
        vk
    }

    /// Rows one in-circuit child verifier costs its parent, by child geometry.
    #[test]
    #[ignore = "measurement: prints the in-circuit verifier row census"]
    fn recursive_verifier_row_census() {
        use super::super::recursive_whir::Counter;
        for regime in [
            WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
            WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
        ] {
            for (log_rows, var_bits, ell_nz) in [(21, 21, 22), (21, 21, 23), (23, 23, 24)] {
                let vk = census_vk(regime, log_rows, var_bits, ell_nz);
                let proof = RecursivePublicHemProof::placeholder(&vk).unwrap();
                let mut whole = Counter::default();
                let public = [F::ZERO; 14];
                verify_public_gadget(&mut whole, &vk, [0; 32], &public, &proof);
                let params = FixedPathWhirParams::new(regime, vk.pack_vars()).unwrap();
                let mut opening = Counter::default();
                let mut tr = RecTranscript::new();
                let zero = RecExt::<F>::zero();
                let point = vec![zero.clone(); vk.pack_vars()];
                verify_correlated3_gadget(
                    &mut opening,
                    &params,
                    &mut tr,
                    &[[F::ZERO; 4]; 3],
                    &[point.clone(), point.clone(), point],
                    &[[None, None, None], [None, None, None], [None, None, None]],
                    &proof.opening,
                );
                std::println!("VERIFIER_SECTIONS {:?}", whole.sections);
                std::println!(
                    "VERIFIER_CENSUS regime={} log_rows={log_rows} var_bits={var_bits} ell_nz={ell_nz} pack_vars={} total_rows={} perms={} mul_rows={} vars={} | opening: rows={} perms={} mul_rows={} | schedule={:?}",
                    regime as u8,
                    vk.pack_vars(),
                    whole.total_rows(),
                    whole.perms,
                    whole.rows,
                    whole.vars,
                    opening.total_rows(),
                    opening.perms,
                    opening.rows,
                    params
                        .schedule
                        .stages
                        .iter()
                        .map(|s| (s.blowup, s.step_vars, s.num_queries))
                        .collect::<Vec<_>>(),
                );
            }
        }
    }

    #[test]
    fn shape_hologram_poseidon2_factorization_and_tamper_rejection() {
        // Build an aligned relation with multiple Poseidon2 permutations, public inputs, and muls.
        let build = |secret_val: u64, pub_claim: Option<F>| {
            let mut cs = ConstraintSystem::new_hologram_aligned();
            let pub_x = cs.alloc(f(secret_val));
            let mut st: [Lc; 12] = core::array::from_fn(|i| {
                if i == 0 {
                    pub_x.into()
                } else {
                    Lc::constant(f(10 + i as u64))
                }
            });
            for _ in 0..5 {
                super::super::relation::poseidon2_perm(&mut cs, &mut st);
            }
            let prod = cs.mul(&st[0], &st[1]);
            let want = pub_claim.unwrap_or_else(|| cs.eval(&prod.into()));
            // Rebuild with `want` as public input 1 so public_input comes first!
            let mut cs2 = ConstraintSystem::new_hologram_aligned();
            let p_in = cs2.public_input(want);
            let w_x = cs2.alloc(f(secret_val));
            let mut st2: [Lc; 12] = core::array::from_fn(|i| {
                if i == 0 {
                    w_x.into()
                } else {
                    Lc::constant(f(10 + i as u64))
                }
            });
            for _ in 0..5 {
                super::super::relation::poseidon2_perm(&mut cs2, &mut st2);
            }
            let prod2 = cs2.mul(&st2[0], &st2[1]);
            cs2.enforce_equal(&p_in.into(), &prod2.into());
            (cs2.finish(), want)
        };
        let ((shape, z), pub_val) = build(42, None);
        assert!(shape.is_satisfied(&z));
        assert_eq!(shape.hologram_meta().poseidon2_perms, 5);

        let regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let holo = ShapeHologram::compile(&shape, regime).unwrap();
        let vk = holo.verifier_key();
        let vk_bytes = vk.to_bytes();
        assert!(vk_bytes.len() < 256, "vk_bytes={}", vk_bytes.len());
        assert_eq!(ShapeVerifierKey::from_bytes(&vk_bytes).as_ref(), Some(vk));
        for mutation in 0..5 {
            let mut bad = vk.clone();
            match mutation {
                0 => bad.hologram_meta.poseidon2_perms = usize::MAX,
                1 => bad.hologram_meta.pub_var_blocks = usize::MAX,
                2 => bad.num_public = bad.num_vars,
                3 => bad.num_sbox = usize::MAX,
                _ => bad.var_bits = usize::MAX,
            }
            assert!(ShapeVerifierKey::from_bytes(&bad.to_bytes()).is_none());
        }

        // 1. Check exact identity: closed-form Poseidon2 interior + residual sparse sum == `matrix_at`.
        let mut stream = SeedStream::new(b"QSAG.TEST.HOLO", &[77; 32]);
        let rx: Vec<E> = (0..shape.log_rows).map(|_| stream.next_ext4()).collect();
        let ry: Vec<E> = (0..vk.var_bits).map(|_| stream.next_ext4()).collect();
        let combine: [E; 3] = core::array::from_fn(|_| stream.next_ext4());
        let expected_m = matrix_at(&shape, &rx, &ry, &combine);
        let p2_m = eval_poseidon2_interior_native(vk.hologram_meta, &rx, &ry, &combine);
        let eq_rx = eq_table(&rx);
        let eq_ry = eq_table(&ry);
        let sparse_m = (0..1usize << vk.ell_nz).fold(E::ZERO, |acc, k| {
            let v = combine[0].mul_base(holo.val_a[k])
                + combine[1].mul_base(holo.val_b[k])
                + combine[2].mul_base(holo.val_c[k]);
            acc + eq_rx[holo.row_idx[k] as usize] * eq_ry[holo.col_idx[k] as usize] * v
        });
        assert_eq!(p2_m + sparse_m, expected_m);

        // 2. Native `HologramPublicProof` round-trip + tamper tests across multiple regimes.
        for reg in [
            WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
            WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128,
        ] {
            let h = ShapeHologram::compile(&shape, reg).unwrap();
            let proof =
                prove_public_hologram(&shape, &h, z.clone(), b"HOLO_STMT", &[9; 32]).unwrap();
            let start = std::time::Instant::now();
            assert!(verify_public_hologram(
                h.verifier_key(),
                &[pub_val],
                b"HOLO_STMT",
                &proof
            ));
            std::println!(
                "HOLOGRAM regime={reg:?} rows={} verify_ms={:.3}",
                shape.num_rows(),
                start.elapsed().as_secs_f64() * 1000.0
            );

            let wire = proof.to_bytes();
            let decoded = HologramPublicProof::from_bytes(&wire, h.verifier_key()).unwrap();
            assert_eq!(decoded, proof);
            assert!(!verify_public_hologram(
                h.verifier_key(),
                &[pub_val + F::ONE],
                b"HOLO_STMT",
                &proof
            ));
            assert!(!verify_public_hologram(
                h.verifier_key(),
                &[pub_val],
                b"WRONG_STMT",
                &proof
            ));
            let mut bad = proof.clone();
            bad.m_sparse_claim += E::ONE;
            assert!(!verify_public_hologram(
                h.verifier_key(),
                &[pub_val],
                b"HOLO_STMT",
                &bad
            ));
            let mut bad = proof.clone();
            bad.e_limbs_at_mat[0] += E::ONE;
            assert!(!verify_public_hologram(
                h.verifier_key(),
                &[pub_val],
                b"HOLO_STMT",
                &bad
            ));
            let mut bad = proof.clone();
            bad.gkr_layers[2].split[0] += E::ONE;
            assert!(!verify_public_hologram(
                h.verifier_key(),
                &[pub_val],
                b"HOLO_STMT",
                &bad
            ));
        }

        // 3. In-circuit `RecursivePublicHemProof` + `verify_public_gadget` satisfaction & tamper!
        let tag = [0xAB; 32];
        let rec_proof = prove_public_for_recursion(&shape, &holo, z, tag).unwrap();
        assert!(verify_public_for_recursion(vk, &[pub_val], tag, &rec_proof));

        let mut parent_cs = ConstraintSystem::new_hologram_aligned();
        let pub_w: Lc = parent_cs.public_input(pub_val).into();
        verify_public_gadget(&mut parent_cs, vk, tag, &[pub_w], &rec_proof);
        let (parent_shape, parent_z) = parent_cs.finish();
        assert!(parent_shape.is_satisfied(&parent_z));

        let mut bad_rec = rec_proof.clone();
        bad_rec.h_at_gkr[0] += E::ONE;
        assert!(!verify_public_for_recursion(vk, &[pub_val], tag, &bad_rec));
        let mut bad_cs = ConstraintSystem::new_hologram_aligned();
        let pub_w2: Lc = bad_cs.public_input(pub_val).into();
        verify_public_gadget(&mut bad_cs, vk, tag, &[pub_w2], &bad_rec);
        let (other_shape, bad_z) = bad_cs.finish();
        assert_eq!(parent_shape, other_shape);
        assert!(!other_shape.is_satisfied(&bad_z));
    }
}
