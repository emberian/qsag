//! Committed zk-Hem: a zero-knowledge argument for a [`Shape`] over the Hem WHIR commitment.
//!
//! One batch commitment holds five base-field tables of `2^l` cells: the masked assignment
//! table `Z` and four uniform companion tables `C_0..C_3`. `Z` is laid out as
//!
//! ```text
//! [ sumcheck masks | 1, variables, masking variables | zeros | opening blinders ]
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
    whir_commit_batch_owned_with_schedule, whir_open_blend, whir_verify_blend,
};
use crate::sponge::{FiatShamirTranscript, InstanceBound};

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
    /// Cells reserved for the two sumcheck masks; variable `v` lives in cell `mask_cells + v`.
    pub mask_cells: usize,
    /// Uniform cells at the top of the table, one per opened Stage-0 symbol.
    pub blind_cells: usize,
    pub schedule: WhirSchedule,
}

impl Layout {
    /// Smallest table that holds the masks, the variables and the opening blinders.
    pub fn new(shape: &Shape, regime: WhirSecurityRegime) -> Option<Self> {
        (4..=MAX_PCS_NUM_VARS).find_map(|log_cells| {
            let cells = 1usize << log_cells;
            let masks = (shape.log_rows * 4 << ROW_MASK_BITS) + (log_cells * 4 << COL_MASK_BITS);
            let mask_cells = masks.next_power_of_two();
            let schedule = regime.schedule(log_cells);
            let st0 = schedule.stages[0];
            let arity = 1usize << st0.step_vars;
            let fibers = cells * st0.blowup / arity;
            let blind_cells = st0.num_queries.min(fibers) * arity;
            (mask_cells + shape.num_vars + blind_cells <= cells).then_some(Self {
                log_cells,
                mask_cells,
                blind_cells,
                schedule,
            })
        })
    }

    #[inline]
    fn row_mask_block(&self, round: usize, limb: usize) -> usize {
        (round * 4 + limb) << ROW_MASK_BITS
    }

    #[inline]
    fn col_mask_block(&self, log_rows: usize, round: usize, limb: usize) -> usize {
        (log_rows * 4 << ROW_MASK_BITS) + ((round * 4 + limb) << COL_MASK_BITS)
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
        self.row_rounds.iter().flatten().for_each(|v| push(&mut out, v));
        self.row_values.iter().for_each(|v| push(&mut out, v));
        push(&mut out, &self.col_mask_sum);
        self.col_rounds.iter().flatten().for_each(|v| push(&mut out, v));
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
        let col_rounds = rounds(&mut pos, layout.log_cells, COL_DEGREE)?;
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
    let col_half = pow2(l - 1);
    for (j, &limb) in basis.iter().enumerate() {
        for i in 0..inp.log_rows {
            let block = inp.layout.row_mask_block(i, j);
            // sum g1 = 2^(n-1) sum_i (g1_i(0) + g1_i(1)).
            push(lam[0] * row_half * limb, block_point(l, block, &zeros(ROW_MASK_BITS)));
            push(lam[0] * row_half * limb, block_point(l, block, &ones(ROW_MASK_BITS)));
            // g1(rx) = sum_i g1_i(rx_i).
            push(
                lam[2] * limb,
                block_point(l, block, &pow2_coords(inp.rx[i], ROW_MASK_BITS)),
            );
        }
        for i in 0..l {
            let block = inp.layout.col_mask_block(inp.log_rows, i, j);
            push(lam[1] * col_half * limb, block_point(l, block, &zeros(COL_MASK_BITS)));
            push(lam[1] * col_half * limb, block_point(l, block, &ones(COL_MASK_BITS)));
            push(
                lam[3] * inp.rho2 * limb,
                block_point(l, block, &pow2_coords(inp.ry[i], COL_MASK_BITS)),
            );
        }
    }
    push(lam[3] * inp.matrix_at_point, inp.ry.to_vec());
    // Variable 0 holds the constant 1; variables 1..=num_public hold the public inputs.
    for i in 0..=inp.num_public {
        push(lam[4 + i], block_point(l, inp.layout.mask_cells + i, &[]));
    }
    terms
}

fn batched_value(lambda: E, values: &[E]) -> E {
    values.iter().rev().fold(E::ZERO, |acc, &v| acc * lambda + v)
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
    for n in [layout.log_cells, layout.mask_cells, layout.blind_cells] {
        params.extend_from_slice(&(n as u64).to_le_bytes());
    }
    FiatShamirTranscript::new()
        .bind_relation(b"QSAG.ZKHEM.COMMITTED/v1", &params, &layout.schedule)
        .bind_instance(&[statement, &public_bytes, &commitment.to_bytes()])
}

fn squeeze_point(
    tr: &mut FiatShamirTranscript<InstanceBound>,
    label: &[u8],
    n: usize,
) -> Vec<E> {
    (0..n).map(|_| tr.squeeze_ext4(label)).collect()
}

// ============================================================================
// Prover
// ============================================================================

fn fold_in_place(table: &mut Vec<E>, r: E) {
    let half = table.len() / 2;
    for i in 0..half {
        let lo = table[2 * i];
        table[i] = lo + r * (table[2 * i + 1] - lo);
    }
    table.truncate(half);
}

/// Sum over the remaining hypercube of `per_pair`, which returns the contributions of one
/// pair of rows to the round polynomial at `0, 1, .., N - 1`.
fn round_evals<const N: usize>(pairs: usize, per_pair: impl Fn(usize) -> [E; N] + Sync) -> [E; N] {
    let add = |mut acc: [E; N], part: [E; N]| {
        for (a, p) in acc.iter_mut().zip(part) {
            *a += p;
        }
        acc
    };
    #[cfg(feature = "std")]
    if pairs >= 1 << 12 && crate::parallel_workers() > 1 {
        let idx: Vec<usize> = (0..pairs).collect();
        return crate::map_chunks_bounded_with_limit(&idx, crate::parallel_workers(), |chunk| {
            chunk.iter().fold([E::ZERO; N], |acc, &i| add(acc, per_pair(i)))
        })
        .into_iter()
        .fold([E::ZERO; N], add);
    }
    (0..pairs).fold([E::ZERO; N], |acc, i| add(acc, per_pair(i)))
}

fn evals_to_coeffs(evals: &[E]) -> Vec<E> {
    let xs: Vec<E> = (0..evals.len() as u64).map(E::from_u64).collect();
    match interp(&xs, evals) {
        Some(coeffs) => coeffs,
        None => unreachable!("the points 0..=d are distinct"),
    }
}

/// Runs one masked sumcheck; returns the round coefficient lists and the challenge point.
fn masked_sumcheck(
    tr: &mut FiatShamirTranscript<InstanceBound>,
    label: &[u8],
    mask: &LibraMask,
    rho: E,
    mut witness_round: impl FnMut(Option<E>) -> Vec<E>,
) -> (Vec<Vec<E>>, Vec<E>) {
    let n = mask.num_rounds();
    let mut rounds = Vec::with_capacity(n);
    let mut point = Vec::with_capacity(n);
    let mut last = None;
    for _ in 0..n {
        let f = witness_round(last);
        let g = mask.round_poly(&point);
        let masked: Vec<E> = f.iter().zip(&g).map(|(&f, &g)| f + rho * g).collect();
        tr.absorb_ext4_slice(label, &masked);
        let c = tr.squeeze_ext4(label);
        rounds.push(masked);
        point.push(c);
        last = Some(c);
    }
    (rounds, point)
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
///   composition over the cell layout, the masking-row determinant and the triangular
///   independence of blinders, masking variables and masks is argued in comments only;
/// * hiding of unopened Stage-0 leaves beyond the salted-leaf coupling of that file (no
///   bound on the bad event is mechanized there);
/// * the batching step uses scalar weights `beta^j`. Its proximity loss is the standard one
///   for random linear combinations and is not re-derived for the regime's query schedule,
///   which was accounted for the affine cascade of the non-hiding opening;
/// * knowledge soundness of the composition (masked sumchecks, linear batching, companion
///   challenge, WHIR) has no concrete bound stated or proved here.
