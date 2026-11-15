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
    mut assignment: Vec<F>,
    statement: &[u8],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
    check: bool,
) -> Result<ZkHemProof, ZkHemError> {
    let layout = Layout::new(shape, regime).ok_or(ZkHemError::RelationTooLarge)?;
    if assignment.len() != shape.num_vars {
        return Err(ZkHemError::Unsatisfied);
    }
    let mut stream = SeedStream::new(b"QSAG.ZKHEM.COINS/v1", seed);
    for slot in &mut assignment[shape.mask_var_base..] {
        *slot = stream.next_base();
    }
    if check && !shape.is_satisfied(&assignment) {
        qsag_asm::volatile_fill(&mut assignment, F::ZERO);
        return Err(ZkHemError::Unsatisfied);
    }

    let cells = 1usize << layout.log_cells;
    let rows = shape.num_rows();
    let row_mask = Mask::sample(&mut stream, shape.log_rows, ROW_DEGREE);
    let col_mask = Mask::sample(&mut stream, layout.log_cells, COL_DEGREE);
    let mut table = vec![F::ZERO; cells];
    row_mask.write(&mut table, ROW_MASK_BITS, |i, j| layout.row_mask_block(i, j));
    col_mask.write(&mut table, COL_MASK_BITS, |i, j| {
        layout.col_mask_block(shape.log_rows, i, j)
    });
    table[layout.mask_cells..layout.mask_cells + shape.num_vars].copy_from_slice(&assignment);
    let public_inputs = assignment[1..=shape.num_public].to_vec();
    for slot in &mut table[cells - layout.blind_cells..] {
        *slot = stream.next_base();
    }

    // Row values before the table moves into the commitment.
    let lift = |m: &super::relation::Csr| -> Vec<E> {
        (0..rows)
            .map(|i| E::from_base(m.row_dot(i, &assignment)))
            .collect()
    };
    let (mut ta, mut tb, mut tc) = (lift(&shape.a), lift(&shape.b), lift(&shape.c));
    qsag_asm::volatile_fill(&mut assignment, F::ZERO);
    let mut tz: Vec<E> = table.iter().map(|&v| E::from_base(v)).collect();

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
        whir_commit_batch_owned_with_schedule(polys, &salt_seed, &layout.schedule);
    qsag_asm::volatile_fill(&mut salt_seed, 0u8);

    let mut tr = start_transcript(shape, &layout, statement, &public_inputs, &commitment);

    // 1. Masked row sumcheck.
    let tau = squeeze_point(&mut tr, b"ZKHEM_TAU", shape.log_rows);
    let row_libra = row_mask.libra();
    let row_mask_sum = row_libra.sum();
    tr.absorb_ext4(b"ZKHEM_ROW_MASK_SUM", row_mask_sum);
    let rho1 = NonzeroChallenge::squeeze(&mut tr, b"ZKHEM_RHO1").get();
    let mut teq = build_eq_table_ext4(&tau);
    let mut ts: Vec<E> = (0..rows)
        .map(|i| if i < shape.num_sbox { E::ONE } else { E::ZERO })
        .collect();
    let (row_rounds, rx) = masked_sumcheck(&mut tr, b"ZKHEM_ROW_ROUND", &row_libra, rho1, |c| {
        if let Some(c) = c {
            for t in [&mut teq, &mut ts, &mut ta, &mut tb, &mut tc] {
                fold_in_place(t, c);
            }
        }
        let (teq, ts, ta, tb, tc) = (&teq, &ts, &ta, &tb, &tc);
        let evals = round_evals::<{ ROW_DEGREE + 1 }>(teq.len() / 2, |i| {
            let step = |t: &Vec<E>| (t[2 * i], t[2 * i + 1] - t[2 * i]);
            let (mut e, de) = step(teq);
            let (mut s, ds) = step(ts);
            let (mut a, da) = step(ta);
            let (mut b, db) = step(tb);
            let (mut c, dc) = step(tc);
            core::array::from_fn(|_| {
                let v = e * row_gate(s, a, b, c);
                e += de;
                s += ds;
                a += da;
                b += db;
                c += dc;
                v
            })
        });
        evals_to_coeffs(&evals)
    });
    for t in [&mut teq, &mut ts, &mut ta, &mut tb, &mut tc] {
        fold_in_place(t, rx[shape.log_rows - 1]);
    }
    if !mask_rows_full_rank(shape, &rx) {
        return Err(ZkHemError::MaskRankDeficient);
    }

    // 2. Row values.
    let row_values = [ta[0], tb[0], tc[0]];
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &row_values);

    // 3. Masked column sumcheck of `M(rx, y) Z(y)`.
    let combine = squeeze_point(&mut tr, b"ZKHEM_COMBINE", 3);
    let col_libra = col_mask.libra();
    let col_mask_sum = col_libra.sum();
    tr.absorb_ext4(b"ZKHEM_COL_MASK_SUM", col_mask_sum);
    let rho2 = NonzeroChallenge::squeeze(&mut tr, b"ZKHEM_RHO2").get();
    let eq_rx = build_eq_table_ext4(&rx);
    let mut tm = vec![E::ZERO; cells];
    for (i, &e) in eq_rx.iter().enumerate() {
        for (m, &r) in [&shape.a, &shape.b, &shape.c].into_iter().zip(&combine) {
            let w = r * e;
            for (col, val) in m.row(i) {
                tm[layout.mask_cells + col] += w.mul_base(val);
            }
        }
    }
    drop(eq_rx);
    let (col_rounds, ry) = masked_sumcheck(&mut tr, b"ZKHEM_COL_ROUND", &col_libra, rho2, |c| {
        if let Some(c) = c {
            fold_in_place(&mut tm, c);
            fold_in_place(&mut tz, c);
        }
        let (tm, tz) = (&tm, &tz);
        let evals = round_evals::<{ COL_DEGREE + 1 }>(tm.len() / 2, |i| {
            let (m0, m1) = (tm[2 * i], tm[2 * i + 1]);
            let (z0, z1) = (tz[2 * i], tz[2 * i + 1]);
            [m0 * z0, m1 * z1, (m1 + m1 - m0) * (z1 + z1 - z0)]
        });
        evals_to_coeffs(&evals)
    });
    fold_in_place(&mut tm, ry[layout.log_cells - 1]);
    let matrix_at_point = tm[0];
    drop(tm);
    qsag_asm::volatile_fill(&mut tz, E::ZERO);
    drop(tz);

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
        let live = term
            .point
            .iter()
            .rposition(|c| !c.is_zero())
            .map_or(0, |p| p + 1);
        add_point_kernel(&mut kernel, term.weight, &term.point[..live]);
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
fn matrix_at(shape: &Shape, layout: &Layout, rx: &[E], ry: &[E], combine: &[E]) -> E {
    let eq_rx = build_eq_table_ext4(rx);
    let eq_ry = build_eq_table_ext4(ry);
    let cols = &eq_ry[layout.mask_cells..layout.mask_cells + shape.num_vars];
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
        || proof.col_rounds.len() != layout.log_cells
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
        matrix_at_point: matrix_at(shape, &layout, &rx, &ry, &combine),
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
        let bump = |x: &mut E| *x += E::ONE;
        let mutations: Vec<fn(&mut ZkHemProof, &dyn Fn(&mut E))> = vec![
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
            assert!(!verify(&shape, &[], b"s", regime, &bad), "mutation {k} accepted");
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
    }

    #[test]
    fn layout_reserves_a_blinder_for_every_opened_stage0_symbol() {
        let (shape, _) = preimage_relation([1, 77]);
        for regime in REGIMES {
            let layout = Layout::new(&shape, regime).unwrap();
            let st0 = layout.schedule.stages[0];
            let proof = prove(&shape, preimage_relation([1, 77]).1, b"s", regime, &[5; 32]).unwrap();
            let opened_per_table = proof.opening.round0_vals.len() / (1 + COMPANIONS);
            assert!(opened_per_table <= layout.blind_cells);
            assert_eq!(layout.blind_cells, st0.num_queries << st0.step_vars);
            assert!(layout.mask_cells.is_power_of_two());
            assert!(
                layout.mask_cells + shape.num_vars + layout.blind_cells <= 1 << layout.log_cells
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
                (0..shape.num_rows())
                    .fold(E::ZERO, |acc, i| acc + eq[i].mul_base(m.row_dot(i, z)))
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
            assert_eq!(E::from_base(z) + beta.get() * pad_map(beta.get(), &pad), target);
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
