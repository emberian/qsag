//! zk-Hem masking layer over `GoldilocksExt4`.
//!
//! Each item here is the executable counterpart of a definition in
//! `lean/Qsag/ZkHemSoundnessAndPrivacy.lean`; the Lean name is given on the item.
//!
//! * [`PrimitiveChallenge`]: challenges rejection-sampled from $\mathbb{F}_{p^4} \setminus
//!   \mathbb{F}_{p^2}$ (tower coordinate `c1 != 0`, i.e. $(c_1, c_3) \ne (0, 0)$ in the
//!   polynomial basis).
//! * [`Pad`], [`pad_map`], [`pad_inv`]: four base-field pad cells against one `Ext4`
//!   evaluation (`padMap`, `padInv`, `quartic_primitive_pad_bijection`).
//! * [`CornerPadBasis`]: a separately checked full-rank basis for four multilinear
//!   corners. Primitivity of either coordinate alone does not certify this basis.
//! * [`LibraMask`], [`libra_prove`], [`libra_verify`], [`libra_sim`]: separable sumcheck
//!   mask (`libraReal`, `libraSim`, `libra_real_eq_sim`).
//! * [`blend`], [`unblend`], [`companion_check`], [`libra_check`]: companion word and the
//!   two batched claims (`blend`, `companionCheck`, `libraCheck`).
//! * [`eval_all`], [`interp`]: `q` blinding coefficients against `q` opened points
//!   (`evalAll`, `interp`, `blindingEvalBij`).
//!
//! This module is the algebra of the masks and their verifier checks; a caller that sends
//! `g_sum` or `sigma` without first committing `g` and `C` gets no soundness (see the
//! `uncommitted_*` tests). [`protocol`] is the committed protocol built from it: masks and
//! companions are committed with the witness and WHIR runs on the blended word only.
//! [`relation`] is the constraint system it proves.

use alloc::vec;
use alloc::vec::Vec;

pub mod blind_vc;
#[cfg(feature = "std")]
pub mod full_shard;
pub mod multisig;
pub mod protocol;
pub mod recursive_whir;
pub mod relation;

use crate::field::{
    Goldilocks, GoldilocksExt2, GoldilocksExt2Ops as _, GoldilocksExt4, GoldilocksOps as _,
};
use crate::sponge::{FiatShamirTranscript, InstanceBound, cshake256_32};

type E = GoldilocksExt4;

// ============================================================================
// 1. Challenges
// ============================================================================

/// A challenge outside the quadratic subfield $\mathbb{F}_{p^2} = \{c_1 = c_3 = 0\}$.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrimitiveChallenge(E);

impl PrimitiveChallenge {
    /// `None` for elements of $\mathbb{F}_{p^2}$.
    #[inline]
    pub fn new(z: E) -> Option<Self> {
        if z.c1.is_zero() { None } else { Some(Self(z)) }
    }

    /// Squeeze `Ext4` challenges under `label` until one lies outside $\mathbb{F}_{p^2}$.
    /// Prover and verifier run the same loop on the same transcript state.
    pub fn squeeze(transcript: &mut FiatShamirTranscript<InstanceBound>, label: &[u8]) -> Self {
        loop {
            if let Some(c) = Self::new(transcript.squeeze_ext4(label)) {
                return c;
            }
        }
    }

    #[inline]
    pub fn get(self) -> E {
        self.0
    }
}

/// A nonzero challenge (the Libra batching challenge `rho` and the blend challenge `gamma`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NonzeroChallenge(E);

impl NonzeroChallenge {
    #[inline]
    pub fn new(x: E) -> Option<Self> {
        if x.is_zero() { None } else { Some(Self(x)) }
    }

    /// Squeeze `Ext4` challenges under `label` until one is nonzero.
    pub fn squeeze(transcript: &mut FiatShamirTranscript<InstanceBound>, label: &[u8]) -> Self {
        loop {
            if let Some(c) = Self::new(transcript.squeeze_ext4(label)) {
                return c;
            }
        }
    }

    #[inline]
    pub fn get(self) -> E {
        self.0
    }
}

// ============================================================================
// 2. Uniform field elements from a seed
// ============================================================================

/// Expands a 32-byte seed into uniform canonical `Goldilocks` elements: 8-byte candidates
/// from `cSHAKE256(domain, seed || counter)` blocks, rejecting candidates `>= p`.
pub struct SeedStream {
    domain: &'static [u8],
    input: [u8; 40],
    block: [u8; 32],
    pos: usize,
    counter: u64,
}

impl SeedStream {
    pub fn new(domain: &'static [u8], seed: &[u8; 32]) -> Self {
        let mut input = [0u8; 40];
        input[..32].copy_from_slice(seed);
        Self {
            domain,
            input,
            block: [0u8; 32],
            pos: 32,
            counter: 0,
        }
    }

    pub fn next_base(&mut self) -> Goldilocks {
        loop {
            if self.pos == 32 {
                self.input[32..].copy_from_slice(&self.counter.to_le_bytes());
                self.block = cshake256_32(self.domain, &self.input);
                self.counter += 1;
                self.pos = 0;
            }
            let mut word = [0u8; 8];
            word.copy_from_slice(&self.block[self.pos..self.pos + 8]);
            self.pos += 8;
            if let Some(x) = Goldilocks::from_canonical_u64(u64::from_le_bytes(word)) {
                return x;
            }
        }
    }

    pub fn next_ext4(&mut self) -> E {
        let l0 = self.next_base();
        let l1 = self.next_base();
        let l2 = self.next_base();
        let l3 = self.next_base();
        E::from_limbs([l0, l1, l2, l3])
    }
}

impl Drop for SeedStream {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.input, 0u8);
        qsag_asm::volatile_fill(&mut self.block, 0u8);
    }
}

// ============================================================================
// 3. Terminal operand pads
// ============================================================================

/// Four base-field pad cells `[r0, r1, r2, r3]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pad(pub [Goldilocks; 4]);

impl Pad {
    pub fn from_stream(stream: &mut SeedStream) -> Self {
        Self([
            stream.next_base(),
            stream.next_base(),
            stream.next_base(),
            stream.next_base(),
        ])
    }
}

/// `r0 + r1 z + r2 z^2 + r3 z^3` (`padMap`).
#[inline]
pub fn pad_map(z: E, pad: &Pad) -> E {
    let [r0, r1, r2, r3] = pad.0;
    let mut acc = E::from_base(r3);
    acc = acc * z + E::from_base(r2);
    acc = acc * z + E::from_base(r1);
    acc * z + E::from_base(r0)
}

/// The pad `r` with `pad_map(z, r) == v` (`padInv`). It exists and is unique because
/// `z` lies outside $\mathbb{F}_{p^2}$.
///
/// With `z = A + B v`, `T = 2A`, `N = A^2 - u B^2`: `z^2 = T z - N` and
/// `z^3 = S z - W` for `S = T^2 - N`, `W = T N`. Writing `v = alpha + beta z` over
/// $\mathbb{F}_{p^2}$, the `u`-coordinates of `alpha, beta` determine `(r2, r3)` through a
/// two-by-two system whose determinant is nonzero (`padDet_ne_zero`), and the
/// `1`-coordinates then give `(r0, r1)`.
pub fn pad_inv(z: PrimitiveChallenge, v: E) -> Pad {
    let a = z.0.c0;
    let b = z.0.c1;
    let t = a + a;
    let n = a * a - (b * b).mul_by_u();
    let s = t * t - n;
    let w = t * n;

    let beta = v.c1 * b.inv_or_zero();
    let alpha = v.c0 - beta * a;

    let m00 = -n.c1;
    let m01 = -w.c1;
    let m10 = t.c1;
    let m11 = s.c1;
    let det_inv = (m00 * m11 - m01 * m10).inv();
    let r2 = (alpha.c1 * m11 - m01 * beta.c1) * det_inv;
    let r3 = (m00 * beta.c1 - alpha.c1 * m10) * det_inv;
    let r0 = alpha.c0 + r2 * n.c0 + r3 * w.c0;
    let r1 = beta.c0 - r2 * t.c0 - r3 * s.c0;
    Pad([r0, r1, r2, r3])
}

/// Four multilinear corner weights, certified to span the quartic field over the base
/// field. The monomial weights `{1, a, b, ab}` and the Boolean-corner weights
/// `{(1-a)(1-b), a(1-b), (1-a)b, ab}` differ by an invertible base-field matrix.
/// This checks the actual corner matrix, rather than applying the univariate pad theorem
/// to an arbitrary pair of sumcheck coordinates (handoff Note 5).
///
/// Branches in construction depend only on the public challenges. Applying the cached
/// inverse to a secret value uses fixed-length field arithmetic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CornerPadBasis {
    weights: [E; 4],
    inverse: [[Goldilocks; 4]; 4],
}

impl CornerPadBasis {
    /// Reject exactly the pairs whose four corner weights have base-field rank below four.
    pub fn new(a: E, b: E) -> Option<Self> {
        let weights = [
            (E::ONE - a) * (E::ONE - b),
            a * (E::ONE - b),
            (E::ONE - a) * b,
            a * b,
        ];
        let columns = weights.map(E::to_limbs);
        let mut matrix: [[Goldilocks; 8]; 4] = core::array::from_fn(|row| {
            core::array::from_fn(|col| {
                if col < 4 {
                    columns[col][row]
                } else if col - 4 == row {
                    Goldilocks::ONE
                } else {
                    Goldilocks::ZERO
                }
            })
        });
        for col in 0..4 {
            let pivot = (col..4).find(|&row| !matrix[row][col].is_zero())?;
            matrix.swap(col, pivot);
            let scale = matrix[col][col].inv();
            for cell in &mut matrix[col] {
                *cell *= scale;
            }
            let pivot_row = matrix[col];
            for (row, cells) in matrix.iter_mut().enumerate() {
                if row != col {
                    let factor = cells[col];
                    for (cell, pivot_cell) in cells.iter_mut().zip(pivot_row) {
                        *cell -= factor * pivot_cell;
                    }
                }
            }
        }
        let inverse = core::array::from_fn(|row| core::array::from_fn(|col| matrix[row][col + 4]));
        Some(Self { weights, inverse })
    }

    pub fn weights(&self) -> &[E; 4] {
        &self.weights
    }

    /// Evaluate four independent base-field cells at the certified corner weights.
    pub fn apply(&self, pad: &Pad) -> E {
        self.weights
            .iter()
            .zip(pad.0)
            .fold(E::ZERO, |sum, (&w, r)| sum + w.mul_base(r))
    }

    /// Unique base-field pad producing `value`.
    pub fn invert(&self, value: E) -> Pad {
        let limbs = value.to_limbs();
        Pad(self.inverse.map(|row| {
            row.iter()
                .zip(limbs)
                .fold(Goldilocks::ZERO, |sum, (&coefficient, limb)| {
                    sum + coefficient * limb
                })
        }))
    }
}

// ============================================================================
// 4. Separable sumcheck mask
// ============================================================================

#[inline]
fn pow2(n: usize) -> E {
    let mut acc = E::ONE;
    for _ in 0..n {
        acc = acc + acc;
    }
    acc
}

#[inline]
fn eval_coeffs(coeffs: &[E], x: E) -> E {
    let mut acc = E::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc * x + c;
    }
    acc
}

/// `c_1 x + ... + c_d x^d` for `coeffs = [c_1, ..., c_d]` (`evalNoConst`).
#[inline]
fn eval_no_const(coeffs: &[E], x: E) -> E {
    x * eval_coeffs(coeffs, x)
}

/// Mask `g(x) = a0 + sum_i sum_{k<d} a[i][k] x_i^{k+1}` over `n` variables (`LibraMask`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraMask {
    pub a0: E,
    pub a: Vec<Vec<E>>,
}

impl LibraMask {
    /// Uniform mask for `n` rounds of degree `d`.
    pub fn from_stream(stream: &mut SeedStream, n: usize, d: usize) -> Self {
        let a0 = stream.next_ext4();
        let a = (0..n)
            .map(|_| (0..d).map(|_| stream.next_ext4()).collect())
            .collect();
        Self { a0, a }
    }

    #[inline]
    pub fn num_rounds(&self) -> usize {
        self.a.len()
    }

    /// `sum_{j in rounds} u_j(1)`: the sum over a variable's two Boolean values of its
    /// univariate, added over the given rounds (`u_j(0) = 0`).
    fn tail_unit_sum(&self, from: usize) -> E {
        let mut acc = E::ZERO;
        for row in &self.a[from..] {
            for &c in row {
                acc += c;
            }
        }
        acc
    }

    /// `sum_{x in {0,1}^m} (kappa + sum_{j >= from} u_j(x_j))` with `m = n - from`
    /// (`sepSum`).
    fn sep_sum(&self, from: usize, kappa: E) -> E {
        let m = self.num_rounds() - from;
        let mut acc = pow2(m) * kappa;
        if m > 0 {
            acc += pow2(m - 1) * self.tail_unit_sum(from);
        }
        acc
    }

    /// `G = sum_{x in {0,1}^n} g(x)` (`maskSum`).
    pub fn sum(&self) -> E {
        self.sep_sum(0, self.a0)
    }

    /// `a0 + sum_{j < i} u_j(c_j)` (`maskKappa`).
    fn kappa(&self, c_prefix: &[E]) -> E {
        let mut acc = self.a0;
        for (row, &cj) in self.a.iter().zip(c_prefix) {
            acc += eval_no_const(row, cj);
        }
        acc
    }

    /// `g(c)` at a full point.
    pub fn eval(&self, c: &[E]) -> E {
        assert_eq!(c.len(), self.num_rounds());
        self.kappa(c)
    }

    /// Coefficients of the round-`i` polynomial
    /// `X -> sum_{x in {0,1}^{n-i-1}} g(c_0, ..., c_{i-1}, X, x)` (`maskMsg`).
    pub fn round_poly(&self, c_prefix: &[E]) -> Vec<E> {
        let i = c_prefix.len();
        assert!(i < self.num_rounds());
        let scale = pow2(self.num_rounds() - (i + 1));
        let mut out = Vec::with_capacity(self.a[i].len() + 1);
        out.push(self.sep_sum(i + 1, self.kappa(c_prefix)));
        out.extend(self.a[i].iter().map(|&c| scale * c));
        out
    }
}

impl Drop for LibraMask {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.a0), E::ZERO);
        for row in &mut self.a {
            qsag_asm::volatile_fill(row, E::ZERO);
        }
    }
}

/// Verifier view of the masked sumcheck (`LibraView`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraView {
    /// The mask sum `G`.
    pub g_sum: E,
    /// Coefficients of the round polynomials of `f + rho g`.
    pub rounds: Vec<Vec<E>>,
    /// The opened mask value `g(c)`.
    pub g_at_point: E,
}

/// Honest prover: `f_rounds[i]` holds the `d + 1` coefficients of the witness round
/// polynomial for the challenges `c[..i]` (`libraReal`).
pub fn libra_prove(f_rounds: &[Vec<E>], mask: &LibraMask, rho: E, c: &[E]) -> LibraView {
    let n = mask.num_rounds();
    assert_eq!(f_rounds.len(), n);
    assert_eq!(c.len(), n);
    let rounds = (0..n)
        .map(|i| {
            let g_round = mask.round_poly(&c[..i]);
            assert_eq!(f_rounds[i].len(), g_round.len());
            f_rounds[i]
                .iter()
                .zip(&g_round)
                .map(|(&f, &g)| f + rho * g)
                .collect()
        })
        .collect();
    LibraView {
        g_sum: mask.sum(),
        rounds,
        g_at_point: mask.eval(c),
    }
}

/// Verifier: checks the telescoping chain from `h + rho * g_sum` and returns the witness
/// value `f(c)` implied by the last round and the opened mask value. The caller must check
/// that value and `g_at_point` against openings of committed `f` and `g`.
pub fn libra_verify(h: E, view: &LibraView, rho: E, c: &[E], d: usize) -> Option<E> {
    if view.rounds.len() != c.len() {
        return None;
    }
    let mut claim = h + rho * view.g_sum;
    for (round, &ci) in view.rounds.iter().zip(c) {
        if round.len() != d + 1 {
            return None;
        }
        if eval_coeffs(round, E::ZERO) + eval_coeffs(round, E::ONE) != claim {
            return None;
        }
        claim = eval_coeffs(round, ci);
    }
    Some(claim - rho * view.g_at_point)
}

/// Simulator coins: the value sent as `G` and the non-constant coefficients of every round
/// (`LibraCoins`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraCoins {
    pub g_sum: E,
    pub coef: Vec<Vec<E>>,
}

impl LibraCoins {
    pub fn from_stream(stream: &mut SeedStream, n: usize, d: usize) -> Self {
        let g_sum = stream.next_ext4();
        let coef = (0..n)
            .map(|_| (0..d).map(|_| stream.next_ext4()).collect())
            .collect();
        Self { g_sum, coef }
    }
}

/// Simulator (`libraSim`): from the public claim `h`, the terminal witness value `y`, the
/// challenges and coins. It takes no witness.
pub fn libra_sim(h: E, y: E, rho: NonzeroChallenge, c: &[E], coins: &LibraCoins) -> LibraView {
    assert_eq!(coins.coef.len(), c.len());
    let half = E::from_base(Goldilocks::TWO.inv());
    let mut claim = h + rho.0 * coins.g_sum;
    let mut rounds = Vec::with_capacity(c.len());
    for (coef, &ci) in coins.coef.iter().zip(c) {
        let mut round = Vec::with_capacity(coef.len() + 1);
        round.push((claim - eval_coeffs(coef, E::ONE)) * half);
        round.extend_from_slice(coef);
        claim = eval_coeffs(&round, ci);
        rounds.push(round);
    }
    LibraView {
        g_sum: coins.g_sum,
        rounds,
        g_at_point: (claim - y) * rho.0.inv(),
    }
}

/// The coins on which the simulator reproduces the honest transcript (`libraCoinsOf`).
pub fn libra_coins_of(f_rounds: &[Vec<E>], mask: &LibraMask, rho: E) -> LibraCoins {
    let n = mask.num_rounds();
    assert_eq!(f_rounds.len(), n);
    let coef = (0..n)
        .map(|i| {
            let scale = rho * pow2(n - (i + 1));
            f_rounds[i][1..]
                .iter()
                .zip(&mask.a[i])
                .map(|(&f, &a)| f + scale * a)
                .collect()
        })
        .collect();
    LibraCoins {
        g_sum: mask.sum(),
        coef,
    }
}

// ============================================================================
// 5. Companion word and the two batched claims
// ============================================================================

/// `U_gamma = (1 - gamma) B + gamma C` (`blend`).
pub fn blend(gamma: E, b: &[E], c: &[E]) -> Vec<E> {
    assert_eq!(b.len(), c.len());
    let one_minus = E::ONE - gamma;
    b.iter()
        .zip(c)
        .map(|(&bi, &ci)| one_minus * bi + gamma * ci)
        .collect()
}

/// The companion `C` with `blend(gamma, b, C) == u` (`unblend`).
pub fn unblend(gamma: NonzeroChallenge, b: &[E], u: &[E]) -> Vec<E> {
    assert_eq!(b.len(), u.len());
    let one_minus = E::ONE - gamma.0;
    let inv = gamma.0.inv();
    b.iter()
        .zip(u)
        .map(|(&bi, &ui)| (ui - one_minus * bi) * inv)
        .collect()
}

/// `sum (f + rho g) = h + rho G` on the committed sums (`libraCheck`).
#[inline]
pub fn libra_check(sum_f: E, h: E, sum_g: E, g_sum: E, rho: E) -> bool {
    sum_f + rho * sum_g == h + rho * g_sum
}

/// `<U_gamma, t> = (1 - gamma) b + gamma sigma` on the committed evaluations
/// (`companionCheck`).
#[inline]
pub fn companion_check(ev_b: E, b: E, ev_c: E, sigma: E, gamma: E) -> bool {
    let one_minus = E::ONE - gamma;
    one_minus * ev_b + gamma * ev_c == one_minus * b + gamma * sigma
}

/// One binary fold of a coefficient vector, `f_even + alpha f_odd` (`foldCoeffs`).
pub fn fold_coeffs(alpha: E, f: &[E]) -> Vec<E> {
    assert!(f.len().is_multiple_of(2));
    f.as_chunks::<2>()
        .0
        .iter()
        .map(|p| p[0] + alpha * p[1])
        .collect()
}

// ============================================================================
// 6. Stage-0 blinding: q coefficients against q opened points
// ============================================================================

/// Values of the polynomial with coefficients `cs` at every point of `xs` (`evalAll`).
pub fn eval_all(cs: &[E], xs: &[E]) -> Vec<E> {
    xs.iter().map(|&x| eval_coeffs(cs, x)).collect()
}

/// Newton interpolation (`interp`): the `xs.len()` coefficients of the polynomial taking
/// the values `ys` at `xs`. `None` if the lengths differ or two points coincide.
pub fn interp(xs: &[E], ys: &[E]) -> Option<Vec<E>> {
    if xs.len() != ys.len() {
        return None;
    }
    let Some((&x, rest_x)) = xs.split_first() else {
        return Some(Vec::new());
    };
    let y = ys[0];
    let mut diffs = Vec::with_capacity(rest_x.len());
    for (&xi, &yi) in rest_x.iter().zip(&ys[1..]) {
        let dx = xi - x;
        if dx.is_zero() {
            qsag_asm::volatile_fill(&mut diffs, E::ZERO);
            return None;
        }
        diffs.push((yi - y) * dx.inv());
    }
    let result = interp(rest_x, &diffs);
    qsag_asm::volatile_fill(&mut diffs, E::ZERO);
    let mut q = result?;
    // Coefficients of `y + (X - x) q(X)` (`unquot`).
    let mut out = vec![E::ZERO; q.len() + 1];
    let mut carry = y;
    for (slot, &qk) in out.iter_mut().zip(&q) {
        *slot = carry - x * qk;
        carry = qk;
    }
    out[q.len()] = carry;
    qsag_asm::volatile_fill(&mut q, E::ZERO);
    Some(out)
}

/// Whether `z` lies in the quadratic subfield; exposed for callers that validate
/// challenges received on the wire.
#[inline]
pub fn in_quadratic_subfield(z: E) -> bool {
    z.c1 == GoldilocksExt2::ZERO
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;

    fn stream(tag: u8) -> SeedStream {
        SeedStream::new(b"QSAG.TEST.ZKHEM", &[tag; 32])
    }

    fn transcript(tag: u8) -> FiatShamirTranscript<InstanceBound> {
        let schedule = crate::pcs::whir_stage_schedule(8);
        FiatShamirTranscript::new()
            .bind_relation(b"QSAG.TEST.ZKHEM.REL", &[tag], &schedule)
            .bind_instance(&[&[tag]])
    }

    fn primitive(s: &mut SeedStream) -> PrimitiveChallenge {
        loop {
            if let Some(z) = PrimitiveChallenge::new(s.next_ext4()) {
                return z;
            }
        }
    }

    fn nonzero(s: &mut SeedStream) -> NonzeroChallenge {
        loop {
            if let Some(z) = NonzeroChallenge::new(s.next_ext4()) {
                return z;
            }
        }
    }

    /// Honest sumcheck for `sum_x prod_j tables[j](x)`: round polynomials as coefficient
    /// lists, the claimed sum, and the terminal product at `c`.
    fn product_sumcheck(tables: &[Vec<E>], c: &[E]) -> (E, Vec<Vec<E>>, E) {
        let d = tables.len();
        let mut cur: Vec<Vec<E>> = tables.to_vec();
        let total = (0..cur[0].len())
            .map(|x| cur.iter().map(|t| t[x]).fold(E::ONE, |a, b| a * b))
            .fold(E::ZERO, |a, b| a + b);
        let mut rounds = Vec::new();
        for &ci in c {
            let half = cur[0].len() / 2;
            let evals: Vec<E> = (0..=d)
                .map(|pt| {
                    let x = E::from_u64(pt as u64);
                    (0..half)
                        .map(|j| {
                            cur.iter()
                                .map(|t| t[2 * j] + x * (t[2 * j + 1] - t[2 * j]))
                                .fold(E::ONE, |a, b| a * b)
                        })
                        .fold(E::ZERO, |a, b| a + b)
                })
                .collect();
            rounds.push(crate::field::RoundPolyExt4::interpolate_from_small_ints(&evals).coeffs);
            for t in &mut cur {
                *t = (0..half)
                    .map(|j| t[2 * j] + ci * (t[2 * j + 1] - t[2 * j]))
                    .collect();
            }
        }
        let terminal = cur.iter().map(|t| t[0]).fold(E::ONE, |a, b| a * b);
        (total, rounds, terminal)
    }

    #[test]
    fn pad_map_and_pad_inv_are_mutually_inverse_outside_the_subfield() {
        let mut s = stream(1);
        for _ in 0..200 {
            let z = primitive(&mut s);
            let pad = Pad::from_stream(&mut s);
            assert_eq!(pad_inv(z, pad_map(z.get(), &pad)), pad);
            let v = s.next_ext4();
            assert_eq!(pad_map(z.get(), &pad_inv(z, v)), v);
        }
    }

    #[test]
    fn subfield_challenge_keeps_the_pad_image_in_the_subfield() {
        let mut s = stream(2);
        for _ in 0..200 {
            let z = E::from_ext2(GoldilocksExt2::new(s.next_base(), s.next_base()));
            assert!(in_quadratic_subfield(z));
            assert!(PrimitiveChallenge::new(z).is_none());
            let pad = Pad::from_stream(&mut s);
            assert!(in_quadratic_subfield(pad_map(z, &pad)));
            // The `(c1, c3)` half of a padded value is the unpadded one.
            let w = s.next_ext4();
            assert_eq!((w + pad_map(z, &pad)).c1, w.c1);
        }
    }

    #[test]
    fn primitive_coordinates_can_have_rank_deficient_corner_pads() {
        let a = E::V;
        for b in [a, a + E::ONE, -a] {
            assert!(PrimitiveChallenge::new(a).is_some());
            assert!(PrimitiveChallenge::new(b).is_some());
            assert!(CornerPadBasis::new(a, b).is_none());
        }
        let u = E::from_ext2(GoldilocksExt2::new(Goldilocks::ZERO, Goldilocks::ONE));
        assert!(CornerPadBasis::new(u, u + E::ONE).is_none());
        // One coordinate may be quadratic: {1, v, u, vu} is still a basis.
        assert!(CornerPadBasis::new(a, u).is_some());
    }

    #[test]
    fn full_rank_corner_pads_invert_actual_multilinear_evaluations() {
        let mut s = stream(14);
        for _ in 0..200 {
            let a = s.next_ext4();
            let b = s.next_ext4();
            let basis = CornerPadBasis::new(a, b).unwrap();
            let pad = Pad::from_stream(&mut s);
            let value = basis.apply(&pad);
            let cells = pad.0.map(E::from_base);
            assert_eq!(value, crate::field::mle_eval_ext4(&cells, &[a, b]));
            assert_eq!(basis.invert(value), pad);
            let target = s.next_ext4();
            assert_eq!(basis.apply(&basis.invert(target)), target);
        }
    }

    /// Full rank for each individual observation does not imply joint hiding when the
    /// same four coins are reused. This is the missing premise in applying the component
    /// pad theorem to two OOD values or to OOD plus terminal observations.
    #[test]
    fn four_pads_do_not_hide_two_joint_quartic_observations() {
        let z = PrimitiveChallenge::new(E::V).unwrap();
        let other = PrimitiveChallenge::new(E::V + E::ONE).unwrap();
        let mut s = stream(15);
        for _ in 0..100 {
            let coins = Pad::from_stream(&mut s);
            let first = pad_map(z.get(), &coins);
            let second = pad_map(other.get(), &coins);
            // Distinguishes witness offsets (0,0) from (0,1) for every pad, despite
            // each marginal observation having a bijective four-cell pad map.
            let predicted = pad_map(other.get(), &pad_inv(z, first));
            assert_eq!(predicted, second);
            assert_ne!(predicted, second + E::ONE);
        }
    }

    #[test]
    fn squeezed_challenges_are_primitive_and_reproducible() {
        let mut prover = transcript(3);
        let mut verifier = transcript(3);
        for _ in 0..64 {
            let a = PrimitiveChallenge::squeeze(&mut prover, b"ZKHEM_Z");
            let b = PrimitiveChallenge::squeeze(&mut verifier, b"ZKHEM_Z");
            assert_eq!(a, b);
            assert!(!in_quadratic_subfield(a.get()));
            let r = NonzeroChallenge::squeeze(&mut prover, b"ZKHEM_RHO");
            assert_eq!(r, NonzeroChallenge::squeeze(&mut verifier, b"ZKHEM_RHO"));
            assert!(!r.get().is_zero());
        }
    }

    #[test]
    fn mask_sum_and_round_polys_match_brute_force_hypercube_sums() {
        let mut s = stream(4);
        for (n, d) in [(1usize, 1usize), (2, 3), (4, 2), (6, 4)] {
            let mask = LibraMask::from_stream(&mut s, n, d);
            let g = |x: &[E]| mask.eval(x);
            let bits = |m: usize, k: usize| -> Vec<E> {
                (0..k).map(|j| E::from_u64(((m >> j) & 1) as u64)).collect()
            };
            let brute: E = (0..1usize << n)
                .map(|m| g(&bits(m, n)))
                .fold(E::ZERO, |a, b| a + b);
            assert_eq!(mask.sum(), brute);

            let c: Vec<E> = (0..n).map(|_| s.next_ext4()).collect();
            for i in 0..n {
                let round = mask.round_poly(&c[..i]);
                assert_eq!(round.len(), d + 1);
                let x = s.next_ext4();
                let rest = n - i - 1;
                let brute_round: E = (0..1usize << rest)
                    .map(|m| {
                        let mut point = c[..i].to_vec();
                        point.push(x);
                        point.extend(bits(m, rest));
                        g(&point)
                    })
                    .fold(E::ZERO, |a, b| a + b);
                assert_eq!(eval_coeffs(&round, x), brute_round);
            }
        }
    }

    #[test]
    fn masked_sumcheck_is_complete_and_equals_the_simulator_on_matching_coins() {
        let mut s = stream(5);
        for (n, d) in [(1usize, 1usize), (3, 2), (5, 3), (4, 8)] {
            let tables: Vec<Vec<E>> = (0..d)
                .map(|_| (0..1usize << n).map(|_| s.next_ext4()).collect())
                .collect();
            let c: Vec<E> = (0..n).map(|_| s.next_ext4()).collect();
            let (h, f_rounds, y) = product_sumcheck(&tables, &c);
            let mask = LibraMask::from_stream(&mut s, n, d);
            let rho = nonzero(&mut s);

            let view = libra_prove(&f_rounds, &mask, rho.get(), &c);
            assert_eq!(libra_verify(h, &view, rho.get(), &c, d), Some(y));
            assert!(libra_check(h, h, mask.sum(), view.g_sum, rho.get()));

            let coins = libra_coins_of(&f_rounds, &mask, rho.get());
            assert_eq!(libra_sim(h, y, rho, &c, &coins), view);

            // Any coins give an accepting view with the same terminal value.
            let fresh = LibraCoins::from_stream(&mut s, n, d);
            let simulated = libra_sim(h, y, rho, &c, &fresh);
            assert_eq!(libra_verify(h, &simulated, rho.get(), &c, d), Some(y));

            // A wrong sum claim is rejected.
            assert_eq!(libra_verify(h + E::ONE, &view, rho.get(), &c, d), None);
        }
    }

    #[test]
    fn without_the_mask_the_round_polynomials_are_the_witness_ones() {
        let mut s = stream(6);
        let (n, d) = (3usize, 2usize);
        let tables: Vec<Vec<E>> = (0..d)
            .map(|_| (0..1usize << n).map(|_| s.next_ext4()).collect())
            .collect();
        let c: Vec<E> = (0..n).map(|_| s.next_ext4()).collect();
        let (_, f_rounds, _) = product_sumcheck(&tables, &c);
        let mask = LibraMask::from_stream(&mut s, n, d);
        assert_eq!(libra_prove(&f_rounds, &mask, E::ZERO, &c).rounds, f_rounds);
    }

    #[test]
    fn blend_and_unblend_are_mutually_inverse_and_carry_the_claim() {
        let mut s = stream(7);
        let len = 64;
        let b: Vec<E> = (0..len).map(|_| E::from_base(s.next_base())).collect();
        let c: Vec<E> = (0..len).map(|_| s.next_ext4()).collect();
        let t: Vec<E> = (0..len).map(|_| s.next_ext4()).collect();
        let dot = |u: &[E]| {
            u.iter()
                .zip(&t)
                .map(|(&a, &w)| a * w)
                .fold(E::ZERO, |a, b| a + b)
        };
        let gamma = nonzero(&mut s);

        let u = blend(gamma.get(), &b, &c);
        assert_eq!(unblend(gamma, &b, &u), c);
        let fresh: Vec<E> = (0..len).map(|_| s.next_ext4()).collect();
        assert_eq!(blend(gamma.get(), &b, &unblend(gamma, &b, &fresh)), fresh);
        assert!(companion_check(
            dot(&b),
            dot(&b),
            dot(&c),
            dot(&c),
            gamma.get()
        ));
        assert_eq!(
            dot(&u),
            (E::ONE - gamma.get()) * dot(&b) + gamma.get() * dot(&c)
        );
        // Folding commutes with blending: the terminal polynomial is a fold of `u`.
        let alpha = s.next_ext4();
        assert_eq!(
            fold_coeffs(alpha, &u),
            blend(
                gamma.get(),
                &fold_coeffs(alpha, &b),
                &fold_coeffs(alpha, &c)
            )
        );
    }

    #[test]
    fn two_accepting_challenges_force_the_claims() {
        let mut s = stream(8);
        for _ in 0..50 {
            let (ev_b, ev_c) = (s.next_ext4(), s.next_ext4());
            let (g1, g2) = (s.next_ext4(), s.next_ext4());
            assert_ne!(g1, g2);
            // True claims pass for both challenges.
            assert!(companion_check(ev_b, ev_b, ev_c, ev_c, g1));
            assert!(companion_check(ev_b, ev_b, ev_c, ev_c, g2));
            // A false claim with a companion claim fitted to `g1` fails at `g2`.
            let b = ev_b + E::ONE;
            let gamma = NonzeroChallenge::new(g1).unwrap();
            let sigma = ev_c + (E::ONE - g1) * (ev_b - b) * gamma.get().inv();
            assert!(companion_check(ev_b, b, ev_c, sigma, g1));
            assert!(!companion_check(ev_b, b, ev_c, sigma, g2));
        }
    }

    #[test]
    fn uncommitted_companion_claim_or_mask_sum_passes_any_statement() {
        let mut s = stream(9);
        for _ in 0..50 {
            let (ev_b, b, ev_c) = (s.next_ext4(), s.next_ext4(), s.next_ext4());
            let gamma = nonzero(&mut s);
            let sigma = ev_c + (E::ONE - gamma.get()) * (ev_b - b) * gamma.get().inv();
            assert!(companion_check(ev_b, b, ev_c, sigma, gamma.get()));

            let (sum_f, h, sum_g) = (s.next_ext4(), s.next_ext4(), s.next_ext4());
            let rho = nonzero(&mut s);
            let g_sum = sum_g + (sum_f - h) * rho.get().inv();
            assert!(libra_check(sum_f, h, sum_g, g_sum, rho.get()));
        }
    }

    #[test]
    fn interpolation_inverts_evaluation_at_distinct_points() {
        let mut s = stream(10);
        for q in [0usize, 1, 2, 7, 33] {
            let xs: Vec<E> = (0..q).map(|_| s.next_ext4()).collect();
            let cs: Vec<E> = (0..q).map(|_| s.next_ext4()).collect();
            assert_eq!(interp(&xs, &eval_all(&cs, &xs)), Some(cs));
            let ys: Vec<E> = (0..q).map(|_| s.next_ext4()).collect();
            assert_eq!(eval_all(&interp(&xs, &ys).unwrap(), &xs), ys);
        }
        let x = s.next_ext4();
        assert_eq!(interp(&[x, x], &[E::ZERO, E::ONE]), None);
    }

    #[test]
    fn blinding_sized_for_stage0_queries_leaves_the_terminal_coefficient_unmasked() {
        let mut s = stream(11);
        let (w0, w1, alpha) = (s.next_ext4(), s.next_ext4(), s.next_ext4());
        for _ in 0..20 {
            let r = s.next_ext4();
            let folded = fold_coeffs(alpha, &[w0, w1, r, E::ZERO]);
            assert_eq!(folded[0], w0 + alpha * w1);
        }
    }

    #[test]
    fn seed_stream_is_deterministic_and_canonical() {
        let mut a = stream(12);
        let mut b = stream(12);
        let mut c = stream(13);
        let xs: Vec<Goldilocks> = (0..1000).map(|_| a.next_base()).collect();
        let ys: Vec<Goldilocks> = (0..1000).map(|_| b.next_base()).collect();
        let zs: Vec<Goldilocks> = (0..1000).map(|_| c.next_base()).collect();
        assert_eq!(xs, ys);
        assert_ne!(xs, zs);
        assert!(
            xs.iter()
                .all(|x| x.to_canonical_u64() < crate::field::GOLDILOCKS_PRIME)
        );
    }
}
