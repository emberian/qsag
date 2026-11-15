//! Relations proved by the committed zk-Hem protocol in [`super::protocol`].
//!
//! A relation is a list of rows over one assignment vector `z` (`z[0] = 1`):
//!
//! * S-box rows `<a, z>^7 = <c, z>`,
//! * multiplication rows `<a, z> * <b, z> = <c, z>`.
//!
//! S-box rows come first, so the row selector is a prefix indicator the verifier evaluates
//! in `O(log rows)`. Public values enter as constants of the linear forms, so they are part
//! of the [`Shape`] and of its digest. Twelve masking rows over twelve masking variables are
//! appended by [`ConstraintSystem::finish`]; the prover fills those variables with fresh
//! uniform values (see [`MASK_ROWS`]).

use alloc::vec;
use alloc::vec::Vec;

use crate::field::{Goldilocks, GoldilocksOps as _};
use crate::sponge::{
    POSEIDON2_HALF_EXT_ROUNDS, POSEIDON2_INT_ROUNDS, cshake256_32, poseidon2_apply_me,
    poseidon2_apply_mi, poseidon2_const_at, poseidon2_perm12, poseidon2_sbox7,
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

/// Sparse matrix in compressed-row form.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Csr {
    ptr: Vec<u32>,
    col: Vec<u32>,
    val: Vec<F>,
}

impl Csr {
    fn new() -> Self {
        Self {
            ptr: vec![0],
            col: Vec::new(),
            val: Vec::new(),
        }
    }

    fn push_row(&mut self, lc: &Lc) {
        for &(v, c) in lc.terms() {
            self.col.push(v);
            self.val.push(c);
        }
        self.ptr.push(self.col.len() as u32);
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        self.ptr.len() - 1
    }

    #[inline]
    pub fn nnz(&self) -> usize {
        self.col.len()
    }

    /// `(column, coefficient)` pairs of row `i`.
    #[inline]
    pub fn row(&self, i: usize) -> impl Iterator<Item = (usize, F)> + '_ {
        let (lo, hi) = (self.ptr[i] as usize, self.ptr[i + 1] as usize);
        self.col[lo..hi]
            .iter()
            .zip(&self.val[lo..hi])
            .map(|(&c, &v)| (c as usize, v))
    }

    #[inline]
    pub fn row_dot(&self, i: usize, z: &[F]) -> F {
        self.row(i)
            .fold(F::ZERO, |acc, (c, v)| acc + v.const_mul(z[c]))
    }

    fn absorb_into(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.ptr.len() as u64).to_le_bytes());
        for &p in &self.ptr {
            out.extend_from_slice(&p.to_le_bytes());
        }
        for (&c, &v) in self.col.iter().zip(&self.val) {
            out.extend_from_slice(&c.to_le_bytes());
            out.extend_from_slice(&v.to_le_bytes());
        }
    }
}

/// Number of masking rows (and masking variables) appended to every relation.
///
/// With `p1, p2, p3` three groups of four masking variables, the rows are
/// `p1_k * 1 = p1_k`, `1 * p2_k = p2_k` and `p3_k * 2 = 2 p3_k`. Each group sits on one
/// two-variable corner of the row hypercube. At a sumcheck point `rx` the groups add
/// `(k1 e1 + k3 e3, k2 e2, k1 e1 + k2 e2 + 2 k3 e3)` to `(Az, Bz, Cz)(rx)`, where `e_g` is
/// the corner-weighted sum of group `g` and `k_g` its common weight. That map has
/// determinant `k1 k2 k3`, so when the corner weights have full base-field rank and the
/// `k_g` are nonzero, the three revealed values are uniform and independent of the rest of
/// the assignment.
pub const MASK_ROWS: usize = 12;

/// Public structure of a relation: row matrices over `num_vars` variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shape {
    /// `log2` of the padded row count.
    pub log_rows: usize,
    /// Rows `0..num_sbox` are S-box rows; all others are multiplication rows.
    pub num_sbox: usize,
    /// Variables, including the constant and the masking variables.
    pub num_vars: usize,
    /// First of the [`MASK_ROWS`] masking variables.
    pub mask_var_base: usize,
    pub a: Csr,
    pub b: Csr,
    pub c: Csr,
}

impl Shape {
    #[inline]
    pub fn num_rows(&self) -> usize {
        1usize << self.log_rows
    }

    /// First row of masking group `g in 0..3`.
    #[inline]
    pub fn mask_row_base(&self, g: usize) -> usize {
        self.num_rows() - 4 * (3 - g)
    }

    /// Binding digest of the whole relation, public constants included.
    pub fn digest(&self) -> [u8; 32] {
        let mut bytes = Vec::with_capacity(64 + 12 * (self.a.nnz() + self.b.nnz() + self.c.nnz()));
        for n in [self.log_rows, self.num_sbox, self.num_vars, self.mask_var_base] {
            bytes.extend_from_slice(&(n as u64).to_le_bytes());
        }
        self.a.absorb_into(&mut bytes);
        self.b.absorb_into(&mut bytes);
        self.c.absorb_into(&mut bytes);
        cshake256_32(b"QSAG.ZKHEM.SHAPE/v1", &bytes)
    }

    /// Whether `z` (with `z[0] = 1`) satisfies every row.
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
    }
}

/// Relation builder that carries an assignment alongside the rows.
///
/// The row structure must not depend on assigned values: the verifier rebuilds the [`Shape`]
/// by running the same synthesis on a placeholder assignment.
pub struct ConstraintSystem {
    values: Vec<F>,
    sbox: Vec<(Lc, Lc)>,
    mul: Vec<(Lc, Lc, Lc)>,
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
            sbox: Vec::new(),
            mul: Vec::new(),
        }
    }

    /// Allocate a free variable with the given assigned value.
    pub fn alloc(&mut self, value: F) -> Var {
        self.values.push(value);
        Var((self.values.len() - 1) as u32)
    }

    pub fn eval(&self, lc: &Lc) -> F {
        lc.terms()
            .iter()
            .fold(F::ZERO, |acc, &(v, c)| acc + c.const_mul(self.values[v as usize]))
    }

    /// Fresh variable `y` with the row `a^7 = y`.
    pub fn sbox7(&mut self, a: &Lc) -> Var {
        let y = self.alloc(poseidon2_sbox7(self.eval(a)));
        self.sbox.push((a.clone(), y.into()));
        y
    }

    /// Fresh variable `y` with the row `a * b = y`.
    pub fn mul(&mut self, a: &Lc, b: &Lc) -> Var {
        let y = self.alloc(self.eval(a).const_mul(self.eval(b)));
        self.mul.push((a.clone(), b.clone(), y.into()));
        y
    }

    pub fn enforce_mul(&mut self, a: Lc, b: Lc, c: Lc) {
        self.mul.push((a, b, c));
    }

    /// Row `lc * 1 = 0`.
    pub fn enforce_zero(&mut self, lc: Lc) {
        self.mul.push((lc, Lc::constant(F::ONE), Lc::zero()));
    }

    pub fn enforce_equal(&mut self, a: &Lc, b: &Lc) {
        self.enforce_zero(a.minus(b));
    }

    /// Row `v * (1 - v) = 0`.
    pub fn enforce_boolean(&mut self, v: &Lc) {
        self.mul
            .push((v.clone(), Lc::constant(F::ONE).minus(v), Lc::zero()));
    }

    /// `if bit { on_one } else { on_zero }`, one multiplication row. `bit` must be
    /// constrained Boolean by the caller.
    pub fn select(&mut self, bit: &Lc, on_one: &Lc, on_zero: &Lc) -> Lc {
        let delta = self.mul(bit, &on_one.minus(on_zero));
        on_zero.plus(&delta.into())
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        self.sbox.len() + self.mul.len()
    }

    /// Close the relation: append the masking variables and rows, pad the row count to a
    /// power of two. Returns the shape and the assignment, whose masking variables are zero
    /// until the prover overwrites them.
    pub fn finish(mut self) -> (Shape, Vec<F>) {
        let mask_var_base = self.values.len();
        let mask: Vec<Var> = (0..MASK_ROWS).map(|_| self.alloc(F::ZERO)).collect();
        let used = self.num_rows();
        let log_rows = (used + MASK_ROWS).next_power_of_two().trailing_zeros().max(4) as usize;
        let total = 1usize << log_rows;
        let one = Lc::constant(F::ONE);
        let two = Lc::constant(F::TWO);
        let empty = Lc::zero();

        let (mut a, mut b, mut c) = (Csr::new(), Csr::new(), Csr::new());
        for (ra, rc) in &self.sbox {
            a.push_row(ra);
            b.push_row(&empty);
            c.push_row(rc);
        }
        for (ra, rb, rc) in &self.mul {
            a.push_row(ra);
            b.push_row(rb);
            c.push_row(rc);
        }
        for _ in used..total - MASK_ROWS {
            a.push_row(&empty);
            b.push_row(&empty);
            c.push_row(&empty);
        }
        for (k, &p) in mask.iter().enumerate() {
            let p: Lc = p.into();
            match k / 4 {
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
        let shape = Shape {
            log_rows,
            num_sbox: self.sbox.len(),
            num_vars: self.values.len(),
            mask_var_base,
            a,
            b,
            c,
        };
        (shape, self.values)
    }
}

// ============================================================================
// Width-12 Poseidon2 gadgets (canonical profile of `crate::sponge`)
// ============================================================================

/// Dense matrix of a linear layer of `crate::sponge`, read off its action on unit vectors.
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

fn apply_matrix(m: &[[F; 12]; 12], st: &mut [Lc; 12]) {
    let next: [Lc; 12] = core::array::from_fn(|i| {
        let parts: [(F, &Lc); 12] = core::array::from_fn(|j| (m[i][j], &st[j]));
        Lc::combine(&parts)
    });
    *st = next;
}

/// The permutation `crate::sponge::poseidon2_perm12` on linear forms: 118 S-box rows, no
/// other rows. Output lanes are linear forms over the last round's S-box outputs.
pub fn poseidon2_perm(cs: &mut ConstraintSystem, st: &mut [Lc; 12]) {
    let me = layer_matrix(poseidon2_apply_me);
    let mi = layer_matrix(poseidon2_apply_mi);
    apply_matrix(&me, st);
    for tag in [0u64, 1, 2] {
        if tag == 1 {
            for r in 0..POSEIDON2_INT_ROUNDS {
                let x = st[0].plus_const(poseidon2_const_at(1, r as u64, 0));
                st[0] = cs.sbox7(&x).into();
                apply_matrix(&mi, st);
            }
        } else {
            for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
                for (lane, slot) in st.iter_mut().enumerate() {
                    let x = slot.plus_const(poseidon2_const_at(tag, r as u64, lane as u64));
                    *slot = cs.sbox7(&x).into();
                }
                apply_matrix(&me, st);
            }
        }
    }
}

/// Rate-6, capacity-6 sponge over [`poseidon2_perm`] with the padding of
/// `qsag-cred::blind_vc::sponge12`: a `1` is added after a short final chunk, or in a
/// further block when the message length is a multiple of six. Returns the final state.
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

#[cfg(test)]
mod tests {
    use super::*;

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    #[test]
    fn permutation_gadget_matches_native_and_uses_only_sbox_rows() {
        let mut cs = ConstraintSystem::new();
        let input: [F; 12] = core::array::from_fn(|i| f(1000 + 7 * i as u64));
        let mut st: [Lc; 12] = core::array::from_fn(|i| cs.alloc(input[i]).into());
        poseidon2_perm(&mut cs, &mut st);
        let mut native = input;
        poseidon2_perm12(&mut native);
        for (lc, want) in st.iter().zip(native) {
            assert_eq!(cs.eval(lc), want);
        }
        assert_eq!(cs.num_rows(), 118);
        let (shape, z) = cs.finish();
        assert_eq!(shape.num_sbox, 118);
        assert!(shape.is_satisfied(&z));
        let mut bad = z.clone();
        bad[20] += F::ONE;
        assert!(!shape.is_satisfied(&bad));
    }

    #[test]
    fn sponge_gadget_matches_native_for_every_padding_case() {
        for len in [1usize, 5, 6, 7, 12, 16, 39] {
            let msg: Vec<F> = (0..len).map(|i| f(3 + 11 * i as u64)).collect();
            let mut cs = ConstraintSystem::new();
            let lcs: Vec<Lc> = msg.iter().map(|&v| cs.alloc(v).into()).collect();
            let out = sponge12(&mut cs, &lcs);
            let want = sponge12_native(&msg);
            for (lc, w) in out.iter().zip(want) {
                assert_eq!(cs.eval(lc), w, "message length {len}");
            }
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
        }
    }

    #[test]
    fn masking_rows_hold_for_any_mask_values_and_shape_is_value_independent() {
        let build = |x: u64| {
            let mut cs = ConstraintSystem::new();
            let v = cs.alloc(f(x));
            let y = cs.sbox7(&v.into());
            let b = cs.alloc(f(1));
            cs.enforce_boolean(&b.into());
            let _ = cs.select(&b.into(), &y.into(), &v.into());
            cs.finish()
        };
        let (shape, mut z) = build(5);
        let (shape2, _) = build(99);
        assert_eq!(shape, shape2);
        assert_eq!(shape.digest(), shape2.digest());
        for k in 0..MASK_ROWS {
            z[shape.mask_var_base + k] = f(0xDEAD_0000 + k as u64);
        }
        assert!(shape.is_satisfied(&z));
        assert_eq!(shape.mask_row_base(2) + 4, shape.num_rows());
    }
}
