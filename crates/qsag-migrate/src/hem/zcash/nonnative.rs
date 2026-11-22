//! Arithmetic modulo an odd prime `p` with `2^248 < p < 2^255` (the Pallas base and scalar
//! fields, the Jubjub base field and the 252-bit Jubjub scalar order) over the Goldilocks
//! constraint system, with unreduced products. Elements are 255-bit representatives of
//! their residue whatever the bit length of `p`.
//!
//! This is the same technique as `hem::curve` (integers as polynomials in `2^8` with
//! proven coefficient intervals, congruences checked limb group by limb group with
//! range-checked carries). It exists separately because the Orchard relations need two
//! things `hem::curve` does not export: products that stay unreduced, so that one
//! congruence can check a sum of several products, and reduction of the high coefficients
//! through the constants `2^(8k) mod p`, which leaves a 32-coefficient integer and a
//! quotient of a few dozen bits instead of about 260. A congruence then costs about 230
//! rows and a product 63. Both could be shared with `hem::curve` if it exported its
//! polynomial type.
//!
//! # Soundness of every step
//!
//! * A [`Num`] is a list of linear forms `c_k` with integer intervals `[lo_k, hi_k]`,
//!   `|lo_k|, |hi_k| < 2^61`, standing for the integer `sum c_k 2^(8k)`. The interval is a
//!   proven fact about every satisfying assignment: it starts from Boolean bits and
//!   constants and is propagated by interval arithmetic.
//! * [`Num::mul`] allocates the `n` coefficients of the product and fixes them with `n`
//!   rows `A(s) B(s) = C(s)` at `s = 0..n`. Two polynomials of degree below `n` over the
//!   Goldilocks field that agree at `n` points are equal, and the integer coefficients of
//!   `A B` are below `2^61` in absolute value, so the field values are those integers.
//! * [`Field::enforce_zero`] first replaces each coefficient at position `k >= 32` by its
//!   multiples of the bytes of `2^(8k) mod p`; the integer changes by a multiple of `p`.
//!   It then proves `X + K p - q p = 0` over the integers: `K` is a public offset that
//!   makes the quotient non-negative, `q` is a bit-decomposed witness, and the identity is
//!   split into groups of `G` coefficients with carries `V_g + c_(g-1) = 2^(8G) c_g`. Each
//!   carry is range-checked to an interval that contains every honest value, and the
//!   builder asserts for each group equation that its left side minus its right side is
//!   below the Goldilocks prime in absolute value over all admitted values, so an equation
//!   that holds in the field holds over the integers. Synthesis panics if an interval is
//!   too wide for any group size.
//!
//! Native arithmetic on witness values (quotients, carries, residues) is branch-free with
//! fixed iteration counts.

use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc};

type F = Goldilocks;

/// The Goldilocks prime.
const PG: i128 = 0xFFFF_FFFF_0000_0001;
/// Largest absolute value a coefficient interval may reach.
const COEF_BOUND: i128 = 1 << 61;
/// Limbs of a reduced element.
pub const LIMBS: usize = 32;
/// Highest coefficient position that can be folded.
const MAX_COEFS: usize = 200;

type Wide = [u64; 6];

fn f_int(v: i128) -> F {
    let m = F::from_u128_reduced(v.unsigned_abs());
    if v < 0 { F::ZERO - m } else { m }
}

fn is_const(lc: &Lc) -> bool {
    lc.terms().iter().all(|&(v, _)| v == 0)
}

// ============================================================================
// Wide integers
// ============================================================================

#[inline(always)]
fn adc(a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + c as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let t = (a as u128).wrapping_sub(b as u128 + borrow as u128);
    (t as u64, ((t >> 64) as u64) & 1)
}

fn wide_add(a: &Wide, b: &Wide) -> Wide {
    let mut out = [0u64; 6];
    let mut c = 0;
    for i in 0..6 {
        (out[i], c) = adc(a[i], b[i], c);
    }
    out
}

fn wide_sub(a: &Wide, b: &Wide) -> Wide {
    let mut out = [0u64; 6];
    let mut c = 0;
    for i in 0..6 {
        (out[i], c) = sbb(a[i], b[i], c);
    }
    out
}

/// `w += v << (8 * byte_pos)` for `v < 2^64` and `byte_pos < 40`.
fn wide_add_shifted(w: &mut Wide, v: u64, byte_pos: usize) {
    let word = byte_pos / 8;
    let x = (v as u128) << (8 * (byte_pos % 8));
    let parts = [x as u64, (x >> 64) as u64];
    let mut c = 0;
    for i in word..6 {
        let add = if i - word < 2 { parts[i - word] } else { 0 };
        (w[i], c) = adc(w[i], add, c);
    }
}

fn wide_mul_u64(a: &[u64; 4], k: u64) -> Wide {
    let mut out = [0u64; 6];
    let mut c = 0u64;
    for i in 0..4 {
        let t = (a[i] as u128) * (k as u128) + c as u128;
        out[i] = t as u64;
        c = (t >> 64) as u64;
    }
    out[4] = c;
    out
}

fn wide_bitlen(a: &Wide) -> usize {
    for i in (0..6).rev() {
        if a[i] != 0 {
            return 64 * i + 64 - a[i].leading_zeros() as usize;
        }
    }
    0
}

fn wide_bytes(a: &Wide) -> [u8; 48] {
    let mut out = [0u8; 48];
    for i in 0..6 {
        out[8 * i..8 * i + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    out
}

/// Quotient and remainder by a modulus `p < 2^255`; 384 fixed iterations.
fn wide_divrem(n: &Wide, p: &[u64; 4]) -> (Wide, [u64; 4]) {
    let mut q = [0u64; 6];
    let mut r = [0u64; 4];
    for bit in (0..384).rev() {
        // r < p < 2^255, so the shift does not overflow.
        for i in (1..4).rev() {
            r[i] = (r[i] << 1) | (r[i - 1] >> 63);
        }
        r[0] = (r[0] << 1) | ((n[bit / 64] >> (bit % 64)) & 1);
        let mut t = [0u64; 4];
        let mut borrow = 0;
        for i in 0..4 {
            (t[i], borrow) = sbb(r[i], p[i], borrow);
        }
        let take = borrow.wrapping_sub(1); // all ones when r >= p
        for i in 0..4 {
            r[i] = (t[i] & take) | (r[i] & !take);
        }
        q[bit / 64] |= (take & 1) << (bit % 64);
    }
    (q, r)
}

// ============================================================================
// Unreduced integers
// ============================================================================

#[derive(Clone)]
struct Coef {
    lc: Lc,
    lo: i128,
    hi: i128,
}

impl Coef {
    fn check(self) -> Self {
        assert!(
            self.lo <= self.hi && self.lo > -COEF_BOUND && self.hi < COEF_BOUND,
            "coefficient interval too wide"
        );
        self
    }
}

/// The integer value of a coefficient under the current assignment.
fn int_value(cs: &ConstraintSystem, c: &Coef) -> i128 {
    let v = cs.eval(&c.lc).to_canonical_u64() as i128;
    // Field values above `hi` are the negative integers.
    let negative = (c.hi - v) >> 127;
    v - (negative & PG)
}

/// An integer as a polynomial in `2^8` with proven coefficient intervals. Sums,
/// differences and products by constants are free.
#[derive(Clone)]
pub struct Num(Vec<Coef>);

impl Num {
    pub fn zero() -> Self {
        Self(Vec::new())
    }

    /// A public non-negative constant, little-endian.
    pub fn constant(value_le: &[u8]) -> Self {
        Self(
            value_le
                .iter()
                .map(|&b| Coef {
                    lc: Lc::constant(F::from_u64_reduced(b as u64)),
                    lo: b as i128,
                    hi: b as i128,
                })
                .collect(),
        )
    }

    /// A small public constant.
    pub fn small(v: i64) -> Self {
        Self(vec![Coef {
            lc: Lc::constant(f_int(v as i128)),
            lo: v as i128,
            hi: v as i128,
        }])
    }

    /// Bits the caller has constrained Boolean, little-endian.
    pub fn from_bits(bits_le: &[Lc]) -> Self {
        Self(
            bits_le
                .chunks(8)
                .map(|chunk| {
                    let parts: Vec<(F, &Lc)> = chunk
                        .iter()
                        .enumerate()
                        .map(|(k, b)| (F::from_u64_reduced(1 << k), b))
                        .collect();
                    Coef {
                        lc: Lc::combine(&parts),
                        lo: 0,
                        hi: (1 << chunk.len()) - 1,
                    }
                })
                .collect(),
        )
    }

    /// Limbs the caller has constrained to `[0, 255]`, little-endian.
    pub fn from_limbs(limbs_le: &[Lc]) -> Self {
        Self(
            limbs_le
                .iter()
                .map(|lc| Coef {
                    lc: lc.clone(),
                    lo: 0,
                    hi: 255,
                })
                .collect(),
        )
    }

    fn zip(&self, rhs: &Num, sign: i128) -> Num {
        let n = self.0.len().max(rhs.0.len());
        let zero = Coef {
            lc: Lc::zero(),
            lo: 0,
            hi: 0,
        };
        Num((0..n)
            .map(|k| {
                let a = self.0.get(k).unwrap_or(&zero);
                let b = rhs.0.get(k).unwrap_or(&zero);
                if sign > 0 {
                    Coef {
                        lc: a.lc.plus(&b.lc),
                        lo: a.lo + b.lo,
                        hi: a.hi + b.hi,
                    }
                } else {
                    Coef {
                        lc: a.lc.minus(&b.lc),
                        lo: a.lo - b.hi,
                        hi: a.hi - b.lo,
                    }
                }
                .check()
            })
            .collect())
    }

    pub fn add(&self, rhs: &Num) -> Num {
        self.zip(rhs, 1)
    }

    pub fn sub(&self, rhs: &Num) -> Num {
        self.zip(rhs, -1)
    }

    /// Multiply by a small public integer.
    pub fn scale(&self, k: i64) -> Num {
        let k = k as i128;
        Num(self
            .0
            .iter()
            .map(|c| {
                let (x, y) = (c.lo * k, c.hi * k);
                Coef {
                    lc: c.lc.scaled(f_int(k)),
                    lo: x.min(y),
                    hi: x.max(y),
                }
                .check()
            })
            .collect())
    }

    /// The coefficient forms, least significant first.
    pub fn limb_forms(&self) -> Vec<Lc> {
        self.0.iter().map(|c| c.lc.clone()).collect()
    }

    fn is_constant(&self) -> bool {
        self.0.iter().all(|c| c.lo == c.hi && is_const(&c.lc))
    }

    /// Largest absolute coefficient bound.
    fn magnitude(&self) -> i128 {
        self.0
            .iter()
            .map(|c| c.lo.abs().max(c.hi.abs()))
            .max()
            .unwrap_or(0)
    }

    /// The product, unreduced. One row per coefficient of the result; no row when either
    /// factor is a public constant.
    pub fn mul(cs: &mut ConstraintSystem, a: &Num, b: &Num) -> Num {
        let (la, lb) = (a.0.len(), b.0.len());
        if la == 0 || lb == 0 {
            return Num::zero();
        }
        let n = la + lb - 1;
        assert!(n <= MAX_COEFS, "product too long");
        assert!(
            a.magnitude()
                .checked_mul(b.magnitude())
                .and_then(|m| m.checked_mul(la.min(lb) as i128))
                .is_some_and(|m| m < COEF_BOUND),
            "product coefficients too wide"
        );
        let interval = |k: usize| {
            let (mut lo, mut hi) = (0i128, 0i128);
            for i in k.saturating_sub(lb - 1)..=k.min(la - 1) {
                let (x, y) = (&a.0[i], &b.0[k - i]);
                let c = [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi];
                lo += c.iter().copied().min().unwrap();
                hi += c.iter().copied().max().unwrap();
            }
            (lo, hi)
        };

        if a.is_constant() || b.is_constant() {
            let (k_side, v_side) = if a.is_constant() { (a, b) } else { (b, a) };
            let (lk, lv) = (k_side.0.len(), v_side.0.len());
            return Num((0..n)
                .map(|k| {
                    let parts: Vec<(F, &Lc)> = (k.saturating_sub(lv - 1)..=k.min(lk - 1))
                        .map(|i| (f_int(k_side.0[i].lo), &v_side.0[k - i].lc))
                        .collect();
                    let (lo, hi) = interval(k);
                    Coef {
                        lc: Lc::combine(&parts),
                        lo,
                        hi,
                    }
                    .check()
                })
                .collect());
        }

        let av: Vec<i128> = a.0.iter().map(|c| int_value(cs, c)).collect();
        let bv: Vec<i128> = b.0.iter().map(|c| int_value(cs, c)).collect();
        let out: Vec<Coef> = (0..n)
            .map(|k| {
                let v: i128 = (k.saturating_sub(lb - 1)..=k.min(la - 1))
                    .map(|i| av[i].wrapping_mul(bv[k - i]))
                    .fold(0i128, i128::wrapping_add);
                let (lo, hi) = interval(k);
                Coef {
                    lc: cs.alloc(f_int_wrapping(v)).into(),
                    lo,
                    hi,
                }
                .check()
            })
            .collect();
        for s in 0..n {
            let point = F::from_u64_reduced(s as u64);
            let mut powers = Vec::with_capacity(n);
            let mut acc = F::ONE;
            for _ in 0..n {
                powers.push(acc);
                acc = acc.const_mul(point);
            }
            let at = |p: &[Coef]| {
                let parts: Vec<(F, &Lc)> = powers
                    .iter()
                    .copied()
                    .zip(p.iter().map(|c| &c.lc))
                    .collect();
                Lc::combine(&parts)
            };
            cs.enforce_mul(at(&a.0), at(&b.0), at(&out));
        }
        Num(out)
    }

    /// `a * a`.
    pub fn square(cs: &mut ConstraintSystem, a: &Num) -> Num {
        Self::mul(cs, a, a)
    }
}

/// Field element of an integer that an inconsistent assignment may have pushed outside
/// the proven interval; the rows then fail, and nothing here may overflow.
fn f_int_wrapping(v: i128) -> F {
    f_int(v % PG)
}

// ============================================================================
// Bit-decomposed witnesses
// ============================================================================

/// A witness in `[0, 2^nbits)` as 8-bit limbs and their bits.
#[derive(Clone)]
pub struct Elem {
    /// Little-endian bits, each Boolean.
    pub bits: Vec<Lc>,
    /// Little-endian limbs; limb `i` holds bits `8i..8i + 8`.
    pub limbs: Vec<Lc>,
}

impl Elem {
    /// The value as an unreduced integer.
    pub fn num(&self) -> Num {
        let nbits = self.bits.len();
        Num(self
            .limbs
            .iter()
            .enumerate()
            .map(|(i, lc)| Coef {
                lc: lc.clone(),
                lo: 0,
                hi: (1i128 << (nbits - 8 * i).min(8)) - 1,
            })
            .collect())
    }

    /// An element over bits the caller has constrained Boolean.
    pub fn from_bits(bits: Vec<Lc>) -> Self {
        let limbs = bits
            .chunks(8)
            .map(|chunk| {
                let parts: Vec<(F, &Lc)> = chunk
                    .iter()
                    .enumerate()
                    .map(|(k, b)| (F::from_u64_reduced(1 << k), b))
                    .collect();
                Lc::combine(&parts)
            })
            .collect();
        Self { bits, limbs }
    }

    /// A public constant of `nbits` bits.
    pub fn constant(value_le: &[u8], nbits: usize) -> Self {
        let bits = (0..nbits)
            .map(|i| {
                Lc::constant(F::from_u64_reduced(
                    ((value_le[i / 8] >> (i % 8)) & 1) as u64,
                ))
            })
            .collect();
        Self::from_bits(bits)
    }

    /// The assigned value, little-endian.
    pub fn value(&self, cs: &ConstraintSystem) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, bit) in self.bits.iter().enumerate() {
            out[i / 8] |= ((cs.eval(bit).to_canonical_u64() & 1) as u8) << (i % 8);
        }
        out
    }
}

/// Allocate `value mod 2^nbits`: one variable per limb, one per bit except the top bit of
/// each limb, which is the linear form that completes the limb. One row per bit.
pub fn alloc_elem(cs: &mut ConstraintSystem, value_le: &[u8], nbits: usize) -> Elem {
    let mut limbs = Vec::with_capacity(nbits.div_ceil(8));
    let mut bits = Vec::with_capacity(nbits);
    for i in 0..nbits.div_ceil(8) {
        let width = (nbits - 8 * i).min(8);
        let byte = value_le.get(i).copied().unwrap_or(0) & (0xffu16 >> (8 - width)) as u8;
        if width == 1 {
            let bit: Lc = cs.alloc(F::from_u64_reduced(byte as u64)).into();
            cs.enforce_boolean(&bit);
            bits.push(bit.clone());
            limbs.push(bit);
            continue;
        }
        let limb: Lc = cs.alloc(F::from_u64_reduced(byte as u64)).into();
        let mut top = limb.clone();
        for k in 0..width - 1 {
            let bit = cs.alloc(F::from_u64_reduced(((byte >> k) & 1) as u64));
            cs.enforce_boolean(&bit.into());
            top = top.minus(&Lc::term(bit, F::from_u64_reduced(1 << k)));
            bits.push(bit.into());
        }
        let top = top.scaled(F::from_u64_reduced(1 << (width - 1)).inv());
        cs.enforce_boolean(&top);
        bits.push(top);
        limbs.push(limb);
    }
    Elem { bits, limbs }
}

/// `value <= k` for Boolean bits (little-endian) and a public constant. One row per
/// one-bit of `k` that is followed by a zero-bit, and one per run of zero-bits.
pub fn enforce_le_const(cs: &mut ConstraintSystem, bits: &[Lc], k_le: &[u8]) {
    let kbit = |i: usize| k_le.get(i / 8).is_some_and(|b| (b >> (i % 8)) & 1 == 1);
    assert!(
        (bits.len()..8 * k_le.len()).all(|i| !kbit(i)),
        "constant wider than the value"
    );
    // `eq`: every one-position of `k` seen so far holds a one. `None` is the constant 1.
    let mut eq: Option<Lc> = None;
    let mut ones: Vec<&Lc> = Vec::new();
    let mut run: Vec<(F, &Lc)> = Vec::new();
    for i in (0..bits.len()).rev() {
        if kbit(i) {
            if !run.is_empty() {
                flush_run(cs, &mut eq, &mut ones, &mut run);
            }
            ones.push(&bits[i]);
        } else {
            run.push((F::ONE, &bits[i]));
        }
    }
    if !run.is_empty() {
        flush_run(cs, &mut eq, &mut ones, &mut run);
    }
}

/// With the prefix equal to `k`'s, every bit of a zero-run must be zero.
fn flush_run(
    cs: &mut ConstraintSystem,
    eq: &mut Option<Lc>,
    ones: &mut Vec<&Lc>,
    run: &mut Vec<(F, &Lc)>,
) {
    for bit in ones.drain(..) {
        *eq = Some(match eq.take() {
            None => bit.clone(),
            Some(e) => cs.mul(&e, bit).into(),
        });
    }
    // A sum of at most 256 Booleans is zero only if each is.
    let sum = Lc::combine(run);
    match eq {
        None => cs.enforce_zero(sum),
        Some(e) => cs.enforce_mul(e.clone(), sum, Lc::zero()),
    }
    run.clear();
}

/// `a != b` as integers, for two limb vectors of the same length with limbs in `[0, 255]`.
/// Five rows for 32 limbs.
