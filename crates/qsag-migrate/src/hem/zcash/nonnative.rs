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
pub fn enforce_limbs_differ(cs: &mut ConstraintSystem, a: &[Lc], b: &[Lc]) {
    assert_eq!(a.len(), b.len());
    // Seven limbs pack into 56 bits: the packed difference is a nonzero field element
    // exactly when the chunks differ.
    let diffs: Vec<Lc> = a
        .chunks(7)
        .zip(b.chunks(7))
        .map(|(x, y)| {
            let parts: Vec<(F, &Lc)> = (0..x.len())
                .flat_map(|i| {
                    let w = F::from_u64_reduced(1 << (8 * i));
                    [(w, &x[i]), (F::ZERO - w, &y[i])]
                })
                .collect();
            Lc::combine(&parts)
        })
        .collect();
    // sum d_c u_c = 1 has a solution exactly when some d_c is nonzero. The prover inverts
    // the first nonzero difference.
    let mut found = 0u64;
    let mut acc = Lc::constant(F::ONE);
    let last = diffs.len() - 1;
    for (c, d) in diffs.iter().enumerate() {
        let dv = cs.eval(d);
        let nonzero = ((dv.to_canonical_u64() | dv.to_canonical_u64().wrapping_neg()) >> 63) & 1;
        let pick = nonzero & (found ^ 1);
        found |= nonzero;
        let u = cs.alloc(dv.inv_or_zero().const_mul(F::from_u64_reduced(pick)));
        if c == last {
            cs.enforce_mul(d.clone(), u.into(), acc.clone());
        } else {
            let m = cs.mul(d, &u.into());
            acc = acc.minus(&m.into());
        }
    }
}

// ============================================================================
// Moduli
// ============================================================================

/// An odd prime `p` with `2^248 < p < 2^255` and the constants `2^(8k) mod p`.
pub struct Field {
    p: [u64; 4],
    p_bytes: [u8; 32],
    /// `fold[k - LIMBS] = 2^(8k) mod p`.
    fold: Vec<[u8; 32]>,
}

struct Folded {
    lc: Vec<Lc>,
    lo: Vec<i128>,
    hi: Vec<i128>,
    value: Vec<i128>,
}

impl Field {
    pub fn new(p_le: &[u8; 32]) -> Self {
        let p: [u64; 4] = core::array::from_fn(|i| {
            u64::from_le_bytes(p_le[8 * i..8 * i + 8].try_into().unwrap())
        });
        // What the rest of this type needs from `p`: `p > 2^248`, so that the doubling
        // chain below starts from a reduced value and a 255-bit representative is below
        // `2^7 p` (the quotients of `enforce_zero` grow by at most seven bits against a
        // 255-bit modulus); `p < 2^255`, so that `2 r` for `r < p` fits four words here and
        // in `wide_divrem`, and every residue has a 255-bit representative; `p` odd, for
        // `enforce_canonical`. For a modulus shorter than 255 bits, `enforce_canonical`
        // also forces the bits above its length to zero.
        assert!(
            p[3] >> 63 == 0 && p[3] >> 56 != 0 && p[0] & 1 == 1,
            "modulus must be odd and between 2^248 and 2^255"
        );
        // r = 2^(8k) mod p by repeated doubling from 2^248.
        let mut r = [0u64, 0, 0, 1 << 56];
        let mut fold = Vec::with_capacity(MAX_COEFS - LIMBS);
        for _ in LIMBS..MAX_COEFS {
            for _ in 0..8 {
                let mut d = [0u64; 4];
                for i in (1..4).rev() {
                    d[i] = (r[i] << 1) | (r[i - 1] >> 63);
                }
                d[0] = r[0] << 1;
                let mut t = [0u64; 4];
                let mut borrow = 0;
                for i in 0..4 {
                    (t[i], borrow) = sbb(d[i], p[i], borrow);
                }
                r = if borrow == 0 { t } else { d };
            }
            let mut bytes = [0u8; 32];
            for i in 0..4 {
                bytes[8 * i..8 * i + 8].copy_from_slice(&r[i].to_le_bytes());
            }
            fold.push(bytes);
        }
        Self {
            p,
            p_bytes: *p_le,
            fold,
        }
    }

    /// The Pallas base field.
    pub fn pallas_base() -> Self {
        Self::new(&super::pallas::BASE_MODULUS_LE)
    }

    /// The Pallas scalar field.
    pub fn pallas_scalar() -> Self {
        Self::new(&super::pallas::SCALAR_MODULUS_LE)
    }

    /// Bit length of every reduced element (and of the longest admitted modulus).
    pub const BITS: usize = 255;

    /// A fresh 255-bit witness.
    pub fn alloc(&self, cs: &mut ConstraintSystem, value_le: &[u8; 32]) -> Elem {
        alloc_elem(cs, value_le, Self::BITS)
    }

    /// Replace the coefficients at positions `>= LIMBS` by multiples of `2^(8k) mod p`.
    fn fold(&self, cs: &ConstraintSystem, x: &Num) -> Folded {
        assert!(x.0.len() <= MAX_COEFS, "integer too long");
        let mut parts: Vec<Vec<(F, &Lc)>> = vec![Vec::new(); LIMBS];
        let mut lo = vec![0i128; LIMBS];
        let mut hi = vec![0i128; LIMBS];
        let mut value = vec![0i128; LIMBS];
        for (k, c) in x.0.iter().enumerate() {
            let v = int_value(cs, c);
            if k < LIMBS {
                parts[k].push((F::ONE, &c.lc));
                lo[k] += c.lo;
                hi[k] += c.hi;
                value[k] = value[k].wrapping_add(v);
            } else {
                for (l, &byte) in self.fold[k - LIMBS].iter().enumerate() {
                    let b = byte as i128;
                    if b != 0 {
                        parts[l].push((F::from_u64_reduced(byte as u64), &c.lc));
                    }
                    lo[l] += b * c.lo;
                    hi[l] += b * c.hi;
                    value[l] = value[l].wrapping_add(b.wrapping_mul(v));
                }
            }
        }
        for l in 0..LIMBS {
            assert!(
                lo[l] > -2 * COEF_BOUND && hi[l] < 2 * COEF_BOUND,
                "folded coefficient interval too wide"
            );
        }
        Folded {
            lc: parts.iter().map(|p| Lc::combine(p)).collect(),
            lo,
            hi,
            value,
        }
    }

    /// The public offset `K` with `X + K p >= 0` for every admitted `X`.
    fn offset(&self, folded: &Folded) -> u64 {
        let mut neg = [0u64; 6];
        for l in 0..LIMBS {
            wide_add_shifted(&mut neg, (-folded.lo[l]).max(0) as u64, l);
        }
        let (q, r) = wide_divrem(&neg, &self.p);
        assert!(q[1..].iter().all(|&w| w == 0) && q[0] < u64::MAX);
        q[0] + u64::from(r != [0; 4])
    }

    /// `X + K p` under the current assignment (non-negative for an honest assignment).
    fn shifted_value(&self, folded: &Folded, k: u64) -> Wide {
        let (mut pos, mut neg) = ([0u64; 6], [0u64; 6]);
        for l in 0..LIMBS {
            let v = folded.value[l];
            let sign = (v >> 127) as u128;
            let mag = ((v as u128) ^ sign).wrapping_sub(sign) as u64;
            let sign = sign as u64;
            wide_add_shifted(&mut pos, mag & !sign, l);
            wide_add_shifted(&mut neg, mag & sign, l);
        }
        wide_sub(&wide_add(&pos, &wide_mul_u64(&self.p, k)), &neg)
    }

    /// The canonical residue of `x` under the current assignment, little-endian.
    pub fn value(&self, cs: &ConstraintSystem, x: &Num) -> [u8; 32] {
        let folded = self.fold(cs, x);
        let k = self.offset(&folded);
        let (_, r) = wide_divrem(&self.shifted_value(&folded, k), &self.p);
        let mut out = [0u8; 32];
        for i in 0..4 {
            out[8 * i..8 * i + 8].copy_from_slice(&r[i].to_le_bytes());
        }
        out
    }

    /// `x = 0 (mod p)`.
    pub fn enforce_zero(&self, cs: &mut ConstraintSystem, x: &Num) {
        let folded = self.fold(cs, x);
        let k = self.offset(&folded);

        // Quotient range: q <= (X_max + K p) / p.
        let kp = wide_mul_u64(&self.p, k);
        let mut top = kp;
        for l in 0..LIMBS {
            wide_add_shifted(&mut top, folded.hi[l].max(0) as u64, l);
        }
        let (q_max, _) = wide_divrem(&top, &self.p);
        let q_bits = wide_bitlen(&q_max).max(1);
        assert!(q_bits <= 120, "quotient too wide");

        let (q_value, _) = wide_divrem(&self.shifted_value(&folded, k), &self.p);
        let q_bytes = wide_bytes(&q_value);
        let q = alloc_elem(cs, &q_bytes, q_bits);
        let q_limbs = q.limbs.len();
        let q_limb_max = |i: usize| (1i128 << (q_bits - 8 * i).min(8)) - 1;

        // e_l = x_l + (K p)_l - (q p)_l.
        let kp_bytes = wide_bytes(&kp);
        let n = LIMBS + q_limbs;
        assert!(kp_bytes[n.min(48)..].iter().all(|&b| b == 0));
        let zero = Lc::zero();
        let mut e_lc = Vec::with_capacity(n);
        let mut e_bound = Vec::with_capacity(n);
        let mut e_value = Vec::with_capacity(n);
        for (l, &kp_byte) in kp_bytes.iter().enumerate().take(n) {
            let kp_l = kp_byte as i128;
            let mut parts: Vec<(F, &Lc)> = vec![(F::ONE, folded.lc.get(l).unwrap_or(&zero))];
            let (mut qp_max, mut qp_value) = (0i128, 0i128);
            // (q p)_l = sum over i + j = l of q_i p_j.
            for (i, (limb, &q_byte)) in q.limbs.iter().zip(&q_bytes).enumerate() {
                if i > l || l - i >= LIMBS {
                    continue;
                }
                let pj = self.p_bytes[l - i] as i128;
                if pj != 0 {
                    parts.push((f_int(-pj), limb));
                }
                qp_max += pj * q_limb_max(i);
                qp_value += pj * q_byte as i128;
            }
            e_lc.push(Lc::combine(&parts).plus_const(f_int(kp_l)));
            let (lo, hi) = (
                folded.lo.get(l).copied().unwrap_or(0),
                folded.hi.get(l).copied().unwrap_or(0),
            );
            e_bound.push((lo + kp_l - qp_max, hi + kp_l));
            e_value.push(
                folded
                    .value
                    .get(l)
                    .copied()
                    .unwrap_or(0)
                    .wrapping_add(kp_l - qp_value),
            );
        }

        // Group size with the fewest carry rows among those whose equations cannot wrap.
        let (g, plan) = (1..=7)
            .filter_map(|g| plan_groups(&e_bound, g).map(|p| (g, p)))
            .min_by_key(|(_, p)| p.iter().map(|&(_, nb)| nb as usize + 1).sum::<usize>())
            .expect("coefficient intervals too wide for any group size");
        let base = 1i128 << (8 * g);
        let mut carry_lc = Lc::zero();
        let mut carry_value = 0i128;
        for (gi, &(c_lo, nb)) in plan.iter().enumerate() {
            let mut parts: Vec<(F, &Lc)> = vec![(F::ONE, &carry_lc)];
            let mut v = carry_value;
            for j in 0..g {
                if let Some(lc) = e_lc.get(gi * g + j) {
                    parts.push((F::from_u64_reduced(1 << (8 * j)), lc));
                    v = v.wrapping_add(e_value[gi * g + j].wrapping_mul(1 << (8 * j)));
                }
            }
            let group = Lc::combine(&parts);
            if gi + 1 == plan.len() {
                cs.enforce_zero(group);
                break;
            }
            let c = v >> (8 * g);
            let u = c.wrapping_sub(c_lo) as u128;
            let mut next = Lc::constant(f_int(c_lo));
            for i in 0..nb {
                let bit = cs.alloc(F::from_u64_reduced(((u >> i) & 1) as u64));
                cs.enforce_boolean(&bit.into());
                next = next.plus(&Lc::term(bit, F::from_u64_reduced(1 << i)));
            }
            cs.enforce_zero(group.minus(&next.scaled(f_int(base))));
            carry_lc = next;
            carry_value = c;
        }
    }

    /// `a = b (mod p)`.
    pub fn enforce_equal(&self, cs: &mut ConstraintSystem, a: &Num, b: &Num) {
        self.enforce_zero(cs, &a.sub(b));
    }

    /// A fresh 255-bit element congruent to `x`. It need not be the canonical residue;
    /// see [`Self::enforce_canonical`].
    pub fn reduce(&self, cs: &mut ConstraintSystem, x: &Num) -> Elem {
        let value = self.value(cs, x);
        let out = self.alloc(cs, &value);
        self.enforce_zero(cs, &x.sub(&out.num()));
        out
    }

    /// `e <= p - 1`: `e` is the unique representative of its residue.
    pub fn enforce_canonical(&self, cs: &mut ConstraintSystem, e: &Elem) {
        let mut pm1 = self.p_bytes;
        pm1[0] -= 1; // p is odd
        enforce_le_const(cs, &e.bits, &pm1);
    }

    /// A fresh canonical element congruent to `x`.
    pub fn reduce_canonical(&self, cs: &mut ConstraintSystem, x: &Num) -> Elem {
        let out = self.reduce(cs, x);
        self.enforce_canonical(cs, &out);
        out
    }
}

/// For group size `g`, the lower bound and bit width of each carry (the last entry is a
/// placeholder for the final group, which has no carry). `None` if some group equation
/// could wrap around the Goldilocks prime.
fn plan_groups(e: &[(i128, i128)], g: usize) -> Option<Vec<(i128, u32)>> {
    let base = 1i128 << (8 * g);
    let groups = e.len().div_ceil(g);
    let (mut in_lo, mut in_hi) = (0i128, 0i128);
    let mut out = Vec::with_capacity(groups);
    for gi in 0..groups {
        let (mut v_lo, mut v_hi) = (in_lo, in_hi);
        for j in 0..g {
            if let Some(&(lo, hi)) = e.get(gi * g + j) {
                v_lo += lo << (8 * j);
                v_hi += hi << (8 * j);
            }
        }
        if gi + 1 == groups {
            if v_lo <= -PG || v_hi >= PG {
                return None;
            }
            out.push((0, 0));
            break;
        }
        // An honest group value is a multiple of the base inside [v_lo, v_hi].
        let c_lo = -((-v_lo).div_euclid(base));
        let c_hi = v_hi.div_euclid(base).max(c_lo);
        let nb = 128 - ((c_hi - c_lo) as u128).leading_zeros();
        let c_max = c_lo + (1i128 << nb) - 1;
        if v_hi - c_lo * base >= PG || v_lo - c_max * base <= -PG {
            return None;
        }
        out.push((c_lo, nb));
        (in_lo, in_hi) = (c_lo, c_max);
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::super::pallas::{BASE_MODULUS_LE, Fp, Fq};
    use super::*;

    fn sample(i: u64) -> Fp {
        // Dense pseudo-random elements.
        let mut x = Fp::from_u64(0x9e37_79b9_7f4a_7c15 ^ i);
        for _ in 0..6 {
            x = x.square() + Fp::from_u64(i + 3);
        }
        x
    }

    #[test]
    fn products_and_congruences_match_native() {
        let field = Field::pallas_base();
        let mut cs = ConstraintSystem::new();
        let (a, b, c) = (sample(1), sample(2), sample(3));
        let (ea, eb, ec) = (
            field.alloc(&mut cs, &a.to_bytes()),
            field.alloc(&mut cs, &b.to_bytes()),
            field.alloc(&mut cs, &c.to_bytes()),
        );
        let rows0 = cs.num_rows();
        let ab = Num::mul(&mut cs, &ea.num(), &eb.num());
        assert_eq!(cs.num_rows() - rows0, 63);
        assert_eq!(field.value(&cs, &ab), (a * b).to_bytes());
        // (a b - c)(a + 3) + 7 b, a degree-3 expression with a negative part.
        let t = Num::mul(&mut cs, &ab.sub(&ec.num()), &ea.num().add(&Num::small(3)));
        let expr = t.add(&eb.num().scale(7));
        let want = (a * b - c) * (a + Fp::from_u64(3)) + b * Fp::from_u64(7);
        assert_eq!(field.value(&cs, &expr), want.to_bytes());
        let rows1 = cs.num_rows();
        let r = field.reduce_canonical(&mut cs, &expr);
        std::println!(
            "reduce of a degree-3 expression: {} rows",
            cs.num_rows() - rows1
        );
        assert_eq!(r.value(&cs), want.to_bytes());
        // Constant factors cost no rows.
        let rows2 = cs.num_rows();
        let k = Num::constant(&sample(9).to_bytes());
        let ka = Num::mul(&mut cs, &k, &ea.num());
        assert_eq!(cs.num_rows(), rows2);
        assert_eq!(field.value(&cs, &ka), (sample(9) * a).to_bytes());
        let rows3 = cs.num_rows();
        field.enforce_equal(&mut cs, &ka, &Num::constant(&(sample(9) * a).to_bytes()));
        std::println!(
            "congruence of a constant product: {} rows",
            cs.num_rows() - rows3
        );
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
    }

    #[test]
    fn a_false_congruence_is_unsatisfiable() {
        let field = Field::pallas_base();
        for delta in [1u64, 2, 1 << 40] {
            let mut cs = ConstraintSystem::new();
            let (a, b) = (sample(4), sample(5));
            let (ea, eb) = (
                field.alloc(&mut cs, &a.to_bytes()),
                field.alloc(&mut cs, &b.to_bytes()),
            );
            let wrong = field.alloc(&mut cs, &(a * b + Fp::from_u64(delta)).to_bytes());
            let ab = Num::mul(&mut cs, &ea.num(), &eb.num());
            field.enforce_equal(&mut cs, &ab, &wrong.num());
            let (shape, z) = cs.finish();
            assert!(!shape.is_satisfied(&z), "delta {delta}");
        }
    }

    #[test]
    fn scalar_field_wide_reduction() {
        // ToScalar: a 512-bit little-endian integer reduced modulo q.
        let field = Field::pallas_scalar();
        let bytes: [u8; 64] = core::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(11));
        let mut cs = ConstraintSystem::new();
        let bits = crate::hem::hash::alloc_bits(&mut cs, &bytes);
        let rows0 = cs.num_rows();
        let r = field.reduce_canonical(&mut cs, &Num::from_bits(&bits));
        std::println!("wide reduction: {} rows", cs.num_rows() - rows0);
        assert_eq!(r.value(&cs), Fq::from_bytes_wide(&bytes).to_bytes());
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
    }

    #[test]
    fn jubjub_scalar_order_wide_reduction() {
        // ToScalar^Sapling: a 512-bit integer modulo the 252-bit order r_J.
        use super::super::sapling::{SCALAR_MODULUS_LE, to_scalar};
        let field = Field::new(&SCALAR_MODULUS_LE);
        let mut all_ones = [0xffu8; 64];
        all_ones[63] = 0x7f;
        let mut order = [0u8; 64];
        order[..32].copy_from_slice(&SCALAR_MODULUS_LE);
        for bytes in [
            core::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(11)),
            [0xff; 64],
            all_ones,
            order,
            [0u8; 64],
        ] {
            let mut cs = ConstraintSystem::new();
            let bits = crate::hem::hash::alloc_bits(&mut cs, &bytes);
            let rows0 = cs.num_rows();
            let r = field.reduce_canonical(&mut cs, &Num::from_bits(&bits));
            std::println!("wide reduction modulo r_J: {} rows", cs.num_rows() - rows0);
            assert_eq!(r.value(&cs), to_scalar(&bytes));
            // A canonical residue of a 252-bit modulus has no bit above 251.
            assert!(r.value(&cs)[31] < 0x10);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
        }
    }

    #[test]
    fn jubjub_scalar_order_false_congruence_is_unsatisfiable() {
        use super::super::sapling::{SCALAR_MODULUS_LE, to_scalar};
        let field = Field::new(&SCALAR_MODULUS_LE);
        let bytes: [u8; 64] = core::array::from_fn(|i| (i as u8).wrapping_mul(91).wrapping_add(3));
        let good = to_scalar(&bytes);
        // The residue plus one, plus 2^200, and the non-canonical representative
        // residue + r_J (congruent, so only the canonical check can reject it).
        let mut plus_one = good;
        plus_one[0] ^= 1;
        let mut plus_high = good;
        plus_high[25] ^= 1;
        let mut plus_order = [0u8; 32];
        let mut carry = 0u16;
        for i in 0..32 {
            let t = good[i] as u16 + SCALAR_MODULUS_LE[i] as u16 + carry;
            plus_order[i] = t as u8;
            carry = t >> 8;
        }
        assert_eq!(carry, 0);
        for (claim, canonical, ok) in [
            (good, true, true),
            (plus_one, false, false),
            (plus_high, false, false),
            (plus_order, false, true),
            (plus_order, true, false),
        ] {
            let mut cs = ConstraintSystem::new();
            let bits = crate::hem::hash::alloc_bits(&mut cs, &bytes);
            let e = field.alloc(&mut cs, &claim);
            field.enforce_equal(&mut cs, &Num::from_bits(&bits), &e.num());
            if canonical {
                field.enforce_canonical(&mut cs, &e);
            }
            let (shape, z) = cs.finish();
            assert_eq!(
                shape.is_satisfied(&z),
                ok,
                "{claim:?} canonical={canonical}"
            );
        }
    }

    #[test]
    #[should_panic(expected = "modulus must be odd")]
    fn a_modulus_below_2_248_is_refused() {
        let mut p = [0u8; 32];
        p[0] = 1;
        p[30] = 0xff;
        let _ = Field::new(&p);
    }

    #[test]
    fn canonical_check_accepts_exactly_the_residues() {
        let field = Field::pallas_base();
        let mut pm1 = BASE_MODULUS_LE;
        pm1[0] -= 1;
        let mut p_plus = BASE_MODULUS_LE;
        p_plus[0] += 4;
        let mut high = [0u8; 32];
        high[31] = 0x7f;
        let mut mid = BASE_MODULUS_LE;
        mid[20] = 1; // p + 2^160
        for (value, ok) in [
            ([0u8; 32], true),
            (pm1, true),
            (sample(7).to_bytes(), true),
            (BASE_MODULUS_LE, false),
            (p_plus, false),
            (mid, false),
            (high, false),
        ] {
            let mut cs = ConstraintSystem::new();
            let e = field.alloc(&mut cs, &value);
            let rows0 = cs.num_rows();
            field.enforce_canonical(&mut cs, &e);
            assert!(cs.num_rows() - rows0 < 120);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok, "{value:?}");
        }
    }

    #[test]
    fn limb_inequality() {
        let field = Field::pallas_base();
        let a = sample(11).to_bytes();
        let mut near = a;
        near[17] ^= 0x10;
        for (b, ok) in [(sample(12).to_bytes(), true), (near, true), (a, false)] {
            let mut cs = ConstraintSystem::new();
            let ea = field.alloc(&mut cs, &a);
            let eb = field.alloc(&mut cs, &b);
            let rows0 = cs.num_rows();
            enforce_limbs_differ(&mut cs, &ea.limbs, &eb.limbs);
            assert_eq!(cs.num_rows() - rows0, 5);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok);
        }
    }

    #[test]
    fn a_quotient_cannot_be_forged() {
        // Changing any single assigned variable of a reduction breaks a row.
        let field = Field::pallas_base();
        let mut cs = ConstraintSystem::new();
        let (a, b) = (sample(21), sample(22));
        let (ea, eb) = (
            field.alloc(&mut cs, &a.to_bytes()),
            field.alloc(&mut cs, &b.to_bytes()),
        );
        let first = 1 + 2 * 255; // after the variables of the two operands
        let ab = Num::mul(&mut cs, &ea.num(), &eb.num());
        let _ = field.reduce(&mut cs, &ab);
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        let last = z.len() - qsag_agg::zk_hem::relation::MASK_ROWS;
        for idx in (first..last).step_by(7) {
            let mut bad = z.clone();
            bad[idx] += F::ONE;
            assert!(!shape.is_satisfied(&bad), "variable {idx}");
        }
    }
}
