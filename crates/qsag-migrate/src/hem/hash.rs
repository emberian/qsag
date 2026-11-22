//! Hash gadgets over the zk-Hem constraint system: SHA-256, SHA-512, HMAC, HKDF-SHA256,
//! RIPEMD-160 and Keccak-256.
//!
//! # Conventions
//!
//! * A **bit** is an [`Lc`] whose value is `0` or `1`. Every gadget here requires its input
//!   bits to be Boolean (constrained by the caller, for instance with [`alloc_bits`]) and
//!   returns bits that are Boolean as a consequence of its rows.
//! * A **byte string** is a `&[Lc]` of `8 * len` bits; byte `i` occupies bits `8i..8i + 8`,
//!   least significant bit first. Messages, keys and digests all use this layout.
//! * A [`Word`] is a fixed-width integer, least significant bit first.
//!
//! # Row costs
//!
//! Linear maps of bits (rotations, shifts, complement, XOR with a constant) are free. Every
//! function of three bits costs one row (see [`OneRow`]): XOR3, Maj, Ch, the Keccak `chi`
//! step and both RIPEMD-160 OR-XOR functions. A modular sum of `n` words costs one row per
//! result bit plus `ceil(log2 n)` carry rows per 32-bit limb. Operations on constant bits
//! fold away, so padding and initial values add no rows. The row structure depends only on
//! which inputs are constants, never on assigned values.

use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Def, Lc, Source};

type F = Goldilocks;

#[inline]
fn fu(v: u64) -> F {
    F::from_u64_reduced(v)
}

#[inline]
fn fi(v: i64) -> F {
    let m = fu(v.unsigned_abs());
    if v < 0 { F::ZERO - m } else { m }
}

#[inline]
fn one() -> Lc {
    Lc::constant(F::ONE)
}

/// The value of a linear form with no variable terms.
fn const_of(lc: &Lc) -> Option<u64> {
    match lc.terms() {
        [] => Some(0),
        [(0, c)] => Some(c.to_canonical_u64()),
        _ => None,
    }
}

#[inline]
fn bit_value(cs: &ConstraintSystem, bit: &Lc) -> u64 {
    cs.eval(bit).to_canonical_u64() & 1
}

// ============================================================================
// Byte strings
// ============================================================================

/// Constant bits of `bytes`.
pub fn const_bits(bytes: &[u8]) -> Vec<Lc> {
    bytes
        .iter()
        .flat_map(|&b| (0..8).map(move |i| Lc::constant(fu(u64::from(b >> i) & 1))))
        .collect()
}

/// Fresh Boolean-constrained bits holding `bytes` (one row per bit).
pub fn alloc_bits(cs: &mut ConstraintSystem, bytes: &[u8]) -> Vec<Lc> {
    let mut out = Vec::with_capacity(8 * bytes.len());
    let source = cs.source(|| Source::Input {
        bits: 8 * bytes.len() as u32,
    });
    for (at, &b) in bytes.iter().enumerate() {
        for i in 0..8 {
            let bit: Lc = cs
                .alloc_defined(fu(u64::from(b >> i) & 1), || Def::Bits {
                    source,
                    lo: (8 * at + i) as u32,
                    width: 1,
                })
                .into();
            cs.enforce_boolean(&bit);
            out.push(bit);
        }
    }
    out
}

/// Assigned bytes of a byte string.
pub fn bits_to_bytes(cs: &ConstraintSystem, bits: &[Lc]) -> Vec<u8> {
    assert!(bits.len() % 8 == 0, "byte strings hold whole bytes");
    bits.chunks(8)
        .map(|byte| {
            byte.iter()
                .enumerate()
                .fold(0u8, |acc, (i, bit)| acc | ((bit_value(cs, bit) as u8) << i))
        })
        .collect()
}

/// `sum_i 2^i bits[i]`, for at most 63 bits (the value then stays below the field modulus).
pub fn pack_bits(bits: &[Lc]) -> Lc {
    assert!(bits.len() < 64, "packed value must stay below the modulus");
    let parts: Vec<(F, &Lc)> = bits
        .iter()
        .enumerate()
        .map(|(i, bit)| (fu(1u64 << i), bit))
        .collect();
    Lc::combine(&parts)
}

// ============================================================================
// Bit gadgets
// ============================================================================

/// `1 - a`.
pub fn not(a: &Lc) -> Lc {
    one().minus(a)
}

/// Product of two linear forms; no row when either is a constant.
fn mul_fold(cs: &mut ConstraintSystem, a: &Lc, b: &Lc) -> Lc {
    if let Some(c) = const_of(a) {
        b.scaled(fu(c))
    } else if let Some(c) = const_of(b) {
        a.scaled(fu(c))
    } else {
        cs.mul(a, b).into()
    }
}

/// `a AND b`: at most one row.
pub fn and(cs: &mut ConstraintSystem, a: &Lc, b: &Lc) -> Lc {
    mul_fold(cs, a, b)
}

/// `a XOR b`: at most one row.
pub fn xor2(cs: &mut ConstraintSystem, a: &Lc, b: &Lc) -> Lc {
    let ab = mul_fold(cs, a, b);
    a.plus(b).minus(&ab.scaled(F::TWO))
}

/// `if bit { on_one } else { on_zero }` for a Boolean `bit`: at most one row, none when
/// `bit` or the difference of the branches is a constant.
pub fn select(cs: &mut ConstraintSystem, bit: &Lc, on_one: &Lc, on_zero: &Lc) -> Lc {
    on_zero.plus(&mul_fold(cs, bit, &on_one.minus(on_zero)))
}

/// A function `f` of three bits as the single row
/// `(pk * p + a(x, y, z)) * b(x, y, z) = c(x, y, z)` over a fresh variable `p`, with `a`,
/// `b`, `c` affine (coefficients of `1, x, y, z`).
///
/// `b` is a nonzero integer of magnitude at most 7 at each of the eight Boolean points, so
/// the row has the unique solution `p = (c / b - a) / pk`, and the tables are chosen so that
/// this is `f(x, y, z)`. `p` is therefore Boolean without a row of its own.
/// `one_row_tables_define_their_functions` checks both facts for every table.
struct OneRow {
    pk: i64,
    a: [i64; 4],
    b: [i64; 4],
    c: [i64; 4],
    f: fn(u64, u64, u64) -> u64,
}

const XOR3: OneRow = OneRow {
    pk: 4,
    a: [1, -2, -2, -2],
    b: [-3, 2, 2, 2],
    c: [-3, 0, 0, 0],
    f: |x, y, z| x ^ y ^ z,
};

const MAJ: OneRow = OneRow {
    pk: 8,
    a: [-1, -2, -2, -2],
    b: [-3, 2, 2, 2],
    c: [3, 0, 0, 0],
    f: |x, y, z| (x & y) | (x & z) | (y & z),
};

/// `x XOR (NOT y AND z)`.
const CHI: OneRow = OneRow {
    pk: 8,
    a: [-3, -10, 2, -2],
    b: [-1, -2, -2, 2],
    c: [3, 12, 0, 0],
    f: |x, y, z| x ^ ((1 ^ y) & z),
};

/// `(x OR NOT y) XOR z`.
const ORN_XOR: OneRow = OneRow {
    pk: 8,
    a: [-11, -2, 2, 10],
    b: [-1, -2, 2, -2],
    c: [3, 12, -12, 0],
    f: |x, y, z| (x | (1 ^ y)) ^ z,
};

fn affine(co: &[i64; 4], x: &Lc, y: &Lc, z: &Lc) -> Lc {
    Lc::combine(&[(fi(co[1]), x), (fi(co[2]), y), (fi(co[3]), z)]).plus_const(fi(co[0]))
}

fn one_row(cs: &mut ConstraintSystem, g: &OneRow, x: &Lc, y: &Lc, z: &Lc) -> Lc {
    let value = (g.f)(bit_value(cs, x), bit_value(cs, y), bit_value(cs, z)) & 1;
    let p = cs.alloc_defined(fu(value), || Def::Ratio {
        num: affine(&g.c, x, y, z),
        den: affine(&g.b, x, y, z),
        minus: affine(&g.a, x, y, z),
        scale: fi(g.pk).inv(),
    });
    cs.enforce_mul(
        affine(&g.a, x, y, z).plus(&Lc::term(p, fi(g.pk))),
        affine(&g.b, x, y, z),
        affine(&g.c, x, y, z),
    );
    p.into()
}

fn any_const(bits: [&Lc; 3]) -> bool {
    bits.iter().any(|b| const_of(b).is_some())
}

/// `a XOR b XOR c`: at most one row.
pub fn xor3(cs: &mut ConstraintSystem, a: &Lc, b: &Lc, c: &Lc) -> Lc {
    if any_const([a, b, c]) {
        let ab = xor2(cs, a, b);
        xor2(cs, &ab, c)
    } else {
        one_row(cs, &XOR3, a, b, c)
    }
}

/// XOR of any number of bits: `ceil((v - 1) / 2)` rows for `v` non-constant bits.
pub fn xor_many(cs: &mut ConstraintSystem, bits: &[Lc]) -> Lc {
    let mut flip = 0u64;
    let mut vars: Vec<&Lc> = Vec::with_capacity(bits.len());
    for bit in bits {
        match const_of(bit) {
            Some(c) => flip ^= c & 1,
            None => vars.push(bit),
        }
    }
    let Some((&first, rest)) = vars.split_first() else {
        return Lc::constant(fu(flip));
    };
    let mut acc = first.clone();
    for pair in rest.chunks(2) {
        acc = match pair {
            [x, y] => one_row(cs, &XOR3, &acc, x, y),
            [x] => xor2(cs, &acc, x),
            _ => unreachable!(),
        };
    }
    if flip == 1 { not(&acc) } else { acc }
}

/// Majority of three bits: at most one row.
pub fn maj(cs: &mut ConstraintSystem, a: &Lc, b: &Lc, c: &Lc) -> Lc {
    if any_const([a, b, c]) {
        // `a (b XOR c) + b c`; a constant among the three leaves one product.
        let bc = mul_fold(cs, b, c);
        let b_xor_c = b.plus(c).minus(&bc.scaled(F::TWO));
        mul_fold(cs, a, &b_xor_c).plus(&bc)
    } else {
        one_row(cs, &MAJ, a, b, c)
    }
}

/// `if e { f } else { g }`: at most one row.
pub fn ch(cs: &mut ConstraintSystem, e: &Lc, f: &Lc, g: &Lc) -> Lc {
    g.plus(&mul_fold(cs, e, &f.minus(g)))
}

/// `a XOR (NOT b AND c)`, the Keccak `chi` step: at most one row.
pub fn chi(cs: &mut ConstraintSystem, a: &Lc, b: &Lc, c: &Lc) -> Lc {
    if any_const([a, b, c]) {
        let t = mul_fold(cs, &not(b), c);
        xor2(cs, a, &t)
    } else {
        one_row(cs, &CHI, a, b, c)
    }
}

/// `(x OR NOT y) XOR z`, the RIPEMD-160 round-3 and round-5 function: at most one row.
pub fn orn_xor(cs: &mut ConstraintSystem, x: &Lc, y: &Lc, z: &Lc) -> Lc {
    if any_const([x, y, z]) {
        let t = not(&mul_fold(cs, &not(x), y));
        xor2(cs, &t, z)
    } else {
        one_row(cs, &ORN_XOR, x, y, z)
    }
}

// ============================================================================
// Words
// ============================================================================

/// Fixed-width unsigned integer as bits, least significant first.
#[derive(Clone, Debug)]
pub struct Word {
    bits: Vec<Lc>,
}

impl Word {
    /// Word over the given bits (least significant first), which must be Boolean.
    pub fn from_bits(bits: Vec<Lc>) -> Self {
        assert!((1..=64).contains(&bits.len()), "word width is 1..=64");
        Self { bits }
    }

    /// The low `width` bits of `value` as constants.
    pub fn constant(value: u64, width: usize) -> Self {
        Self::from_bits(
            (0..width)
                .map(|i| Lc::constant(fu((value >> i) & 1)))
                .collect(),
        )
    }

    /// Fresh Boolean-constrained word holding the low `width` bits of `value`.
    pub fn alloc(cs: &mut ConstraintSystem, value: u64, width: usize) -> Self {
        let source = cs.source(|| Source::Input { bits: width as u32 });
        Self::from_bits(
            (0..width)
                .map(|i| {
                    let bit: Lc = cs
                        .alloc_defined(fu((value >> i) & 1), || Def::Bits {
                            source,
                            lo: i as u32,
                            width: 1,
                        })
                        .into();
                    cs.enforce_boolean(&bit);
                    bit
                })
                .collect(),
        )
    }

    #[inline]
    pub fn width(&self) -> usize {
        self.bits.len()
    }

    #[inline]
    pub fn bits(&self) -> &[Lc] {
        &self.bits
    }

    #[inline]
    pub fn into_bits(self) -> Vec<Lc> {
        self.bits
    }

    /// Assigned value.
    pub fn value(&self, cs: &ConstraintSystem) -> u64 {
        self.bits
            .iter()
            .enumerate()
            .fold(0, |acc, (i, bit)| acc | (bit_value(cs, bit) << i))
    }

    fn const_value(&self) -> Option<u64> {
        self.bits
            .iter()
            .enumerate()
            .try_fold(0u64, |acc, (i, bit)| {
                Some(acc | ((const_of(bit)? & 1) << i))
            })
    }

    pub fn rotr(&self, n: usize) -> Self {
        let w = self.width();
        Self::from_bits((0..w).map(|i| self.bits[(i + n) % w].clone()).collect())
    }

    pub fn rotl(&self, n: usize) -> Self {
        let w = self.width();
        self.rotr(w - n % w)
    }

    /// Logical right shift.
    pub fn shr(&self, n: usize) -> Self {
        let w = self.width();
        Self::from_bits(
            (0..w)
                .map(|i| self.bits.get(i + n).cloned().unwrap_or_else(Lc::zero))
                .collect(),
        )
    }

    /// XOR with a constant.
    pub fn xor_const(&self, k: u64) -> Self {
        Self::from_bits(
            self.bits
                .iter()
                .enumerate()
                .map(|(i, bit)| {
                    if (k >> i) & 1 == 1 {
                        not(bit)
                    } else {
                        bit.clone()
                    }
                })
                .collect(),
        )
    }
}

fn bitwise3(
    cs: &mut ConstraintSystem,
    x: &Word,
    y: &Word,
    z: &Word,
    f: fn(&mut ConstraintSystem, &Lc, &Lc, &Lc) -> Lc,
) -> Word {
    Word::from_bits(
        (0..x.width())
            .map(|i| f(cs, &x.bits[i], &y.bits[i], &z.bits[i]))
            .collect(),
    )
}

/// `(sum plus - sum minus) mod 2^width` over words of one width.
///
/// Constant words are summed natively. The rest is added limb by limb (limbs of at most 32
/// bits, so no sum approaches the modulus): each limb's sum, offset by `2^limb` per
/// subtracted word to keep it non-negative, equals `r + 2^limb * carry` with `r` fresh
/// Boolean result bits and `carry` below a power of two covering its largest honest value.
/// The top carry bit is the linear form the equation leaves and is constrained Boolean
/// directly, so the limb costs `limb + carry_bits` rows and the equation needs no row.
pub fn add_mod(cs: &mut ConstraintSystem, plus: &[&Word], minus: &[&Word]) -> Word {
    let width = plus
        .first()
        .or(minus.first())
        .expect("a sum has at least one word")
        .width();
    assert!(
        plus.iter().chain(minus).all(|x| x.width() == width),
        "words of one sum share a width"
    );
    let mask = u64::MAX >> (64 - width);

    let mut k = 0u64;
    let mut pos: Vec<&Word> = Vec::with_capacity(plus.len());
    let mut neg: Vec<&Word> = Vec::with_capacity(minus.len());
    for &x in plus {
        match x.const_value() {
            Some(c) => k = k.wrapping_add(c),
            None => pos.push(x),
        }
    }
    for &x in minus {
        match x.const_value() {
            Some(c) => k = k.wrapping_sub(c),
            None => neg.push(x),
        }
    }
    k &= mask;
    if neg.is_empty() {
        match pos.as_slice() {
            [] => return Word::constant(k, width),
            [x] if k == 0 => return (*x).clone(),
            _ => {}
        }
    }
    assert!(pos.len() + neg.len() < 1 << 16, "too many addends");

    let n_neg = neg.len() as u64;
    let minus_one = F::ZERO - F::ONE;
    let mut out: Vec<Lc> = Vec::with_capacity(width);
    // Carry into the current limb, already reduced by `n_neg`'s offset below, and its
    // largest honest value.
    let mut carry: Option<(Lc, u64)> = None;
    let mut lo = 0;
    while lo < width {
        let hi = (lo + 32).min(width);
        let limb = hi - lo;
        let limb_mask = (1u64 << limb) - 1;
        // A subtracted limb is at most `2^limb - 1`; the borrow of a lower limb is repaid
        // by the `- n_neg` here, which the offset `n_neg * 2^limb` always covers.
        let offset = ((k >> lo) & limb_mask) + (n_neg << limb) - if lo == 0 { 0 } else { n_neg };

        let packed_pos: Vec<Lc> = pos.iter().map(|x| pack_bits(&x.bits[lo..hi])).collect();
        let packed_neg: Vec<Lc> = neg.iter().map(|x| pack_bits(&x.bits[lo..hi])).collect();
        let mut parts: Vec<(F, &Lc)> = Vec::with_capacity(pos.len() + neg.len() + 1);
        parts.extend(packed_pos.iter().map(|lc| (F::ONE, lc)));
        parts.extend(packed_neg.iter().map(|lc| (minus_one, lc)));
        let mut max = pos.len() as u64 * limb_mask + offset;
        if let Some((lc, carry_max)) = &carry {
            parts.push((F::ONE, lc));
            max += carry_max;
        }
        let sum = Lc::combine(&parts).plus_const(fu(offset));
        let total = cs.eval(&sum).to_canonical_u64();
        let source = cs.source(|| Source::Form {
            lc: sum.clone(),
            bits: (64 - max.leading_zeros()).max(limb as u32),
        });

        let result: Vec<Lc> = (0..limb)
            .map(|i| {
                let bit: Lc = cs
                    .alloc_defined(fu((total >> i) & 1), || Def::Bits {
                        source,
                        lo: i as u32,
                        width: 1,
                    })
                    .into();
                cs.enforce_boolean(&bit);
                bit
            })
            .collect();
        let rest = sum.minus(&pack_bits(&result));
        out.extend(result);

        let carry_max = max >> limb;
        let carry_bits = (64 - carry_max.leading_zeros()) as usize;
        if carry_bits == 0 {
            cs.enforce_zero(rest);
            carry = None;
        } else {
            let low: Vec<Lc> = (0..carry_bits - 1)
                .map(|j| {
                    let bit: Lc = cs
                        .alloc_defined(fu((total >> (limb + j)) & 1), || Def::Bits {
                            source,
                            lo: (limb + j) as u32,
                            width: 1,
                        })
                        .into();
                    cs.enforce_boolean(&bit);
                    bit
                })
                .collect();
            let top = rest
                .minus(&pack_bits(&low).scaled(fu(1u64 << limb)))
                .scaled(fu(1u64 << (limb + carry_bits - 1)).inv());
            cs.enforce_boolean(&top);
            carry = Some((rest.scaled(fu(1u64 << limb).inv()), carry_max));
        }
        lo = hi;
    }
    Word::from_bits(out)
}

/// `(a + b) mod 2^len` for two little-endian integers of the same length, in 32-bit limbs:
/// one row per result bit and one carry row per limb.
pub fn add_wide(cs: &mut ConstraintSystem, a: &[Lc], b: &[Lc]) -> Vec<Lc> {
    assert_eq!(a.len(), b.len());
    let mut out = Vec::with_capacity(a.len());
    let mut carry = Lc::zero();
    for (x, y) in a.chunks(32).zip(b.chunks(32)) {
        let limb = x.len();
        let sum = pack_bits(x).plus(&pack_bits(y)).plus(&carry);
        let total = cs.eval(&sum).to_canonical_u64();
        let source = cs.source(|| Source::Form {
            lc: sum.clone(),
            bits: limb as u32 + 1,
        });
        let result: Vec<Lc> = (0..limb)
            .map(|i| {
                let bit: Lc = cs
                    .alloc_defined(fu((total >> i) & 1), || Def::Bits {
                        source,
                        lo: i as u32,
                        width: 1,
                    })
                    .into();
                cs.enforce_boolean(&bit);
                bit
            })
            .collect();
        // Two limbs and a carry bit sum to less than `2^(limb + 1)`, so the carry is a bit.
        carry = sum
            .minus(&pack_bits(&result))
            .scaled(fu(1u64 << limb).inv());
        cs.enforce_boolean(&carry);
        out.extend(result);
    }
    out
}

/// A byte string as words of `wbytes` big-endian bytes each.
pub fn be_words(bits: &[Lc], wbytes: usize) -> Vec<Word> {
    bits.chunks(8 * wbytes)
        .map(|chunk| {
            Word::from_bits(
                (0..8 * wbytes)
                    .map(|k| chunk[8 * (wbytes - 1 - k / 8) + k % 8].clone())
                    .collect(),
            )
        })
        .collect()
}

/// Inverse of [`be_words`]: the byte string of big-endian words.
pub fn be_bits(words: &[Word]) -> Vec<Lc> {
    let mut out = Vec::new();
    for word in words {
        for byte in word.bits.chunks(8).rev() {
            out.extend_from_slice(byte);
        }
    }
    out
}

/// `message || first || 0.. || length`, a whole number of `block`-byte blocks.
fn md_pad(message: &[Lc], block: usize, first: u8, length: &[u8]) -> Vec<Lc> {
    assert!(message.len() % 8 == 0, "messages hold whole bytes");
    let n = message.len() / 8;
    let total = (n + 1 + length.len()).div_ceil(block) * block;
    let mut out = Vec::with_capacity(8 * total);
    out.extend_from_slice(message);
    out.extend(const_bits(&[first]));
    out.resize(8 * (total - length.len()), Lc::zero());
    out.extend(const_bits(length));
    out
}

// ============================================================================
// SHA-2
// ============================================================================

const SHA512_K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

const SHA512_IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

/// One SHA-2 variant. The SHA-256 round constants and initial values are the high halves
/// of the SHA-512 ones (both are leading fraction bits of the same roots).
struct Sha2 {
    width: usize,
    rounds: usize,
    big0: [usize; 3],
    big1: [usize; 3],
    /// Two rotations and a shift.
    small0: [usize; 3],
    small1: [usize; 3],
}

const SHA256: Sha2 = Sha2 {
    width: 32,
    rounds: 64,
    big0: [2, 13, 22],
    big1: [6, 11, 25],
    small0: [7, 18, 3],
    small1: [17, 19, 10],
};

const SHA512: Sha2 = Sha2 {
    width: 64,
    rounds: 80,
    big0: [28, 34, 39],
    big1: [14, 18, 41],
    small0: [1, 8, 7],
    small1: [19, 61, 6],
};

impl Sha2 {
    fn k(&self, t: usize) -> Word {
        Word::constant(SHA512_K[t] >> (64 - self.width), self.width)
    }

    fn iv(&self) -> [Word; 8] {
        SHA512_IV.map(|v| Word::constant(v >> (64 - self.width), self.width))
    }

    fn sigma(&self, cs: &mut ConstraintSystem, x: &Word, r: [usize; 3], shift: bool) -> Word {
        let third = if shift { x.shr(r[2]) } else { x.rotr(r[2]) };
        bitwise3(cs, &x.rotr(r[0]), &x.rotr(r[1]), &third, xor3)
    }

    fn compress(
        &self,
        cs: &mut ConstraintSystem,
        state: &[Word; 8],
        block: &[Word; 16],
    ) -> [Word; 8] {
        assert!(
            state.iter().chain(block).all(|x| x.width() == self.width),
            "word width"
        );
        // The last two schedule words feed no later word, only their own round, so they
        // are never decomposed: their four addends go into that round's sums.
        let mut w: Vec<Word> = block.to_vec();
        let mut schedule: Vec<Vec<Word>> = block.iter().map(|x| vec![x.clone()]).collect();
        for t in 16..self.rounds {
            let s0 = self.sigma(cs, &w[t - 15], self.small0, true);
            let s1 = self.sigma(cs, &w[t - 2], self.small1, true);
            if t + 2 < self.rounds {
                let next = add_mod(cs, &[&s1, &w[t - 7], &s0, &w[t - 16]], &[]);
                schedule.push(vec![next.clone()]);
                w.push(next);
            } else {
                schedule.push(vec![s1, w[t - 7].clone(), s0, w[t - 16].clone()]);
            }
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state.clone();
        for (t, wt) in schedule.iter().enumerate() {
            let s1 = self.sigma(cs, &e, self.big1, false);
            let choose = bitwise3(cs, &e, &f, &g, ch);
            let s0 = self.sigma(cs, &a, self.big0, false);
            let major = bitwise3(cs, &a, &b, &c, maj);
            let k = self.k(t);
            if t + 1 == self.rounds {
                // The last round's `a` and `e` are used only by the feed-forward sum, so
                // they are never decomposed on their own.
                let mut terms_a = vec![&state[0], &h, &s1, &choose, &k, &s0, &major];
                terms_a.extend(wt);
                let out_a = add_mod(cs, &terms_a, &[]);
                let mut terms_e = vec![&state[4], &d, &h, &s1, &choose, &k];
                terms_e.extend(wt);
                let out_e = add_mod(cs, &terms_e, &[]);
                return [
                    out_a,
                    add_mod(cs, &[&state[1], &a], &[]),
                    add_mod(cs, &[&state[2], &b], &[]),
                    add_mod(cs, &[&state[3], &c], &[]),
                    out_e,
                    add_mod(cs, &[&state[5], &e], &[]),
                    add_mod(cs, &[&state[6], &f], &[]),
                    add_mod(cs, &[&state[7], &g], &[]),
                ];
            }
            let mut terms_e = vec![&d, &h, &s1, &choose, &k];
            terms_e.extend(wt);
            let new_e = add_mod(cs, &terms_e, &[]);
            // `T1 + T2 = new_e - d + T2`: four addends instead of seven.
            let new_a = add_mod(cs, &[&new_e, &s0, &major], &[&d]);
            h = g;
            g = f;
            f = e;
            e = new_e;
            d = c;
            c = b;
            b = a;
            a = new_a;
        }
        unreachable!("the last round returns")
    }

    /// The hash of `prefix || message`, where `state` is the chaining value after the
    /// `absorbed` prefix bytes (a whole number of blocks).
    fn hash_from(
        &self,
        cs: &mut ConstraintSystem,
        mut state: [Word; 8],
        absorbed: usize,
        message: &[Lc],
    ) -> Vec<Lc> {
        let wbytes = self.width / 8;
        assert!(absorbed % (16 * wbytes) == 0, "prefix of whole blocks");
        let bit_len = ((8 * absorbed + message.len()) as u128).to_be_bytes();
        let padded = md_pad(message, 16 * wbytes, 0x80, &bit_len[16 - 2 * wbytes..]);
        let words = be_words(&padded, wbytes);
        for block in words.chunks(16) {
            let block: &[Word; 16] = block.try_into().expect("padded to whole blocks");
            state = self.compress(cs, &state, block);
        }
        be_bits(&state)
    }

    fn hash(&self, cs: &mut ConstraintSystem, message: &[Lc]) -> Vec<Lc> {
        self.hash_from(cs, self.iv(), 0, message)
    }
}

/// SHA-256 initial state.
pub fn sha256_iv() -> [Word; 8] {
    SHA256.iv()
}

/// SHA-256 compression over 32-bit words (`block` holds the big-endian message words).
pub fn sha256_compress(
    cs: &mut ConstraintSystem,
    state: &[Word; 8],
    block: &[Word; 16],
) -> [Word; 8] {
    SHA256.compress(cs, state, block)
}

/// SHA-256 of a byte string; 256 output bits.
pub fn sha256(cs: &mut ConstraintSystem, message: &[Lc]) -> Vec<Lc> {
    SHA256.hash(cs, message)
}

/// The SHA-256 chaining value after `prefix`, a whole number of 64-byte blocks.
pub fn sha256_midstate(prefix: &[u8]) -> [u32; 8] {
    assert!(prefix.len() % 64 == 0, "prefix of whole blocks");
    // On constants every gadget folds, so this adds no row and reads no assignment.
    let mut cs = ConstraintSystem::new();
    let mut state = SHA256.iv();
    for block in be_words(&const_bits(prefix), 4).chunks(16) {
        let block: &[Word; 16] = block.try_into().expect("whole blocks");
        state = SHA256.compress(&mut cs, &state, block);
    }
    state.map(|word| word.const_value().expect("constants fold") as u32)
}

/// SHA-256 of `prefix || message` given the chaining value `midstate` after the
/// `absorbed` bytes of `prefix` (see [`sha256_midstate`]); 256 output bits.
pub fn sha256_from_midstate(
    cs: &mut ConstraintSystem,
    midstate: &[Word; 8],
    absorbed: usize,
    message: &[Lc],
) -> Vec<Lc> {
    SHA256.hash_from(cs, midstate.clone(), absorbed, message)
}

/// SHA-512 initial state.
pub fn sha512_iv() -> [Word; 8] {
    SHA512.iv()
}

/// SHA-512 compression over 64-bit words (`block` holds the big-endian message words).
pub fn sha512_compress(
    cs: &mut ConstraintSystem,
    state: &[Word; 8],
    block: &[Word; 16],
) -> [Word; 8] {
    SHA512.compress(cs, state, block)
}

/// SHA-512 of a byte string; 512 output bits.
pub fn sha512(cs: &mut ConstraintSystem, message: &[Lc]) -> Vec<Lc> {
    SHA512.hash(cs, message)
}

// ============================================================================
// HMAC and HKDF
// ============================================================================

/// An HMAC key after its two pad blocks: the chaining values of `key ^ ipad` and
/// `key ^ opad`. Every MAC under the key starts from them, so they are computed once
/// (two compressions; none for a constant key, whose pad blocks fold).
#[derive(Clone)]
pub struct HmacKey {
    variant: &'static Sha2,
    inner: [Word; 8],
    outer: [Word; 8],
}

impl HmacKey {
    fn new(cs: &mut ConstraintSystem, variant: &'static Sha2, key: &[Lc]) -> Self {
        assert!(key.len() % 8 == 0, "keys hold whole bytes");
        let block = 2 * variant.width;
        let mut k0 = if key.len() > 8 * block {
            variant.hash(cs, key)
        } else {
            key.to_vec()
        };
        k0.resize(8 * block, Lc::zero());
        let mut pad = |byte: u8| -> [Word; 8] {
            let bits: Vec<Lc> = k0
                .iter()
                .enumerate()
                .map(|(i, bit)| {
                    if (byte >> (i % 8)) & 1 == 1 {
                        not(bit)
                    } else {
                        bit.clone()
                    }
                })
                .collect();
            let words = be_words(&bits, variant.width / 8);
            let words: &[Word; 16] = words.as_slice().try_into().expect("one block");
            variant.compress(cs, &variant.iv(), words)
        };
        let inner = pad(0x36);
        let outer = pad(0x5c);
        Self {
            variant,
            inner,
            outer,
        }
    }

    /// Key for HMAC-SHA256; a key longer than 64 bytes is hashed first.
    pub fn sha256(cs: &mut ConstraintSystem, key: &[Lc]) -> Self {
        Self::new(cs, &SHA256, key)
    }

    /// Key for HMAC-SHA512; a key longer than 128 bytes is hashed first.
    pub fn sha512(cs: &mut ConstraintSystem, key: &[Lc]) -> Self {
        Self::new(cs, &SHA512, key)
    }

    /// Chaining value after `key ^ ipad`, for a caller that builds the inner message
    /// block itself.
    pub fn inner_state(&self) -> &[Word; 8] {
        &self.inner
    }

    /// The inner digest `H((key ^ ipad) || message)`.
    pub fn inner_digest(&self, cs: &mut ConstraintSystem, message: &[Lc]) -> Vec<Lc> {
        let block = 2 * self.variant.width;
        self.variant
            .hash_from(cs, self.inner.clone(), block, message)
    }

    /// The MAC from an inner digest: `H((key ^ opad) || inner_digest)`.
    pub fn finish(&self, cs: &mut ConstraintSystem, inner_digest: &[Lc]) -> Vec<Lc> {
        let block = 2 * self.variant.width;
        self.variant
            .hash_from(cs, self.outer.clone(), block, inner_digest)
    }

    /// RFC 2104 HMAC of a byte string.
    pub fn mac(&self, cs: &mut ConstraintSystem, message: &[Lc]) -> Vec<Lc> {
        let inner = self.inner_digest(cs, message);
        self.finish(cs, &inner)
    }
}

/// RFC 2104 HMAC-SHA256 of a byte string under a byte-string key of any length.
pub fn hmac_sha256(cs: &mut ConstraintSystem, key: &[Lc], message: &[Lc]) -> Vec<Lc> {
    HmacKey::sha256(cs, key).mac(cs, message)
}

/// RFC 2104 HMAC-SHA512 of a byte string under a byte-string key of any length.
pub fn hmac_sha512(cs: &mut ConstraintSystem, key: &[Lc], message: &[Lc]) -> Vec<Lc> {
    HmacKey::sha512(cs, key).mac(cs, message)
}

/// RFC 5869 HKDF-Extract with SHA-256: the 256-bit pseudorandom key.
pub fn hkdf_sha256_extract(cs: &mut ConstraintSystem, salt: &[Lc], ikm: &[Lc]) -> Vec<Lc> {
    hmac_sha256(cs, salt, ikm)
}

/// RFC 5869 HKDF-Expand with SHA-256 for `L = 32`: the single block `T(1)`.
