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
//! function of three bits costs one row (see `OneRow`): XOR3, Maj, Ch, the Keccak `chi`
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
pub fn hkdf_sha256_expand(cs: &mut ConstraintSystem, prk: &[Lc], info: &[Lc]) -> Vec<Lc> {
    let mut message = info.to_vec();
    message.extend(const_bits(&[1]));
    hmac_sha256(cs, prk, &message)
}

// ============================================================================
// RIPEMD-160
// ============================================================================

const RMD_RL: [usize; 80] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5,
    2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4,
    13, 3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
];

const RMD_RR: [usize; 80] = [
    5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12,
    4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5,
    12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
];

const RMD_SL: [usize; 80] = [
    11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15,
    9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14,
    15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
];

const RMD_SR: [usize; 80] = [
    8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12,
    7, 6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14,
    6, 14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
];

const RMD_KL: [u64; 5] = [0, 0x5a82_7999, 0x6ed9_eba1, 0x8f1b_bcdc, 0xa953_fd4e];
const RMD_KR: [u64; 5] = [0x50a2_8be6, 0x5c4d_d124, 0x6d70_3ef3, 0x7a6d_76e9, 0];
const RMD_IV: [u64; 5] = [
    0x6745_2301,
    0xefcd_ab89,
    0x98ba_dcfe,
    0x1032_5476,
    0xc3d2_e1f0,
];

/// Registers after one 80-step line. The last step's `b` is left as the two addends
/// `b_rot + b_add`, which the caller folds into the final sum.
struct RmdLine {
    a: Word,
    b_rot: Word,
    b_add: Word,
    c: Word,
    d: Word,
    e: Word,
}

fn rmd_line(cs: &mut ConstraintSystem, state: &[Word; 5], x: &[Word; 16], left: bool) -> RmdLine {
    let [mut a, mut b, mut c, mut d, mut e] = state.clone();
    for j in 0..80 {
        let (func, r, s, k) = if left {
            (j / 16, RMD_RL[j], RMD_SL[j], RMD_KL[j / 16])
        } else {
            (4 - j / 16, RMD_RR[j], RMD_SR[j], RMD_KR[j / 16])
        };
        let fw = match func {
            0 => bitwise3(cs, &b, &c, &d, xor3),
            1 => bitwise3(cs, &b, &c, &d, ch),
            2 => bitwise3(cs, &b, &c, &d, orn_xor),
            3 => bitwise3(cs, &d, &b, &c, ch),
            _ => bitwise3(cs, &c, &d, &b, orn_xor),
        };
        let t = add_mod(cs, &[&a, &fw, &x[r], &Word::constant(k, 32)], &[]).rotl(s);
        if j == 79 {
            return RmdLine {
                a: e.clone(),
                b_rot: t,
                b_add: e,
                c: b,
                d: c.rotl(10),
                e: d,
            };
        }
        let next = add_mod(cs, &[&t, &e], &[]);
        a = e;
        e = d;
        d = c.rotl(10);
        c = b;
        b = next;
    }
    unreachable!("the last step returns")
}

/// RIPEMD-160 initial state.
pub fn ripemd160_iv() -> [Word; 5] {
    RMD_IV.map(|v| Word::constant(v, 32))
}

/// RIPEMD-160 compression over 32-bit words (`block` holds the little-endian message words).
pub fn ripemd160_compress(
    cs: &mut ConstraintSystem,
    state: &[Word; 5],
    block: &[Word; 16],
) -> [Word; 5] {
    assert!(
        state.iter().chain(block).all(|x| x.width() == 32),
        "word width"
    );
    let l = rmd_line(cs, state, block, true);
    let r = rmd_line(cs, state, block, false);
    [
        add_mod(cs, &[&state[1], &l.c, &r.d], &[]),
        add_mod(cs, &[&state[2], &l.d, &r.e], &[]),
        add_mod(cs, &[&state[3], &l.e, &r.a], &[]),
        add_mod(cs, &[&state[4], &l.a, &r.b_rot, &r.b_add], &[]),
        add_mod(cs, &[&state[0], &l.b_rot, &l.b_add, &r.c], &[]),
    ]
}

/// RIPEMD-160 of a byte string; 160 output bits.
pub fn ripemd160(cs: &mut ConstraintSystem, message: &[Lc]) -> Vec<Lc> {
    let bit_len = (message.len() as u64).to_le_bytes();
    let padded = md_pad(message, 64, 0x80, &bit_len);
    let mut state = ripemd160_iv();
    for block in padded.chunks(512) {
        let words: Vec<Word> = block
            .chunks(32)
            .map(|w| Word::from_bits(w.to_vec()))
            .collect();
        let words: &[Word; 16] = words.as_slice().try_into().expect("sixteen words");
        state = ripemd160_compress(cs, &state, words);
    }
    state.into_iter().flat_map(Word::into_bits).collect()
}

/// Bitcoin `HASH160`: RIPEMD-160 of SHA-256; 160 output bits.
pub fn hash160(cs: &mut ConstraintSystem, message: &[Lc]) -> Vec<Lc> {
    let inner = sha256(cs, message);
    ripemd160(cs, &inner)
}

// ============================================================================
// Keccak
// ============================================================================

/// `Keccak-f[1600]` on lanes `state[x + 5y]`: 3,840 rows per round on a non-constant state
/// (640 for the column parities, 1,600 for theta, 1,600 for chi).
pub fn keccak_f1600(cs: &mut ConstraintSystem, state: &mut [Word; 25]) {
    assert!(state.iter().all(|lane| lane.width() == 64), "lane width");
    for rc in qsag_accel::keccak::KECCAK_RC {
        let parity: Vec<Vec<Lc>> = (0..5)
            .map(|x| {
                (0..64)
                    .map(|z| {
                        let column: Vec<Lc> =
                            (0..5).map(|y| state[x + 5 * y].bits[z].clone()).collect();
                        xor_many(cs, &column)
                    })
                    .collect()
            })
            .collect();
        let mut moved: Vec<Word> = state.to_vec();
        for x in 0..5 {
            for y in 0..5 {
                let lane = x + 5 * y;
                let theta = Word::from_bits(
                    (0..64)
                        .map(|z| {
                            xor_many(
                                cs,
                                &[
                                    state[lane].bits[z].clone(),
                                    parity[(x + 4) % 5][z].clone(),
                                    parity[(x + 1) % 5][(z + 63) % 64].clone(),
                                ],
                            )
                        })
                        .collect(),
                );
                let offset = qsag_asm::KECCAK_ROTATION_OFFSETS[lane] as usize;
                moved[y + 5 * ((2 * x + 3 * y) % 5)] = theta.rotl(offset);
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] = bitwise3(
                    cs,
                    &moved[x + 5 * y],
                    &moved[(x + 1) % 5 + 5 * y],
                    &moved[(x + 2) % 5 + 5 * y],
                    chi,
                );
            }
        }
        state[0] = state[0].xor_const(rc);
    }
}

/// Keccak-256 (the pre-FIPS `0x01` padding used by Ethereum) of a byte string; 256 output
/// bits. Blocks after the first cost 1,088 further rows to absorb.
pub fn keccak256(cs: &mut ConstraintSystem, message: &[Lc]) -> Vec<Lc> {
    const RATE: usize = 136;
    assert!(message.len() % 8 == 0, "messages hold whole bytes");
    let total = (message.len() / 8 + 1).div_ceil(RATE) * RATE;
    let mut padded = message.to_vec();
    padded.resize(8 * total, Lc::zero());
    padded[message.len()] = one();
    // Bit 7 of the last byte; distinct from the first padding bit even when they share a byte.
    padded[8 * total - 1] = one();

    let mut state: [Word; 25] = core::array::from_fn(|_| Word::constant(0, 64));
    for block in padded.chunks(8 * RATE) {
        for (lane, bits) in state.iter_mut().zip(block.chunks(64)) {
            *lane = Word::from_bits(
                lane.bits
                    .iter()
                    .zip(bits)
                    .map(|(s, m)| xor2(cs, s, m))
                    .collect(),
            );
        }
        keccak_f1600(cs, &mut state);
    }
    state
        .into_iter()
        .take(4)
        .flat_map(Word::into_bits)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use qsag_accel::keccak::keccak256 as keccak256_native;
    use qsag_accel::sha2 as native;
    use qsag_agg::zk_hem::relation::Shape;

    type Hash = fn(&mut ConstraintSystem, &[Lc]) -> Vec<Lc>;

    fn hex(s: &str) -> Vec<u8> {
        let digits: Vec<u8> = s
            .bytes()
            .filter(|b| !b.is_ascii_whitespace())
            .map(|b| (b as char).to_digit(16).expect("hex digit") as u8)
            .collect();
        assert!(digits.len() % 2 == 0);
        digits.chunks(2).map(|p| (p[0] << 4) | p[1]).collect()
    }

    fn splitmix(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn bytes(len: usize, seed: u64) -> Vec<u8> {
        let mut s = seed;
        (0..len).map(|_| splitmix(&mut s) as u8).collect()
    }

    /// Circuit output bytes, shape and assignment for `build` over allocated `inputs`.
    fn run(
        inputs: &[&[u8]],
        build: impl Fn(&mut ConstraintSystem, &[Vec<Lc>]) -> Vec<Lc>,
    ) -> (Vec<u8>, Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        let bits: Vec<Vec<Lc>> = inputs.iter().map(|b| alloc_bits(&mut cs, b)).collect();
        let out = build(&mut cs, &bits);
        let out = bits_to_bytes(&cs, &out);
        let (shape, z) = cs.finish();
        (out, shape, z)
    }

    /// Whether the circuit with its output pinned to `digest` is satisfied.
    fn pinned(
        inputs: &[&[u8]],
        digest: &[u8],
        build: impl Fn(&mut ConstraintSystem, &[Vec<Lc>]) -> Vec<Lc>,
    ) -> bool {
        let mut cs = ConstraintSystem::new();
        let bits: Vec<Vec<Lc>> = inputs.iter().map(|b| alloc_bits(&mut cs, b)).collect();
        let out = build(&mut cs, &bits);
        let want = const_bits(digest);
        assert_eq!(out.len(), want.len());
        for (o, w) in out.iter().zip(&want) {
            cs.enforce_equal(o, w);
        }
        let (shape, z) = cs.finish();
        shape.is_satisfied(&z)
    }

    /// Flip about `samples` evenly spaced witness variables, one at a time; each flip must
    /// break the relation. Returns the number of variables tried.
    fn flips_are_rejected(shape: &Shape, z: &[F], samples: usize) -> usize {
        let vars = shape.mask_var_base;
        let stride = (vars / samples).max(1);
        let mut tried = 0;
        for i in (1..vars).step_by(stride) {
            let mut bad = z.to_vec();
            bad[i] = F::ONE - bad[i];
            assert_ne!(bad[i], z[i]);
            assert!(!shape.is_satisfied(&bad), "flip of variable {i} accepted");
            tried += 1;
        }
        tried
    }

    /// Parity with `want`, satisfaction, rejection of flipped witness bits and of a wrong
    /// pinned digest.
    fn check(
        inputs: &[&[u8]],
        want: &[u8],
        build: impl Fn(&mut ConstraintSystem, &[Vec<Lc>]) -> Vec<Lc> + Copy,
    ) {
        let (got, shape, z) = run(inputs, build);
        assert_eq!(got, want);
        assert!(shape.is_satisfied(&z));
        if inputs.iter().any(|b| !b.is_empty()) {
            assert!(flips_are_rejected(&shape, &z, 48) >= 8);
        }
        assert!(pinned(inputs, want, build));
        let mut wrong = want.to_vec();
        wrong[want.len() / 2] ^= 0x10;
        assert!(!pinned(inputs, &wrong, build));
    }

    fn check_hash(hash: Hash, reference: impl Fn(&[u8]) -> Vec<u8>, lengths: &[usize]) {
        for &len in lengths {
            let msg = bytes(len, 0x5eed ^ len as u64);
            check(&[&msg], &reference(&msg), |cs, i| hash(cs, &i[0]));
        }
    }

    #[test]
    fn one_row_tables_define_their_functions() {
        for (name, g) in [
            ("xor3", &XOR3),
            ("maj", &MAJ),
            ("chi", &CHI),
            ("orn_xor", &ORN_XOR),
        ] {
            for v in 0..8u64 {
                let (x, y, z) = (v & 1, (v >> 1) & 1, (v >> 2) & 1);
                let at =
                    |co: &[i64; 4]| co[0] + co[1] * x as i64 + co[2] * y as i64 + co[3] * z as i64;
                let f = (g.f)(x, y, z) as i64;
                assert!(f == 0 || f == 1);
                // Nonzero small integers stay nonzero in the field, so `p` is unique.
                assert!(at(&g.b) != 0 && at(&g.b).abs() <= 7, "{name} at {v}");
                assert_eq!((g.pk * f + at(&g.a)) * at(&g.b), at(&g.c), "{name} at {v}");

                let mut cs = ConstraintSystem::new();
                let ins: Vec<Lc> = [x, y, z]
                    .iter()
                    .map(|&b| {
                        let bit: Lc = cs.alloc(fu(b)).into();
                        cs.enforce_boolean(&bit);
                        bit
                    })
                    .collect();
                let out = one_row(&mut cs, g, &ins[0], &ins[1], &ins[2]);
                assert_eq!(cs.num_rows(), 4);
                assert_eq!(cs.eval(&out), fu(f as u64));
                let (shape, w) = cs.finish();
                assert!(shape.is_satisfied(&w));
                // Variables 1..=3 are the inputs, 4 is the output.
                assert_eq!(w[4], fu(f as u64));
                for wrong in [
                    fu(1 - f as u64),
                    fu(2),
                    F::ZERO - F::ONE,
                    fu(1) - fu(2).inv(),
                ] {
                    let mut bad = w.clone();
                    bad[4] = wrong;
                    assert!(!shape.is_satisfied(&bad), "{name} at {v}");
                }
                for input in 1..=3 {
                    let mut bad = w.clone();
                    bad[input] = F::ONE - bad[input];
                    let (bx, by, bz) = (
                        bad[1].to_canonical_u64(),
                        bad[2].to_canonical_u64(),
                        bad[3].to_canonical_u64(),
                    );
                    assert_eq!(
                        shape.is_satisfied(&bad),
                        (g.f)(bx, by, bz) as i64 == f,
                        "{name} at {v}"
                    );
                }
            }
        }
    }

    /// Every bit gadget on every mix of constant and allocated inputs.
    #[test]
    fn bit_gadgets_match_truth_tables_with_constant_folding() {
        type Gadget = fn(&mut ConstraintSystem, &Lc, &Lc, &Lc) -> Lc;
        type Truth = fn(u64, u64, u64) -> u64;
        let gadgets: [(&str, Gadget, Truth); 7] = [
            ("xor3", xor3, |a, b, c| a ^ b ^ c),
            ("maj", maj, |a, b, c| (a & b) | (a & c) | (b & c)),
            ("ch", ch, |e, f, g| (e & f) | ((1 ^ e) & g)),
            ("chi", chi, |a, b, c| a ^ ((1 ^ b) & c)),
            ("orn_xor", orn_xor, |x, y, z| (x | (1 ^ y)) ^ z),
            ("xor2", |cs, a, b, _| xor2(cs, a, b), |a, b, _| a ^ b),
            ("and", |cs, a, b, _| and(cs, a, b), |a, b, _| a & b),
        ];
        let mut rejected = 0;
        for (name, gadget, f) in gadgets {
            // Bit `i` of `consts` makes input `i` a constant.
            for consts in 0..8u32 {
                for v in 0..8u64 {
                    let vals = [v & 1, (v >> 1) & 1, (v >> 2) & 1];
                    let mut cs = ConstraintSystem::new();
                    let ins: Vec<Lc> = (0..3)
                        .map(|i| {
                            if (consts >> i) & 1 == 1 {
                                Lc::constant(fu(vals[i]))
                            } else {
                                let bit: Lc = cs.alloc(fu(vals[i])).into();
                                cs.enforce_boolean(&bit);
                                bit
                            }
                        })
                        .collect();
                    let inputs = cs.num_rows();
                    let out = gadget(&mut cs, &ins[0], &ins[1], &ins[2]);
                    let rows = cs.num_rows() - inputs;
                    assert!(rows <= 1, "{name} consts {consts:03b}: {rows} rows");
                    let want = f(vals[0], vals[1], vals[2]);
                    assert_eq!(cs.eval(&out), fu(want), "{name} {consts:03b} {v:03b}");
                    // Pin the output to its complement: no assignment of the gadget's own
                    // variable may satisfy that.
                    cs.enforce_equal(&out, &Lc::constant(fu(1 - want)));
                    let (shape, w) = cs.finish();
                    assert!(!shape.is_satisfied(&w));
                    if rows == 1 {
                        let own = shape.mask_var_base - 1;
                        for candidate in [0u64, 1] {
                            let mut bad = w.clone();
                            bad[own] = fu(candidate);
                            assert!(!shape.is_satisfied(&bad), "{name} {consts:03b} {v:03b}");
                            rejected += 1;
                        }
                    }
                }
            }
        }
        assert!(rejected > 300, "{rejected}");
    }

    #[test]
    fn xor_many_is_parity() {
        for n in 0..=7usize {
            for v in 0..(1u64 << n) {
                // Odd positions are constants when `n` is odd, to cover folding.
                let mut cs = ConstraintSystem::new();
                let bits: Vec<Lc> = (0..n)
                    .map(|i| {
                        let b = (v >> i) & 1;
                        if n % 2 == 1 && i % 2 == 1 {
                            Lc::constant(fu(b))
                        } else {
                            let bit: Lc = cs.alloc(fu(b)).into();
                            cs.enforce_boolean(&bit);
                            bit
                        }
                    })
                    .collect();
                let vars = cs.num_rows();
                let out = xor_many(&mut cs, &bits);
                assert_eq!(cs.num_rows() - vars, vars.saturating_sub(1).div_ceil(2));
                let want = u64::from(v.count_ones() & 1);
                assert_eq!(cs.eval(&out), fu(want));
                // With the parity pinned, a flipped input or intermediate is a wrong witness.
                cs.enforce_equal(&out, &Lc::constant(fu(want)));
                let (shape, w) = cs.finish();
                assert!(shape.is_satisfied(&w));
                for i in 1..shape.mask_var_base {
                    let mut bad = w.clone();
                    bad[i] = F::ONE - bad[i];
                    assert!(!shape.is_satisfied(&bad), "n {n} v {v} var {i}");
                }
            }
        }
    }

    #[test]
    fn word_operations_match_integers() {
        let mut seed = 7;
        for width in [32usize, 64] {
            let mask = u64::MAX >> (64 - width);
            let v = splitmix(&mut seed) & mask;
            let mut cs = ConstraintSystem::new();
            let word = Word::alloc(&mut cs, v, width);
            assert_eq!(cs.num_rows(), width);
            assert_eq!(word.value(&cs), v);
            assert_eq!(Word::constant(v, width).const_value(), Some(v));
            assert_eq!(word.const_value(), None);
            let rot = |x: u64, n: u32| ((x >> n) | (x << (width as u32 - n))) & mask;
            for n in [1usize, 7, 31] {
                assert_eq!(word.rotr(n).value(&cs), rot(v, n as u32));
                assert_eq!(word.rotl(n).value(&cs), rot(v, (width - n) as u32));
                assert_eq!(word.shr(n).value(&cs), v >> n);
            }
            let k = splitmix(&mut seed) & mask;
            assert_eq!(word.xor_const(k).value(&cs), v ^ k);
            assert_eq!(cs.num_rows(), width);
        }
    }

    #[test]
    fn add_mod_matches_wrapping_arithmetic() {
        let mut seed = 99;
        let mut cases = 0;
        for width in [8usize, 32, 40, 64] {
            let mask = u64::MAX >> (64 - width);
            for n_plus in 0..=8usize {
                for n_minus in 0..=2usize {
                    if n_plus + n_minus == 0 {
                        continue;
                    }
                    // Extremes drive every carry to its bound; `mode` 3 mixes in constants.
                    for mode in 0..4 {
                        let mut cs = ConstraintSystem::new();
                        // Subtracted words take the opposite extreme.
                        let mut pick = |cs: &mut ConstraintSystem, i: usize, sub: bool| {
                            let v = match (mode, sub) {
                                (0, false) | (1, true) => mask,
                                (0, true) | (1, false) => 0,
                                _ => splitmix(&mut seed) & mask,
                            };
                            if mode == 3 && i % 2 == 0 {
                                (Word::constant(v, width), v)
                            } else {
                                (Word::alloc(cs, v, width), v)
                            }
                        };
                        let plus: Vec<(Word, u64)> =
                            (0..n_plus).map(|i| pick(&mut cs, i, false)).collect();
                        let minus: Vec<(Word, u64)> =
                            (0..n_minus).map(|i| pick(&mut cs, i + 1, true)).collect();
                        let want = plus.iter().fold(0u64, |acc, (_, v)| acc.wrapping_add(*v));
                        let want =
                            minus.iter().fold(want, |acc, (_, v)| acc.wrapping_sub(*v)) & mask;
                        let before = cs.num_rows();
                        let p: Vec<&Word> = plus.iter().map(|(w, _)| w).collect();
                        let m: Vec<&Word> = minus.iter().map(|(w, _)| w).collect();
                        let sum = add_mod(&mut cs, &p, &m);
                        let added_rows = cs.num_rows() - before;
                        assert_eq!(sum.width(), width);
                        assert_eq!(
                            sum.value(&cs),
                            want,
                            "w{width} +{n_plus} -{n_minus} m{mode}"
                        );
                        let (shape, z) = cs.finish();
                        assert!(shape.is_satisfied(&z));
                        if added_rows > 0 {
                            // Every result and carry bit is pinned by the limb equation.
                            let first =
                                shape.mask_var_base - added_rows.min(shape.mask_var_base - 1);
                            for i in first..shape.mask_var_base {
                                let mut bad = z.clone();
                                bad[i] = F::ONE - bad[i];
                                assert!(
                                    !shape.is_satisfied(&bad),
                                    "w{width} +{n_plus} -{n_minus} m{mode} var {i}"
                                );
                            }
                            // And so is every input bit.
                            assert!(flips_are_rejected(&shape, &z, 16) > 0);
                        }
                        cases += 1;
                    }
                }
            }
        }
        assert!(cases > 300);
    }

    /// A result that is off by the modulus of the limb, with the carry left alone, and a
    /// result that is off by one with every other bit consistent.
    #[test]
    fn add_mod_rejects_consistent_looking_forgeries() {
        let mut cs = ConstraintSystem::new();
        let a = Word::alloc(&mut cs, 0xffff_fff0, 32);
        let b = Word::alloc(&mut cs, 0x0000_0025, 32);
        let c = Word::alloc(&mut cs, 0x8000_0000, 32);
        let sum = add_mod(&mut cs, &[&a, &b, &c], &[]);
        assert_eq!(sum.value(&cs), 0x8000_0015);
        // 32 result bits, two carry bits of which one is allocated.
        assert_eq!(cs.num_rows(), 96 + 34);
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        let result = 97..129;
        let carry_low = 129;
        assert_eq!(z[carry_low], F::ONE);
        // Claim 0x8000_0014 or 0x8000_0017 instead.
        for delta in [1u64, 2] {
            let mut bad = z.clone();
            let forged = 0x8000_0015u64 ^ delta;
            for (bit, i) in result.clone().enumerate() {
                bad[i] = fu((forged >> bit) & 1);
            }
            assert!(!shape.is_satisfied(&bad));
        }
        // Drop the carry: the top carry bit would have to be 1/2.
        let mut bad = z.clone();
        bad[carry_low] = F::ZERO;
        assert!(!shape.is_satisfied(&bad));

        // A limb that cannot carry (the constant's low half is zero) keeps its equation row.
        let mut cs = ConstraintSystem::new();
        let x = Word::alloc(&mut cs, 0xffff_ffff_0000_0007, 64);
        let sum = add_mod(&mut cs, &[&x, &Word::constant(5 << 32, 64)], &[]);
        assert_eq!(sum.value(&cs), 0x0000_0004_0000_0007);
        assert_eq!(cs.num_rows(), 64 + 33 + 33);
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        for i in 1..shape.mask_var_base {
            let mut bad = z.clone();
            bad[i] = F::ONE - bad[i];
            assert!(!shape.is_satisfied(&bad), "var {i}");
        }
    }

    #[test]
    fn sha256_matches_native() {
        let reference = |m: &[u8]| native::sha256(m).to_vec();
        assert_eq!(
            reference(b"abc"),
            hex("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
        );
        check(&[b"abc"], &reference(b"abc"), |cs, i| sha256(cs, &i[0]));
        check(
            &[b""],
            &hex("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
            |cs, i| sha256(cs, &i[0]),
        );
        check_hash(sha256, reference, &[1, 55, 56, 63, 64, 65, 119, 120]);
    }

    #[test]
    fn sha256_from_midstate_matches_native() {
        for (prefix_len, len) in [(64usize, 32usize), (64, 0), (128, 56), (0, 3)] {
            let (prefix, msg) = (bytes(prefix_len, 41), bytes(len, 42));
            let mid = sha256_midstate(&prefix);
            let whole = [prefix.as_slice(), msg.as_slice()].concat();
            let want = native::sha256(&whole).to_vec();
            let build = |cs: &mut ConstraintSystem, i: &[Vec<Lc>]| {
                let state = mid.map(|w| Word::constant(u64::from(w), 32));
                sha256_from_midstate(cs, &state, prefix_len, &i[0])
            };
            check(&[&msg], &want, build);
            // The same message under another prefix of the same length hashes differently.
            if prefix_len > 0 {
                let mut other = prefix.clone();
                other[prefix_len / 2] ^= 1;
                assert_ne!(sha256_midstate(&other), mid);
            }
        }
        assert_eq!(
            sha256_midstate(&[]),
            sha256_iv().map(|w| w.const_value().unwrap() as u32)
        );
    }

    #[test]
    fn add_wide_and_select_match_integers() {
        let mut seed = 5;
        for (len, mode) in [(256usize, 0), (256, 1), (256, 2), (224, 2), (40, 2)] {
            let draw = |seed: &mut u64| -> Vec<u8> {
                (0..len / 8)
                    .map(|_| match mode {
                        0 => 0xff,
                        1 => 0,
                        _ => splitmix(seed) as u8,
                    })
                    .collect()
            };
            let (a, b) = (draw(&mut seed), draw(&mut seed));
            let mut want = vec![0u8; len / 8];
            let mut carry = 0u16;
            for i in 0..len / 8 {
                let v = u16::from(a[i]) + u16::from(b[i]) + carry;
                want[i] = v as u8;
                carry = v >> 8;
            }
            let (got, shape, z) = run(&[&a, &b], |cs, i| add_wide(cs, &i[0], &i[1]));
            assert_eq!(got, want);
            assert!(shape.is_satisfied(&z));
            assert!(flips_are_rejected(&shape, &z, 64) >= 32);
        }
        for v in 0..8u64 {
            let mut cs = ConstraintSystem::new();
            let bits: Vec<Lc> = (0..3)
                .map(|i| {
                    let bit: Lc = cs.alloc(fu((v >> i) & 1)).into();
                    cs.enforce_boolean(&bit);
                    bit
                })
                .collect();
            let out = select(&mut cs, &bits[0], &bits[1], &bits[2]);
            assert_eq!(cs.num_rows(), 4);
            let want = if v & 1 == 1 {
                (v >> 1) & 1
            } else {
                (v >> 2) & 1
            };
            assert_eq!(cs.eval(&out), fu(want));
            assert_eq!(
                select(&mut cs, &Lc::constant(F::ONE), &bits[1], &bits[2]),
                bits[1]
            );
            assert_eq!(select(&mut cs, &Lc::zero(), &bits[1], &bits[2]), bits[2]);
            assert_eq!(cs.num_rows(), 4);
        }
    }

    #[test]
    fn hmac_key_is_reusable_and_folds_for_constant_keys() {
        let key = bytes(32, 71);
        let (m1, m2) = (bytes(37, 72), bytes(69, 73));
        let mut want = native::hmac_sha512(&key, &m1).to_vec();
        want.extend(native::hmac_sha512(&key, &m2));
        check(&[&key, &m1, &m2], &want, |cs, i| {
            let hk = HmacKey::sha512(cs, &i[0]);
            let mut out = hk.mac(cs, &i[1]);
            out.extend(hk.mac(cs, &i[2]));
            out
        });
        // Sharing the key saves its two pad compressions on the second MAC.
        let rows = |shared: bool| {
            let mut cs = ConstraintSystem::new();
            let k = alloc_bits(&mut cs, &key);
            let (a, b) = (alloc_bits(&mut cs, &m1), alloc_bits(&mut cs, &m1));
            if shared {
                let hk = HmacKey::sha512(&mut cs, &k);
                let _ = (hk.mac(&mut cs, &a), hk.mac(&mut cs, &b));
            } else {
                let _ = (hmac_sha512(&mut cs, &k, &a), hmac_sha512(&mut cs, &k, &b));
            }
            cs.num_rows()
        };
        assert!(rows(false) - rows(true) > 80_000);
        // A constant key costs nothing itself.
        let mut cs = ConstraintSystem::new();
        let hk = HmacKey::sha512(&mut cs, &const_bits(b"Bitcoin seed"));
        assert_eq!(cs.num_rows(), 0);
        let msg = alloc_bits(&mut cs, &m1);
        let out = hk.mac(&mut cs, &msg);
        assert_eq!(
            bits_to_bytes(&cs, &out),
            native::hmac_sha512(b"Bitcoin seed", &m1).to_vec()
        );
    }

    #[test]
    fn sha512_matches_native() {
        let reference = |m: &[u8]| native::sha512(m).to_vec();
        assert_eq!(
            reference(b"abc"),
            hex(
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a
                 2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
            )
        );
        check(&[b"abc"], &reference(b"abc"), |cs, i| sha512(cs, &i[0]));
        check_hash(sha512, reference, &[0, 1, 111, 112, 127, 128, 129]);
    }

    #[test]
    fn ripemd160_and_hash160_match_native() {
        let reference = |m: &[u8]| native::ripemd160(m).to_vec();
        assert_eq!(
            reference(b"abc"),
            hex("8eb208f7e05d987a9b044a8e98c6b087f15a0bfc")
        );
        check(&[b"abc"], &reference(b"abc"), |cs, i| ripemd160(cs, &i[0]));
        check(
            &[b""],
            &hex("9c1185a5c5e9fc54612808977ee8f548b2258d31"),
            |cs, i| ripemd160(cs, &i[0]),
        );
        check_hash(ripemd160, reference, &[1, 55, 56, 63, 64, 65, 120]);
        // A compressed public key.
        check_hash(hash160, |m| native::hash160(m).to_vec(), &[33, 65]);
    }

    #[test]
    fn keccak256_matches_native() {
        let reference = |m: &[u8]| keccak256_native(m).to_vec();
        assert_eq!(
            reference(b""),
            hex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
        );
        assert_eq!(
            reference(b"abc"),
            hex("4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")
        );
        check(&[b"abc"], &reference(b"abc"), |cs, i| keccak256(cs, &i[0]));
        check_hash(keccak256, reference, &[0, 1, 64, 135, 136, 137, 272]);
    }

    #[test]
    fn keccak_f1600_matches_native() {
        let mut seed = 3;
        let lanes: [u64; 25] = core::array::from_fn(|_| splitmix(&mut seed));
        let mut cs = ConstraintSystem::new();
        let mut state: [Word; 25] = core::array::from_fn(|i| Word::alloc(&mut cs, lanes[i], 64));
        keccak_f1600(&mut cs, &mut state);
        assert_eq!(cs.num_rows(), 1600 + 24 * 3840);
        let mut want = lanes;
        qsag_accel::keccak::keccak_f1600(&mut want);
        assert_eq!(state.each_ref().map(|lane| lane.value(&cs)), want);
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        assert!(flips_are_rejected(&shape, &z, 64) >= 64);
    }

    fn hmac_reference(
        hash: impl Fn(&[u8]) -> Vec<u8>,
        block: usize,
        key: &[u8],
        msg: &[u8],
    ) -> Vec<u8> {
        let mut k0 = if key.len() > block {
            hash(key)
        } else {
            key.to_vec()
        };
        k0.resize(block, 0);
        let mut inner: Vec<u8> = k0.iter().map(|b| b ^ 0x36).collect();
        inner.extend_from_slice(msg);
        let mut outer: Vec<u8> = k0.iter().map(|b| b ^ 0x5c).collect();
        outer.extend(hash(&inner));
        hash(&outer)
    }

    fn hmac_sha256_reference(key: &[u8], msg: &[u8]) -> Vec<u8> {
        hmac_reference(|m| native::sha256(m).to_vec(), 64, key, msg)
    }

    #[test]
    fn hmac_sha256_matches_rfc4231_and_reference() {
        // RFC 4231 test cases 1, 2 and 6 (key longer than a block).
        let long_key = vec![0xaa; 131];
        let vectors: [(&[u8], &[u8], &str); 3] = [
            (
                &[0x0b; 20],
                b"Hi There",
                "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
            ),
            (
                b"Jefe",
                b"what do ya want for nothing?",
                "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
            ),
            (
                &long_key,
                b"Test Using Larger Than Block-Size Key - Hash Key First",
                "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
            ),
        ];
        for (key, msg, want) in vectors {
            assert_eq!(hmac_sha256_reference(key, msg), hex(want));
            check(&[key, msg], &hex(want), |cs, i| {
                hmac_sha256(cs, &i[0], &i[1])
            });
        }
        for (key_len, msg_len) in [(0, 0), (32, 55), (64, 56), (65, 1)] {
            let (key, msg) = (bytes(key_len, 11), bytes(msg_len, 12));
            check(
                &[&key, &msg],
                &hmac_sha256_reference(&key, &msg),
                |cs, i| hmac_sha256(cs, &i[0], &i[1]),
            );
        }
    }

    #[test]
    fn hmac_sha512_matches_rfc4231_and_native() {
        let want = hex(
            "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cde
             daa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854",
        );
        assert_eq!(native::hmac_sha512(&[0x0b; 20], b"Hi There").to_vec(), want);
        check(&[&[0x0b; 20], b"Hi There"], &want, |cs, i| {
            hmac_sha512(cs, &i[0], &i[1])
        });
        // (32, 37) is the BIP-32 hardened step: chain code, `0x00 || key || index`.
        for (key_len, msg_len) in [(32, 37), (0, 0), (128, 111), (129, 112)] {
            let (key, msg) = (bytes(key_len, 21), bytes(msg_len, 22));
            let want = native::hmac_sha512(&key, &msg).to_vec();
            assert_eq!(
                want,
                hmac_reference(|m| native::sha512(m).to_vec(), 128, &key, &msg)
            );
            check(&[&key, &msg], &want, |cs, i| hmac_sha512(cs, &i[0], &i[1]));
        }
    }

    #[test]
    fn hkdf_sha256_matches_rfc5869() {
        // RFC 5869 test case 1; `T(1)` is the first 32 bytes of its 42-byte OKM.
        let ikm = [0x0b; 22];
        let salt = hex("000102030405060708090a0b0c");
        let info = hex("f0f1f2f3f4f5f6f7f8f9");
        let prk = hex("077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5");
        let okm = hex("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf");
        assert_eq!(hmac_sha256_reference(&salt, &ikm), prk);
        let mut info1 = info.clone();
        info1.push(1);
        assert_eq!(hmac_sha256_reference(&prk, &info1), okm);

        check(&[&salt, &ikm], &prk, |cs, i| {
            hkdf_sha256_extract(cs, &i[0], &i[1])
        });
        check(&[&prk, &info], &okm, |cs, i| {
            hkdf_sha256_expand(cs, &i[0], &i[1])
        });
        // Extract then expand in one relation, with an empty salt and empty info.
        let ikm = bytes(32, 31);
        let prk = hmac_sha256_reference(&[], &ikm);
        let okm = hmac_sha256_reference(&prk, &[1]);
        check(&[&ikm], &okm, |cs, i| {
            let prk = hkdf_sha256_extract(cs, &[], &i[0]);
            hkdf_sha256_expand(cs, &prk, &[])
        });
    }

    #[test]
    fn compression_functions_match_the_hashes_and_shapes_ignore_values() {
        // One padded block of "abc" through the public compression entry points.
        let mut cs = ConstraintSystem::new();
        let mut block = b"abc".to_vec();
        block.push(0x80);
        block.resize(63, 0);
        block.push(24);
        let bits = alloc_bits(&mut cs, &block);
        let words: [Word; 16] = be_words(&bits, 4).try_into().unwrap();
        let out = sha256_compress(&mut cs, &sha256_iv(), &words);
        assert_eq!(
            bits_to_bytes(&cs, &be_bits(&out)),
            native::sha256(b"abc").to_vec()
        );
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));

        let shape_of = |hash: Hash, msg: &[u8]| run(&[msg], |cs, i| hash(cs, &i[0])).1;
        for hash in [sha256 as Hash, sha512, ripemd160, keccak256] {
            let a = shape_of(hash, &bytes(70, 1));
            let b = shape_of(hash, &[0xff; 70]);
            let c = shape_of(hash, &bytes(71, 1));
            assert_eq!(a.digest(), b.digest());
            assert_ne!(a.digest(), c.digest());
        }
    }

    /// `cargo test --release -p qsag-migrate --lib hem::hash -- --ignored --nocapture`
    #[test]
    #[ignore = "measurement"]
    fn measure_rows() {
        fn words<const N: usize>(cs: &mut ConstraintSystem, width: usize, seed: u64) -> [Word; N] {
            let mut s = seed;
            core::array::from_fn(|_| Word::alloc(cs, splitmix(&mut s), width))
        }
        let mut cs = ConstraintSystem::new();
        let (state, block) = (words::<8>(&mut cs, 32, 1), words::<16>(&mut cs, 32, 2));
        let before = cs.num_rows();
        let _ = sha256_compress(&mut cs, &state, &block);
        std::println!("SHA-256 block:        {:>7} rows", cs.num_rows() - before);

        let mut cs = ConstraintSystem::new();
        let (state, block) = (words::<8>(&mut cs, 64, 3), words::<16>(&mut cs, 64, 4));
        let before = cs.num_rows();
        let _ = sha512_compress(&mut cs, &state, &block);
        std::println!("SHA-512 block:        {:>7} rows", cs.num_rows() - before);

        let mut cs = ConstraintSystem::new();
        let (state, block) = (words::<5>(&mut cs, 32, 5), words::<16>(&mut cs, 32, 6));
        let before = cs.num_rows();
        let _ = ripemd160_compress(&mut cs, &state, &block);
        std::println!("RIPEMD-160 block:     {:>7} rows", cs.num_rows() - before);

        let mut cs = ConstraintSystem::new();
        let mut state = words::<25>(&mut cs, 64, 7);
        let before = cs.num_rows();
        keccak_f1600(&mut cs, &mut state);
        std::println!("Keccak-f[1600]:       {:>7} rows", cs.num_rows() - before);

        let mut cs = ConstraintSystem::new();
        let key = alloc_bits(&mut cs, &bytes(32, 8));
        let msg = alloc_bits(&mut cs, &bytes(37, 9));
        let before = cs.num_rows();
        let _ = hmac_sha512(&mut cs, &key, &msg);
        std::println!(
            "HMAC-SHA512, 32-byte key, 37-byte message: {} rows (plus {} input-bit rows)",
            cs.num_rows() - before,
            before
        );

        for (name, hash, len) in [
            ("SHA-256 of 33 bytes", sha256 as Hash, 33),
            ("HASH160 of 33 bytes", hash160, 33),
            ("Keccak-256 of 64 bytes", keccak256, 64),
            ("SHA-512 of 32 bytes", sha512, 32),
        ] {
            let mut cs = ConstraintSystem::new();
            let msg = alloc_bits(&mut cs, &bytes(len, 10));
            let before = cs.num_rows();
            let _ = hash(&mut cs, &msg);
            std::println!("{name}: {} rows", cs.num_rows() - before);
        }
        let mut cs = ConstraintSystem::new();
        let ikm = alloc_bits(&mut cs, &bytes(32, 11));
        let info = alloc_bits(&mut cs, &bytes(32, 12));
        let before = cs.num_rows();
        let prk = hkdf_sha256_extract(&mut cs, &[], &ikm);
        let _ = hkdf_sha256_expand(&mut cs, &prk, &info);
        std::println!(
            "HKDF-SHA256 extract(32-byte ikm) + expand(32-byte info): {} rows",
            cs.num_rows() - before
        );
    }
}
