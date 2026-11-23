//! Binary tower arithmetic through GF(2^128) and the Frobenius Booleanity check.

/// Element of Wiedemann tower `T_2 = GF(2^4)` (canonical lower 4 bits `< 16`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gf16(pub u8);

/// Element of Wiedemann tower `T_3 = GF(2^8)` (Shamir evaluation & share field).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gf256(pub u8);

/// Element of Wiedemann tower `T_7 = GF(2^128)` (128-bit BDOZ MAC & triple-sacrifice field).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tower128(pub u128);

#[inline]
const fn diff_bytes8(a: &[u8; 32], b: &[u8; 32], base: usize) -> u8 {
    ((a[base] ^ b[base]) | (a[base + 1] ^ b[base + 1]))
        | ((a[base + 2] ^ b[base + 2]) | (a[base + 3] ^ b[base + 3]))
        | ((a[base + 4] ^ b[base + 4]) | (a[base + 5] ^ b[base + 5]))
        | ((a[base + 6] ^ b[base + 6]) | (a[base + 7] ^ b[base + 7]))
}

/// Branchless constant-time 32-byte equality check (`0` data-dependent branches).
#[inline]
pub const fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let d = (diff_bytes8(a, b, 0) | diff_bytes8(a, b, 8))
        | (diff_bytes8(a, b, 16) | diff_bytes8(a, b, 24));
    d == 0
}

#[inline]
const fn scale_x_t1(a: u8) -> u8 {
    let lo = a & 1;
    let hi = (a >> 1) & 1;
    hi | ((lo ^ hi) << 1)
}

#[inline]
const fn mul_t1(a: u8, b: u8) -> u8 {
    let a_lo = a & 1;
    let a_hi = (a >> 1) & 1;
    let b_lo = b & 1;
    let b_hi = (b >> 1) & 1;
    let p = a_lo & b_lo;
    let q = a_hi & b_hi;
    let r = (a_lo ^ a_hi) & (b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p;
    lo | (hi << 1)
}

#[inline]
const fn scale_x_t2(a: u8) -> u8 {
    let lo = a & 0x3;
    let hi = (a >> 2) & 0x3;
    let s = scale_x_t1(hi);
    hi | ((lo ^ s) << 2)
}

#[inline]
const fn mul_t2(a: u8, b: u8) -> u8 {
    let a_lo = a & 0x3;
    let a_hi = (a >> 2) & 0x3;
    let b_lo = b & 0x3;
    let b_hi = (b >> 2) & 0x3;
    let p = mul_t1(a_lo, b_lo);
    let q = mul_t1(a_hi, b_hi);
    let r = mul_t1(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t1(q);
    lo | (hi << 2)
}

#[inline]
const fn scale_x_t3(a: u8) -> u8 {
    let lo = a & 0x0F;
    let hi = (a >> 4) & 0x0F;
    let s = scale_x_t2(hi);
    hi | ((lo ^ s) << 4)
}

#[inline]
const fn mul_t3(a: u8, b: u8) -> u8 {
    gf256_mul(Gf256(a), Gf256(b)).0
}

#[inline]
const fn scale_x_t4(a: u16) -> u16 {
    let lo = (a & 0xFF) as u8;
    let hi = ((a >> 8) & 0xFF) as u8;
    let s = scale_x_t3(hi);
    (hi as u16) | (((lo ^ s) as u16) << 8)
}

#[inline]
const fn mul_t4(a: u16, b: u16) -> u16 {
    let a_lo = (a & 0xFF) as u8;
    let a_hi = ((a >> 8) & 0xFF) as u8;
    let b_lo = (b & 0xFF) as u8;
    let b_hi = ((b >> 8) & 0xFF) as u8;
    let p = mul_t3(a_lo, b_lo);
    let q = mul_t3(a_hi, b_hi);
    let r = mul_t3(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t3(q);
    (lo as u16) | ((hi as u16) << 8)
}

#[inline]
const fn scale_x_t5(a: u32) -> u32 {
    let lo = (a & 0xFFFF) as u16;
    let hi = ((a >> 16) & 0xFFFF) as u16;
    let s = scale_x_t4(hi);
    (hi as u32) | (((lo ^ s) as u32) << 16)
}

#[inline]
const fn mul_t5(a: u32, b: u32) -> u32 {
    let a_lo = (a & 0xFFFF) as u16;
    let a_hi = ((a >> 16) & 0xFFFF) as u16;
    let b_lo = (b & 0xFFFF) as u16;
    let b_hi = ((b >> 16) & 0xFFFF) as u16;
    let p = mul_t4(a_lo, b_lo);
    let q = mul_t4(a_hi, b_hi);
    let r = mul_t4(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t4(q);
    (lo as u32) | ((hi as u32) << 16)
}

#[inline]
const fn scale_x_t6(a: u64) -> u64 {
    let lo = (a & 0xFFFF_FFFF) as u32;
    let hi = ((a >> 32) & 0xFFFF_FFFF) as u32;
    let s = scale_x_t5(hi);
    (hi as u64) | (((lo ^ s) as u64) << 32)
}

#[inline]
const fn mul_t6(a: u64, b: u64) -> u64 {
    let a_lo = (a & 0xFFFF_FFFF) as u32;
    let a_hi = ((a >> 32) & 0xFFFF_FFFF) as u32;
    let b_lo = (b & 0xFFFF_FFFF) as u32;
    let b_hi = ((b >> 32) & 0xFFFF_FFFF) as u32;
    let p = mul_t5(a_lo, b_lo);
    let q = mul_t5(a_hi, b_hi);
    let r = mul_t5(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t5(q);
    (lo as u64) | ((hi as u64) << 32)
}

/// Branchless addition (XOR) in `Gf16 = T_2`.
#[inline]
pub const fn gf16_add(a: Gf16, b: Gf16) -> Gf16 {
    Gf16((a.0 ^ b.0) & 0x0F)
}

/// Branchless stratified Karatsuba multiplication in `Gf16 = T_2`.
#[inline]
pub const fn gf16_mul(a: Gf16, b: Gf16) -> Gf16 {
    Gf16(mul_t2(a.0 & 0x0F, b.0 & 0x0F))
}

/// Branchless addition (XOR) in `Gf256 = T_3`.
#[inline]
pub const fn gf256_add(a: Gf256, b: Gf256) -> Gf256 {
    Gf256(a.0 ^ b.0)
}

/// Branchless stratified Karatsuba multiplication in `Gf256 = T_3`.
#[inline]
pub const fn gf256_mul(a: Gf256, b: Gf256) -> Gf256 {
    let a_lo = a.0 & 0x0F;
    let a_hi = (a.0 >> 4) & 0x0F;
    let b_lo = b.0 & 0x0F;
    let b_hi = (b.0 >> 4) & 0x0F;
    let p = mul_t2(a_lo, b_lo);
    let q = mul_t2(a_hi, b_hi);
    let r = mul_t2(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = gf16_add(Gf16(r ^ p ^ q), Gf16(scale_x_t2(q)));
    Gf256(lo | (hi.0 << 4))
}

/// Pure straight-line branchless Fermat inversion `a^254` in `Gf256` (`0` maps to `0`).
/// Executes 13 `gf256_mul` calls: 7 squarings and 6 additional multiplications,
/// with zero secret-dependent control flow in Rust source.
#[inline]
pub const fn gf256_inv_or_zero(a: Gf256) -> Gf256 {
    let a2 = gf256_mul(a, a);
    let a4 = gf256_mul(a2, a2);
    let a6 = gf256_mul(a4, a2);
    let a8 = gf256_mul(a4, a4);
    let a14 = gf256_mul(a8, a6);
    let a16 = gf256_mul(a8, a8);
    let a32 = gf256_mul(a16, a16);
    let a64 = gf256_mul(a32, a32);
    let a128 = gf256_mul(a64, a64);
    let hi = gf256_mul(gf256_mul(a128, a64), gf256_mul(a32, a16));
    gf256_mul(hi, a14)
}

/// Partial multiplicative inverse in `Gf256^*` for public Shamir denominators (`None` iff `a == 0`).
/// Always executes the full straight-line `gf256_inv_or_zero` Fermat chain unconditionally.
#[inline]
pub const fn gf256_inv(a: Gf256) -> Option<Gf256> {
    let inv = gf256_inv_or_zero(a);
    if inv.0 == 0 { None } else { Some(inv) }
}

/// Branchless Frobenius Booleanity residual `x^2 ⊕ x` over `Gf256 = T_3`.
/// Vanishes (`Gf256(0)`) if and only if `x` lies in the prime subfield `GF(2) = {0, 1}`.
#[inline]
pub const fn gf256_frobenius_residual(x: Gf256) -> Gf256 {
    gf256_add(gf256_mul(x, x), x)
}

/// Exact subfield Booleanity predicate `x^2 ⊕ x == 0` over `Gf256 = T_3`.
#[inline]
pub const fn gf256_is_boolean_frobenius(x: Gf256) -> bool {
    gf256_frobenius_residual(x).0 == 0
}

/// Subfield embedding `Gf256 = T_3 -> Tower128 = T_7`.
#[inline]
pub const fn embed_gf256_to_tower128(x: Gf256) -> Tower128 {
    Tower128(x.0 as u128)
}

/// Branchless addition (XOR) in `Tower128 = T_7`.
#[inline]
pub const fn tower128_add(a: Tower128, b: Tower128) -> Tower128 {
    Tower128(a.0 ^ b.0)
}

/// Branchless stratified Karatsuba multiplication in `Tower128 = T_7 = GF(2^128)`.
#[inline]
pub const fn tower128_mul(a: Tower128, b: Tower128) -> Tower128 {
    let a_lo = (a.0 & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let a_hi = ((a.0 >> 64) & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let b_lo = (b.0 & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let b_hi = ((b.0 >> 64) & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let p = mul_t6(a_lo, b_lo);
    let q = mul_t6(a_hi, b_hi);
    let r = mul_t6(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t6(q);
    Tower128((lo as u128) | ((hi as u128) << 64))
}
