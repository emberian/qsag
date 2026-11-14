//! Canonical 64-bit Goldilocks prime field (`p = 2^64 - 2^32 + 1`) and
//! quadratic extension `GoldilocksExt2` (`F_p[u] / (u^2 - 7)`), written in
//! branchless, borrow-checker-clean `#![no_std]` safe Rust for `Charon` + `Aeneas` MIR extraction.
//!
//! Security Invariant: Every field arithmetic operation (`goldilocks_canon`,
//! `goldilocks_add`, `goldilocks_sub`, `goldilocks_neg`, `goldilocks_reduce128`, `goldilocks_mul`,
//! `goldilocks_square`, `goldilocks_pow7`, `goldilocks_inv_or_zero`, and all `GoldilocksExt2` ops)
//! uses branch-free arithmetic expressions with zero secret-dependent control flow in Rust source.

/// The Goldilocks prime `p = 2^64 - 2^32 + 1 = 0xFFFF_FFFF_0000_0001`.
pub const GOLDILOCKS_PRIME: u64 = 0xFFFF_FFFF_0000_0001;

/// Reduction constant `epsilon = 2^32 - 1 = 2^64 - p`.
pub const GOLDILOCKS_EPSILON: u64 = 0xFFFF_FFFF;

/// Quadratic non-residue `u^2 = 7` defining `GoldilocksExt2`.
pub const GOLDILOCKS_NON_RESIDUE: u64 = 7;

/// Error returned when a public wire 64-bit word lies in the non-canonical alias band `[p, 2^64)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CanonicalLiftError {
    pub raw_value: u64,
}

/// Canonical element of `F_p` (`0 <= self.0 < GOLDILOCKS_PRIME`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Goldilocks(pub u64);

/// Quadratic extension element `c0 + c1 * u` in `F_p[u] / (u^2 - 7)`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GoldilocksExt2 {
    pub c0: Goldilocks,
    pub c1: Goldilocks,
}

/// Strict canonical lift for untrusted public wire inputs, rejecting `[p, 2^64)`.
#[inline]
pub const fn goldilocks_from_canonical(raw: u64) -> Result<Goldilocks, CanonicalLiftError> {
    if raw < GOLDILOCKS_PRIME {
        Ok(Goldilocks(raw))
    } else {
        Err(CanonicalLiftError { raw_value: raw })
    }
}

/// Branchless constant-time canonical reduction `x mod p` in `[0, p)`.
///
/// Computes `d = 2^64 + x - p` in `u128` (`1 <= d < 2^65`, never overflowing or underflowing):
/// - Bit 64 `ge = (d >> 64) & 1` is `1` iff `x >= p`, and `0` iff `x < p`.
/// - Adding `p * (1 - ge)` yields `2^64 + (x mod p)`, whose low 64 bits equal `x mod p` with
///   zero secret-dependent control flow in Rust source.
#[inline]
pub const fn goldilocks_canon(x: u64) -> Goldilocks {
    let d: u128 = (1u128 << 64) + (x as u128) - (GOLDILOCKS_PRIME as u128);
    let ge: u128 = (d >> 64) & 1;
    let adj: u128 = (GOLDILOCKS_PRIME as u128) * (1 - ge);
    Goldilocks(((d + adj) & 0xFFFF_FFFF_FFFF_FFFF) as u64)
}

/// Branchless, overflow-free canonical modular addition `(a + b) mod p` in `[0, p)`.
///
/// For canonical `ca, cb < p`, `sum = ca + cb <= 2p - 2 < 2^64 + p`, so
/// `d = 2^64 + sum - p` satisfies `1 <= d < 2^65`:
/// - `ge = (d >> 64) & 1 == 1` iff `sum >= p` (giving low 64 bits `sum - p`),
/// - `ge == 0` iff `sum < p` (adding `p` restores `2^64 + sum`, giving low 64 bits `sum`).
#[inline]
pub const fn goldilocks_add(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    let ca = goldilocks_canon(a.0).0;
    let cb = goldilocks_canon(b.0).0;
    let sum: u128 = (ca as u128) + (cb as u128);
    let d: u128 = (1u128 << 64) + sum - (GOLDILOCKS_PRIME as u128);
    let ge: u128 = (d >> 64) & 1;
    let adj: u128 = (GOLDILOCKS_PRIME as u128) * (1 - ge);
    Goldilocks(((d + adj) & 0xFFFF_FFFF_FFFF_FFFF) as u64)
}

/// Branchless, overflow-free canonical modular subtraction `(a - b) mod p` in `[0, p)`.
///
/// For canonical `ca, cb < p`, `d = 2^64 + ca - cb` satisfies `2^64 - p < d < 2^64 + p < 2^65`:
/// - `ge = (d >> 64) & 1 == 1` iff `ca >= cb` (giving low 64 bits `ca - cb`),
/// - `ge == 0` iff `ca < cb` (adding `p` yields `2^64 + ca + p - cb`, giving `ca + p - cb`).
#[inline]
pub const fn goldilocks_sub(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    let ca = goldilocks_canon(a.0).0;
    let cb = goldilocks_canon(b.0).0;
    let d: u128 = (1u128 << 64) + (ca as u128) - (cb as u128);
    let ge: u128 = (d >> 64) & 1;
    let adj: u128 = (GOLDILOCKS_PRIME as u128) * (1 - ge);
    Goldilocks(((d + adj) & 0xFFFF_FFFF_FFFF_FFFF) as u64)
}

/// Branchless canonical modular negation `(-a) mod p` in `[0, p)`.
#[inline]
pub const fn goldilocks_neg(a: Goldilocks) -> Goldilocks {
    goldilocks_sub(Goldilocks(0), a)
}

/// Exact branchless 128-to-64 Goldilocks shift/mask modular reduction `x mod p` in `[0, p)`.
/// Uses `2^64 ≡ 2^32 - 1 (mod p)` and `2^96 ≡ -1 (mod p)`:
/// `x = lo + 2^64 * hi_lo + 2^96 * hi_hi ≡ lo + (hi_lo * 2^32 - hi_lo) - hi_hi (mod p)`.
#[inline]
pub const fn goldilocks_reduce128(x: u128) -> Goldilocks {
    let lo = (x & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let hi = (x >> 64) as u64;
    let hi_lo = hi & GOLDILOCKS_EPSILON;
    let hi_hi = hi >> 32;
    let mid = (hi_lo << 32) - hi_lo;
    let sum = goldilocks_add(Goldilocks(lo), Goldilocks(mid));
    goldilocks_sub(sum, Goldilocks(hi_hi))
}

/// Branchless canonical modular multiplication `(a * b) mod p` in `[0, p)`.
#[inline]
pub const fn goldilocks_mul(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    let ca = goldilocks_canon(a.0).0;
    let cb = goldilocks_canon(b.0).0;
    let prod = (ca as u128) * (cb as u128);
    goldilocks_reduce128(prod)
}

/// Branchless canonical modular squaring `a^2 mod p`.
#[inline]
pub const fn goldilocks_square(a: Goldilocks) -> Goldilocks {
    goldilocks_mul(a, a)
}

/// Branchless Poseidon2 monomial S-box `x -> x^7 mod p` via 4 canonical multiplications (`gcd(7, p - 1) = 1`).
#[inline]
pub const fn goldilocks_pow7(x: Goldilocks) -> Goldilocks {
    let x2 = goldilocks_mul(x, x);
    let x3 = goldilocks_mul(x2, x);
    let x4 = goldilocks_mul(x2, x2);
    goldilocks_mul(x3, x4)
}

#[inline]
const fn goldilocks_sq3(x: Goldilocks) -> Goldilocks {
    goldilocks_square(goldilocks_square(goldilocks_square(x)))
}

#[inline]
const fn goldilocks_sq6(x: Goldilocks) -> Goldilocks {
    goldilocks_sq3(goldilocks_sq3(x))
}

#[inline]
const fn goldilocks_sq12(x: Goldilocks) -> Goldilocks {
    goldilocks_sq6(goldilocks_sq6(x))
}

#[inline]
const fn goldilocks_sq33(x: Goldilocks) -> Goldilocks {
    let s24 = goldilocks_sq12(goldilocks_sq12(x));
    goldilocks_sq3(goldilocks_sq6(s24))
}

/// Straight-line, loop-free, branchless Fermat inversion `a^(p - 2) mod p` (`0` maps to `0`).
/// Executes a fixed sequence of 64 squarings and 9 additional multiplications with zero secret-dependent control flow in Rust source.
#[inline]
pub const fn goldilocks_inv_or_zero(a: Goldilocks) -> Goldilocks {
    let c = goldilocks_canon(a.0);
    let t2 = goldilocks_mul(goldilocks_square(c), c);
    let t3 = goldilocks_mul(goldilocks_square(t2), c);
    let t6 = goldilocks_mul(goldilocks_sq3(t3), t3);
    let t12 = goldilocks_mul(goldilocks_sq6(t6), t6);
    let t24 = goldilocks_mul(goldilocks_sq12(t12), t12);
    let t30 = goldilocks_mul(goldilocks_sq6(t24), t6);
    let t31 = goldilocks_mul(goldilocks_square(t30), c);
    let t32 = goldilocks_mul(goldilocks_square(t31), c);
    let hi = goldilocks_sq33(t31);
    goldilocks_mul(hi, t32)
}

/// Partial multiplicative inverse in `F_p^*` for public denominators (`None` iff `a mod p == 0`).
/// Always executes the full straight-line `goldilocks_inv_or_zero` Fermat chain unconditionally.
#[inline]
pub const fn goldilocks_inv(a: Goldilocks) -> Option<Goldilocks> {
    let inv = goldilocks_inv_or_zero(a);
    if inv.0 == 0 { None } else { Some(inv) }
}

/// Branchless addition in `GoldilocksExt2 = F_p[u] / (u^2 - 7)`.
#[inline]
pub const fn goldilocks_ext2_add(a: GoldilocksExt2, b: GoldilocksExt2) -> GoldilocksExt2 {
    GoldilocksExt2 {
        c0: goldilocks_add(a.c0, b.c0),
        c1: goldilocks_add(a.c1, b.c1),
    }
}

/// Branchless subtraction in `GoldilocksExt2 = F_p[u] / (u^2 - 7)`.
#[inline]
pub const fn goldilocks_ext2_sub(a: GoldilocksExt2, b: GoldilocksExt2) -> GoldilocksExt2 {
    GoldilocksExt2 {
        c0: goldilocks_sub(a.c0, b.c0),
        c1: goldilocks_sub(a.c1, b.c1),
    }
}

/// Branchless negation in `GoldilocksExt2 = F_p[u] / (u^2 - 7)`.
#[inline]
pub const fn goldilocks_ext2_neg(a: GoldilocksExt2) -> GoldilocksExt2 {
    GoldilocksExt2 {
        c0: goldilocks_neg(a.c0),
        c1: goldilocks_neg(a.c1),
    }
}

/// Branchless Karatsuba multiplication `(a0 + a1*u)(b0 + b1*u) = (a0*b0 + 7*a1*b1) + (a0*b1 + a1*b0)*u`
/// in `GoldilocksExt2 = F_p[u] / (u^2 - 7)`.
#[inline]
pub const fn goldilocks_ext2_mul(a: GoldilocksExt2, b: GoldilocksExt2) -> GoldilocksExt2 {
    let a0b0 = goldilocks_mul(a.c0, b.c0);
    let a1b1 = goldilocks_mul(a.c1, b.c1);
    let sum_a = goldilocks_add(a.c0, a.c1);
    let sum_b = goldilocks_add(b.c0, b.c1);
    let prod_sum = goldilocks_mul(sum_a, sum_b);
    let c1 = goldilocks_sub(goldilocks_sub(prod_sum, a0b0), a1b1);
    let seven_a1b1 = goldilocks_mul(Goldilocks(GOLDILOCKS_NON_RESIDUE), a1b1);
    let c0 = goldilocks_add(a0b0, seven_a1b1);
    GoldilocksExt2 { c0, c1 }
}
