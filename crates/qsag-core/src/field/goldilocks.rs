//! Canonical 64-bit Goldilocks field ($\mathbb{F}_p, p = 2^{64} - 2^{32} + 1$) and
//! 128-bit quadratic extension `GoldilocksExt2` ($\mathbb{F}_p[u]/(u^2 - 7)$).
//!
//! Matches `lean/Qsag/Math/Goldilocks.lean` down to every reduction identity and non-aliasing guard.

use alloc::vec::Vec;
use core::fmt;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::wipe::ct_eq_u64;

/// The Goldilocks prime $p = 2^{64} - 2^{32} + 1 = \text{0xFFFF\_FFFF\_0000\_0001}$.
pub const GOLDILOCKS_PRIME: u64 = qsag_asm::GOLDILOCKS_PRIME;

/// Reduction constant $\epsilon = 2^{32} - 1 = 2^{64} - p$.
pub const GOLDILOCKS_EPSILON: u64 = qsag_asm::GOLDILOCKS_EPSILON;

/// Multiplicative generator $g = 7$ of $\mathbb{F}_p^\times$ (and quadratic non-residue for $\mathbb{F}_{p^2}$).
pub const GOLDILOCKS_GENERATOR: u64 = qsag_accel::goldilocks::GOLDILOCKS_GENERATOR;

/// Primitive $2^{32}$-th root of unity $\omega_{2^{32}} = 7^{2^{32} - 1} \bmod p$.
pub const GOLDILOCKS_ROOT_2_32: u64 = qsag_accel::goldilocks::GOLDILOCKS_ROOT_2_32;

/// Maximum 2-adicity of $\mathbb{F}_p^\times$ ($2^{32} \mid p - 1$).
pub const GOLDILOCKS_TWO_ADICITY: u32 = qsag_accel::goldilocks::GOLDILOCKS_TWO_ADICITY;

/// Error returned when a 64-bit word lies in the non-canonical alias band $[p, 2^{64})$.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CanonicalLiftError {
    pub raw_value: u64,
}

impl fmt::Display for CanonicalLiftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "non-canonical Goldilocks encoding 0x{:016x} >= p (0x{:016x})",
            self.raw_value, GOLDILOCKS_PRIME
        )
    }
}

/// Canonical element of $\mathbb{F}_p$. Invariant: `self.0 < GOLDILOCKS_PRIME`.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Goldilocks(pub(crate) u64);

impl fmt::Debug for Goldilocks {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Goldilocks({})", self.0)
    }
}

/// Explicit witness-carrying canonical integer lift $< p$.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalLift(Goldilocks);

impl CanonicalLift {
    /// Strictly validate `raw < GOLDILOCKS_PRIME`, rejecting all $2^{32} - 1$ aliases in $[p, 2^{64})$.
    #[inline]
    pub const fn try_new(raw: u64) -> Result<Self, CanonicalLiftError> {
        if raw < GOLDILOCKS_PRIME {
            Ok(Self(Goldilocks(raw)))
        } else {
            Err(CanonicalLiftError { raw_value: raw })
        }
    }

    #[inline]
    pub const fn into_field(self) -> Goldilocks {
        self.0
    }

    #[inline]
    pub const fn value(self) -> u64 {
        self.0.0
    }
}

#[inline]
const fn exp_pow2(mut x: Goldilocks, mut k: u32) -> Goldilocks {
    while k > 0 {
        x = x.square();
        k -= 1;
    }
    x
}

impl Goldilocks {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    pub const TWO: Self = Self(2);
    pub const NON_RESIDUE: Self = Self(7);
    pub const NEG_ONE: Self = Self(GOLDILOCKS_PRIME - 1);

    /// Strict canonical lift: rejects every integer in $[p, 2^{64})$.
    #[inline]
    pub const fn from_canonical(raw: u64) -> Result<Self, CanonicalLiftError> {
        match CanonicalLift::try_new(raw) {
            Ok(lift) => Ok(lift.0),
            Err(err) => Err(err),
        }
    }

    /// Branchless canonicalization of an arbitrary `u64` modulo $p$ (`x < p ? x : x - p`).
    #[inline(always)]
    pub const fn from_u64_reduced(x: u64) -> Self {
        let (diff, borrow) = x.overflowing_sub(GOLDILOCKS_PRIME);
        let mask = (borrow as u64).wrapping_neg();
        Self((x & mask) | (diff & !mask))
    }

    /// Reduce `lo + 2^64 * hi` for `hi < 2^32`, using $2^{64} \equiv 2^{32} - 1 \pmod p$.
    #[inline(always)]
    pub const fn reduce96(lo: u64, hi: u64) -> Self {
        debug_assert!(hi >> 32 == 0);
        let adj = (hi << 32).wrapping_sub(hi);
        let (s, c) = lo.overflowing_add(adj);
        Self::from_u64_reduced(s.wrapping_add((c as u64).wrapping_neg() & GOLDILOCKS_EPSILON))
    }

    /// `7 * self` (the quadratic non-residue) without a 64x64 multiplication.
    #[inline(always)]
    pub const fn mul_by_7(self) -> Self {
        let v = self.0 as u128;
        let prod = (v << 3) - v;
        Self::reduce96(prod as u64, (prod >> 64) as u64)
    }

    /// Branchless 128-to-64 Goldilocks modular reduction.
    #[inline(always)]
    pub const fn reduce128(x: u128) -> Self {
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        let hi_lo = hi & GOLDILOCKS_EPSILON;
        let hi_hi = hi >> 32;
        let mid = (hi_lo << 32).wrapping_sub(hi_lo);
        let lo_c = Self::from_u64_reduced(lo);
        lo_c.const_add(Self(mid)).const_sub(Self(hi_hi))
    }

    /// Reduce an arbitrary 128-bit integer modulo $p$ (used for 128-bit challenge squeezing).
    #[inline]
    pub const fn from_u128_reduced(x: u128) -> Self {
        Self::reduce128(x)
    }

    /// Branchless 192-bit (`24` little-endian bytes) to `Goldilocks` reduction (`[P1-01]`).
    ///
    /// Because $2^{96} = (2^{32} + 1)p - 1 \equiv -1 \pmod p$, we have
    /// $\text{lo}_{96} + 2^{96} \text{hi}_{96} \equiv \text{lo}_{96} - \text{hi}_{96} \pmod p$,
    /// and $2^{192} \equiv 1 \pmod p$, achieving $< 2^{-192}$ statistical distance from uniform
    /// with **zero branches and zero rejection loops**!
    #[inline]
    pub const fn from_bytes24_unbiased(bytes: &[u8; 24]) -> Self {
        let mut lo_b = [0u8; 16];
        let mut hi_b = [0u8; 16];
        let mut i = 0usize;
        while i < 12 {
            lo_b[i] = bytes[i];
            hi_b[i] = bytes[12 + i];
            i += 1;
        }
        let lo96 = u128::from_le_bytes(lo_b);
        let hi96 = u128::from_le_bytes(hi_b);
        Self::reduce128(lo96).const_sub(Self::reduce128(hi96))
    }

    /// Return the guaranteed-canonical representative in $[0, p - 1]$.
    #[inline(always)]
    pub const fn to_canonical_u64(self) -> u64 {
        self.0
    }

    /// Alias for [`Self::to_canonical_u64`].
    #[inline(always)]
    pub const fn canonical(self) -> u64 {
        self.0
    }

    #[inline]
    pub const fn to_be_bytes(self) -> [u8; 8] {
        self.0.to_be_bytes()
    }

    #[inline]
    pub const fn to_le_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    #[inline]
    pub const fn from_be_bytes_canonical(bytes: [u8; 8]) -> Result<Self, CanonicalLiftError> {
        Self::from_canonical(u64::from_be_bytes(bytes))
    }

    #[inline]
    pub const fn from_le_bytes_canonical(bytes: [u8; 8]) -> Result<Self, CanonicalLiftError> {
        Self::from_canonical(u64::from_le_bytes(bytes))
    }

    /// Constant-time equality over secret `Goldilocks` shares.
    #[inline]
    pub fn ct_eq(self, rhs: Self) -> bool {
        ct_eq_u64(self.0, rhs.0)
    }

    /// Branchless modular addition.
    #[inline(always)]
    pub const fn const_add(self, rhs: Self) -> Self {
        let rem_p = GOLDILOCKS_PRIME - rhs.0;
        let (diff, borrow) = self.0.overflowing_sub(rem_p);
        let plain_sum = self.0.wrapping_add(rhs.0);
        let mask = (borrow as u64).wrapping_neg();
        Self((plain_sum & mask) | (diff & !mask))
    }

    /// Branchless modular subtraction.
    #[inline(always)]
    pub const fn const_sub(self, rhs: Self) -> Self {
        let (diff, borrow) = self.0.overflowing_sub(rhs.0);
        let adj = (borrow as u64).wrapping_neg() & GOLDILOCKS_PRIME;
        Self(diff.wrapping_add(adj))
    }

    /// Branchless negation (`0 - self mod p`).
    #[inline(always)]
    pub const fn const_neg(self) -> Self {
        Self::ZERO.const_sub(self)
    }

    /// Branchless modular multiplication via 128-to-64 shift/mask reduction.
    #[inline(always)]
    pub const fn const_mul(self, rhs: Self) -> Self {
        Self::reduce128((self.0 as u128) * (rhs.0 as u128))
    }

    #[inline(always)]
    pub const fn square(self) -> Self {
        self.const_mul(self)
    }

    /// Public-exponent binary exponentiation.
    #[inline]
    pub const fn pow(self, mut exp: u64) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        while exp > 0 {
            if (exp & 1) == 1 {
                acc = acc.const_mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }

    /// Fixed addition chain $a^{p - 2} \bmod p$ (`0` maps to `0` unconditionally without data branch).
    #[inline]
    pub const fn inv_or_zero(self) -> Self {
        let t2 = self.square().const_mul(self);
        let t3 = t2.square().const_mul(self);
        let t6 = exp_pow2(t3, 3).const_mul(t3);
        let t12 = exp_pow2(t6, 6).const_mul(t6);
        let t24 = exp_pow2(t12, 12).const_mul(t12);
        let t30 = exp_pow2(t24, 6).const_mul(t6);
        let t31 = t30.square().const_mul(self);
        let t32 = t31.square().const_mul(self);
        let hi = exp_pow2(t31, 33);
        hi.const_mul(t32)
    }

    /// Fixed-work inverse, mapping zero to zero without a secret-dependent branch.
    #[inline]
    pub const fn inv(self) -> Self {
        self.inv_or_zero()
    }

    /// Checked inverse for public validation (`None` iff `self == ZERO`).
    #[inline]
    pub const fn checked_inv(self) -> Option<Self> {
        let cand = self.inv_or_zero();
        if self.0 == 0 { None } else { Some(cand) }
    }
}

impl Add for Goldilocks {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}

impl AddAssign for Goldilocks {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}

impl Sub for Goldilocks {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}

impl SubAssign for Goldilocks {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}

impl Neg for Goldilocks {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        self.const_neg()
    }
}

impl Mul for Goldilocks {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self(qsag_asm::goldilocks_mul_ct(self.0, rhs.0))
    }
}

impl MulAssign for Goldilocks {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

/// Quadratic extension $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$ ($|\mathbb{F}_{p^2}| = p^2 > 2^{127}$).
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GoldilocksExt2 {
    pub c0: Goldilocks,
    pub c1: Goldilocks,
}

impl fmt::Debug for GoldilocksExt2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Ext2({} + {}*u)",
            self.c0.to_canonical_u64(),
            self.c1.to_canonical_u64()
        )
    }
}

impl GoldilocksExt2 {
    pub const ZERO: Self = Self {
        c0: Goldilocks::ZERO,
        c1: Goldilocks::ZERO,
    };
    pub const ONE: Self = Self {
        c0: Goldilocks::ONE,
        c1: Goldilocks::ZERO,
    };
    pub const U_BASIS: Self = Self {
        c0: Goldilocks::ZERO,
        c1: Goldilocks::ONE,
    };

    #[inline(always)]
    pub const fn new(c0: Goldilocks, c1: Goldilocks) -> Self {
        Self { c0, c1 }
    }

    #[inline(always)]
    pub const fn from_base(c0: Goldilocks) -> Self {
        Self {
            c0,
            c1: Goldilocks::ZERO,
        }
    }

    #[inline]
    pub const fn from_canonical_u64_pair(c0: u64, c1: u64) -> Result<Self, CanonicalLiftError> {
        let a0 = match Goldilocks::from_canonical(c0) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        let a1 = match Goldilocks::from_canonical(c1) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        Ok(Self { c0: a0, c1: a1 })
    }

    #[inline]
    pub const fn to_be_bytes(self) -> [u8; 16] {
        let b0 = self.c0.to_be_bytes();
        let b1 = self.c1.to_be_bytes();
        [
            b0[0], b0[1], b0[2], b0[3], b0[4], b0[5], b0[6], b0[7], b1[0], b1[1], b1[2], b1[3],
            b1[4], b1[5], b1[6], b1[7],
        ]
    }

    #[inline]
    pub const fn from_be_bytes_canonical(bytes: [u8; 16]) -> Result<Self, CanonicalLiftError> {
        let b0 = [
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ];
        let b1 = [
            bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        ];
        let c0 = match Goldilocks::from_be_bytes_canonical(b0) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        let c1 = match Goldilocks::from_be_bytes_canonical(b1) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        Ok(Self { c0, c1 })
    }

    /// Constant-time equality over secret/MAC `GoldilocksExt2` elements.
    #[inline]
    pub fn ct_eq(self, rhs: Self) -> bool {
        let d0 = self.c0.0 ^ rhs.c0.0;
        let d1 = self.c1.0 ^ rhs.c1.0;
        ct_eq_u64(d0 | d1, 0)
    }

    #[inline(always)]
    pub const fn const_add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0.const_add(rhs.c0),
            c1: self.c1.const_add(rhs.c1),
        }
    }

    #[inline(always)]
    pub const fn const_sub(self, rhs: Self) -> Self {
        Self {
            c0: self.c0.const_sub(rhs.c0),
            c1: self.c1.const_sub(rhs.c1),
        }
    }

    #[inline(always)]
    pub const fn const_neg(self) -> Self {
        Self {
            c0: self.c0.const_neg(),
            c1: self.c1.const_neg(),
        }
    }

    /// $(a_0 + a_1 u)(b_0 + b_1 u) = (a_0 b_0 + 7 a_1 b_1) + (a_0 b_1 + a_1 b_0) u$.
    #[inline(always)]
    pub const fn const_mul(self, rhs: Self) -> Self {
        let a0b0 = self.c0.const_mul(rhs.c0);
        let a1b1 = self.c1.const_mul(rhs.c1);
        let sum_a = self.c0.const_add(self.c1);
        let sum_b = rhs.c0.const_add(rhs.c1);
        let c1 = sum_a.const_mul(sum_b).const_sub(a0b0).const_sub(a1b1);
        let c0 = a0b0.const_add(a1b1.mul_by_7());
        Self { c0, c1 }
    }

    #[inline(always)]
    pub const fn mul_base(self, scalar: Goldilocks) -> Self {
        Self {
            c0: self.c0.const_mul(scalar),
            c1: self.c1.const_mul(scalar),
        }
    }

    /// `(c_0^2 + 7 c_1^2) + 2 c_0 c_1 u`: two base squarings and one base product.
    #[inline(always)]
    pub const fn square(self) -> Self {
        let ab = self.c0.const_mul(self.c1);
        Self {
            c0: self.c0.square().const_add(self.c1.square().mul_by_7()),
            c1: ab.const_add(ab),
        }
    }

    #[inline(always)]
    pub const fn conj(self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c1.const_neg(),
        }
    }

    #[inline(always)]
    pub const fn norm(self) -> Goldilocks {
        let a0_sq = self.c0.square();
        let a1_sq = self.c1.square();
        a0_sq.const_sub(a1_sq.mul_by_7())
    }

    #[inline]
    pub const fn inv(self) -> Option<Self> {
        match self.norm().checked_inv() {
            Some(norm_inv) => Some(self.conj().mul_base(norm_inv)),
            None => None,
        }
    }
}

impl Add for GoldilocksExt2 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}

impl AddAssign for GoldilocksExt2 {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}

impl Sub for GoldilocksExt2 {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}

impl SubAssign for GoldilocksExt2 {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}

impl Neg for GoldilocksExt2 {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        self.const_neg()
    }
}

impl Mul for GoldilocksExt2 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}

impl MulAssign for GoldilocksExt2 {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

pub use crate::wipe::{wipe_ext2, wipe_goldilocks};

/// Evaluate polynomial `coeffs[0] + coeffs[1]*x + ...` over `Goldilocks`.
#[inline]
pub fn eval_poly_goldilocks(coeffs: &[Goldilocks], x: Goldilocks) -> Goldilocks {
    let mut acc = Goldilocks::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.const_mul(x).const_add(c);
    }
    acc
}

/// Evaluate polynomial over `GoldilocksExt2` at base-field coordinate `x`.
#[inline]
pub fn eval_poly_ext2_at_base(coeffs: &[GoldilocksExt2], x: Goldilocks) -> GoldilocksExt2 {
    let xb = GoldilocksExt2::from_base(x);
    let mut acc = GoldilocksExt2::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.const_mul(xb).const_add(c);
    }
    acc
}

/// Evaluate polynomial over `GoldilocksExt2` at extension-field coordinate `x`.
#[inline]
pub fn eval_poly_ext2(coeffs: &[GoldilocksExt2], x: GoldilocksExt2) -> GoldilocksExt2 {
    let mut acc = GoldilocksExt2::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.const_mul(x).const_add(c);
    }
    acc
}

/// Compute Lagrange interpolation weights at `0` for distinct non-zero `Goldilocks` points.
pub fn lagrange_weights_zero_goldilocks(pts: &[Goldilocks]) -> Option<Vec<Goldilocks>> {
    let t = pts.len();
    let mut weights = Vec::with_capacity(t);
    for i in 0..t {
        if pts[i] == Goldilocks::ZERO {
            return None;
        }
        let mut num = Goldilocks::ONE;
        let mut den = Goldilocks::ONE;
        for j in 0..t {
            if i == j {
                continue;
            }
            let diff = pts[j].const_sub(pts[i]);
            if diff == Goldilocks::ZERO {
                return None;
            }
            num = num.const_mul(pts[j]);
            den = den.const_mul(diff);
        }
        weights.push(num.const_mul(den.checked_inv()?));
    }
    Some(weights)
}

impl core::error::Error for CanonicalLiftError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_lift_rejects_alias_band() {
        assert!(CanonicalLift::try_new(GOLDILOCKS_PRIME - 1).is_ok());
        assert!(CanonicalLift::try_new(GOLDILOCKS_PRIME).is_err());
        assert!(CanonicalLift::try_new(u64::MAX).is_err());
        assert!(Goldilocks::from_be_bytes_canonical(GOLDILOCKS_PRIME.to_be_bytes()).is_err());
    }

    #[test]
    fn goldilocks_and_ext2_field_laws() {
        let vals = [
            0u64,
            1,
            2,
            7,
            (1u64 << 32) - 1,
            1u64 << 32,
            GOLDILOCKS_PRIME - 2,
            GOLDILOCKS_PRIME - 1,
        ];
        let p = GOLDILOCKS_PRIME as u128;
        for &ar in &vals {
            let a = Goldilocks::from_canonical(ar).unwrap();
            assert_eq!(
                a.mul_by_7().to_canonical_u64(),
                ((ar as u128 * 7) % p) as u64
            );
            for hi in [0u64, 1, 6, (1 << 32) - 1] {
                assert_eq!(
                    Goldilocks::reduce96(ar, hi).to_canonical_u64(),
                    ((ar as u128 + ((hi as u128) << 64)) % p) as u64
                );
            }
            if ar != 0 {
                assert_eq!(a * a.inv(), Goldilocks::ONE);
            } else {
                assert_eq!(a.inv(), Goldilocks::ZERO);
            }
            for &br in &vals {
                let b = Goldilocks::from_canonical(br).unwrap();
                assert_eq!(
                    (a + b).to_canonical_u64(),
                    ((ar as u128 + br as u128) % p) as u64
                );
                assert_eq!(
                    (a - b).to_canonical_u64(),
                    ((ar as u128 + p - br as u128) % p) as u64
                );
                assert_eq!(
                    (a * b).to_canonical_u64(),
                    ((ar as u128 * br as u128) % p) as u64
                );
                assert_eq!(a.const_mul(b), a * b);
                // Schoolbook product and square over u^2 = 7.
                let (e, g) = (GoldilocksExt2::new(a, b), GoldilocksExt2::new(b, a + a));
                let seven = Goldilocks::NON_RESIDUE;
                assert_eq!(
                    e * g,
                    GoldilocksExt2::new(a * b + seven * b * (a + a), a * (a + a) + b * b)
                );
                assert_eq!(
                    e.square(),
                    GoldilocksExt2::new(a * a + seven * b * b, a * b + a * b)
                );
                assert_eq!(e.norm(), a * a - seven * b * b);
            }
        }
        let x = GoldilocksExt2::from_canonical_u64_pair(GOLDILOCKS_PRIME - 5, 123_456_789).unwrap();
        let y = GoldilocksExt2::from_canonical_u64_pair(987_654_321, GOLDILOCKS_PRIME - 2).unwrap();
        let z = GoldilocksExt2::from_canonical_u64_pair(42, 777).unwrap();
        assert_eq!((x + y) * z, x * z + y * z);
        assert_eq!((x * y) * z, x * (y * z));
        assert_eq!(x * x.inv().unwrap(), GoldilocksExt2::ONE);
        assert!(x.ct_eq(x));
        assert!(!x.ct_eq(y));
    }
}
