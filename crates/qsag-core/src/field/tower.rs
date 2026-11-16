//! Wiedemann binary tower $\mathcal{T}_0 \subset \mathcal{T}_1 \subset \dots \subset \mathcal{T}_7$
//! (`TowerGf256` = $\mathcal{T}_3 = \mathbb{F}_{2^8}$ for Shamir sharing up to $n \le 255$ parties,
//! `Tower128` = $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$ for 2-lane BDOZ MACs and triple sacrifice).
//!
//! Includes [`PublicGf256Matrix`]: precomputed Four-Russians nibble XOR schedule for **public**
//! Lagrange/Vandermonde scalars ($\sim 7\times$ fewer instructions than 64-mask bit-by-bit scaling),
//! paired with 100% branchless [`bs_gf256_scale_secret_ct`] for secret scalars.

use alloc::vec::Vec;
use core::hint::black_box;

use crate::wipe::ct_eq_u128;

#[inline(always)]
const fn scale_x_t1(a: u8) -> u8 {
    let lo = a & 1;
    let hi = (a >> 1) & 1;
    hi | ((lo ^ hi) << 1)
}

#[inline(always)]
const fn scale_x_t2(a: u8) -> u8 {
    let lo = a & 0x3;
    let hi = (a >> 2) & 0x3;
    hi | ((lo ^ scale_x_t1(hi)) << 2)
}

#[inline(always)]
const fn scale_x_t3(a: u8) -> u8 {
    let lo = a & 0xF;
    let hi = a >> 4;
    hi | ((lo ^ scale_x_t2(hi)) << 4)
}

#[inline(always)]
const fn scale_x_t4(a: u16) -> u16 {
    let lo = (a & 0xFF) as u8;
    let hi = (a >> 8) as u8;
    (hi as u16) | (((lo ^ scale_x_t3(hi)) as u16) << 8)
}

#[inline(always)]
const fn scale_x_t5(a: u32) -> u32 {
    let lo = (a & 0xFFFF) as u16;
    let hi = (a >> 16) as u16;
    (hi as u32) | (((lo ^ scale_x_t4(hi)) as u32) << 16)
}

#[inline(always)]
const fn scale_x_t6(a: u64) -> u64 {
    let lo = (a & 0xFFFF_FFFF) as u32;
    let hi = (a >> 32) as u32;
    (hi as u64) | (((lo ^ scale_x_t5(hi)) as u64) << 32)
}

#[inline(always)]
const fn tower_mul_t1(a: u8, b: u8) -> u8 {
    let a0 = a & 1;
    let a1 = (a >> 1) & 1;
    let b0 = b & 1;
    let b1 = (b >> 1) & 1;
    let p = a0 & b0;
    let q = a1 & b1;
    let r = (a0 ^ a1) & (b0 ^ b1);
    (p ^ q) | ((r ^ p) << 1)
}

#[inline(always)]
const fn tower_mul_t2(a: u8, b: u8) -> u8 {
    let a0 = a & 0x3;
    let a1 = (a >> 2) & 0x3;
    let b0 = b & 0x3;
    let b1 = (b >> 2) & 0x3;
    let p = tower_mul_t1(a0, b0);
    let q = tower_mul_t1(a1, b1);
    let r = tower_mul_t1(a0 ^ a1, b0 ^ b1);
    (p ^ q) | ((r ^ p ^ q ^ scale_x_t1(q)) << 2)
}

#[inline(always)]
pub const fn tower_mul_t3(a: u8, b: u8) -> u8 {
    let a0 = a & 0xF;
    let a1 = a >> 4;
    let b0 = b & 0xF;
    let b1 = b >> 4;
    let p = tower_mul_t2(a0, b0);
    let q = tower_mul_t2(a1, b1);
    let r = tower_mul_t2(a0 ^ a1, b0 ^ b1);
    (p ^ q) | ((r ^ p ^ q ^ scale_x_t2(q)) << 4)
}

#[inline(always)]
const fn tower_mul_t4(a: u16, b: u16) -> u16 {
    let a0 = (a & 0xFF) as u8;
    let a1 = (a >> 8) as u8;
    let b0 = (b & 0xFF) as u8;
    let b1 = (b >> 8) as u8;
    let p = tower_mul_t3(a0, b0);
    let q = tower_mul_t3(a1, b1);
    let r = tower_mul_t3(a0 ^ a1, b0 ^ b1);
    ((p ^ q) as u16) | (((r ^ p ^ q ^ scale_x_t3(q)) as u16) << 8)
}

#[inline]
const fn tower_mul_t5(a: u32, b: u32) -> u32 {
    let a0 = (a & 0xFFFF) as u16;
    let a1 = (a >> 16) as u16;
    let b0 = (b & 0xFFFF) as u16;
    let b1 = (b >> 16) as u16;
    let p = tower_mul_t4(a0, b0);
    let q = tower_mul_t4(a1, b1);
    let r = tower_mul_t4(a0 ^ a1, b0 ^ b1);
    ((p ^ q) as u32) | (((r ^ p ^ q ^ scale_x_t4(q)) as u32) << 16)
}

#[inline]
const fn tower_mul_t6(a: u64, b: u64) -> u64 {
    let a0 = (a & 0xFFFF_FFFF) as u32;
    let a1 = (a >> 32) as u32;
    let b0 = (b & 0xFFFF_FFFF) as u32;
    let b1 = (b >> 32) as u32;
    let p = tower_mul_t5(a0, b0);
    let q = tower_mul_t5(a1, b1);
    let r = tower_mul_t5(a0 ^ a1, b0 ^ b1);
    ((p ^ q) as u64) | (((r ^ p ^ q ^ scale_x_t5(q)) as u64) << 32)
}

#[inline(always)]
const fn swar_mul_x0_128(v: u128) -> u128 {
    const M1: u128 = 0x5555_5555_5555_5555_5555_5555_5555_5555;
    let lo = v & M1;
    let hi = (v >> 1) & M1;
    hi | ((lo ^ hi) << 1)
}

#[inline(always)]
const fn swar_mul_x1_128(v: u128) -> u128 {
    const M2: u128 = 0x3333_3333_3333_3333_3333_3333_3333_3333;
    let lo = v & M2;
    let hi = (v >> 2) & M2;
    hi | ((lo ^ swar_mul_x0_128(hi)) << 2)
}

#[inline(always)]
const fn swar_mul_x2_128(v: u128) -> u128 {
    const M4: u128 = 0x0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F;
    let lo = v & M4;
    let hi = (v >> 4) & M4;
    hi | ((lo ^ swar_mul_x1_128(hi)) << 4)
}

#[inline(always)]
const fn swar_mul_x3_128(v: u128) -> u128 {
    const M8: u128 = 0x00FF_00FF_00FF_00FF_00FF_00FF_00FF_00FF;
    let lo = v & M8;
    let hi = (v >> 8) & M8;
    hi | ((lo ^ swar_mul_x2_128(hi)) << 8)
}

#[inline(always)]
const fn swar_mul_x4_128(v: u128) -> u128 {
    const M16: u128 = 0x0000_FFFF_0000_FFFF_0000_FFFF_0000_FFFF;
    let lo = v & M16;
    let hi = (v >> 16) & M16;
    hi | ((lo ^ swar_mul_x3_128(hi)) << 16)
}

/// 100% branchless 4-lane SWAR multiplication in $\mathcal{T}_5^4 = (\mathbb{F}_{2^{32}})^4$ packed
/// inside a single `u128` register (`0` secret branches, `0` table lookups).
#[inline]
const fn swar_mul_t5_x4(x: u128, y: u128) -> u128 {
    const LANE_LSB_32: u128 = 0x0000_0001_0000_0001_0000_0001_0000_0001;
    let mut basis = [0u128; 32];
    basis[0] = x;
    basis[1] = swar_mul_x0_128(basis[0]);
    let mut j = 0usize;
    while j < 2 {
        basis[2 + j] = swar_mul_x1_128(basis[j]);
        j += 1;
    }
    let mut j = 0usize;
    while j < 4 {
        basis[4 + j] = swar_mul_x2_128(basis[j]);
        j += 1;
    }
    let mut j = 0usize;
    while j < 8 {
        basis[8 + j] = swar_mul_x3_128(basis[j]);
        j += 1;
    }
    let mut j = 0usize;
    while j < 16 {
        basis[16 + j] = swar_mul_x4_128(basis[j]);
        j += 1;
    }

    let mut acc = 0u128;
    let mut bit = 0usize;
    while bit < 32 {
        let lane_bits = (y >> bit) & LANE_LSB_32;
        let mask = lane_bits.wrapping_mul(0xFFFF_FFFF);
        acc ^= basis[bit] & mask;
        bit += 1;
    }
    acc
}

#[inline]
pub const fn tower_mul_t7_karatsuba_ref(a: u128, b: u128) -> u128 {
    let a0 = a as u64;
    let a1 = (a >> 64) as u64;
    let b0 = b as u64;
    let b1 = (b >> 64) as u64;
    let p = tower_mul_t6(a0, b0);
    let q = tower_mul_t6(a1, b1);
    let r = tower_mul_t6(a0 ^ a1, b0 ^ b1);
    ((p ^ q) as u128) | (((r ^ p ^ q ^ scale_x_t6(q)) as u128) << 64)
}

#[inline]
pub const fn tower_mul_t7(a: u128, b: u128) -> u128 {
    let a_lo = a as u64;
    let a_hi = (a >> 64) as u64;
    let a_xr = a_lo ^ a_hi;
    let b_lo = b as u64;
    let b_hi = (b >> 64) as u64;
    let b_xr = b_lo ^ b_hi;

    let a_lo0 = a_lo as u32;
    let a_lo1 = (a_lo >> 32) as u32;
    let a_hi0 = a_hi as u32;
    let a_hi1 = (a_hi >> 32) as u32;
    let a_xr0 = a_xr as u32;
    let a_xr1 = (a_xr >> 32) as u32;

    let b_lo0 = b_lo as u32;
    let b_lo1 = (b_lo >> 32) as u32;
    let b_hi0 = b_hi as u32;
    let b_hi1 = (b_hi >> 32) as u32;
    let b_xr0 = b_xr as u32;
    let b_xr1 = (b_xr >> 32) as u32;

    let x0 = (a_lo0 as u128)
        | ((a_lo1 as u128) << 32)
        | (((a_lo0 ^ a_lo1) as u128) << 64)
        | ((a_hi0 as u128) << 96);
    let y0 = (b_lo0 as u128)
        | ((b_lo1 as u128) << 32)
        | (((b_lo0 ^ b_lo1) as u128) << 64)
        | ((b_hi0 as u128) << 96);
    let z0 = swar_mul_t5_x4(x0, y0);

    let x1 = (a_hi1 as u128)
        | (((a_hi0 ^ a_hi1) as u128) << 32)
        | ((a_xr0 as u128) << 64)
        | ((a_xr1 as u128) << 96);
    let y1 = (b_hi1 as u128)
        | (((b_hi0 ^ b_hi1) as u128) << 32)
        | ((b_xr0 as u128) << 64)
        | ((b_xr1 as u128) << 96);
    let z1 = swar_mul_t5_x4(x1, y1);

    let p_p = z0 as u32;
    let p_q = (z0 >> 32) as u32;
    let p_r = (z0 >> 64) as u32;
    let q_p = (z0 >> 96) as u32;

    let q_q = z1 as u32;
    let q_r = (z1 >> 32) as u32;
    let r_p = (z1 >> 64) as u32;
    let r_q = (z1 >> 96) as u32;

    let r_r = tower_mul_t5(a_xr0 ^ a_xr1, b_xr0 ^ b_xr1);

    let p = ((p_p ^ p_q) as u64) | (((p_r ^ p_p ^ p_q ^ scale_x_t5(p_q)) as u64) << 32);
    let q = ((q_p ^ q_q) as u64) | (((q_r ^ q_p ^ q_q ^ scale_x_t5(q_q)) as u64) << 32);
    let r = ((r_p ^ r_q) as u64) | (((r_r ^ r_p ^ r_q ^ scale_x_t5(r_q)) as u64) << 32);
    ((p ^ q) as u128) | (((r ^ p ^ q ^ scale_x_t6(q)) as u128) << 64)
}

#[inline]
const fn tower_scale_x_bits(k: u32, a: u128) -> u128 {
    if k == 0 {
        a & 1
    } else {
        let half = 1u32 << (k - 1);
        let mask = if half == 128 {
            u128::MAX
        } else {
            (1u128 << half) - 1
        };
        let lo = a & mask;
        let hi = (a >> half) & mask;
        let scaled_hi = tower_scale_x_bits(k - 1, hi);
        hi | ((lo ^ scaled_hi) << half)
    }
}

/// Constant-time branchless multiplication in Wiedemann tower level $\mathcal{T}_k$ ($0 \le k \le 7$).
/// Dispatches statically on public level `k` into unrolled register-width Karatsuba circuits (`0` secret branches).
#[inline]
pub const fn tower_mul_bits(k: u32, a: u128, b: u128) -> u128 {
    match k {
        0 => (a & 1) & (b & 1),
        1 => tower_mul_t1((a & 0x3) as u8, (b & 0x3) as u8) as u128,
        2 => tower_mul_t2((a & 0xF) as u8, (b & 0xF) as u8) as u128,
        3 => tower_mul_t3(a as u8, b as u8) as u128,
        4 => tower_mul_t4(a as u16, b as u16) as u128,
        5 => tower_mul_t5(a as u32, b as u32) as u128,
        6 => tower_mul_t6(a as u64, b as u64) as u128,
        7 => tower_mul_t7(a, b),
        _ => {
            let half = 1u32 << (k - 1);
            let mask = (1u128 << half) - 1;
            let a_lo = a & mask;
            let a_hi = (a >> half) & mask;
            let b_lo = b & mask;
            let b_hi = (b >> half) & mask;
            let p = tower_mul_bits(k - 1, a_lo, b_lo);
            let q = tower_mul_bits(k - 1, a_hi, b_hi);
            let r = tower_mul_bits(k - 1, a_lo ^ a_hi, b_lo ^ b_hi);
            let lo = p ^ q;
            let hi = r ^ p ^ q ^ tower_scale_x_bits(k - 1, q);
            lo | (hi << half)
        }
    }
}

/// Compile-time $256 \times 8$ basis-column table for $\mathcal{T}_3 = \mathbb{F}_{2^8}$:
/// `GF256_MUL_BASIS[c][in_bit] == (TowerGf256(c) * TowerGf256(1 << in_bit)).0`.
pub const GF256_MUL_BASIS: [[u8; 8]; 256] = {
    let mut tbl = [[0u8; 8]; 256];
    let mut c = 0usize;
    while c < 256 {
        let mut bit = 0usize;
        while bit < 8 {
            tbl[c][bit] = tower_mul_bits(3, c as u128, 1u128 << bit) as u8;
            bit += 1;
        }
        c += 1;
    }
    tbl
};

/// 100% branchless Fermat inversion $a^{2^8 - 2} = a^{254}$ in $\mathcal{T}_3 = \mathbb{F}_{2^8}$
/// (`0` subfield zero-branches `[P1-06]`; maps `0 -> 0`).
#[inline]
pub const fn tower_fermat_inv_gf256(a: u8) -> u8 {
    let x = a as u128;
    let x2 = tower_mul_bits(3, x, x);
    let x3 = tower_mul_bits(3, x2, x);
    let x6 = tower_mul_bits(3, x3, x3);
    let x7 = tower_mul_bits(3, x6, x);
    let x12 = tower_mul_bits(3, x6, x6);
    let x15 = tower_mul_bits(3, x12, x3);
    let x30 = tower_mul_bits(3, x15, x15);
    let x60 = tower_mul_bits(3, x30, x30);
    let x120 = tower_mul_bits(3, x60, x60);
    let x127 = tower_mul_bits(3, x120, x7);
    tower_mul_bits(3, x127, x127) as u8
}

/// 100% branchless Fermat inversion $a^{2^{128} - 2}$ in $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$
/// (`0` subfield zero-branches `[P1-06]`; maps `0 -> 0`).
#[inline]
pub const fn tower_fermat_inv_128(a: u128) -> u128 {
    #[inline]
    const fn sq_n(mut v: u128, mut n: u32) -> u128 {
        while n > 0 {
            v = tower_mul_bits(7, v, v);
            n -= 1;
        }
        v
    }
    let t1 = a; // a^(2^1 - 1)
    let t2 = tower_mul_bits(7, sq_n(t1, 1), t1); // a^(2^2 - 1)
    let t4 = tower_mul_bits(7, sq_n(t2, 2), t2); // a^(2^4 - 1)
    let t8 = tower_mul_bits(7, sq_n(t4, 4), t4); // a^(2^8 - 1)
    let t16 = tower_mul_bits(7, sq_n(t8, 8), t8); // a^(2^16 - 1)
    let t32 = tower_mul_bits(7, sq_n(t16, 16), t16); // a^(2^32 - 1)
    let t64 = tower_mul_bits(7, sq_n(t32, 32), t32); // a^(2^64 - 1)
    let t96 = tower_mul_bits(7, sq_n(t64, 32), t32);
    let t112 = tower_mul_bits(7, sq_n(t96, 16), t16);
    let t120 = tower_mul_bits(7, sq_n(t112, 8), t8);
    let t124 = tower_mul_bits(7, sq_n(t120, 4), t4);
    let t126 = tower_mul_bits(7, sq_n(t124, 2), t2);
    let t127 = tower_mul_bits(7, sq_n(t126, 1), t1); // a^(2^127 - 1)
    sq_n(t127, 1) // a^(2^128 - 2)
}

/// Element of Wiedemann tower level $\mathcal{T}_3 = \mathbb{F}_{2^8}$ (`lean/Qsag/BinaryTower.lean`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct TowerGf256(pub u8);

impl TowerGf256 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    #[inline]
    pub const fn embed_bit(b: bool) -> Self {
        Self(b as u8)
    }

    #[inline]
    pub const fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }

    /// Constant-time branchless multiplication in $\mathcal{T}_3 = \mathbb{F}_{2^8}$.
    #[inline]
    pub const fn mul(self, rhs: Self) -> Self {
        Self(tower_mul_bits(3, self.0 as u128, rhs.0 as u128) as u8)
    }

    /// Branchless constant-time Fermat inverse $x^{254}$ (`0 -> 0`, zero internal branches).
    #[inline]
    pub const fn ct_inv(self) -> Self {
        Self(tower_fermat_inv_gf256(self.0))
    }

    #[inline]
    pub fn inv(self) -> Option<Self> {
        let out = self.ct_inv();
        if crate::wipe::ct_eq_u64(self.0 as u64, 0) {
            None
        } else {
            Some(out)
        }
    }
}

/// Element of Wiedemann tower level $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$ (`Tower128` in Lean).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Tower128(pub u128);

impl Tower128 {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    #[inline]
    pub const fn embed_bit(b: bool) -> Self {
        Self(b as u128)
    }

    #[inline]
    pub const fn embed_gf256(x: TowerGf256) -> Self {
        Self(x.0 as u128)
    }

    #[inline]
    pub const fn to_be_bytes(self) -> [u8; 16] {
        self.0.to_be_bytes()
    }

    #[inline]
    pub const fn from_be_bytes(bytes: [u8; 16]) -> Self {
        Self(u128::from_be_bytes(bytes))
    }

    #[inline]
    pub fn ct_eq(self, rhs: Self) -> bool {
        ct_eq_u128(self.0, rhs.0)
    }

    #[inline]
    pub const fn add(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0)
    }

    /// Constant-time branchless multiplication in $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$.
    #[inline]
    pub const fn mul(self, rhs: Self) -> Self {
        Self(tower_mul_bits(7, self.0, rhs.0))
    }

    /// 100% branchless 16-lane SWAR subfield scalar multiplication
    /// `self * Tower128::embed_gf256(rhs)` in $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$
    /// (`~36x` faster than general `Tower128::mul`, `0` table lookups, `0` branches).
    #[inline]
    pub fn mul_gf256(self, rhs: TowerGf256) -> Self {
        let b0 = self.0;
        let b1 = swar_mul_x0_128(b0);
        let b2 = swar_mul_x1_128(b0);
        let b3 = swar_mul_x0_128(b2);
        let b4 = swar_mul_x2_128(b0);
        let b5 = swar_mul_x0_128(b4);
        let b6 = swar_mul_x1_128(b4);
        let b7 = swar_mul_x0_128(b6);

        let s = black_box(rhs.0);
        let basis = [b0, b1, b2, b3, b4, b5, b6, b7];
        let mut acc = 0u128;
        for (bit, &basis_elem) in basis.iter().enumerate() {
            let mask = 0u128.wrapping_sub(((s >> bit) & 1) as u128);
            acc ^= basis_elem & mask;
        }
        Self(acc)
    }

    /// Branchless constant-time Fermat inverse $x^{2^{128}-2}$ (`0 -> 0`, zero internal branches).
    #[inline]
    pub const fn ct_inv(self) -> Self {
        Self(tower_fermat_inv_128(self.0))
    }

    #[inline]
    pub fn inv(self) -> Option<Self> {
        let out = self.ct_inv();
        if ct_eq_u128(self.0, 0) {
            None
        } else {
            Some(out)
        }
    }
}

pub use crate::wipe::{wipe_gf256_slice as wipe_gf256, wipe_tower128_slice as wipe_tower128};

/// Evaluate polynomial `coeffs[0] + coeffs[1]*x + ...` over `TowerGf256`.
#[inline]
pub fn eval_poly_gf256(coeffs: &[TowerGf256], x: TowerGf256) -> TowerGf256 {
    let mut acc = TowerGf256::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul(x).add(c);
    }
    acc
}

/// Evaluate polynomial over `Tower128` at embedded `TowerGf256` coordinate `x`.
#[inline]
pub fn eval_poly_tower128_at_gf256(coeffs: &[Tower128], x: TowerGf256) -> Tower128 {
    let mut acc = Tower128::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul_gf256(x).add(c);
    }
    acc
}

/// Compute Lagrange interpolation weights at `0` for distinct non-zero points in `TowerGf256`.
pub fn lagrange_weights_zero_gf256(pts: &[TowerGf256]) -> Option<Vec<TowerGf256>> {
    let t = pts.len();
    let mut weights = Vec::with_capacity(t);
    for i in 0..t {
        if pts[i] == TowerGf256::ZERO {
            return None;
        }
        let mut num = TowerGf256::ONE;
        let mut den = TowerGf256::ONE;
        for j in 0..t {
            if i == j {
                continue;
            }
            let diff = pts[i].add(pts[j]);
            if diff == TowerGf256::ZERO {
                return None;
            }
            num = num.mul(pts[j]);
            den = den.mul(diff);
        }
        weights.push(num.mul(den.inv()?));
    }
    Some(weights)
}

/// Evaluate GHASH-style polynomial `((0 + c_0) * h + c_1) * h ...` over `Tower128`,
/// matching `BinaryTower.ghashPoly` in Lean.
#[inline]
pub fn ghash_poly_tower128(h: Tower128, blocks: &[Tower128]) -> Tower128 {
    let mut acc = Tower128::ZERO;
    for &blk in blocks {
        acc = acc.add(blk).mul(h);
    }
    acc
}

/// Bitsliced vector of 64 parallel $\mathcal{T}_3 = \mathbb{F}_{2^8}$ elements (`8` `u64` bit-planes).
pub type BitslicedGf256x64 = [u64; 8];

#[inline]
pub const fn bs_gf256_xor(a: &BitslicedGf256x64, b: &BitslicedGf256x64) -> BitslicedGf256x64 {
    [
        a[0] ^ b[0],
        a[1] ^ b[1],
        a[2] ^ b[2],
        a[3] ^ b[3],
        a[4] ^ b[4],
        a[5] ^ b[5],
        a[6] ^ b[6],
        a[7] ^ b[7],
    ]
}

#[inline]
pub const fn bs_gf256_xor_assign(dst: &mut BitslicedGf256x64, rhs: &BitslicedGf256x64) {
    dst[0] ^= rhs[0];
    dst[1] ^= rhs[1];
    dst[2] ^= rhs[2];
    dst[3] ^= rhs[3];
    dst[4] ^= rhs[4];
    dst[5] ^= rhs[5];
    dst[6] ^= rhs[6];
    dst[7] ^= rhs[7];
}

#[inline]
pub const fn bs_gf256_mask_bit(mask64: u64, a: &BitslicedGf256x64) -> BitslicedGf256x64 {
    [
        a[0] & mask64,
        a[1] & mask64,
        a[2] & mask64,
        a[3] & mask64,
        a[4] & mask64,
        a[5] & mask64,
        a[6] & mask64,
        a[7] & mask64,
    ]
}

/// Precomputed $8 \times 8$ $\mathbb{F}_2$-linear operator for a **PUBLIC** $\mathcal{T}_3 = \mathbb{F}_{2^8}$
/// scalar (such as a public Lagrange weight $\lambda_q$ or public Vandermonde point $x_p$).
///
/// ### Side-Channel Invariant
/// - Construct **only** from public protocol constants (`from_public_scalar`).
/// - Secret planes `a: &BitslicedGf256x64` undergo unconditional `22 + 8 = 30` register XORs
///   (Four-Russians low/high 4-bit Gray/subset tables) and are indexed **exclusively** by the
///   public nibble indices `lo_nib` / `hi_nib` (~6.5x–8x fewer ops than 64-mask bit scaling).
/// - For **secret** scalars, callers MUST use [`bs_gf256_scale_secret_ct`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicGf256Matrix {
    scalar: TowerGf256,
    lo_nib: [u8; 8],
    hi_nib: [u8; 8],
}

impl PublicGf256Matrix {
    /// Precompute the Four-Russians nibble row indices for a **public** `TowerGf256` scalar.
    #[inline]
    pub const fn from_public_scalar(public_c: TowerGf256) -> Self {
        let cols = GF256_MUL_BASIS[public_c.0 as usize];
        let mut lo_nib = [0u8; 8];
        let mut hi_nib = [0u8; 8];
        let mut out_bit = 0usize;
        while out_bit < 8 {
            let mut row = 0u8;
            let mut in_bit = 0usize;
            while in_bit < 8 {
                let bit = (cols[in_bit] >> out_bit) & 1;
                row |= bit << in_bit;
                in_bit += 1;
            }
            lo_nib[out_bit] = row & 0x0F;
            hi_nib[out_bit] = row >> 4;
            out_bit += 1;
        }
        Self {
            scalar: public_c,
            lo_nib,
            hi_nib,
        }
    }

    #[inline]
    pub const fn from_mul_const(public_c: TowerGf256) -> Self {
        Self::from_public_scalar(public_c)
    }

    #[inline]
    pub const fn scalar(&self) -> TowerGf256 {
        self.scalar
    }

    /// Multiply a single secret `TowerGf256` share by this public scalar without secret-indexed tables.
    #[inline]
    pub const fn mul_elem(&self, x: TowerGf256) -> TowerGf256 {
        let mut planes = [0u64; 8];
        let mut b = 0usize;
        while b < 8 {
            planes[b] = ((x.0 >> b) & 1) as u64;
            b += 1;
        }
        let scaled = self.scale_planes(&planes);
        let mut out = 0u8;
        let mut i = 0usize;
        while i < 8 {
            out |= ((scaled[i] & 1) as u8) << i;
            i += 1;
        }
        TowerGf256(out)
    }

    /// Multiply 64 bitsliced $\mathcal{T}_3$ secret shares simultaneously by `self.scalar`
    /// in 30 unconditional `u64` XORs (`0` secret-dependent branches or indices).
    #[inline]
    pub const fn scale_planes(&self, a: &BitslicedGf256x64) -> BitslicedGf256x64 {
        let a0 = a[0];
        let a1 = a[1];
        let a2 = a[2];
        let a3 = a[3];
        let x01 = a0 ^ a1;
        let x23 = a2 ^ a3;
        let lo_lut: [u64; 16] = [
            0,
            a0,
            a1,
            x01,
            a2,
            a0 ^ a2,
            a1 ^ a2,
            x01 ^ a2,
            a3,
            a0 ^ a3,
            a1 ^ a3,
            x01 ^ a3,
            x23,
            x23 ^ a0,
            x23 ^ a1,
            x01 ^ x23,
        ];

        let a4 = a[4];
        let a5 = a[5];
        let a6 = a[6];
        let a7 = a[7];
        let x45 = a4 ^ a5;
        let x67 = a6 ^ a7;
        let hi_lut: [u64; 16] = [
            0,
            a4,
            a5,
            x45,
            a6,
            a4 ^ a6,
            a5 ^ a6,
            x45 ^ a6,
            a7,
            a4 ^ a7,
            a5 ^ a7,
            x45 ^ a7,
            x67,
            x67 ^ a4,
            x67 ^ a5,
            x45 ^ x67,
        ];

        [
            lo_lut[self.lo_nib[0] as usize] ^ hi_lut[self.hi_nib[0] as usize],
            lo_lut[self.lo_nib[1] as usize] ^ hi_lut[self.hi_nib[1] as usize],
            lo_lut[self.lo_nib[2] as usize] ^ hi_lut[self.hi_nib[2] as usize],
            lo_lut[self.lo_nib[3] as usize] ^ hi_lut[self.hi_nib[3] as usize],
            lo_lut[self.lo_nib[4] as usize] ^ hi_lut[self.hi_nib[4] as usize],
            lo_lut[self.lo_nib[5] as usize] ^ hi_lut[self.hi_nib[5] as usize],
            lo_lut[self.lo_nib[6] as usize] ^ hi_lut[self.hi_nib[6] as usize],
            lo_lut[self.lo_nib[7] as usize] ^ hi_lut[self.hi_nib[7] as usize],
        ]
    }

    /// Fused multiply-accumulate `acc ^= self.scale_planes(a)`.
    #[inline]
    pub const fn scale_xor_into(&self, acc: &mut BitslicedGf256x64, a: &BitslicedGf256x64) {
        let scaled = self.scale_planes(a);
        bs_gf256_xor_assign(acc, &scaled);
    }
}

/// Extract the `TowerGf256` element at bit-lane `lane` (`0..64`) from `BitslicedGf256x64`.
#[inline]
pub const fn bs_gf256_extract_lane(planes: &BitslicedGf256x64, lane: usize) -> TowerGf256 {
    let mut v = 0u8;
    let mut b = 0usize;
    while b < 8 {
        v |= (((planes[b] >> lane) & 1) as u8) << b;
        b += 1;
    }
    TowerGf256(v)
}

/// Insert `val: TowerGf256` at bit-lane `lane` (`0..64`) of `BitslicedGf256x64`.
#[inline]
pub fn bs_gf256_insert_lane(planes: &mut BitslicedGf256x64, lane: usize, val: TowerGf256) {
    let clear = !(1u64 << lane);
    let v = black_box(val.0);
    for (b, plane) in planes.iter_mut().enumerate() {
        let bit = ((v >> b) & 1) as u64;
        *plane = (*plane & clear) | (bit << lane);
    }
}

/// 100% constant-time, table-free bitsliced $\mathcal{T}_3 = \mathbb{F}_{2^8}$ multiplication
/// when the scalar `secret_c` is **SECRET** (zero memory/table lookups on `secret_c`).
#[inline]
pub fn bs_gf256_scale_secret_ct(secret_c: TowerGf256, a: &BitslicedGf256x64) -> BitslicedGf256x64 {
    // Expand the 8 bits of `secret_c` into 8 all-ones/all-zeros `u64` planes and run Karatsuba/tower mul
    let c_val = black_box(secret_c.0);
    let mut b = [0u64; 8];
    for (bit, mask) in b.iter_mut().enumerate() {
        *mask = 0u64.wrapping_sub(((c_val >> bit) & 1) as u64);
    }
    bs_gf256_mul_planes_ct(&b, a)
}

/// Constant-time bitsliced $\mathcal{T}_3$ multiplication of two 64-wide plane arrays (`a * b` in $\mathcal{T}_3^{64}$).
#[inline]
pub const fn bs_gf256_mul_planes_ct(
    a: &BitslicedGf256x64,
    b: &BitslicedGf256x64,
) -> BitslicedGf256x64 {
    // Recursive Wiedemann tower over u64 planes: T_3 = T_2[X_2]/(X_2^2 + x_2 X_2 + 1)
    #[inline]
    const fn scale_x1(v: [u64; 2]) -> [u64; 2] {
        // x_0 = 1 -> scale_x0(hi) = hi
        [v[1], v[0] ^ v[1]]
    }
    #[inline]
    const fn mul_t1(x: [u64; 2], y: [u64; 2]) -> [u64; 2] {
        let p = x[0] & y[0];
        let q = x[1] & y[1];
        let r = (x[0] ^ x[1]) & (y[0] ^ y[1]);
        [p ^ q, r ^ p]
    }
    #[inline]
    const fn scale_x2(v: [u64; 4]) -> [u64; 4] {
        let hi = [v[2], v[3]];
        let s = scale_x1(hi);
        [v[2], v[3], v[0] ^ s[0], v[1] ^ s[1]]
    }
    #[inline]
    const fn mul_t2(x: [u64; 4], y: [u64; 4]) -> [u64; 4] {
        let x_lo = [x[0], x[1]];
        let x_hi = [x[2], x[3]];
        let y_lo = [y[0], y[1]];
        let y_hi = [y[2], y[3]];
        let p = mul_t1(x_lo, y_lo);
        let q = mul_t1(x_hi, y_hi);
        let r = mul_t1(
            [x_lo[0] ^ x_hi[0], x_lo[1] ^ x_hi[1]],
            [y_lo[0] ^ y_hi[0], y_lo[1] ^ y_hi[1]],
        );
        let sq = scale_x1(q);
        [
            p[0] ^ q[0],
            p[1] ^ q[1],
            r[0] ^ p[0] ^ q[0] ^ sq[0],
            r[1] ^ p[1] ^ q[1] ^ sq[1],
        ]
    }

    let a_lo = [a[0], a[1], a[2], a[3]];
    let a_hi = [a[4], a[5], a[6], a[7]];
    let b_lo = [b[0], b[1], b[2], b[3]];
    let b_hi = [b[4], b[5], b[6], b[7]];
    let p = mul_t2(a_lo, b_lo);
    let q = mul_t2(a_hi, b_hi);
    let r = mul_t2(
        [
            a_lo[0] ^ a_hi[0],
            a_lo[1] ^ a_hi[1],
            a_lo[2] ^ a_hi[2],
            a_lo[3] ^ a_hi[3],
        ],
        [
            b_lo[0] ^ b_hi[0],
            b_lo[1] ^ b_hi[1],
            b_lo[2] ^ b_hi[2],
            b_lo[3] ^ b_hi[3],
        ],
    );
    let sq = scale_x2(q);
    [
        p[0] ^ q[0],
        p[1] ^ q[1],
        p[2] ^ q[2],
        p[3] ^ q[3],
        r[0] ^ p[0] ^ q[0] ^ sq[0],
        r[1] ^ p[1] ^ q[1] ^ sq[1],
        r[2] ^ p[2] ^ q[2] ^ sq[2],
        r[3] ^ p[3] ^ q[3] ^ sq[3],
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pack_lanes64_for_test(lanes: &[TowerGf256; 64]) -> BitslicedGf256x64 {
        let mut planes = [0u64; 8];
        for (lane, elem) in lanes.iter().enumerate() {
            for (b, plane) in planes.iter_mut().enumerate() {
                *plane |= (((elem.0 >> b) & 1) as u64) << lane;
            }
        }
        planes
    }

    fn unpack_lanes64_for_test(planes: &BitslicedGf256x64) -> [TowerGf256; 64] {
        let mut lanes = [TowerGf256::ZERO; 64];
        for (lane, out) in lanes.iter_mut().enumerate() {
            let mut v = 0u8;
            for (b, &plane) in planes.iter().enumerate() {
                v |= (((plane >> lane) & 1) as u8) << b;
            }
            *out = TowerGf256(v);
        }
        lanes
    }

    #[test]
    fn exhaustive_public_gf256_matrix_and_secret_ct_parity() {
        let sample_planes: BitslicedGf256x64 = [
            0x0123_4567_89AB_CDEF,
            0xFEDC_BA98_7654_3210,
            0xAAAA_5555_AAAA_5555,
            0x0F0F_0F0F_F0F0_F0F0,
            0x1357_9BDF_2468_ACE0,
            0xDEAD_BEEF_CAFE_BABE,
            0x8000_0000_0000_0001,
            0xFFFF_0000_FFFF_0000,
        ];
        let input_lanes = unpack_lanes64_for_test(&sample_planes);
        for c_raw in 0..=255u8 {
            let c = TowerGf256(c_raw);
            let mut expected_lanes = [TowerGf256::ZERO; 64];
            for lane in 0..64 {
                expected_lanes[lane] = c.mul(input_lanes[lane]);
            }
            let expected = pack_lanes64_for_test(&expected_lanes);
            let mat = PublicGf256Matrix::from_public_scalar(c);
            assert_eq!(mat.scale_planes(&sample_planes), expected);
            assert_eq!(bs_gf256_scale_secret_ct(c, &sample_planes), expected);
            assert_eq!(mat.mul_elem(input_lanes[0]), expected_lanes[0]);
            if c_raw != 0 {
                let inv = c.inv().expect("non-zero GF(2^8) element invertible");
                assert_eq!(c.mul(inv), TowerGf256::ONE);
            } else {
                assert!(c.inv().is_none());
            }
        }
    }

    #[test]
    fn tower128_inversion_and_subfield_embedding() {
        let a = TowerGf256(0x53);
        let b = TowerGf256(0xCA);
        assert_eq!(
            Tower128::embed_gf256(a.mul(b)),
            Tower128::embed_gf256(a).mul(Tower128::embed_gf256(b))
        );
        let z = Tower128(0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3211);
        assert_eq!(z.mul(z.inv().unwrap()), Tower128::ONE);
        for s_raw in 0..=255u8 {
            let s = TowerGf256(s_raw);
            assert_eq!(z.mul_gf256(s), z.mul(Tower128::embed_gf256(s)));
        }
        // Exhaustive 128 x 128 = 16,384 basis-product check proving `swar_mul_t5_x4` `tower_mul_t7`
        // matches `tower_mul_t7_karatsuba_ref` across all 2^256 pairs by F_2-bilinearity!
        for i in 0..128 {
            let ei = 1u128 << i;
            for j in 0..128 {
                let ej = 1u128 << j;
                assert_eq!(tower_mul_t7(ei, ej), tower_mul_t7_karatsuba_ref(ei, ej));
            }
        }
    }
}
