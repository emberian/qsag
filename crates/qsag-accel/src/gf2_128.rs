//! 100% constant-time, branchless, LUT-free arithmetic in $\mathbb{F}_{2^{128}}$ for 2-lane BDOZ
//! MAC dot products (`bdoz_gf2_128_batch_dot`) and Wiedemann binary tower $\mathcal{T}_7$.

use crate::AccelError;
use crate::ct::ct_select_u128;

/// Irreducible pentanomial $x^{128} + x^7 + x^2 + x + 1$ (`0x87` low reduction polynomial).
pub const GF2_128_POLY_LO: u128 = 0x87;

/// Constant-time branchless multiplication in $\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$.
/// Performs a fixed 128-iteration shift-and-mask loop with zero secret-indexed lookup tables
/// and zero secret-dependent branches.
#[inline]
pub const fn gf2_128_mul(mut a: u128, mut b: u128) -> u128 {
    let mut acc = 0u128;
    let mut step = 0u32;
    while step < 128 {
        let b_lsb = (b & 1) == 1;
        acc = ct_select_u128(b_lsb, acc ^ a, acc);
        let a_msb = (a >> 127) == 1;
        let shifted = a << 1;
        a = ct_select_u128(a_msb, shifted ^ GF2_128_POLY_LO, shifted);
        b >>= 1;
        step += 1;
    }
    acc
}

/// Constant-time squaring in $\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$.
#[inline]
pub const fn gf2_128_sq(a: u128) -> u128 {
    gf2_128_mul(a, a)
}

#[inline]
const fn gf2_128_exp_pow2(mut x: u128, mut k: u32) -> u128 {
    while k > 0 {
        x = gf2_128_sq(x);
        k -= 1;
    }
    x
}

/// Constant-time Fermat addition chain $a^{2^{128} - 2}$ in $\mathbb{F}_{2^{128}}$ (`0` maps to `0`
/// with zero secret-dependent branches!).
#[inline]
pub const fn gf2_128_inv_or_zero(a: u128) -> u128 {
    // 2^128 - 2 = 2 * (2^127 - 1).
    let x1 = a;
    let x2 = gf2_128_mul(gf2_128_sq(x1), x1); // a^{2^2 - 1}
    let x4 = gf2_128_mul(gf2_128_exp_pow2(x2, 2), x2); // a^{2^4 - 1}
    let x8 = gf2_128_mul(gf2_128_exp_pow2(x4, 4), x4); // a^{2^8 - 1}
    let x16 = gf2_128_mul(gf2_128_exp_pow2(x8, 8), x8); // a^{2^16 - 1}
    let x32 = gf2_128_mul(gf2_128_exp_pow2(x16, 16), x16); // a^{2^32 - 1}
    let x64 = gf2_128_mul(gf2_128_exp_pow2(x32, 32), x32); // a^{2^64 - 1}
    let x96 = gf2_128_mul(gf2_128_exp_pow2(x64, 32), x32);
    let x112 = gf2_128_mul(gf2_128_exp_pow2(x96, 16), x16);
    let x120 = gf2_128_mul(gf2_128_exp_pow2(x112, 8), x8);
    let x124 = gf2_128_mul(gf2_128_exp_pow2(x120, 4), x4);
    let x126 = gf2_128_mul(gf2_128_exp_pow2(x124, 2), x2);
    let x127 = gf2_128_mul(gf2_128_sq(x126), x1); // a^{2^127 - 1}
    gf2_128_sq(x127) // a^{2^128 - 2}
}

/// Wiedemann binary tower $\mathcal{T}_k$ ($0 \le k \le 7$) constant-time multiplication,
/// matching `lean/Qsag/BinaryTower.lean` with zero data-dependent branches.
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

/// Constant-time Wiedemann tower multiplication at level `k` (`0 <= k <= 7`).
#[inline]
pub const fn tower_mul_bits(k: u32, a: u128, b: u128) -> u128 {
    if k == 0 {
        (a & 1) & (b & 1)
    } else {
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

/// 2-lane BDOZ GF($2^{128}$) inner product:
/// Computes $\bigl(\bigoplus_i s_{i,0} \cdot w_{i,0},\; \bigoplus_i s_{i,1} \cdot w_{i,1}\bigr)$
/// in 100% constant time over $\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$.
pub fn bdoz_gf2_128_batch_dot_cpu(
    shares: &[(u128, u128)],
    weights: &[(u128, u128)],
) -> Result<(u128, u128), AccelError> {
    if shares.len() != weights.len() {
        return Err(AccelError::LengthMismatch {
            what: "BDOZ batch dot weights",
            expected: shares.len(),
            actual: weights.len(),
        });
    }
    let mut lane0 = 0u128;
    let mut lane1 = 0u128;
    for (&(s0, s1), &(w0, w1)) in shares.iter().zip(weights.iter()) {
        lane0 ^= gf2_128_mul(s0, w0);
        lane1 ^= gf2_128_mul(s1, w1);
    }
    Ok((lane0, lane1))
}

/// Element in the polynomial basis with modulus x^128 + x^7 + x^2 + x + 1.
#[derive(Clone, Copy)]
pub struct PolyGf2_128(pub u128);
/// Element in the recursive Wiedemann T_7 basis.
#[derive(Clone, Copy)]
pub struct WiedemannTower128(pub u128);
impl From<WiedemannTower128> for PolyGf2_128 {
    fn from(x: WiedemannTower128) -> Self {
        Self(qsag_asm::tower128_to_poly128_ct(x.0))
    }
}
impl From<PolyGf2_128> for WiedemannTower128 {
    fn from(x: PolyGf2_128) -> Self {
        Self(qsag_asm::poly128_to_tower128_ct(x.0))
    }
}

#[cfg(test)]
mod basis_tests {
    use super::*;
    #[test]
    fn basis_roundtrip_and_product() {
        for i in 0..128 {
            let a = 1u128 << i;
            let pa = PolyGf2_128::from(WiedemannTower128(a));
            assert_eq!(WiedemannTower128::from(pa).0, a);
            for j in 0..128 {
                let b = 1u128 << j;
                let pb = PolyGf2_128::from(WiedemannTower128(b));
                let product = tower_mul_bits(7, a, b);
                assert_eq!(
                    PolyGf2_128::from(WiedemannTower128(product)).0,
                    gf2_128_mul(pa.0, pb.0)
                );
            }
        }
    }
}
