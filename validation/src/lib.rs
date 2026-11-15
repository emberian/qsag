// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Shared reference-oracle helpers, basis isomorphisms, and algebraic inverse
//! utilities for QSAG external differential validation and property-based testing.

use qsag_core::field::goldilocks::{GOLDILOCKS_PRIME, Goldilocks};
use qsag_core::sponge::poseidon2::{
    POSEIDON2_HALF_EXTERNAL_ROUNDS, POSEIDON2_INTERNAL_ROUNDS, Poseidon2State12,
    poseidon2_apply_me, poseidon2_apply_mi, poseidon2_const_at,
};

/// Exact inverse exponent $d_{\text{inv}} = \frac{4(p - 1) + 1}{7}$ for $x \mapsto x^7 \bmod p$
/// over Goldilocks ($p = 2^{64} - 2^{32} + 1$).
pub const POSEIDON2_SBOX7_INV_EXP: u64 = 10_540_996_611_094_048_183;

/// Compute $x^e \bmod p$ in `Goldilocks` via binary square-and-multiply.
#[inline]
pub fn goldilocks_pow_u64(mut base: Goldilocks, mut exp: u64) -> Goldilocks {
    let mut acc = Goldilocks::ONE;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc *= base;
        }
        base = base.square();
        exp >>= 1;
    }
    acc
}

/// Exact inverse S-box $y \mapsto y^{d_{\text{inv}}} \bmod p$ satisfying `sbox7_inv(sbox7(x)) == x`.
#[inline]
pub fn poseidon2_sbox7_inv(y: Goldilocks) -> Goldilocks {
    if y == Goldilocks::ZERO {
        Goldilocks::ZERO
    } else {
        goldilocks_pow_u64(y, POSEIDON2_SBOX7_INV_EXP)
    }
}

/// Invert a $12 \times 12$ matrix over `Goldilocks` via Gauss-Jordan elimination,
/// panicking if the matrix is singular ($\det = 0$).
pub fn invert_matrix_12(mut a: [[Goldilocks; 12]; 12]) -> [[Goldilocks; 12]; 12] {
    let mut inv = [[Goldilocks::ZERO; 12]; 12];
    for (i, row) in inv.iter_mut().enumerate() {
        row[i] = Goldilocks::ONE;
    }
    for col in 0..12 {
        let pivot_row = (col..12)
            .find(|&r| a[r][col] != Goldilocks::ZERO)
            .expect("12x12 Poseidon2 diffusion matrix must be invertible over Goldilocks");
        if pivot_row != col {
            a.swap(col, pivot_row);
            inv.swap(col, pivot_row);
        }
        let pivot_inv = a[col][col]
            .checked_inv()
            .expect("nonzero Goldilocks pivot has multiplicative inverse");
        for j in 0..12 {
            a[col][j] *= pivot_inv;
            inv[col][j] *= pivot_inv;
        }
        for r in 0..12 {
            if r == col {
                continue;
            }
            let factor = a[r][col];
            if factor != Goldilocks::ZERO {
                for j in 0..12 {
                    let sub_a = factor * a[col][j];
                    let sub_i = factor * inv[col][j];
                    a[r][j] -= sub_a;
                    inv[r][j] -= sub_i;
                }
            }
        }
    }
    inv
}

/// Reconstruct the exact $12 \times 12$ matrices $(M_E^{-1}, M_I^{-1})$ directly from the live
/// `poseidon2_apply_me` and `poseidon2_apply_mi` operators in `qsag_core`.
pub fn build_poseidon2_inverse_matrices() -> ([[Goldilocks; 12]; 12], [[Goldilocks; 12]; 12]) {
    let mut me_cols = [[Goldilocks::ZERO; 12]; 12];
    let mut mi_cols = [[Goldilocks::ZERO; 12]; 12];
    for j in 0..12 {
        let mut e_me = [Goldilocks::ZERO; 12];
        e_me[j] = Goldilocks::ONE;
        poseidon2_apply_me(&mut e_me);
        for i in 0..12 {
            me_cols[i][j] = e_me[i];
        }

        let mut e_mi = [Goldilocks::ZERO; 12];
        e_mi[j] = Goldilocks::ONE;
        poseidon2_apply_mi(&mut e_mi);
        for i in 0..12 {
            mi_cols[i][j] = e_mi[i];
        }
    }
    (invert_matrix_12(me_cols), invert_matrix_12(mi_cols))
}

#[inline]
pub fn apply_matrix_12(mat: &[[Goldilocks; 12]; 12], st: &mut Poseidon2State12) {
    let inp = *st;
    for (i, out_lane) in st.iter_mut().enumerate() {
        let mut acc = Goldilocks::ZERO;
        for j in 0..12 {
            acc += mat[i][j] * inp[j];
        }
        *out_lane = acc;
    }
}

/// Exact inverse of `qsag_core::sponge::poseidon2::poseidon2_perm12` using precomputed
/// $(M_E^{-1}, M_I^{-1})$ and $x^{d_{\text{inv}}}$.
pub fn poseidon2_perm12_inv_with_mats(
    st: &mut Poseidon2State12,
    me_inv: &[[Goldilocks; 12]; 12],
    mi_inv: &[[Goldilocks; 12]; 12],
) {
    for r in (0..POSEIDON2_HALF_EXTERNAL_ROUNDS).rev() {
        apply_matrix_12(me_inv, st);
        for (lane, x) in st.iter_mut().enumerate() {
            *x = poseidon2_sbox7_inv(*x) - poseidon2_const_at(2, r, lane as u64);
        }
    }
    for r in (0..POSEIDON2_INTERNAL_ROUNDS).rev() {
        apply_matrix_12(mi_inv, st);
        st[0] = poseidon2_sbox7_inv(st[0]) - poseidon2_const_at(1, r, 0);
    }
    for r in (0..POSEIDON2_HALF_EXTERNAL_ROUNDS).rev() {
        apply_matrix_12(me_inv, st);
        for (lane, x) in st.iter_mut().enumerate() {
            *x = poseidon2_sbox7_inv(*x) - poseidon2_const_at(0, r, lane as u64);
        }
    }
    apply_matrix_12(me_inv, st);
}

/// Reference AES / Rijndael $\mathbb{F}_{2}[x]/(x^8 + x^4 + x^3 + x + 1)$ (`0x11B`) byte multiplication.
#[inline]
pub const fn gf256_poly11b_mul(mut a: u8, mut b: u8) -> u8 {
    let mut p = 0u8;
    let mut i = 0;
    while i < 8 {
        if (b & 1) != 0 {
            p ^= a;
        }
        let hi = a & 0x80;
        a <<= 1;
        if hi != 0 {
            a ^= 0x1B;
        }
        b >>= 1;
        i += 1;
    }
    p
}

/// Multiplicative inverse in $\mathbb{F}_{2}[x]/(x^8 + x^4 + x^3 + x + 1)$ via $a^{254}$ (`0 -> 0`).
#[inline]
pub const fn gf256_poly11b_inv(a: u8) -> u8 {
    let mut acc = 1u8;
    let mut base = a;
    let mut exp = 254u8;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = gf256_poly11b_mul(acc, base);
        }
        base = gf256_poly11b_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// Intel `GF2P8AFFINEQB` byte map (`mat` is row-major MSB-to-LSB `u64` matching `GFNI_MAT_*`):
/// output bit `i` (`0..8`, LSB-first) is `parity(((mat >> (8 * (7 - i))) as u8) & x) ^ ((imm8 >> i) & 1)`.
#[inline]
pub const fn gfni_affine_byte(mat: u64, x: u8, imm8: u8) -> u8 {
    let mut out = 0u8;
    let mut i = 0usize;
    while i < 8 {
        let row = ((mat >> (8 * (7 - i))) & 0xFF) as u8;
        let parity = ((row & x).count_ones() & 1) as u8;
        out |= parity << i;
        i += 1;
    }
    out ^ imm8
}

/// Reference multiplication in $\mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$ (`0x87`, LSB = coeff of $z^0$).
#[inline]
pub const fn gf2_128_poly87_mul_ref(mut a: u128, mut b: u128) -> u128 {
    let mut acc = 0u128;
    let mut i = 0;
    while i < 128 {
        if (b & 1) != 0 {
            acc ^= a;
        }
        let carry = (a >> 127) & 1;
        a <<= 1;
        if carry != 0 {
            a ^= 0x87;
        }
        b >>= 1;
        i += 1;
    }
    acc
}

/// Reference schoolbook negacyclic polynomial multiplication in $\mathbb{Z}_q[X]/(X^{256} + 1)$
/// for NIST FIPS 204 ML-DSA ($q = 8{,}380{,}417$).
pub fn mldsa_poly_mul_negacyclic_ref(a: &[i32; 256], b: &[i32; 256]) -> [i32; 256] {
    const Q: i64 = 8_380_417;
    let mut out = [0i64; 256];
    for i in 0..256 {
        let ai = (a[i] as i64).rem_euclid(Q);
        for j in 0..256 {
            let bj = (b[j] as i64).rem_euclid(Q);
            let prod = (ai * bj) % Q;
            if i + j < 256 {
                out[i + j] = (out[i + j] + prod).rem_euclid(Q);
            } else {
                out[i + j - 256] = (out[i + j - 256] - prod).rem_euclid(Q);
            }
        }
    }
    let mut res = [0i32; 256];
    for (dst, &v) in res.iter_mut().zip(out.iter()) {
        *dst = v as i32;
    }
    res
}

/// Reference Goldilocks multiplication in `u128` -> canonical `[0, p)`.
#[inline]
pub const fn goldilocks_mul_u128_ref(a: u64, b: u64) -> u64 {
    (((a as u128) * (b as u128)) % (GOLDILOCKS_PRIME as u128)) as u64
}
