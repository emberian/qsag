//! 100% constant-time, branchless, LUT-free arithmetic in $\mathbb{F}_{2^{128}}$ for 2-lane BDOZ
//! MAC dot products (`bdoz_gf2_128_batch_dot`) and Wiedemann binary tower $\mathcal{T}_7$.

use qsag_asm::portable;

use crate::AccelError;

/// Irreducible pentanomial $x^{128} + x^7 + x^2 + x + 1$ (`0x87` low reduction polynomial).
pub const GF2_128_POLY_LO: u128 = 0x87;

/// Constant-time branchless multiplication in $\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$
/// usable in `const` evaluation contexts (`0` lookup tables, `0` secret-dependent branches).
#[inline]
pub const fn gf2_128_mul_const(a: u128, b: u128) -> u128 {
    portable::poly128_mul_const(a, b)
}

/// Constant-time multiplication in $\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$.
/// Dispatches through certified carry-less `PCLMULQDQ` / `VPCLMULQDQ` / `PMULL` kernels in
/// `qsag_asm` (with `PSTATE.DIT` guard on `aarch64` and branchless portable fallback).
#[inline]
pub fn gf2_128_mul(a: u128, b: u128) -> u128 {
    let mut acc = [0u64; 2];
    let lhs = [[a as u64, (a >> 64) as u64]];
    let rhs = [[b as u64, (b >> 64) as u64]];
    qsag_asm::gf2_128_mul_acc_batch(&mut acc, &lhs, &rhs);
    u128::from(acc[0]) | (u128::from(acc[1]) << 64)
}

/// Constant-time squaring in $\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$.
#[inline]
pub const fn gf2_128_sq(a: u128) -> u128 {
    gf2_128_mul_const(a, a)
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
    let x2 = gf2_128_mul_const(gf2_128_sq(x1), x1); // a^{2^2 - 1}
    let x4 = gf2_128_mul_const(gf2_128_exp_pow2(x2, 2), x2); // a^{2^4 - 1}
    let x8 = gf2_128_mul_const(gf2_128_exp_pow2(x4, 4), x4); // a^{2^8 - 1}
    let x16 = gf2_128_mul_const(gf2_128_exp_pow2(x8, 8), x8); // a^{2^16 - 1}
    let x32 = gf2_128_mul_const(gf2_128_exp_pow2(x16, 16), x16); // a^{2^32 - 1}
    let x64 = gf2_128_mul_const(gf2_128_exp_pow2(x32, 32), x32); // a^{2^64 - 1}
    let x96 = gf2_128_mul_const(gf2_128_exp_pow2(x64, 32), x32);
    let x112 = gf2_128_mul_const(gf2_128_exp_pow2(x96, 16), x16);
    let x120 = gf2_128_mul_const(gf2_128_exp_pow2(x112, 8), x8);
    let x124 = gf2_128_mul_const(gf2_128_exp_pow2(x120, 4), x4);
    let x126 = gf2_128_mul_const(gf2_128_exp_pow2(x124, 2), x2);
    let x127 = gf2_128_mul_const(gf2_128_sq(x126), x1); // a^{2^127 - 1}
    gf2_128_sq(x127) // a^{2^128 - 2}
}

/// Constant-time Wiedemann binary tower $\mathcal{T}_k$ multiplication at level `k`, matching
/// `lean/Qsag/Math/Gf2Pow128.lean`. Operands are read modulo $2^{2^k}$.
///
/// # Panics
/// Panics if `k > 7`: the tower stops at $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$.
#[inline]
pub const fn tower_mul_bits(k: u32, a: u128, b: u128) -> u128 {
    match k {
        0 => a & b & 1,
        1 => portable::tower_mul_t1(a as u8 & 0x3, b as u8 & 0x3) as u128,
        2 => portable::tower_mul_t2(a as u8 & 0xF, b as u8 & 0xF) as u128,
        3 => portable::wiedemann_mul_t3_u8(a as u8, b as u8) as u128,
        4 => portable::tower_mul_t4(a as u16, b as u16) as u128,
        5 => portable::tower_mul_t5(a as u32, b as u32) as u128,
        6 => portable::tower_mul_t6(a as u64, b as u64) as u128,
        7 => portable::wiedemann_mul_t7_u128(a, b),
        _ => panic!("Wiedemann tower level above 7"),
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
    #[cfg(feature = "std")]
    {
        // SIMD already handles small batches cheaply; amortize thread startup over 128K
        // pairs per worker (parallelize only at 256K+ pairs).
        let workers = crate::cpu_workers(shares.len(), 131_072);
        if workers > 1 {
            let chunk_len = shares.len().div_ceil(workers);
            let acc = std::sync::Mutex::new((0u128, 0u128));
            let chunks = shares.chunks(chunk_len).zip(weights.chunks(chunk_len));
            crate::cpu_drain(workers, chunks, |(s, w)| {
                let partial = bdoz_dot_chunk(s, w);
                let mut acc = acc
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                acc.0 ^= partial.0;
                acc.1 ^= partial.1;
            });
            return Ok(acc
                .into_inner()
                .unwrap_or_else(std::sync::PoisonError::into_inner));
        }
    }
    Ok(bdoz_dot_chunk(shares, weights))
}

// Each worker batches through the carry-less SIMD dispatcher and wipes its packing buffers.
fn bdoz_dot_chunk(shares: &[(u128, u128)], weights: &[(u128, u128)]) -> (u128, u128) {
    const CHUNK: usize = 256;
    let mut acc0 = [0u64; 2];
    let mut acc1 = [0u64; 2];
    let mut s0_buf = [[0u64; 2]; CHUNK];
    let mut s1_buf = [[0u64; 2]; CHUNK];
    let mut w0_buf = [[0u64; 2]; CHUNK];
    let mut w1_buf = [[0u64; 2]; CHUNK];
    for (s_chunk, w_chunk) in shares.chunks(CHUNK).zip(weights.chunks(CHUNK)) {
        let n = s_chunk.len();
        for i in 0..n {
            let (s0, s1) = s_chunk[i];
            let (w0, w1) = w_chunk[i];
            s0_buf[i] = [s0 as u64, (s0 >> 64) as u64];
            s1_buf[i] = [s1 as u64, (s1 >> 64) as u64];
            w0_buf[i] = [w0 as u64, (w0 >> 64) as u64];
            w1_buf[i] = [w1 as u64, (w1 >> 64) as u64];
        }
        qsag_asm::gf2_128_mul_acc_batch(&mut acc0, &s0_buf[..n], &w0_buf[..n]);
        qsag_asm::gf2_128_mul_acc_batch(&mut acc1, &s1_buf[..n], &w1_buf[..n]);
    }
    qsag_asm::volatile_fill(&mut s0_buf, [0u64; 2]);
    qsag_asm::volatile_fill(&mut s1_buf, [0u64; 2]);
    qsag_asm::volatile_fill(&mut w0_buf, [0u64; 2]);
    qsag_asm::volatile_fill(&mut w1_buf, [0u64; 2]);
    let lane0 = u128::from(acc0[0]) | (u128::from(acc0[1]) << 64);
    let lane1 = u128::from(acc1[0]) | (u128::from(acc1[1]) << 64);
    qsag_asm::volatile_fill(&mut acc0, 0);
    qsag_asm::volatile_fill(&mut acc1, 0);
    (lane0, lane1)
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
    fn every_tower_level_is_the_subfield_of_the_top_level() {
        // Exhaustive through T_2, then the generators and their sums at each higher level.
        for k in 0..=2u32 {
            let size = 1u128 << (1 << k);
            for a in 0..size {
                for b in 0..size {
                    assert_eq!(tower_mul_bits(k, a, b), tower_mul_bits(7, a, b), "T_{k}");
                    // Operands are read modulo the level's width.
                    assert_eq!(
                        tower_mul_bits(k, a | size, b | (size << 3)),
                        tower_mul_bits(k, a, b)
                    );
                }
            }
        }
        for k in 3..=6u32 {
            let width = 1u32 << k;
            let mask = (1u128 << width) - 1;
            let mut x = 0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c835u128;
            for i in 0..width {
                for j in 0..width {
                    x = x
                        .wrapping_mul(0x2360_ed05_1fc6_5da4_4385_df64_9fcc_f645)
                        .wrapping_add(1);
                    for (a, b) in [(1u128 << i, 1u128 << j), (x & mask, (x >> 64 ^ x) & mask)] {
                        assert_eq!(tower_mul_bits(k, a, b), tower_mul_bits(7, a, b), "T_{k}");
                        assert_eq!(
                            tower_mul_bits(k, a | !mask, b | !mask),
                            tower_mul_bits(k, a, b)
                        );
                    }
                }
            }
        }
    }
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
                let hw = gf2_128_mul(pa.0, pb.0);
                assert_eq!(hw, gf2_128_mul_const(pa.0, pb.0));
                assert_eq!(PolyGf2_128::from(WiedemannTower128(product)).0, hw);
            }
        }
    }
}
