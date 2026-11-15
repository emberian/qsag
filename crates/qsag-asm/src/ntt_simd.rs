//! Seiler (`IACR ePrint 2018/039`) Signed-Montgomery `AVX2` (`8 x i32`) and `AVX-512` (`16 x i32`)
//! constant-time Number-Theoretic Transform (`NTT`, `InvNTT`, and `PointwiseMul`) for NIST FIPS 204
//! `ML-DSA` ($q = 8\_380\_417 = 2^{23} - 2^{13} + 1$, $N = 256$, $\zeta = 1753$).
//!
//! Bit-for-bit identical (`[0, q)` canonical input and output) to scalar FIPS 204 Algorithms 41,
//! 42, and 45, with zero secret-dependent branches, zero variable shifts, zero hardware divisions,
//! and explicit live-at-`ret` SIMD register zeroization (`vpxor`/`vxorps` + `vzeroupper`).

use crate::cpuid::{self, SimdBackend};

/// FIPS 204 prime modulus $q = 8\_380\_417$.
pub const MLDSA_Q: u32 = 8_380_417;
/// Cyclotomic degree $N = 256$.
pub const MLDSA_N: usize = 256;
/// Primitive 512th root of unity $\zeta = 1753 \bmod q$.
const MLDSA_ZETA: u32 = 1753;
/// $256^{-1} \bmod q = 8\_347\_681$.
const MLDSA_INV_256: u32 = 8_347_681;
/// $q^{-1} \bmod^\pm 2^{32} = 58\_728\_449$ (`8380417 * 58728449 == 1 mod 2^32`).
const MLDSA_QINV: i32 = 58_728_449;
/// $2^{64} \bmod q = 2\_365\_951$.
const MLDSA_R2_MOD_Q: i32 = 2_365_951;

const fn bitrev8(mut x: u8) -> u8 {
    let mut out = 0u8;
    let mut i = 0;
    while i < 8 {
        out = (out << 1) | (x & 1);
        x >>= 1;
        i += 1;
    }
    out
}

/// Division-free constant-time modular multiplication in `const` context (`a, b < q`).
const fn fq_mul_const(a: u32, b: u32) -> u32 {
    const BARRETT_M64: u128 = (1u128 << 64) / (MLDSA_Q as u128);
    let prod = (a as u64) * (b as u64);
    let q_est = (((prod as u128) * BARRETT_M64) >> 64) as u64;
    let rem = prod - q_est * (MLDSA_Q as u64);
    if rem >= (MLDSA_Q as u64) {
        (rem - (MLDSA_Q as u64)) as u32
    } else {
        rem as u32
    }
}

const fn fq_pow_const(mut base: u32, mut exp: u32) -> u32 {
    let mut acc = 1u32;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = fq_mul_const(acc, base);
        }
        base = fq_mul_const(base, base);
        exp >>= 1;
    }
    acc
}

/// Center `[0, q)` representative into `(-q/2, q/2)`.
const fn center_mod_q(x: u32) -> i32 {
    if x > (MLDSA_Q / 2) {
        (x as i32) - (MLDSA_Q as i32)
    } else {
        x as i32
    }
}

/// Convert `x in [0, q)` to centered signed Montgomery representative `(x * 2^32) mod^+- q`.
const fn to_mont_centered(x: u32) -> i32 {
    // `2^32 mod 8380417 = 4294967296 - 512 * 8380417 - 4193792 = 4193792`
    const R_MOD_Q: u32 = ((1u64 << 32) % (MLDSA_Q as u64)) as u32;
    center_mod_q(fq_mul_const(x, R_MOD_Q))
}

#[repr(C, align(64))]
struct NttMontTables {
    /// `ZETAS_MONT[i] = (1753^{BitRev_8(i)} * 2^32) mod^+- q`.
    zetas_mont: [i32; MLDSA_N],
    /// `NEG_ZETAS_MONT[i] = (-1753^{BitRev_8(i)} * 2^32) mod^+- q`.
    neg_zetas_mont: [i32; MLDSA_N],
    /// `(256^{-1} * 2^32) mod^+- q` for fused final `InvNTT` stage (`len = 128`).
    inv256_mont: i32,
    /// `(-ZETAS[1] * 256^{-1} * 2^32) mod^+- q` for fused final `InvNTT` stage (`len = 128`).
    neg_zeta1_inv256_mont: i32,
}

const fn build_ntt_mont_tables() -> NttMontTables {
    let mut zetas = [0u32; MLDSA_N];
    let mut zetas_mont = [0i32; MLDSA_N];
    let mut neg_zetas_mont = [0i32; MLDSA_N];
    let mut i = 0usize;
    while i < MLDSA_N {
        let z = fq_pow_const(MLDSA_ZETA, bitrev8(i as u8) as u32);
        zetas[i] = z;
        zetas_mont[i] = to_mont_centered(z);
        let z_neg = if z == 0 { 0 } else { MLDSA_Q - z };
        neg_zetas_mont[i] = to_mont_centered(z_neg);
        i += 1;
    }
    let inv256_mont = to_mont_centered(MLDSA_INV_256);
    let neg_z1 = MLDSA_Q - zetas[1];
    let neg_zeta1_inv256_mont = to_mont_centered(fq_mul_const(neg_z1, MLDSA_INV_256));
    NttMontTables {
        zetas_mont,
        neg_zetas_mont,
        inv256_mont,
        neg_zeta1_inv256_mont,
    }
}

static NTT_TABLES: NttMontTables = build_ntt_mont_tables();

// Compile-time verification of Seiler signed Montgomery identity on edge values.
const _: () = {
    assert!(
        (MLDSA_Q as i32).wrapping_mul(MLDSA_QINV) == 1,
        "Q * QINV must equal 1 mod 2^32"
    );
    let a = ((MLDSA_Q - 1) as i64) * (NTT_TABLES.inv256_mont as i64);
    let t = (a as i32).wrapping_mul(MLDSA_QINV);
    let r = ((a - (t as i64) * (MLDSA_Q as i64)) >> 32) as i32;
    let canon = r + ((r >> 31) & (MLDSA_Q as i32));
    let exp = fq_mul_const(MLDSA_Q - 1, MLDSA_INV_256) as i32;
    assert!(canon == exp, "Seiler signed Montgomery reduction mismatch");
};

/// Constant-time portable Seiler Montgomery reduction `(a * b_mont * 2^{-32}) mod^+- q`.
#[inline(always)]
const fn mont_mul_scalar(a: i32, b_mont: i32) -> i32 {
    let prod = (a as i64) * (b_mont as i64);
    let t = (prod as i32).wrapping_mul(MLDSA_QINV);
    ((prod - (t as i64) * (MLDSA_Q as i64)) >> 32) as i32
}

/// Constant-time canonicalization of `|a| <= 250 * q` into `[0, q)`.
#[inline(always)]
const fn canon_0_q_scalar(a: i32) -> u32 {
    let t = (a + (1 << 22)) >> 23;
    let r = a - t * (MLDSA_Q as i32);
    (r + ((r >> 31) & (MLDSA_Q as i32))) as u32
}

/// Portable constant-time FIPS 204 forward `NTT` (`Algorithm 41`).
#[cfg_attr(target_arch = "x86_64", inline(never))]
pub fn mldsa_ntt_portable(coeffs: &mut [u32; MLDSA_N]) {
    let mut s = [0i32; MLDSA_N];
    for (dst, &src) in s.iter_mut().zip(coeffs.iter()) {
        *dst = src as i32;
    }

    macro_rules! ct_stage {
        ($len:literal, $m_base:literal) => {{
            let mut blk = 0usize;
            while blk < (MLDSA_N / (2 * $len)) {
                let z = NTT_TABLES.zetas_mont[$m_base + blk];
                let start = blk * (2 * $len);
                let mut j = 0usize;
                while j < $len {
                    let lo = s[start + j];
                    let t = mont_mul_scalar(s[start + $len + j], z);
                    s[start + $len + j] = lo - t;
                    s[start + j] = lo + t;
                    j += 1;
                }
                blk += 1;
            }
        }};
    }

    ct_stage!(128, 1);
    ct_stage!(64, 2);
    ct_stage!(32, 4);
    ct_stage!(16, 8);
    ct_stage!(8, 16);
    ct_stage!(4, 32);
    ct_stage!(2, 64);
    ct_stage!(1, 128);

    for (dst, &val) in coeffs.iter_mut().zip(s.iter()) {
        *dst = canon_0_q_scalar(val);
    }
    crate::volatile_fill(&mut s, 0);
}

/// Portable constant-time FIPS 204 inverse `InvNTT` (`Algorithm 42`).
#[cfg_attr(target_arch = "x86_64", inline(never))]
pub fn mldsa_inv_ntt_portable(coeffs: &mut [u32; MLDSA_N]) {
    let mut s = [0i32; MLDSA_N];
    for (dst, &src) in s.iter_mut().zip(coeffs.iter()) {
        *dst = src as i32;
    }

    macro_rules! gs_stage {
        ($len:literal, $m_top:literal) => {{
            let mut blk = 0usize;
            while blk < (MLDSA_N / (2 * $len)) {
                let z_neg = NTT_TABLES.neg_zetas_mont[$m_top - blk];
                let start = blk * (2 * $len);
                let mut j = 0usize;
                while j < $len {
                    let lo = s[start + j];
                    let hi = s[start + $len + j];
                    s[start + j] = lo + hi;
                    s[start + $len + j] = mont_mul_scalar(lo - hi, z_neg);
                    j += 1;
                }
                blk += 1;
            }
        }};
    }

    gs_stage!(1, 255);
    gs_stage!(2, 127);
    gs_stage!(4, 63);
    gs_stage!(8, 31);
    gs_stage!(16, 15);
    gs_stage!(32, 7);
    for slot in &mut s {
        let t = (*slot + (1 << 22)) >> 23;
        *slot -= t * (MLDSA_Q as i32);
    }
    gs_stage!(64, 3);

    // Fused `len = 128` (`m = 1`) + `256^{-1} mod q` scaling + canonicalization into `[0, q)`
    let inv256_m = NTT_TABLES.inv256_mont;
    let neg_z1_inv256_m = NTT_TABLES.neg_zeta1_inv256_mont;
    let mut j = 0usize;
    while j < 128 {
        let lo = s[j];
        let hi = s[128 + j];
        let r0 = mont_mul_scalar(lo + hi, inv256_m);
        let r1 = mont_mul_scalar(lo - hi, neg_z1_inv256_m);
        coeffs[j] = (r0 + ((r0 >> 31) & (MLDSA_Q as i32))) as u32;
        coeffs[128 + j] = (r1 + ((r1 >> 31) & (MLDSA_Q as i32))) as u32;
        j += 1;
    }
    crate::volatile_fill(&mut s, 0);
}

/// Portable constant-time FIPS 204 pointwise NTT multiplication (`Algorithm 45`).
pub fn mldsa_pointwise_mul_portable(
    out: &mut [u32; MLDSA_N],
    lhs: &[u32; MLDSA_N],
    rhs: &[u32; MLDSA_N],
) {
    for i in 0..MLDSA_N {
        let b_mont = mont_mul_scalar(rhs[i] as i32, MLDSA_R2_MOD_Q);
        let r = mont_mul_scalar(lhs[i] as i32, b_mont);
        out[i] = (r + ((r >> 31) & (MLDSA_Q as i32))) as u32;
    }
}

/// Runtime-dispatched constant-time FIPS 204 forward `NTT` (`Algorithm 41`).
#[inline]
pub fn mldsa_ntt(coeffs: &mut [u32; MLDSA_N]) {
    mldsa_ntt_with_backend(coeffs, cpuid::detect_backend());
}

/// Explicit-backend constant-time FIPS 204 forward `NTT`.
pub fn mldsa_ntt_with_backend(coeffs: &mut [u32; MLDSA_N], backend: SimdBackend) {
    #[cfg(target_arch = "x86_64")]
    {
        let cap_bits = cpuid::probe_capabilities_bits();
        if backend == SimdBackend::X86Avx512GfniVpclmul && (cap_bits & cpuid::CAP_AVX512) != 0 {
            // SAFETY: `CAP_AVX512` verified `AVX512F + AVX512DQ + AVX512BW + AVX512VL` and OS ZMM.
            unsafe {
                x86_simd::mldsa_ntt_avx512(coeffs);
            }
            return;
        }
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul
                | SimdBackend::X86Avx2GfniVpclmul
                | SimdBackend::X86Avx512GfniVpclmul
        ) && (cap_bits & cpuid::CAP_AVX2) != 0
        {
            // SAFETY: `CAP_AVX2` verified CPUID AVX2 and OS YMM state.
            unsafe {
                x86_simd::mldsa_ntt_avx2(coeffs);
            }
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
    let _ = backend;
    mldsa_ntt_portable(coeffs);
}

/// Runtime-dispatched constant-time FIPS 204 inverse `InvNTT` (`Algorithm 42`).
#[inline]
pub fn mldsa_inv_ntt(coeffs: &mut [u32; MLDSA_N]) {
    mldsa_inv_ntt_with_backend(coeffs, cpuid::detect_backend());
}

/// Explicit-backend constant-time FIPS 204 inverse `InvNTT`.
pub fn mldsa_inv_ntt_with_backend(coeffs: &mut [u32; MLDSA_N], backend: SimdBackend) {
    #[cfg(target_arch = "x86_64")]
    {
        let cap_bits = cpuid::probe_capabilities_bits();
        if backend == SimdBackend::X86Avx512GfniVpclmul && (cap_bits & cpuid::CAP_AVX512) != 0 {
            unsafe {
                x86_simd::mldsa_inv_ntt_avx512(coeffs);
            }
            return;
        }
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul
                | SimdBackend::X86Avx2GfniVpclmul
                | SimdBackend::X86Avx512GfniVpclmul
        ) && (cap_bits & cpuid::CAP_AVX2) != 0
        {
            unsafe {
                x86_simd::mldsa_inv_ntt_avx2(coeffs);
            }
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
    let _ = backend;
    mldsa_inv_ntt_portable(coeffs);
}

/// Runtime-dispatched constant-time FIPS 204 pointwise NTT multiplication (`Algorithm 45`).
#[inline]
pub fn mldsa_pointwise_mul(
    out: &mut [u32; MLDSA_N],
    lhs: &[u32; MLDSA_N],
    rhs: &[u32; MLDSA_N],
) {
    mldsa_pointwise_mul_with_backend(out, lhs, rhs, cpuid::detect_backend());
}

/// Explicit-backend constant-time FIPS 204 pointwise NTT multiplication.
