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
pub(crate) const MLDSA_QINV: i32 = 58_728_449;
/// $2^{64} \bmod q = 2\_365\_951$.
pub(crate) const MLDSA_R2_MOD_Q: i32 = 2_365_951;

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
pub(crate) struct NttMontTables {
    /// `ZETAS_MONT[i] = (1753^{BitRev_8(i)} * 2^32) mod^+- q`.
    pub(crate) zetas_mont: [i32; MLDSA_N],
    /// `NEG_ZETAS_MONT[i] = (-1753^{BitRev_8(i)} * 2^32) mod^+- q`.
    pub(crate) neg_zetas_mont: [i32; MLDSA_N],
    /// `(256^{-1} * 2^32) mod^+- q` for fused final `InvNTT` stage (`len = 128`).
    pub(crate) inv256_mont: i32,
    /// `(-ZETAS[1] * 256^{-1} * 2^32) mod^+- q` for fused final `InvNTT` stage (`len = 128`).
    pub(crate) neg_zeta1_inv256_mont: i32,
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

pub(crate) static NTT_TABLES: NttMontTables = build_ntt_mont_tables();

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
    {
        if backend == SimdBackend::Aarch64NeonSha3Pmull
            && (cpuid::probe_capabilities_bits() & cpuid::CAP_A64_NEON) != 0
        {
            // SAFETY: `CAP_A64_NEON` verified runtime NEON; `mldsa_ntt_neon` acquires a scoped
            // `FEAT_DIT` guard and wipes volatile NEON scratch registers before `ret`.
            unsafe {
                crate::aarch64_simd::mldsa_ntt_neon(coeffs);
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
    {
        if backend == SimdBackend::Aarch64NeonSha3Pmull
            && (cpuid::probe_capabilities_bits() & cpuid::CAP_A64_NEON) != 0
        {
            // SAFETY: `CAP_A64_NEON` verified runtime NEON; `mldsa_inv_ntt_neon` acquires a scoped
            // `FEAT_DIT` guard and wipes volatile NEON scratch registers before `ret`.
            unsafe {
                crate::aarch64_simd::mldsa_inv_ntt_neon(coeffs);
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
pub fn mldsa_pointwise_mul(out: &mut [u32; MLDSA_N], lhs: &[u32; MLDSA_N], rhs: &[u32; MLDSA_N]) {
    mldsa_pointwise_mul_with_backend(out, lhs, rhs, cpuid::detect_backend());
}

/// Explicit-backend constant-time FIPS 204 pointwise NTT multiplication.
pub fn mldsa_pointwise_mul_with_backend(
    out: &mut [u32; MLDSA_N],
    lhs: &[u32; MLDSA_N],
    rhs: &[u32; MLDSA_N],
    backend: SimdBackend,
) {
    #[cfg(target_arch = "x86_64")]
    {
        let cap_bits = cpuid::probe_capabilities_bits();
        if backend == SimdBackend::X86Avx512GfniVpclmul && (cap_bits & cpuid::CAP_AVX512) != 0 {
            unsafe {
                x86_simd::mldsa_pointwise_mul_avx512(out, lhs, rhs);
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
                x86_simd::mldsa_pointwise_mul_avx2(out, lhs, rhs);
            }
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if backend == SimdBackend::Aarch64NeonSha3Pmull
            && (cpuid::probe_capabilities_bits() & cpuid::CAP_A64_NEON) != 0
        {
            // SAFETY: `CAP_A64_NEON` verified runtime NEON; `mldsa_pointwise_mul_neon` acquires a
            // scoped `FEAT_DIT` guard and wipes volatile NEON scratch registers before `ret`.
            unsafe {
                crate::aarch64_simd::mldsa_pointwise_mul_neon(out, lhs, rhs);
            }
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
    let _ = backend;
    mldsa_pointwise_mul_portable(out, lhs, rhs);
}

#[cfg(target_arch = "x86_64")]
#[allow(clippy::incompatible_msrv)]
mod x86_simd {
    use core::arch::x86_64::*;

    use super::{MLDSA_N, MLDSA_Q, MLDSA_QINV, MLDSA_R2_MOD_Q, NTT_TABLES};

    /// Seiler (`2018/039`) 8-lane signed Montgomery multiplication `(a * b_mont * 2^{-32}) mod^+- q`.
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn fqmul_avx2(a: __m256i, b_mont: __m256i, qinv: __m256i, q: __m256i) -> __m256i {
        let prod_ev = _mm256_mul_epi32(a, b_mont);
        let a_od = _mm256_srli_epi64::<32>(a);
        let b_od = _mm256_srli_epi64::<32>(b_mont);
        let prod_od = _mm256_mul_epi32(a_od, b_od);

        let m_ev = _mm256_mul_epi32(prod_ev, qinv);
        let m_od = _mm256_mul_epi32(prod_od, qinv);

        let u_ev = _mm256_mul_epi32(m_ev, q);
        let u_od = _mm256_mul_epi32(m_od, q);

        let d_ev = _mm256_srli_epi64::<32>(_mm256_sub_epi64(prod_ev, u_ev));
        let d_od = _mm256_sub_epi64(prod_od, u_od);

        _mm256_blend_epi32::<0xAA>(d_ev, d_od)
    }

    /// Broadcast-twiddle fast path (saves `vpsrlq` on `b_mont`).
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn fqmul_bcast_avx2(a: __m256i, z_bcast: __m256i, qinv: __m256i, q: __m256i) -> __m256i {
        let prod_ev = _mm256_mul_epi32(a, z_bcast);
        let a_od = _mm256_srli_epi64::<32>(a);
        let prod_od = _mm256_mul_epi32(a_od, z_bcast);

        let m_ev = _mm256_mul_epi32(prod_ev, qinv);
        let m_od = _mm256_mul_epi32(prod_od, qinv);

        let u_ev = _mm256_mul_epi32(m_ev, q);
        let u_od = _mm256_mul_epi32(m_od, q);

        let d_ev = _mm256_srli_epi64::<32>(_mm256_sub_epi64(prod_ev, u_ev));
        let d_od = _mm256_sub_epi64(prod_od, u_od);

        _mm256_blend_epi32::<0xAA>(d_ev, d_od)
    }

    /// Shift-add centered reduction `r = a - ((a + 2^22) >> 23) * q` (`|r| < q` for `|a| <= 250 q`).
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn reduce32_avx2(a: __m256i, half23: __m256i, q: __m256i) -> __m256i {
        let t = _mm256_srai_epi32::<23>(_mm256_add_epi32(a, half23));
        _mm256_sub_epi32(a, _mm256_mullo_epi32(t, q))
    }

    /// Map `r in (-q, q)` to canonical `[0, q)`.
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn caddq_avx2(r: __m256i, q: __m256i) -> __m256i {
        let mask = _mm256_srai_epi32::<31>(r);
        _mm256_add_epi32(r, _mm256_and_si256(mask, q))
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn wipe_ymm_and_zeroupper() {
        unsafe {
            core::arch::asm!(
                "vpxor ymm0,  ymm0,  ymm0",
                "vpxor ymm1,  ymm1,  ymm1",
                "vpxor ymm2,  ymm2,  ymm2",
                "vpxor ymm3,  ymm3,  ymm3",
                "vpxor ymm4,  ymm4,  ymm4",
                "vpxor ymm5,  ymm5,  ymm5",
                "vpxor ymm6,  ymm6,  ymm6",
                "vpxor ymm7,  ymm7,  ymm7",
                "vpxor ymm8,  ymm8,  ymm8",
                "vpxor ymm9,  ymm9,  ymm9",
                "vpxor ymm10, ymm10, ymm10",
                "vpxor ymm11, ymm11, ymm11",
                "vpxor ymm12, ymm12, ymm12",
                "vpxor ymm13, ymm13, ymm13",
                "vpxor ymm14, ymm14, ymm14",
                "vpxor ymm15, ymm15, ymm15",
                "vzeroupper",
                out("ymm0") _, out("ymm1") _, out("ymm2") _, out("ymm3") _,
                out("ymm4") _, out("ymm5") _, out("ymm6") _, out("ymm7") _,
                out("ymm8") _, out("ymm9") _, out("ymm10") _, out("ymm11") _,
                out("ymm12") _, out("ymm13") _, out("ymm14") _, out("ymm15") _,
                options(nostack),
            );
        }
    }

    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn wipe_zmm_and_zeroupper() {
        unsafe {
            core::arch::asm!(
                "vxorps zmm0,  zmm0,  zmm0",
                "vxorps zmm1,  zmm1,  zmm1",
                "vxorps zmm2,  zmm2,  zmm2",
                "vxorps zmm3,  zmm3,  zmm3",
                "vxorps zmm4,  zmm4,  zmm4",
                "vxorps zmm5,  zmm5,  zmm5",
                "vxorps zmm6,  zmm6,  zmm6",
                "vxorps zmm7,  zmm7,  zmm7",
                "vxorps zmm8,  zmm8,  zmm8",
                "vxorps zmm9,  zmm9,  zmm9",
                "vxorps zmm10, zmm10, zmm10",
                "vxorps zmm11, zmm11, zmm11",
                "vxorps zmm12, zmm12, zmm12",
                "vxorps zmm13, zmm13, zmm13",
                "vxorps zmm14, zmm14, zmm14",
                "vxorps zmm15, zmm15, zmm15",
                "vxorps zmm16, zmm16, zmm16",
                "vxorps zmm17, zmm17, zmm17",
                "vxorps zmm18, zmm18, zmm18",
                "vxorps zmm19, zmm19, zmm19",
                "vxorps zmm20, zmm20, zmm20",
                "vxorps zmm21, zmm21, zmm21",
                "vxorps zmm22, zmm22, zmm22",
                "vxorps zmm23, zmm23, zmm23",
                "vxorps zmm24, zmm24, zmm24",
                "vxorps zmm25, zmm25, zmm25",
                "vxorps zmm26, zmm26, zmm26",
                "vxorps zmm27, zmm27, zmm27",
                "vxorps zmm28, zmm28, zmm28",
                "vxorps zmm29, zmm29, zmm29",
                "vxorps zmm30, zmm30, zmm30",
                "vxorps zmm31, zmm31, zmm31",
                "vzeroupper",
                out("zmm0") _, out("zmm1") _, out("zmm2") _, out("zmm3") _,
                out("zmm4") _, out("zmm5") _, out("zmm6") _, out("zmm7") _,
                out("zmm8") _, out("zmm9") _, out("zmm10") _, out("zmm11") _,
                out("zmm12") _, out("zmm13") _, out("zmm14") _, out("zmm15") _,
                out("zmm16") _, out("zmm17") _, out("zmm18") _, out("zmm19") _,
                out("zmm20") _, out("zmm21") _, out("zmm22") _, out("zmm23") _,
                out("zmm24") _, out("zmm25") _, out("zmm26") _, out("zmm27") _,
                out("zmm28") _, out("zmm29") _, out("zmm30") _, out("zmm31") _,
                options(nostack),
            );
        }
    }

    /// Constant-time 8-lane `AVX2` FIPS 204 forward `NTT` (`Algorithm 41`).
    #[inline(never)]
    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn mldsa_ntt_avx2(coeffs: &mut [u32; MLDSA_N]) {
        let p = coeffs.as_mut_ptr().cast::<__m256i>();
        let zp = NTT_TABLES.zetas_mont.as_ptr();
        let qinv = _mm256_set1_epi32(MLDSA_QINV);
        let q = _mm256_set1_epi32(MLDSA_Q as i32);
        let half23 = _mm256_set1_epi32(1 << 22);

        // SAFETY: `p` points to 32 valid `__m256i` vectors (256 x u32) and `zp` points to 256 i32s;
        // raw pointer offsets use compile-time bounded indices (`0..32`), emitting zero panic calls.
        unsafe {
            macro_rules! vec_ct_stage {
                ($vecs_per_half:literal, $blocks:literal, $m_base:literal) => {{
                    let mut blk = 0usize;
                    while blk < $blocks {
                        let z = _mm256_set1_epi32(*zp.add($m_base + blk));
                        let base = blk * (2 * $vecs_per_half);
                        let mut v = 0usize;
                        while v < $vecs_per_half {
                            let lo = _mm256_loadu_si256(p.add(base + v));
                            let hi = _mm256_loadu_si256(p.add(base + $vecs_per_half + v));
                            let t = fqmul_bcast_avx2(hi, z, qinv, q);
                            _mm256_storeu_si256(p.add(base + v), _mm256_add_epi32(lo, t));
                            _mm256_storeu_si256(
                                p.add(base + $vecs_per_half + v),
                                _mm256_sub_epi32(lo, t),
                            );
                            v += 1;
                        }
                        blk += 1;
                    }
                }};
            }

            // Stages len = 128, 64, 32, 16, 8
            vec_ct_stage!(16, 1, 1);
            vec_ct_stage!(8, 2, 2);
            vec_ct_stage!(4, 4, 4);
            vec_ct_stage!(2, 8, 8);
            vec_ct_stage!(1, 16, 16);

            // Fused in-register stages len = 4, 2, 1 + canonicalization into `[0, q)`
            let mut k = 0usize;
            while k < 16 {
                let mut v0 = _mm256_loadu_si256(p.add(2 * k));
                let mut v1 = _mm256_loadu_si256(p.add(2 * k + 1));

                // Stage len = 4 (`m = 32 + 2*k`, `32 + 2*k + 1`)
                let z4_0 = *zp.add(32 + 2 * k);
                let z4_1 = *zp.add(32 + 2 * k + 1);
                let z4 = _mm256_setr_epi32(z4_0, z4_0, z4_0, z4_0, z4_1, z4_1, z4_1, z4_1);
                let lo4 = _mm256_permute2x128_si256::<0x20>(v0, v1);
                let hi4 = _mm256_permute2x128_si256::<0x31>(v0, v1);
                let t4 = fqmul_avx2(hi4, z4, qinv, q);
                let s4 = _mm256_add_epi32(lo4, t4);
                let d4 = _mm256_sub_epi32(lo4, t4);
                v0 = _mm256_permute2x128_si256::<0x20>(s4, d4);
                v1 = _mm256_permute2x128_si256::<0x31>(s4, d4);

                // Stage len = 2 (`m = 64 + 4*k + 0..3`)
                let z2_a0 = *zp.add(64 + 4 * k);
                let z2_a1 = *zp.add(64 + 4 * k + 1);
                let z2_b0 = *zp.add(64 + 4 * k + 2);
                let z2_b1 = *zp.add(64 + 4 * k + 3);
                let z2 = _mm256_setr_epi32(z2_a0, z2_a0, z2_b0, z2_b0, z2_a1, z2_a1, z2_b1, z2_b1);
                let lo2 = _mm256_unpacklo_epi64(v0, v1);
                let hi2 = _mm256_unpackhi_epi64(v0, v1);
                let t2 = fqmul_avx2(hi2, z2, qinv, q);
                let s2 = _mm256_add_epi32(lo2, t2);
                let d2 = _mm256_sub_epi32(lo2, t2);
                v0 = _mm256_unpacklo_epi64(s2, d2);
                v1 = _mm256_unpackhi_epi64(s2, d2);

                // Stage len = 1 (`m = 128 + 8*k + 0..7`)
                let za0 = *zp.add(128 + 8 * k);
                let za1 = *zp.add(128 + 8 * k + 1);
                let za2 = *zp.add(128 + 8 * k + 2);
                let za3 = *zp.add(128 + 8 * k + 3);
                let zb0 = *zp.add(128 + 8 * k + 4);
                let zb1 = *zp.add(128 + 8 * k + 5);
                let zb2 = *zp.add(128 + 8 * k + 6);
                let zb3 = *zp.add(128 + 8 * k + 7);
                let z1 = _mm256_setr_epi32(za0, za1, zb0, zb1, za2, za3, zb2, zb3);
                let v0_sh = _mm256_shuffle_epi32::<0xD8>(v0);
                let v1_sh = _mm256_shuffle_epi32::<0xD8>(v1);
                let lo1 = _mm256_unpacklo_epi64(v0_sh, v1_sh);
                let hi1 = _mm256_unpackhi_epi64(v0_sh, v1_sh);
                let t1 = fqmul_avx2(hi1, z1, qinv, q);
                let s1 = _mm256_add_epi32(lo1, t1);
                let d1 = _mm256_sub_epi32(lo1, t1);
                v0 = _mm256_unpacklo_epi32(s1, d1);
                v1 = _mm256_unpackhi_epi32(s1, d1);

                v0 = caddq_avx2(reduce32_avx2(v0, half23, q), q);
                v1 = caddq_avx2(reduce32_avx2(v1, half23, q), q);
                _mm256_storeu_si256(p.add(2 * k), v0);
                _mm256_storeu_si256(p.add(2 * k + 1), v1);
                k += 1;
            }

            wipe_ymm_and_zeroupper();
        }
    }

    /// Constant-time 8-lane `AVX2` FIPS 204 inverse `InvNTT` (`Algorithm 42`).
    #[inline(never)]
    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn mldsa_inv_ntt_avx2(coeffs: &mut [u32; MLDSA_N]) {
        let p = coeffs.as_mut_ptr().cast::<__m256i>();
        let nzp = NTT_TABLES.neg_zetas_mont.as_ptr();
        let qinv = _mm256_set1_epi32(MLDSA_QINV);
        let q = _mm256_set1_epi32(MLDSA_Q as i32);
        let half23 = _mm256_set1_epi32(1 << 22);

        unsafe {
            // Fused in-register stages len = 1, 2, 4
            let mut k = 0usize;
            while k < 16 {
                let mut v0 = _mm256_loadu_si256(p.add(2 * k));
                let mut v1 = _mm256_loadu_si256(p.add(2 * k + 1));

                // Stage len = 1 (`m = 255 - (8*k + 0..7)`)
                let za0 = *nzp.add(255 - (8 * k));
                let za1 = *nzp.add(255 - (8 * k + 1));
                let za2 = *nzp.add(255 - (8 * k + 2));
                let za3 = *nzp.add(255 - (8 * k + 3));
                let zb0 = *nzp.add(255 - (8 * k + 4));
                let zb1 = *nzp.add(255 - (8 * k + 5));
                let zb2 = *nzp.add(255 - (8 * k + 6));
                let zb3 = *nzp.add(255 - (8 * k + 7));
                let z1 = _mm256_setr_epi32(za0, za1, zb0, zb1, za2, za3, zb2, zb3);
                let v0_sh = _mm256_shuffle_epi32::<0xD8>(v0);
                let v1_sh = _mm256_shuffle_epi32::<0xD8>(v1);
                let lo1 = _mm256_unpacklo_epi64(v0_sh, v1_sh);
                let hi1 = _mm256_unpackhi_epi64(v0_sh, v1_sh);
                let s1 = _mm256_add_epi32(lo1, hi1);
                let d1 = fqmul_avx2(_mm256_sub_epi32(lo1, hi1), z1, qinv, q);
                v0 = _mm256_unpacklo_epi32(s1, d1);
                v1 = _mm256_unpackhi_epi32(s1, d1);

                // Stage len = 2 (`m = 127 - (4*k + 0..3)`)
                let z2_a0 = *nzp.add(127 - (4 * k));
                let z2_a1 = *nzp.add(127 - (4 * k + 1));
                let z2_b0 = *nzp.add(127 - (4 * k + 2));
                let z2_b1 = *nzp.add(127 - (4 * k + 3));
                let z2 = _mm256_setr_epi32(z2_a0, z2_a0, z2_b0, z2_b0, z2_a1, z2_a1, z2_b1, z2_b1);
                let lo2 = _mm256_unpacklo_epi64(v0, v1);
                let hi2 = _mm256_unpackhi_epi64(v0, v1);
                let s2 = _mm256_add_epi32(lo2, hi2);
                let d2 = fqmul_avx2(_mm256_sub_epi32(lo2, hi2), z2, qinv, q);
                v0 = _mm256_unpacklo_epi64(s2, d2);
                v1 = _mm256_unpackhi_epi64(s2, d2);

                // Stage len = 4 (`m = 63 - 2*k`, `63 - (2*k + 1)`)
                let z4_0 = *nzp.add(63 - (2 * k));
                let z4_1 = *nzp.add(63 - (2 * k + 1));
                let z4 = _mm256_setr_epi32(z4_0, z4_0, z4_0, z4_0, z4_1, z4_1, z4_1, z4_1);
                let lo4 = _mm256_permute2x128_si256::<0x20>(v0, v1);
                let hi4 = _mm256_permute2x128_si256::<0x31>(v0, v1);
                let s4 = _mm256_add_epi32(lo4, hi4);
                let d4 = fqmul_avx2(_mm256_sub_epi32(lo4, hi4), z4, qinv, q);
                v0 = _mm256_permute2x128_si256::<0x20>(s4, d4);
                v1 = _mm256_permute2x128_si256::<0x31>(s4, d4);

                _mm256_storeu_si256(p.add(2 * k), v0);
                _mm256_storeu_si256(p.add(2 * k + 1), v1);
                k += 1;
            }

            macro_rules! vec_gs_stage {
                ($vecs_per_half:literal, $blocks:literal, $m_top:literal, $reduce_lo:literal) => {{
                    let mut blk = 0usize;
                    while blk < $blocks {
                        let z_neg = _mm256_set1_epi32(*nzp.add($m_top - blk));
                        let base = blk * (2 * $vecs_per_half);
                        let mut v = 0usize;
                        while v < $vecs_per_half {
                            let lo = _mm256_loadu_si256(p.add(base + v));
                            let hi = _mm256_loadu_si256(p.add(base + $vecs_per_half + v));
                            let mut sum = _mm256_add_epi32(lo, hi);
                            if $reduce_lo {
                                sum = reduce32_avx2(sum, half23, q);
                            }
                            let dif = fqmul_bcast_avx2(_mm256_sub_epi32(lo, hi), z_neg, qinv, q);
                            _mm256_storeu_si256(p.add(base + v), sum);
                            _mm256_storeu_si256(p.add(base + $vecs_per_half + v), dif);
                            v += 1;
                        }
                        blk += 1;
                    }
                }};
            }

            // Stages len = 8, 16, 32 (with lazy-bound reset at len = 32), 64
            vec_gs_stage!(1, 16, 31, false);
            vec_gs_stage!(2, 8, 15, false);
            vec_gs_stage!(4, 4, 7, true);
            vec_gs_stage!(8, 2, 3, false);

            // Fused stage len = 128 + `256^{-1} mod q` scaling + canonicalization into `[0, q)`
            let inv256_v = _mm256_set1_epi32(NTT_TABLES.inv256_mont);
            let neg_z1_inv256_v = _mm256_set1_epi32(NTT_TABLES.neg_zeta1_inv256_mont);
            let mut v = 0usize;
            while v < 16 {
                let lo = _mm256_loadu_si256(p.add(v));
                let hi = _mm256_loadu_si256(p.add(16 + v));
                let r0 = fqmul_bcast_avx2(_mm256_add_epi32(lo, hi), inv256_v, qinv, q);
                let r1 = fqmul_bcast_avx2(_mm256_sub_epi32(lo, hi), neg_z1_inv256_v, qinv, q);
                _mm256_storeu_si256(p.add(v), caddq_avx2(r0, q));
                _mm256_storeu_si256(p.add(16 + v), caddq_avx2(r1, q));
                v += 1;
            }

            wipe_ymm_and_zeroupper();
        }
    }

    /// Constant-time 8-lane `AVX2` pointwise NTT multiplication (`Algorithm 45`).
    #[target_feature(enable = "avx2")]
    pub(super) unsafe fn mldsa_pointwise_mul_avx2(
        out: &mut [u32; MLDSA_N],
        lhs: &[u32; MLDSA_N],
        rhs: &[u32; MLDSA_N],
    ) {
        let op = out.as_mut_ptr().cast::<__m256i>();
        let lp = lhs.as_ptr().cast::<__m256i>();
        let rp = rhs.as_ptr().cast::<__m256i>();
        let qinv = _mm256_set1_epi32(MLDSA_QINV);
        let q = _mm256_set1_epi32(MLDSA_Q as i32);
        let r2 = _mm256_set1_epi32(MLDSA_R2_MOD_Q);

        unsafe {
            let mut v = 0usize;
            while v < 32 {
                let a = _mm256_loadu_si256(lp.add(v));
                let b = _mm256_loadu_si256(rp.add(v));
                let b_mont = fqmul_bcast_avx2(b, r2, qinv, q);
                let prod = fqmul_avx2(a, b_mont, qinv, q);
                _mm256_storeu_si256(op.add(v), caddq_avx2(prod, q));
                v += 1;
            }
            wipe_ymm_and_zeroupper();
        }
    }

    /// Seiler (`2018/039`) 16-lane `AVX-512` signed Montgomery multiplication.
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn fqmul_avx512(a: __m512i, b_mont: __m512i, qinv: __m512i, q: __m512i) -> __m512i {
        let prod_ev = _mm512_mul_epi32(a, b_mont);
        let a_od = _mm512_srli_epi64::<32>(a);
        let b_od = _mm512_srli_epi64::<32>(b_mont);
        let prod_od = _mm512_mul_epi32(a_od, b_od);

        let m_ev = _mm512_mul_epi32(prod_ev, qinv);
        let m_od = _mm512_mul_epi32(prod_od, qinv);

        let u_ev = _mm512_mul_epi32(m_ev, q);
        let u_od = _mm512_mul_epi32(m_od, q);

        let d_ev = _mm512_srli_epi64::<32>(_mm512_sub_epi64(prod_ev, u_ev));
        let d_od = _mm512_sub_epi64(prod_od, u_od);

        _mm512_mask_blend_epi32(0xAAAA, d_ev, d_od)
    }

    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn fqmul_bcast_avx512(
        a: __m512i,
        z_bcast: __m512i,
        qinv: __m512i,
        q: __m512i,
    ) -> __m512i {
        let prod_ev = _mm512_mul_epi32(a, z_bcast);
        let a_od = _mm512_srli_epi64::<32>(a);
        let prod_od = _mm512_mul_epi32(a_od, z_bcast);

        let m_ev = _mm512_mul_epi32(prod_ev, qinv);
        let m_od = _mm512_mul_epi32(prod_od, qinv);

        let u_ev = _mm512_mul_epi32(m_ev, q);
        let u_od = _mm512_mul_epi32(m_od, q);

        let d_ev = _mm512_srli_epi64::<32>(_mm512_sub_epi64(prod_ev, u_ev));
        let d_od = _mm512_sub_epi64(prod_od, u_od);

        _mm512_mask_blend_epi32(0xAAAA, d_ev, d_od)
    }

    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn caddq_avx512(r: __m512i, q: __m512i) -> __m512i {
        let mask = _mm512_srai_epi32::<31>(r);
        _mm512_add_epi32(r, _mm512_and_si512(mask, q))
    }

    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn reduce32_avx512(a: __m512i, half23: __m512i, q: __m512i) -> __m512i {
        let t = _mm512_srai_epi32::<23>(_mm512_add_epi32(a, half23));
        _mm512_sub_epi32(a, _mm512_mullo_epi32(t, q))
    }

    /// Constant-time 16-lane `AVX-512` FIPS 204 forward `NTT` (`Algorithm 41`).
    #[inline(never)]
    #[target_feature(enable = "avx512f,avx512dq,avx512bw,avx512vl")]
    pub(super) unsafe fn mldsa_ntt_avx512(coeffs: &mut [u32; MLDSA_N]) {
        let p512 = coeffs.as_mut_ptr().cast::<__m512i>();
        let p256 = coeffs.as_mut_ptr().cast::<__m256i>();
        let zp = NTT_TABLES.zetas_mont.as_ptr();
        let qinv512 = _mm512_set1_epi32(MLDSA_QINV);
        let q512 = _mm512_set1_epi32(MLDSA_Q as i32);
        let qinv256 = _mm256_set1_epi32(MLDSA_QINV);
        let q256 = _mm256_set1_epi32(MLDSA_Q as i32);
        let half23_256 = _mm256_set1_epi32(1 << 22);

        unsafe {
            macro_rules! vec512_ct_stage {
                ($vecs_per_half:literal, $blocks:literal, $m_base:literal) => {{
                    let mut blk = 0usize;
                    while blk < $blocks {
                        let z = _mm512_set1_epi32(*zp.add($m_base + blk));
                        let base = blk * (2 * $vecs_per_half);
                        let mut v = 0usize;
                        while v < $vecs_per_half {
                            let lo = _mm512_loadu_si512(p512.add(base + v).cast());
                            let hi = _mm512_loadu_si512(p512.add(base + $vecs_per_half + v).cast());
                            let t = fqmul_bcast_avx512(hi, z, qinv512, q512);
                            _mm512_storeu_si512(p512.add(base + v).cast(), _mm512_add_epi32(lo, t));
                            _mm512_storeu_si512(
                                p512.add(base + $vecs_per_half + v).cast(),
                                _mm512_sub_epi32(lo, t),
                            );
                            v += 1;
                        }
                        blk += 1;
                    }
                }};
            }

            // 512-bit stages len = 128, 64, 32, 16 (half the vector ops of AVX2!)
            vec512_ct_stage!(8, 1, 1);
            vec512_ct_stage!(4, 2, 2);
            vec512_ct_stage!(2, 4, 4);
            vec512_ct_stage!(1, 8, 8);

            // Fused in-register stages len = 8, 4, 2, 1 per 16-coeff block (`k = 0..16`)
            let mut k = 0usize;
            while k < 16 {
                // Stage len = 8 (`m = 16 + k`)
                let mut v0 = _mm256_loadu_si256(p256.add(2 * k));
                let mut v1 = _mm256_loadu_si256(p256.add(2 * k + 1));
                let z8 = _mm256_set1_epi32(*zp.add(16 + k));
                let t8 = fqmul_bcast_avx2(v1, z8, qinv256, q256);
                v1 = _mm256_sub_epi32(v0, t8);
                v0 = _mm256_add_epi32(v0, t8);

                // Stage len = 4
                let z4_0 = *zp.add(32 + 2 * k);
                let z4_1 = *zp.add(32 + 2 * k + 1);
                let z4 = _mm256_setr_epi32(z4_0, z4_0, z4_0, z4_0, z4_1, z4_1, z4_1, z4_1);
                let lo4 = _mm256_permute2x128_si256::<0x20>(v0, v1);
                let hi4 = _mm256_permute2x128_si256::<0x31>(v0, v1);
                let t4 = fqmul_avx2(hi4, z4, qinv256, q256);
                let s4 = _mm256_add_epi32(lo4, t4);
                let d4 = _mm256_sub_epi32(lo4, t4);
                v0 = _mm256_permute2x128_si256::<0x20>(s4, d4);
                v1 = _mm256_permute2x128_si256::<0x31>(s4, d4);

                // Stage len = 2
                let z2_a0 = *zp.add(64 + 4 * k);
                let z2_a1 = *zp.add(64 + 4 * k + 1);
                let z2_b0 = *zp.add(64 + 4 * k + 2);
                let z2_b1 = *zp.add(64 + 4 * k + 3);
                let z2 = _mm256_setr_epi32(z2_a0, z2_a0, z2_b0, z2_b0, z2_a1, z2_a1, z2_b1, z2_b1);
                let lo2 = _mm256_unpacklo_epi64(v0, v1);
                let hi2 = _mm256_unpackhi_epi64(v0, v1);
                let t2 = fqmul_avx2(hi2, z2, qinv256, q256);
                let s2 = _mm256_add_epi32(lo2, t2);
                let d2 = _mm256_sub_epi32(lo2, t2);
                v0 = _mm256_unpacklo_epi64(s2, d2);
                v1 = _mm256_unpackhi_epi64(s2, d2);

                // Stage len = 1
                let za0 = *zp.add(128 + 8 * k);
                let za1 = *zp.add(128 + 8 * k + 1);
                let za2 = *zp.add(128 + 8 * k + 2);
                let za3 = *zp.add(128 + 8 * k + 3);
                let zb0 = *zp.add(128 + 8 * k + 4);
                let zb1 = *zp.add(128 + 8 * k + 5);
                let zb2 = *zp.add(128 + 8 * k + 6);
                let zb3 = *zp.add(128 + 8 * k + 7);
                let z1 = _mm256_setr_epi32(za0, za1, zb0, zb1, za2, za3, zb2, zb3);
                let v0_sh = _mm256_shuffle_epi32::<0xD8>(v0);
                let v1_sh = _mm256_shuffle_epi32::<0xD8>(v1);
                let lo1 = _mm256_unpacklo_epi64(v0_sh, v1_sh);
                let hi1 = _mm256_unpackhi_epi64(v0_sh, v1_sh);
                let t1 = fqmul_avx2(hi1, z1, qinv256, q256);
                let s1 = _mm256_add_epi32(lo1, t1);
                let d1 = _mm256_sub_epi32(lo1, t1);
                v0 = _mm256_unpacklo_epi32(s1, d1);
                v1 = _mm256_unpackhi_epi32(s1, d1);

                v0 = caddq_avx2(reduce32_avx2(v0, half23_256, q256), q256);
                v1 = caddq_avx2(reduce32_avx2(v1, half23_256, q256), q256);
                _mm256_storeu_si256(p256.add(2 * k), v0);
                _mm256_storeu_si256(p256.add(2 * k + 1), v1);
                k += 1;
            }

            wipe_zmm_and_zeroupper();
        }
    }

    /// Constant-time 16-lane `AVX-512` FIPS 204 inverse `InvNTT` (`Algorithm 42`).
    #[inline(never)]
    #[target_feature(enable = "avx512f,avx512dq,avx512bw,avx512vl")]
    pub(super) unsafe fn mldsa_inv_ntt_avx512(coeffs: &mut [u32; MLDSA_N]) {
        let p512 = coeffs.as_mut_ptr().cast::<__m512i>();
        let p256 = coeffs.as_mut_ptr().cast::<__m256i>();
        let nzp = NTT_TABLES.neg_zetas_mont.as_ptr();
        let qinv512 = _mm512_set1_epi32(MLDSA_QINV);
        let q512 = _mm512_set1_epi32(MLDSA_Q as i32);
        let half23_512 = _mm512_set1_epi32(1 << 22);
        let qinv256 = _mm256_set1_epi32(MLDSA_QINV);
        let q256 = _mm256_set1_epi32(MLDSA_Q as i32);

        unsafe {
            // Fused in-register stages len = 1, 2, 4, 8 per 16-coeff block (`k = 0..16`)
            let mut k = 0usize;
            while k < 16 {
                let mut v0 = _mm256_loadu_si256(p256.add(2 * k));
                let mut v1 = _mm256_loadu_si256(p256.add(2 * k + 1));

                let za0 = *nzp.add(255 - (8 * k));
                let za1 = *nzp.add(255 - (8 * k + 1));
                let za2 = *nzp.add(255 - (8 * k + 2));
                let za3 = *nzp.add(255 - (8 * k + 3));
                let zb0 = *nzp.add(255 - (8 * k + 4));
                let zb1 = *nzp.add(255 - (8 * k + 5));
                let zb2 = *nzp.add(255 - (8 * k + 6));
                let zb3 = *nzp.add(255 - (8 * k + 7));
                let z1 = _mm256_setr_epi32(za0, za1, zb0, zb1, za2, za3, zb2, zb3);
                let v0_sh = _mm256_shuffle_epi32::<0xD8>(v0);
                let v1_sh = _mm256_shuffle_epi32::<0xD8>(v1);
                let lo1 = _mm256_unpacklo_epi64(v0_sh, v1_sh);
                let hi1 = _mm256_unpackhi_epi64(v0_sh, v1_sh);
                let s1 = _mm256_add_epi32(lo1, hi1);
                let d1 = fqmul_avx2(_mm256_sub_epi32(lo1, hi1), z1, qinv256, q256);
                v0 = _mm256_unpacklo_epi32(s1, d1);
                v1 = _mm256_unpackhi_epi32(s1, d1);

                let z2_a0 = *nzp.add(127 - (4 * k));
                let z2_a1 = *nzp.add(127 - (4 * k + 1));
                let z2_b0 = *nzp.add(127 - (4 * k + 2));
                let z2_b1 = *nzp.add(127 - (4 * k + 3));
                let z2 = _mm256_setr_epi32(z2_a0, z2_a0, z2_b0, z2_b0, z2_a1, z2_a1, z2_b1, z2_b1);
                let lo2 = _mm256_unpacklo_epi64(v0, v1);
                let hi2 = _mm256_unpackhi_epi64(v0, v1);
                let s2 = _mm256_add_epi32(lo2, hi2);
                let d2 = fqmul_avx2(_mm256_sub_epi32(lo2, hi2), z2, qinv256, q256);
                v0 = _mm256_unpacklo_epi64(s2, d2);
                v1 = _mm256_unpackhi_epi64(s2, d2);

                let z4_0 = *nzp.add(63 - (2 * k));
                let z4_1 = *nzp.add(63 - (2 * k + 1));
                let z4 = _mm256_setr_epi32(z4_0, z4_0, z4_0, z4_0, z4_1, z4_1, z4_1, z4_1);
                let lo4 = _mm256_permute2x128_si256::<0x20>(v0, v1);
                let hi4 = _mm256_permute2x128_si256::<0x31>(v0, v1);
                let s4 = _mm256_add_epi32(lo4, hi4);
                let d4 = fqmul_avx2(_mm256_sub_epi32(lo4, hi4), z4, qinv256, q256);
                v0 = _mm256_permute2x128_si256::<0x20>(s4, d4);
                v1 = _mm256_permute2x128_si256::<0x31>(s4, d4);

                // Stage len = 8 (`m = 31 - k`) in register before storing!
                let z8 = _mm256_set1_epi32(*nzp.add(31 - k));
                let s8 = _mm256_add_epi32(v0, v1);
                let d8 = fqmul_bcast_avx2(_mm256_sub_epi32(v0, v1), z8, qinv256, q256);
                _mm256_storeu_si256(p256.add(2 * k), s8);
                _mm256_storeu_si256(p256.add(2 * k + 1), d8);
                k += 1;
            }

            macro_rules! vec512_gs_stage {
                ($vecs_per_half:literal, $blocks:literal, $m_top:literal, $reduce_lo:literal) => {{
                    let mut blk = 0usize;
                    while blk < $blocks {
                        let z_neg = _mm512_set1_epi32(*nzp.add($m_top - blk));
                        let base = blk * (2 * $vecs_per_half);
                        let mut v = 0usize;
                        while v < $vecs_per_half {
                            let lo = _mm512_loadu_si512(p512.add(base + v).cast());
                            let hi = _mm512_loadu_si512(p512.add(base + $vecs_per_half + v).cast());
                            let mut sum = _mm512_add_epi32(lo, hi);
                            if $reduce_lo {
                                sum = reduce32_avx512(sum, half23_512, q512);
                            }
                            let dif =
                                fqmul_bcast_avx512(_mm512_sub_epi32(lo, hi), z_neg, qinv512, q512);
                            _mm512_storeu_si512(p512.add(base + v).cast(), sum);
                            _mm512_storeu_si512(p512.add(base + $vecs_per_half + v).cast(), dif);
                            v += 1;
                        }
                        blk += 1;
                    }
                }};
            }

            // 512-bit stages len = 16, 32 (with lazy-bound reset), 64
            vec512_gs_stage!(1, 8, 15, false);
            vec512_gs_stage!(2, 4, 7, true);
            vec512_gs_stage!(4, 2, 3, false);

            // Fused 512-bit stage len = 128 + `256^{-1} mod q` scaling + canonicalization
            let inv256_v = _mm512_set1_epi32(NTT_TABLES.inv256_mont);
            let neg_z1_inv256_v = _mm512_set1_epi32(NTT_TABLES.neg_zeta1_inv256_mont);
            let mut v = 0usize;
            while v < 8 {
                let lo = _mm512_loadu_si512(p512.add(v).cast());
                let hi = _mm512_loadu_si512(p512.add(8 + v).cast());
                let r0 = fqmul_bcast_avx512(_mm512_add_epi32(lo, hi), inv256_v, qinv512, q512);
                let r1 =
                    fqmul_bcast_avx512(_mm512_sub_epi32(lo, hi), neg_z1_inv256_v, qinv512, q512);
                _mm512_storeu_si512(p512.add(v).cast(), caddq_avx512(r0, q512));
                _mm512_storeu_si512(p512.add(8 + v).cast(), caddq_avx512(r1, q512));
                v += 1;
            }

            wipe_zmm_and_zeroupper();
        }
    }

    /// Constant-time 16-lane `AVX-512` pointwise NTT multiplication (`Algorithm 45`).
    #[target_feature(enable = "avx512f,avx512dq,avx512bw,avx512vl")]
    pub(super) unsafe fn mldsa_pointwise_mul_avx512(
        out: &mut [u32; MLDSA_N],
        lhs: &[u32; MLDSA_N],
        rhs: &[u32; MLDSA_N],
    ) {
        let op = out.as_mut_ptr().cast::<__m512i>();
        let lp = lhs.as_ptr().cast::<__m512i>();
        let rp = rhs.as_ptr().cast::<__m512i>();
        let qinv = _mm512_set1_epi32(MLDSA_QINV);
        let q = _mm512_set1_epi32(MLDSA_Q as i32);
        let r2 = _mm512_set1_epi32(MLDSA_R2_MOD_Q);

        unsafe {
            let mut v = 0usize;
            while v < 16 {
                let a = _mm512_loadu_si512(lp.add(v).cast());
                let b = _mm512_loadu_si512(rp.add(v).cast());
                let b_mont = fqmul_bcast_avx512(b, r2, qinv, q);
                let prod = fqmul_avx512(a, b_mont, qinv, q);
                _mm512_storeu_si512(op.add(v).cast(), caddq_avx512(prod, q));
                v += 1;
            }
            wipe_zmm_and_zeroupper();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const Q: u64 = MLDSA_Q as u64;

    fn pow_mod(mut base: u64, mut exp: u64) -> u64 {
        let mut acc = 1u64;
        base %= Q;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc * base % Q;
            }
            base = base * base % Q;
            exp >>= 1;
        }
        acc
    }

    /// FIPS 204 section 7.5 definition: `NTT(w)[i] = w(zeta^(2 * BitRev8(i) + 1))`.
    fn ntt_by_definition(a: &[u32; MLDSA_N]) -> [u32; MLDSA_N] {
        core::array::from_fn(|i| {
            let x = pow_mod(MLDSA_ZETA as u64, 2 * bitrev8(i as u8) as u64 + 1);
            let mut acc = 0u64;
            let mut xp = 1u64;
            for &c in a {
                acc = (acc + c as u64 * xp) % Q;
                xp = xp * x % Q;
            }
            acc as u32
        })
    }

    fn backends() -> [SimdBackend; 4] {
        [
            SimdBackend::Portable,
            SimdBackend::X86Avx2Pclmul,
            SimdBackend::X86Avx512GfniVpclmul,
            SimdBackend::Aarch64NeonSha3Pmull,
        ]
    }

    /// Inputs that drive the lazy (unreduced) butterfly sums to their extremes: all-`q-1` makes
    /// every `InvNTT` sum path reach `64 (q - 1)` before the `len = 32` reduction.
    fn extreme_inputs() -> [[u32; MLDSA_N]; 9] {
        let qm1 = MLDSA_Q - 1;
        let mut state = 0x2018_0039_0838_0417_u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        [
            [0; MLDSA_N],
            [qm1; MLDSA_N],
            core::array::from_fn(|i| if i % 2 == 0 { qm1 } else { 0 }),
            core::array::from_fn(|i| if i < 128 { qm1 } else { 0 }),
            core::array::from_fn(|i| if i == 255 { qm1 } else { 0 }),
            core::array::from_fn(|i| if i == 0 { 1 } else { 0 }),
            core::array::from_fn(|i| (MLDSA_Q / 2 + (i as u32 & 1)) % MLDSA_Q),
            core::array::from_fn(|_| if next() & 1 == 0 { qm1 } else { 1 }),
            core::array::from_fn(|_| (next() % Q) as u32),
        ]
    }

    #[test]
    fn forward_ntt_matches_fips204_definition_on_extreme_inputs_for_every_backend() {
        for (n, input) in extreme_inputs().iter().enumerate() {
            let expected = ntt_by_definition(input);
            for backend in backends() {
                let mut got = *input;
                mldsa_ntt_with_backend(&mut got, backend);
                assert_eq!(got, expected, "input #{n} backend={backend:?}");
            }
        }
    }

    #[test]
    fn inverse_ntt_inverts_the_definition_on_extreme_inputs_for_every_backend() {
        for (n, input) in extreme_inputs().iter().enumerate() {
            // `input` is read as an NTT-domain vector: maximal lazy growth in `InvNTT`.
            for backend in backends() {
                let mut time = *input;
                mldsa_inv_ntt_with_backend(&mut time, backend);
                assert!(
                    time.iter().all(|&c| c < MLDSA_Q),
                    "non-canonical #{n} {backend:?}"
                );
                assert_eq!(
                    ntt_by_definition(&time),
                    *input,
                    "input #{n} backend={backend:?}"
                );
            }
        }
    }

    #[test]
    fn pointwise_mul_is_canonical_product_on_extreme_inputs_for_every_backend() {
        let inputs = extreme_inputs();
        for lhs in &inputs {
            for rhs in &inputs {
                let expected: [u32; MLDSA_N] =
                    core::array::from_fn(|i| (lhs[i] as u64 * rhs[i] as u64 % Q) as u32);
                for backend in backends() {
                    let mut got = [0xFFFF_FFFFu32; MLDSA_N];
                    mldsa_pointwise_mul_with_backend(&mut got, lhs, rhs, backend);
                    assert_eq!(got, expected, "backend={backend:?}");
                }
            }
        }
    }
}
