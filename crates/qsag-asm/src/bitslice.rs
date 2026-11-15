#![cfg_attr(not(test), deny(clippy::unwrap_used, clippy::expect_used))]
//! 256-way bitslice transpose and batched `GF(2^128)` multiply-accumulate kernels.
//!
//! * [`pack_256x200_bitslice`] / [`unpack_256x200_bitslice`] convert 256 `Keccak-f[1600]`
//!   states between byte form and 1600 bit planes of 256 lanes each. The conversion is a
//!   64x64 bit-matrix transpose applied to four columns at once ([`transpose64x256`]): six
//!   shift-and-mask butterfly stages, no branch, loop bound or address that depends on data.
//! * [`gf2_128_mul_acc_batch`] computes `acc ^= sum_i a[i] * b[i]` in
//!   `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)` with three carryless multiplications per
//!   product (Karatsuba) and one reduction for the whole batch. [`gf2_128_dot`] is the same
//!   sum over `u128` slices, read in place.
//! * [`gf2_64x128_clmul_acc`] accumulates unreduced `64 x 128`-bit carryless products of
//!   64-bit words with one fixed 128-bit scalar: two multiplications per word, no reduction.
//! * [`gf2_xor_combine_planes`] forms 128 GF(2) combinations of 64 rows of four words,
//!   selected by public coefficient nibbles (method of the four Russians).
//!
//! ### Kernel discipline
//! The assembly kernels follow the rules that `scripts/audit_elf_ct.py` enforces: one
//! bottom-tested loop over a public count per stage, `base + immediate` addressing only,
//! immediate shift counts, every touched vector register zeroed before `ret`, and
//! `vzeroupper` on the `AVX2` paths. The transpose works in place on the caller's buffer and
//! the multiply-accumulate keeps its state in registers, so neither kernel has stack scratch.
//!
//! ### What has and has not been executed
//! Each kernel is selected only when the CPU reports the feature it needs and is compared
//! against the portable reference by the unit tests on every backend the test host supports.
//! A backend the host lacks is skipped by those tests, not vouched for.

use crate::cpuid::{self, SimdBackend};

/// One bit plane: bit `j % 64` of word `j / 64` belongs to lane `j`.
pub type BitPlane256 = [u64; 4];

/// Number of lanes in one bitsliced batch.
pub const BITSLICE_LANES: usize = 256;
/// Bytes in one `Keccak-f[1600]` state.
pub const KECCAK_STATE_BYTES: usize = 200;
/// Bit planes in one bitsliced `Keccak-f[1600]` batch.
pub const KECCAK_STATE_BITS: usize = 1600;

/// One butterfly stage with the shift as a compile-time constant, so the generated code
/// shifts by an immediate.
#[inline(always)]
fn butterfly_stage<const J: usize>(rows: &mut [BitPlane256; 64], mask: u64) {
    let mut base = 0usize;
    while base < 64 {
        let (lo, hi) = rows[base..base + 2 * J].split_at_mut(J);
        for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
            for (x, y) in a.iter_mut().zip(b.iter_mut()) {
                let t = ((*x >> J) ^ *y) & mask;
                *y ^= t;
                *x ^= t << J;
            }
        }
        base += 2 * J;
    }
}

/// Portable in-place transpose of four 64x64 bit matrices stored column-wise in 64 rows of
/// four words: afterwards bit `r` of `rows[c][q]` is the former bit `c` of `rows[r][q]`.
pub fn transpose64x256_portable(rows: &mut [BitPlane256; 64]) {
    butterfly_stage::<32>(rows, 0x0000_0000_FFFF_FFFF);
    butterfly_stage::<16>(rows, 0x0000_FFFF_0000_FFFF);
    butterfly_stage::<8>(rows, 0x00FF_00FF_00FF_00FF);
    butterfly_stage::<4>(rows, 0x0F0F_0F0F_0F0F_0F0F);
    butterfly_stage::<2>(rows, 0x3333_3333_3333_3333);
    butterfly_stage::<1>(rows, 0x5555_5555_5555_5555);
}

/// In-place transpose of four 64x64 bit matrices on the detected backend.
#[inline]
pub fn transpose64x256(rows: &mut [BitPlane256; 64]) {
    transpose64x256_with_backend(rows, cpuid::detect_backend());
}

/// [`transpose64x256`] on an explicit backend; falls back to the portable code when the CPU
/// lacks the backend's features.
pub fn transpose64x256_with_backend(rows: &mut [BitPlane256; 64], backend: SimdBackend) {
    #[cfg(target_arch = "x86_64")]
    {
        let caps = cpuid::probe_capabilities();
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul
                | SimdBackend::X86Avx2GfniVpclmul
                | SimdBackend::X86Avx512GfniVpclmul
        ) && caps.avx2
        {
            // SAFETY: `rows` is 64 * 32 writable bytes and the CPU supports AVX2.
            unsafe { x86::qsag_asm_transpose64x256_avx2(rows.as_mut_ptr().cast::<u8>()) };
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        let caps = cpuid::probe_capabilities();
        if backend == SimdBackend::Aarch64NeonSha3Pmull && caps.aarch64_neon {
            let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
            // SAFETY: `rows` is 64 * 32 writable bytes and the CPU supports NEON.
            unsafe { a64::qsag_asm_transpose64x256_neon(rows.as_mut_ptr().cast::<u8>()) };
            return;
        }
    }
    let _ = backend;
    transpose64x256_portable(rows);
}

/// Pack 256 states into bit planes: bit `j` of `planes[i]` is bit `i` of `states[j]`, where
/// bit `i` of a state is bit `i % 8` of byte `i / 8`.
#[inline]
pub fn pack_256x200_bitslice(
    states: &[[u8; KECCAK_STATE_BYTES]; BITSLICE_LANES],
    planes: &mut [BitPlane256; KECCAK_STATE_BITS],
) {
    pack_256x200_bitslice_with_backend(states, planes, cpuid::detect_backend());
}

/// [`pack_256x200_bitslice`] on an explicit backend.
#[allow(clippy::chunks_exact_to_as_chunks)]
pub fn pack_256x200_bitslice_with_backend(
    states: &[[u8; KECCAK_STATE_BYTES]; BITSLICE_LANES],
    planes: &mut [BitPlane256; KECCAK_STATE_BITS],
    backend: SimdBackend,
) {
    #[cfg(target_arch = "aarch64")]
    let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
    let mut bytes = [0u8; 8];
    for (word, rows) in planes.chunks_exact_mut(64).enumerate() {
        let Ok(rows): Result<&mut [BitPlane256; 64], _> = rows.try_into() else {
            unreachable!("chunks_exact_mut always produces 64 planes");
        };
        for (r, row) in rows.iter_mut().enumerate() {
            for (q, slot) in row.iter_mut().enumerate() {
                bytes.copy_from_slice(&states[64 * q + r][8 * word..8 * word + 8]);
                *slot = u64::from_le_bytes(bytes);
            }
        }
        transpose64x256_with_backend(rows, backend);
    }
    crate::ct_memzero(&mut bytes);
}

/// Inverse of [`pack_256x200_bitslice`].
#[inline]
pub fn unpack_256x200_bitslice(
    planes: &[BitPlane256; KECCAK_STATE_BITS],
    states: &mut [[u8; KECCAK_STATE_BYTES]; BITSLICE_LANES],
) {
    unpack_256x200_bitslice_with_backend(planes, states, cpuid::detect_backend());
}

/// [`unpack_256x200_bitslice`] on an explicit backend. The transpose scratch is wiped.
#[allow(clippy::chunks_exact_to_as_chunks)]
pub fn unpack_256x200_bitslice_with_backend(
    planes: &[BitPlane256; KECCAK_STATE_BITS],
    states: &mut [[u8; KECCAK_STATE_BYTES]; BITSLICE_LANES],
    backend: SimdBackend,
) {
    #[cfg(target_arch = "aarch64")]
    let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
    let mut rows = [[0u64; 4]; 64];
    let mut bytes = [0u8; 8];
    for (word, src) in planes.chunks_exact(64).enumerate() {
        rows.copy_from_slice(src);
        transpose64x256_with_backend(&mut rows, backend);
        for (r, row) in rows.iter().enumerate() {
            for (q, value) in row.iter().enumerate() {
                bytes = value.to_le_bytes();
                states[64 * q + r][8 * word..8 * word + 8].copy_from_slice(&bytes);
            }
        }
    }
    crate::ct_memzero(&mut bytes);
    crate::volatile_fill(&mut rows, [0u64; 4]);
}

/// Portable branch-free product in `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`; an element is
/// `[low 64 coefficients, high 64 coefficients]`.
pub fn gf2_128_mul_portable(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    let mut x = u128::from(a[0]) | (u128::from(a[1]) << 64);
    let mut y = u128::from(b[0]) | (u128::from(b[1]) << 64);
    let mut r = 0u128;
    for _ in 0..128 {
        let take = 0u128.wrapping_sub(y & 1);
        y >>= 1;
        r ^= x & take;
        let carry = 0u128.wrapping_sub(x >> 127);
        x = (x << 1) ^ (carry & 0x87);
    }
    let out = [r as u64, (r >> 64) as u64];
    crate::volatile_fill(core::slice::from_mut(&mut x), 0);
    crate::volatile_fill(core::slice::from_mut(&mut y), 0);
    crate::volatile_fill(core::slice::from_mut(&mut r), 0);
    out
}

// This kernel uses legacy PCLMUL for its odd tail as well as VPCLMUL for pairs.
#[cfg(target_arch = "x86_64")]
fn vpclmul_batch_supported(caps: cpuid::CpuCapabilities) -> bool {
    caps.avx2 && caps.vpclmulqdq && caps.pclmulqdq
}

#[cfg(all(test, target_arch = "x86_64"))]
#[test]
fn vpclmul_without_legacy_pclmul_rejects_batch_kernel() {
    let mut caps = cpuid::probe_capabilities();
    caps.avx2 = true;
    caps.vpclmulqdq = true;
    caps.pclmulqdq = false;
    assert!(!vpclmul_batch_supported(caps));
    let a = [[1, 2], [3, 4], [5, 6]];
    let b = [[7, 8], [9, 10], [11, 12]];
    let mut expected = [13, 14];
    gf2_128_mul_acc_batch_portable(&mut expected, &a, &b);
    let mut actual = [13, 14];
    gf2_128_mul_acc_batch_with_caps(&mut actual, &a, &b, SimdBackend::X86Avx2GfniVpclmul, caps);
    assert_eq!(actual, expected);
    caps.pclmulqdq = true;
    assert!(vpclmul_batch_supported(caps));
}

/// Portable `acc ^= sum_i a[i] * b[i]`.
pub fn gf2_128_mul_acc_batch_portable(acc: &mut [u64; 2], a: &[[u64; 2]], b: &[[u64; 2]]) {
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter().zip(b) {
        let mut p = gf2_128_mul_portable(*x, *y);
        acc[0] ^= p[0];
        acc[1] ^= p[1];
        crate::volatile_fill(&mut p, 0);
    }
}

/// `acc ^= sum_i a[i] * b[i]` in `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)` on the detected
/// backend. Panics if the slices differ in length.
#[inline]
pub fn gf2_128_mul_acc_batch(acc: &mut [u64; 2], a: &[[u64; 2]], b: &[[u64; 2]]) {
    gf2_128_mul_acc_batch_with_backend(acc, a, b, cpuid::detect_backend());
}

/// Elementwise `dst[i] ^= src[i] * scalar` in the polynomial field
/// `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)`. Dispatch is amortized over the slice.
/// This is not multiplication in the Wiedemann tower representation.
pub fn gf2_128_scale_xor(dst: &mut [u128], src: &[u128], scalar: u128) {
    gf2_128_scale_xor_with_backend(dst, src, scalar, cpuid::detect_backend());
}

/// Explicit-backend scale-XOR; unsupported hardware falls back safely.
pub fn gf2_128_scale_xor_with_backend(
    dst: &mut [u128],
    src: &[u128],
    scalar: u128,
    backend: SimdBackend,
) {
    assert_eq!(dst.len(), src.len());
    if dst.is_empty() {
        return;
    }
    #[cfg(target_arch = "x86_64")]
    {
        let cap_bits = cpuid::probe_capabilities_bits();
        const AVX512_VPCLMUL_MASK: u32 =
            cpuid::CAP_AVX512 | cpuid::CAP_VPCLMULQDQ | cpuid::CAP_PCLMULQDQ;
        if backend == SimdBackend::X86Avx512GfniVpclmul
            && (cap_bits & AVX512_VPCLMUL_MASK) == AVX512_VPCLMUL_MASK
        {
            let quads = dst.len() / 4;
            let rem = dst.len() % 4;
            let slo = scalar as u64;
            let shi = (scalar >> 64) as u64;
            // SAFETY: `caps.avx512 && caps.vpclmulqdq && caps.pclmulqdq` verified; slices are
            // equal-length and non-overlapping.
            unsafe {
                if quads > 0 {
                    crate::avx512::poly_scale_xor_avx512_evex(
                        dst.as_mut_ptr().cast::<u8>(),
                        src.as_ptr().cast::<u8>(),
                        slo,
                        shi,
                        quads,
                    );
                }
                if rem > 0 {
                    poly_scale_xor_x86(&mut dst[4 * quads..], &src[4 * quads..], &scalar);
                }
            }
            return;
        }
        const AVX2_PCLMUL_MASK: u32 = cpuid::CAP_AVX2 | cpuid::CAP_PCLMULQDQ;
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul
                | SimdBackend::X86Avx2GfniVpclmul
                | SimdBackend::X86Avx512GfniVpclmul
        ) && (cap_bits & AVX2_PCLMUL_MASK) == AVX2_PCLMUL_MASK
        {
            // SAFETY: AVX OS state and PCLMUL are checked. The nonempty slices
            // have equal lengths and cannot overlap; unaligned loads are used.
            unsafe {
                poly_scale_xor_x86(dst, src, &scalar);
            }
            return;
        }
    }
    let _ = backend;
    let b = [scalar as u64, (scalar >> 64) as u64];
    for (d, s) in dst.iter_mut().zip(src) {
        let mut product = [0; 2];
        // Retain the existing PMULL path on supported AArch64 CPUs.
        gf2_128_mul_acc_batch_with_backend(
            &mut product,
            &[[*s as u64, (*s >> 64) as u64]],
            &[b],
            backend,
        );
        *d ^= u128::from(product[0]) | (u128::from(product[1]) << 64);
        crate::volatile_fill(&mut product, 0);
    }
}

/// One public-count loop, fixed-address stride, no stack scratch. Every touched
/// vector register is cleared before returning, as in the dot-product kernels.
#[cfg(target_arch = "x86_64")]
unsafe fn poly_scale_xor_x86(dst: &mut [u128], src: &[u128], scalar: &u128) {
    // SAFETY: caller checks features, slice lengths, and nonemptiness.
    unsafe {
        core::arch::asm!(
            "vmovdqu xmm5, xmmword ptr [{scalar}]",
            "vpshufd xmm9, xmm5, 0x4e",
            "vpxor xmm9, xmm9, xmm5",
            "mov {scratch:e}, 0x87",
            "vmovq xmm10, {scratch}",
            "2:",
            "vmovdqu xmm4, xmmword ptr [{src}]",
            "vpclmulqdq xmm0, xmm4, xmm5, 0x00",
            "vpclmulqdq xmm1, xmm4, xmm5, 0x11",
            "vpshufd xmm8, xmm4, 0x4e",
            "vpxor xmm8, xmm8, xmm4",
            "vpclmulqdq xmm2, xmm8, xmm9, 0x00",
            "vpxor xmm2, xmm2, xmm0",
            "vpxor xmm2, xmm2, xmm1",
            "vpslldq xmm3, xmm2, 8",
            "vpsrldq xmm2, xmm2, 8",
            "vpxor xmm0, xmm0, xmm3",
            "vpxor xmm1, xmm1, xmm2",
            "vpclmulqdq xmm6, xmm1, xmm10, 0x01",
            "vpslldq xmm7, xmm6, 8",
            "vpsrldq xmm8, xmm6, 8",
            "vpxor xmm0, xmm0, xmm7",
            "vpxor xmm1, xmm1, xmm8",
            "vpclmulqdq xmm6, xmm1, xmm10, 0x00",
            "vpxor xmm0, xmm0, xmm6",
            "vpxor xmm0, xmm0, xmmword ptr [{dst}]",
            "vmovdqu xmmword ptr [{dst}], xmm0",
            "add {src}, 16",
            "add {dst}, 16",
            "dec {count}",
            "jnz 2b",
            "vpxor xmm0, xmm0, xmm0",
            "vpxor xmm1, xmm1, xmm1",
            "vpxor xmm2, xmm2, xmm2",
            "vpxor xmm3, xmm3, xmm3",
            "vpxor xmm4, xmm4, xmm4",
            "vpxor xmm5, xmm5, xmm5",
            "vpxor xmm6, xmm6, xmm6",
            "vpxor xmm7, xmm7, xmm7",
            "vpxor xmm8, xmm8, xmm8",
            "vpxor xmm9, xmm9, xmm9",
            "vpxor xmm10, xmm10, xmm10",
            "vzeroupper",
            src = inout(reg) src.as_ptr() => _,
            dst = inout(reg) dst.as_mut_ptr() => _,
            count = inout(reg) dst.len() => _,
            scalar = in(reg) scalar,
            scratch = out(reg) _,
            out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
            out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
            out("xmm8") _, out("xmm9") _, out("xmm10") _,
            options(nostack),
        );
    }
}

/// `sum_i a[i] * b[i]` in `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)` over elements stored as
/// `u128` (bit `k` is the coefficient of `x^k`), on the detected backend. Both operands may be
/// secret. Panics if the slices differ in length.
#[inline]
pub fn gf2_128_dot(a: &[u128], b: &[u128]) -> u128 {
    gf2_128_dot_with_backend(a, b, cpuid::detect_backend())
}

/// [`gf2_128_dot`] on an explicit backend. The operands are handed to the
/// [`gf2_128_mul_acc_batch`] kernels where they lie, without a copy into limb pairs.
pub fn gf2_128_dot_with_backend(a: &[u128], b: &[u128], backend: SimdBackend) -> u128 {
    assert_eq!(a.len(), b.len());
    let mut acc = [0u64; 2];
    #[cfg(target_endian = "little")]
    {
        // SAFETY: a `u128` is 16 bytes without padding, aligned at least as strictly as
        // `[u64; 2]`, and on a little-endian target its low limb comes first, which is the
        // `[low, high]` element layout of the kernels. The views borrow `a` and `b` for
        // exactly this block and are only read.
        let (limbs_a, limbs_b) = unsafe {
            (
                core::slice::from_raw_parts(a.as_ptr().cast::<[u64; 2]>(), a.len()),
                core::slice::from_raw_parts(b.as_ptr().cast::<[u64; 2]>(), b.len()),
            )
        };
        gf2_128_mul_acc_batch_with_backend(&mut acc, limbs_a, limbs_b, backend);
    }
    #[cfg(not(target_endian = "little"))]
    {
        let _ = backend;
        for (x, y) in a.iter().zip(b) {
            gf2_128_mul_acc_batch_portable(
                &mut acc,
                &[[*x as u64, (*x >> 64) as u64]],
                &[[*y as u64, (*y >> 64) as u64]],
            );
        }
    }
    let out = u128::from(acc[0]) | (u128::from(acc[1]) << 64);
    crate::volatile_fill(&mut acc, 0);
    out
}

/// Portable branch-free [`gf2_64x128_clmul_acc`]: one masked shift-and-add step per bit of the
/// word, with immediate shift counts.
pub fn gf2_64x128_clmul_acc_portable(acc: &mut [[u128; 2]], words: &[u64], scalar: u128) {
    assert_eq!(acc.len(), words.len());
    for (slot, word) in acc.iter_mut().zip(words) {
        let mut w = *word;
        let mut lo = scalar & u128::from(u64::MAX);
        let mut hi = scalar >> 64;
        let mut product = [0u128; 2];
        for _ in 0..64 {
            let take = 0u128.wrapping_sub(u128::from(w & 1));
            w >>= 1;
            product[0] ^= lo & take;
            product[1] ^= hi & take;
            lo <<= 1;
            hi <<= 1;
        }
        slot[0] ^= product[0];
        slot[1] ^= product[1];
        crate::volatile_fill(&mut product, 0);
        crate::volatile_fill(core::slice::from_mut(&mut w), 0);
    }
}

/// Unreduced carryless multiply-accumulate of 64-bit words by one 128-bit scalar:
/// `acc[i][0] ^= words[i] (x) low 64 bits of scalar` and
/// `acc[i][1] ^= words[i] (x) high 64 bits of scalar`, each a polynomial of degree below 127.
/// The product of `words[i]` and `scalar` is `acc[i][0] + x^64 * acc[i][1]`; the caller sums
/// over as many calls as it likes and reduces once.
///
/// Every path is constant-time in both operands: `words` may be secret shares and `scalar`
/// is a public weight in the callers, but nothing here relies on that. Panics if the slices
/// differ in length.
#[inline]
pub fn gf2_64x128_clmul_acc(acc: &mut [[u128; 2]], words: &[u64], scalar: u128) {
    gf2_64x128_clmul_acc_with_backend(acc, words, scalar, cpuid::detect_backend());
}

/// [`gf2_64x128_clmul_acc`] on an explicit backend; falls back to the portable code when
/// the CPU lacks the backend's features.
pub fn gf2_64x128_clmul_acc_with_backend(
    acc: &mut [[u128; 2]],
    words: &[u64],
    scalar: u128,
    backend: SimdBackend,
) {
    assert_eq!(acc.len(), words.len());
    if words.is_empty() {
        return;
    }
    #[cfg(target_arch = "x86_64")]
    {
        let caps = cpuid::probe_capabilities();
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul
                | SimdBackend::X86Avx2GfniVpclmul
                | SimdBackend::X86Avx512GfniVpclmul
        ) && caps.avx2
            && caps.pclmulqdq
        {
            // SAFETY: AVX OS state and PCLMUL are checked. The slices are nonempty, have
            // equal lengths and cannot overlap; unaligned loads and stores are used.
            unsafe {
                clmul_64x128_acc_x86(acc, words, &scalar);
            }
            return;
        }
    }
    let _ = backend;
    gf2_64x128_clmul_acc_portable(acc, words, scalar);
}

/// One public-count loop, fixed-address stride, no stack scratch. Every touched
/// vector register is cleared before returning, as in the dot-product kernels.
#[cfg(target_arch = "x86_64")]
unsafe fn clmul_64x128_acc_x86(acc: &mut [[u128; 2]], words: &[u64], scalar: &u128) {
    // SAFETY: caller checks features, slice lengths, and nonemptiness.
    unsafe {
        core::arch::asm!(
            "vmovdqu xmm5, xmmword ptr [{scalar}]",
            "2:",
            "vmovq xmm4, qword ptr [{words}]",
            "vpclmulqdq xmm0, xmm4, xmm5, 0x00",
            "vpclmulqdq xmm1, xmm4, xmm5, 0x10",
            "vpxor xmm0, xmm0, xmmword ptr [{acc}]",
            "vpxor xmm1, xmm1, xmmword ptr [{acc} + 16]",
            "vmovdqu xmmword ptr [{acc}], xmm0",
            "vmovdqu xmmword ptr [{acc} + 16], xmm1",
            "add {words}, 8",
            "add {acc}, 32",
            "dec {count}",
            "jnz 2b",
            "vpxor xmm0, xmm0, xmm0",
            "vpxor xmm1, xmm1, xmm1",
            "vpxor xmm4, xmm4, xmm4",
            "vpxor xmm5, xmm5, xmm5",
            "vzeroupper",
            words = inout(reg) words.as_ptr() => _,
            acc = inout(reg) acc.as_mut_ptr() => _,
            count = inout(reg) words.len() => _,
            scalar = in(reg) scalar,
            out("xmm0") _, out("xmm1") _, out("xmm4") _, out("xmm5") _,
            options(nostack),
        );
    }
}

/// Coefficient bits per output of [`gf2_xor_combine_planes`].
pub const XOR_COMBINE_PLANES: usize = 128;
/// Four-row groups of [`gf2_xor_combine_planes`]; one public nibble selects within each.
pub const XOR_COMBINE_NIBBLES: usize = 16;

/// Public selection pattern of [`gf2_xor_combine_planes`]: bit `d` of `pattern[k][g]` says
/// whether row `4 * g + d` enters combination `k`. Only the low four bits are read.
pub type XorCombinePattern = [[u8; XOR_COMBINE_NIBBLES]; XOR_COMBINE_PLANES];

/// Portable [`gf2_xor_combine_planes`].
#[cfg_attr(target_arch = "x86_64", inline(never))]
pub fn gf2_xor_combine_planes_portable(
    rows: &[BitPlane256; 64],
    pattern: &XorCombinePattern,
    planes: &mut [[BitPlane256; 64]; 2],
) {
    let mut tables = [[[0u64; 4]; 16]; XOR_COMBINE_NIBBLES];
    for (g, table) in tables.iter_mut().enumerate() {
        for n in 1..16usize {
            let prev = table[n & (n - 1)];
            let row = &rows[4 * g + n.trailing_zeros() as usize];
            for ((dst, a), b) in table[n].iter_mut().zip(prev).zip(row) {
                *dst = a ^ b;
            }
        }
    }
    for (k, nibbles) in pattern.iter().enumerate() {
        let mut acc = [0u64; 4];
        for (table, nibble) in tables.iter().zip(nibbles) {
            for (dst, src) in acc.iter_mut().zip(&table[usize::from(nibble & 15)]) {
                *dst ^= src;
            }
        }
        planes[k / 64][k % 64] = acc;
    }
    crate::volatile_fill(&mut tables, [[0; 4]; 16]);
}

/// `planes[k / 64][k % 64] = XOR of rows[4 * g + d]` over all `(g, d)` with bit `d` of
/// `pattern[k][g]` set: 128 GF(2)-linear combinations of 64 rows, four independent 64-bit
/// columns per row, on the detected backend.
///
/// `rows` may be secret. `pattern` is the public operand: its nibbles index the subset-XOR
/// tables built from the rows, so memory addresses and the instruction trace depend on
/// `pattern` only. The tables are wiped before returning.
#[inline]
pub fn gf2_xor_combine_planes(
    rows: &[BitPlane256; 64],
    pattern: &XorCombinePattern,
    planes: &mut [[BitPlane256; 64]; 2],
) {
    gf2_xor_combine_planes_with_backend(rows, pattern, planes, cpuid::detect_backend());
}

/// [`gf2_xor_combine_planes`] on an explicit backend; falls back to the portable code when
/// the CPU lacks the backend's features.
pub fn gf2_xor_combine_planes_with_backend(
    rows: &[BitPlane256; 64],
    pattern: &XorCombinePattern,
    planes: &mut [[BitPlane256; 64]; 2],
    backend: SimdBackend,
) {
    #[cfg(target_arch = "x86_64")]
    {
        let caps = cpuid::probe_capabilities();
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul
                | SimdBackend::X86Avx2GfniVpclmul
                | SimdBackend::X86Avx512GfniVpclmul
        ) && caps.avx2
        {
            // SAFETY: the CPU and the OS support AVX2.
            unsafe { xor_combine_planes_avx2(rows, pattern, planes) };
            return;
        }
    }
    let _ = backend;
    gf2_xor_combine_planes_portable(rows, pattern, planes);
}

/// One 256-bit register per row and per table entry: a combination costs sixteen
/// `vpxor ymm, ymm, [table]` for all four columns together.
#[cfg(target_arch = "x86_64")]
#[inline(never)]
#[target_feature(enable = "avx2")]
unsafe fn xor_combine_planes_avx2(
    rows: &[BitPlane256; 64],
    pattern: &XorCombinePattern,
    planes: &mut [[BitPlane256; 64]; 2],
) {
    use core::arch::x86_64::{
        __m256i, _mm256_loadu_si256, _mm256_setzero_si256, _mm256_storeu_si256, _mm256_xor_si256,
    };
    let mut tables = [[_mm256_setzero_si256(); 16]; XOR_COMBINE_NIBBLES];
    for (g, table) in tables.iter_mut().enumerate() {
        for n in 1..16usize {
            let row = &rows[4 * g + n.trailing_zeros() as usize];
            // SAFETY: `row` is 32 readable bytes; the load is unaligned.
            let row = unsafe { _mm256_loadu_si256(row.as_ptr().cast::<__m256i>()) };
            table[n] = _mm256_xor_si256(table[n & (n - 1)], row);
        }
    }
    for (k, nibbles) in pattern.iter().enumerate() {
        let mut acc = _mm256_setzero_si256();
        for (table, nibble) in tables.iter().zip(nibbles) {
            acc = _mm256_xor_si256(acc, table[usize::from(nibble & 15)]);
        }
        let plane = &mut planes[k / 64][k % 64];
        // SAFETY: `plane` is 32 writable bytes; the store is unaligned.
        unsafe { _mm256_storeu_si256(plane.as_mut_ptr().cast::<__m256i>(), acc) };
    }
    crate::volatile_fill(&mut tables, [_mm256_setzero_si256(); 16]);
}

/// [`gf2_128_mul_acc_batch`] on an explicit backend; falls back to the portable code when
/// the CPU lacks the backend's features.
pub fn gf2_128_mul_acc_batch_with_backend(
    acc: &mut [u64; 2],
    a: &[[u64; 2]],
    b: &[[u64; 2]],
    backend: SimdBackend,
) {
    gf2_128_mul_acc_batch_with_caps(acc, a, b, backend, cpuid::probe_capabilities());
}

fn gf2_128_mul_acc_batch_with_caps(
    acc: &mut [u64; 2],
    a: &[[u64; 2]],
    b: &[[u64; 2]],
    backend: SimdBackend,
    caps: cpuid::CpuCapabilities,
) {
    #[cfg(target_arch = "aarch64")]
    let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
    assert_eq!(a.len(), b.len());
    if a.is_empty() {
        return;
    }
    #[cfg(target_arch = "x86_64")]
    {
        let acc_ptr = acc.as_mut_ptr().cast::<u8>();
        let a_ptr = a.as_ptr().cast::<u8>();
        let b_ptr = b.as_ptr().cast::<u8>();
        if backend == SimdBackend::X86Avx512GfniVpclmul
            && caps.avx512
            && vpclmul_batch_supported(caps)
        {
            let quads = a.len() / 4;
            let rem = a.len() % 4;
            let rem_pairs = rem / 2;
            // SAFETY: `caps.avx512 && vpclmul_batch_supported(caps)` verified; `a` and `b` hold
            // `4 * quads + 2 * rem_pairs + (rem % 2)` 16-byte elements.
            unsafe {
                if quads > 0 {
                    crate::avx512::gf2_128_mul_acc_avx512_evex(acc_ptr, a_ptr, b_ptr, quads);
                }
                if rem_pairs > 0 {
                    x86::qsag_asm_gf2_128_mul_acc_vpclmul(
                        acc_ptr,
                        a_ptr.add(64 * quads),
                        b_ptr.add(64 * quads),
                        rem_pairs,
                    );
                }
                if rem % 2 == 1 {
                    let off = 64 * quads + 32 * rem_pairs;
                    x86::qsag_asm_gf2_128_mul_acc_pclmul(
                        acc_ptr,
                        a_ptr.add(off),
                        b_ptr.add(off),
                        1,
                    );
                }
            }
            return;
        }
        if matches!(
            backend,
            SimdBackend::X86Avx2GfniVpclmul | SimdBackend::X86Avx512GfniVpclmul
        ) && vpclmul_batch_supported(caps)
        {
            let pairs = a.len() / 2;
            // SAFETY: both inputs hold `2 * pairs` (plus at most one) 16-byte elements, `acc`
            // is 16 writable bytes, and the CPU supports AVX2 with VPCLMULQDQ.
            unsafe {
                if pairs > 0 {
                    x86::qsag_asm_gf2_128_mul_acc_vpclmul(acc_ptr, a_ptr, b_ptr, pairs);
                }
                if a.len() % 2 == 1 {
                    x86::qsag_asm_gf2_128_mul_acc_pclmul(
                        acc_ptr,
                        a_ptr.add(32 * pairs),
                        b_ptr.add(32 * pairs),
                        1,
                    );
                }
            }
            return;
        }
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul
                | SimdBackend::X86Avx2GfniVpclmul
                | SimdBackend::X86Avx512GfniVpclmul
        ) && caps.avx2
            && caps.pclmulqdq
        {
            // SAFETY: both inputs hold `a.len() >= 1` 16-byte elements, `acc` is 16 writable
            // bytes, and the CPU supports AVX with PCLMULQDQ.
            unsafe { x86::qsag_asm_gf2_128_mul_acc_pclmul(acc_ptr, a_ptr, b_ptr, a.len()) };
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if backend == SimdBackend::Aarch64NeonSha3Pmull && caps.aarch64_neon && caps.aarch64_pmull {
            let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
            // SAFETY: both inputs hold `a.len() >= 1` 16-byte elements, `acc` is 16 writable
            // bytes, and the CPU supports NEON with PMULL.
            unsafe {
                a64::qsag_asm_gf2_128_mul_acc_pmull(
                    acc.as_mut_ptr().cast::<u8>(),
                    a.as_ptr().cast::<u8>(),
                    b.as_ptr().cast::<u8>(),
                    a.len(),
                );
            }
            return;
        }
    }
    let _ = (backend, caps);
    gf2_128_mul_acc_batch_portable(acc, a, b);
}

#[cfg(target_arch = "x86_64")]
mod x86 {
    use core::arch::global_asm;

    #[cfg(target_vendor = "apple")]
    macro_rules! sym_header {
        ($name:literal) => {
            concat!(".globl _", $name, "\n.p2align 4\n_", $name, ":\n")
        };
    }
    #[cfg(target_os = "windows")]
    macro_rules! sym_header {
        ($name:literal) => {
            concat!(".globl ", $name, "\n.p2align 4\n", $name, ":\n")
        };
    }
    #[cfg(not(any(target_vendor = "apple", target_os = "windows")))]
    macro_rules! sym_header {
        ($name:literal) => {
            concat!(
                ".globl ",
                $name,
                "\n.type ",
                $name,
                ", @function\n.p2align 4\n",
                $name,
                ":\n"
            )
        };
    }
    #[cfg(any(target_vendor = "apple", target_os = "windows"))]
    macro_rules! sym_footer {
        ($name:literal) => {
            "\n"
        };
    }
    #[cfg(not(any(target_vendor = "apple", target_os = "windows")))]
    macro_rules! sym_footer {
        ($name:literal) => {
            concat!(".size ", $name, ", .-", $name, "\n")
        };
    }

    global_asm!(
        // qsag_asm_transpose64x256_avx2(rows: *mut u8 /* 64 * 32 bytes */)
        sym_header!("qsag_asm_transpose64x256_avx2"),
        include_str!("asm/x86_64_transpose64x256.s"),
        sym_footer!("qsag_asm_transpose64x256_avx2"),
        // qsag_asm_gf2_128_mul_acc_pclmul(acc: *mut u8, a: *const u8, b: *const u8, n: usize)
        // Caller guarantees `n >= 1`. xmm0/xmm1/xmm2 accumulate the low, high and Karatsuba
        // middle products; one reduction by x^128 = x^7 + x^2 + x + 1 follows the loop.
        sym_header!("qsag_asm_gf2_128_mul_acc_pclmul"),
        "vpxor xmm0, xmm0, xmm0",
        "vpxor xmm1, xmm1, xmm1",
        "vpxor xmm2, xmm2, xmm2",
        "2:",
        "vmovdqu xmm4, xmmword ptr [rsi + 0]",
        "vmovdqu xmm5, xmmword ptr [rdx + 0]",
        "vpclmulqdq xmm6, xmm4, xmm5, 0x00",
        "vpclmulqdq xmm7, xmm4, xmm5, 0x11",
        "vpshufd xmm8, xmm4, 0x4E",
        "vpshufd xmm9, xmm5, 0x4E",
        "vpxor xmm8, xmm8, xmm4",
        "vpxor xmm9, xmm9, xmm5",
        "vpclmulqdq xmm8, xmm8, xmm9, 0x00",
        "vpxor xmm0, xmm0, xmm6",
        "vpxor xmm1, xmm1, xmm7",
        "vpxor xmm2, xmm2, xmm8",
        "add rsi, 16",
        "add rdx, 16",
        "dec rcx",
        "jnz 2b",
        "vpxor xmm2, xmm2, xmm0",
        "vpxor xmm2, xmm2, xmm1",
        "vpslldq xmm3, xmm2, 8",
        "vpsrldq xmm2, xmm2, 8",
        "vpxor xmm0, xmm0, xmm3",
        "vpxor xmm1, xmm1, xmm2",
        "mov eax, 0x87",
        "vmovq xmm10, rax",
        "vpclmulqdq xmm6, xmm1, xmm10, 0x01",
        "vpslldq xmm7, xmm6, 8",
        "vpsrldq xmm8, xmm6, 8",
        "vpxor xmm0, xmm0, xmm7",
        "vpxor xmm1, xmm1, xmm8",
        "vpclmulqdq xmm6, xmm1, xmm10, 0x00",
        "vpxor xmm0, xmm0, xmm6",
        "vpxor xmm0, xmm0, xmmword ptr [rdi + 0]",
        "vmovdqu xmmword ptr [rdi + 0], xmm0",
        "vpxor xmm0, xmm0, xmm0",
        "vpxor xmm1, xmm1, xmm1",
        "vpxor xmm2, xmm2, xmm2",
        "vpxor xmm3, xmm3, xmm3",
        "vpxor xmm4, xmm4, xmm4",
        "vpxor xmm5, xmm5, xmm5",
        "vpxor xmm6, xmm6, xmm6",
        "vpxor xmm7, xmm7, xmm7",
        "vpxor xmm8, xmm8, xmm8",
        "vpxor xmm9, xmm9, xmm9",
        "vpxor xmm10, xmm10, xmm10",
        "xor eax, eax",
        "vzeroupper",
        "ret",
        sym_footer!("qsag_asm_gf2_128_mul_acc_pclmul"),
        // qsag_asm_gf2_128_mul_acc_vpclmul(acc: *mut u8, a: *const u8, b: *const u8, pairs: usize)
        // Two products per iteration in the two 128-bit lanes; caller guarantees `pairs >= 1`.
        sym_header!("qsag_asm_gf2_128_mul_acc_vpclmul"),
        "vpxor xmm0, xmm0, xmm0",
        "vpxor xmm1, xmm1, xmm1",
        "vpxor xmm2, xmm2, xmm2",
        "2:",
        "vmovdqu ymm4, ymmword ptr [rsi + 0]",
        "vmovdqu ymm5, ymmword ptr [rdx + 0]",
        "vpclmulqdq ymm6, ymm4, ymm5, 0x00",
        "vpclmulqdq ymm7, ymm4, ymm5, 0x11",
        "vpshufd ymm8, ymm4, 0x4E",
        "vpshufd ymm9, ymm5, 0x4E",
        "vpxor ymm8, ymm8, ymm4",
        "vpxor ymm9, ymm9, ymm5",
        "vpclmulqdq ymm8, ymm8, ymm9, 0x00",
        "vpxor ymm0, ymm0, ymm6",
        "vpxor ymm1, ymm1, ymm7",
        "vpxor ymm2, ymm2, ymm8",
        "add rsi, 32",
        "add rdx, 32",
        "dec rcx",
        "jnz 2b",
        "vextracti128 xmm3, ymm0, 1",
        "vpxor xmm0, xmm0, xmm3",
        "vextracti128 xmm3, ymm1, 1",
        "vpxor xmm1, xmm1, xmm3",
        "vextracti128 xmm3, ymm2, 1",
        "vpxor xmm2, xmm2, xmm3",
        "vpxor xmm2, xmm2, xmm0",
        "vpxor xmm2, xmm2, xmm1",
        "vpslldq xmm3, xmm2, 8",
        "vpsrldq xmm2, xmm2, 8",
        "vpxor xmm0, xmm0, xmm3",
        "vpxor xmm1, xmm1, xmm2",
        "mov eax, 0x87",
        "vmovq xmm10, rax",
        "vpclmulqdq xmm6, xmm1, xmm10, 0x01",
        "vpslldq xmm7, xmm6, 8",
        "vpsrldq xmm8, xmm6, 8",
        "vpxor xmm0, xmm0, xmm7",
        "vpxor xmm1, xmm1, xmm8",
        "vpclmulqdq xmm6, xmm1, xmm10, 0x00",
        "vpxor xmm0, xmm0, xmm6",
        "vpxor xmm0, xmm0, xmmword ptr [rdi + 0]",
        "vmovdqu xmmword ptr [rdi + 0], xmm0",
        "vpxor xmm0, xmm0, xmm0",
        "vpxor xmm1, xmm1, xmm1",
        "vpxor xmm2, xmm2, xmm2",
        "vpxor xmm3, xmm3, xmm3",
        "vpxor xmm4, xmm4, xmm4",
        "vpxor xmm5, xmm5, xmm5",
        "vpxor xmm6, xmm6, xmm6",
        "vpxor xmm7, xmm7, xmm7",
        "vpxor xmm8, xmm8, xmm8",
        "vpxor xmm9, xmm9, xmm9",
        "vpxor xmm10, xmm10, xmm10",
        "xor eax, eax",
        "vzeroupper",
        "ret",
        sym_footer!("qsag_asm_gf2_128_mul_acc_vpclmul"),
    );

    // `sysv64` pins the argument registers the kernels read, on every x86_64 target.
    unsafe extern "sysv64" {
        pub(super) fn qsag_asm_transpose64x256_avx2(rows: *mut u8);
        pub(super) fn qsag_asm_gf2_128_mul_acc_pclmul(
            acc: *mut u8,
            a: *const u8,
            b: *const u8,
            n: usize,
        );
        pub(super) fn qsag_asm_gf2_128_mul_acc_vpclmul(
            acc: *mut u8,
            a: *const u8,
            b: *const u8,
            pairs: usize,
        );
    }
}

#[cfg(target_arch = "aarch64")]
mod a64 {
    use core::arch::global_asm;

    #[cfg(target_vendor = "apple")]
    macro_rules! sym_header {
        ($name:literal) => {
            concat!(".globl _", $name, "\n.p2align 2\n_", $name, ":\n")
        };
    }
    #[cfg(not(target_vendor = "apple"))]
    macro_rules! sym_header {
        ($name:literal) => {
            concat!(
                ".globl ",
                $name,
                "\n.p2align 2\n.type ",
                $name,
                ", %function\n",
                $name,
                ":\n"
            )
        };
    }
    #[cfg(target_vendor = "apple")]
    macro_rules! sym_footer {
        ($name:literal) => {
            "\n"
        };
    }
    #[cfg(not(target_vendor = "apple"))]
    macro_rules! sym_footer {
        ($name:literal) => {
            concat!(".size ", $name, ", .-", $name, "\n")
        };
    }

    global_asm!(
        ".arch armv8.4-a+sha3+crypto",
        ".text",
        // qsag_asm_transpose64x256_neon(rows: *mut u8 /* 64 * 32 bytes */)
        sym_header!("qsag_asm_transpose64x256_neon"),
        include_str!("asm/aarch64_transpose64x256.s"),
        sym_footer!("qsag_asm_transpose64x256_neon"),
        // qsag_asm_gf2_128_mul_acc_pmull(acc: *mut u8, a: *const u8, b: *const u8, n: usize)
        // Caller guarantees `n >= 1`. v0/v1/v2 accumulate the low, high and Karatsuba middle
        // products; one reduction by x^128 = x^7 + x^2 + x + 1 follows the loop.
        sym_header!("qsag_asm_gf2_128_mul_acc_pmull"),
        "eor v0.16b, v0.16b, v0.16b",
        "eor v1.16b, v1.16b, v1.16b",
        "eor v2.16b, v2.16b, v2.16b",
        "eor v22.16b, v22.16b, v22.16b",
        "1:",
        "ldr q4, [x1, #0]",
        "ldr q5, [x2, #0]",
        "pmull v6.1q, v4.1d, v5.1d",
        "pmull2 v7.1q, v4.2d, v5.2d",
        "ext v16.16b, v4.16b, v4.16b, #8",
        "ext v17.16b, v5.16b, v5.16b, #8",
        "eor v16.16b, v16.16b, v4.16b",
        "eor v17.16b, v17.16b, v5.16b",
        "pmull v18.1q, v16.1d, v17.1d",
        "eor v0.16b, v0.16b, v6.16b",
        "eor v1.16b, v1.16b, v7.16b",
        "eor v2.16b, v2.16b, v18.16b",
        "add x1, x1, #16",
        "add x2, x2, #16",
        "subs x3, x3, #1",
        "b.ne 1b",
        "eor v2.16b, v2.16b, v0.16b",
        "eor v2.16b, v2.16b, v1.16b",
        "ext v19.16b, v22.16b, v2.16b, #8",
        "ext v20.16b, v2.16b, v22.16b, #8",
        "eor v0.16b, v0.16b, v19.16b",
        "eor v1.16b, v1.16b, v20.16b",
        "mov x4, #0x87",
        "fmov d21, x4",
        "ext v16.16b, v1.16b, v22.16b, #8",
        "pmull v6.1q, v16.1d, v21.1d",
        "ext v19.16b, v22.16b, v6.16b, #8",
        "ext v20.16b, v6.16b, v22.16b, #8",
        "eor v0.16b, v0.16b, v19.16b",
        "eor v1.16b, v1.16b, v20.16b",
        "pmull v6.1q, v1.1d, v21.1d",
        "eor v0.16b, v0.16b, v6.16b",
        "ldr q4, [x0, #0]",
        "eor v0.16b, v0.16b, v4.16b",
        "str q0, [x0, #0]",
        "eor v0.16b, v0.16b, v0.16b",
        "eor v1.16b, v1.16b, v1.16b",
        "eor v2.16b, v2.16b, v2.16b",
        "eor v4.16b, v4.16b, v4.16b",
        "eor v5.16b, v5.16b, v5.16b",
        "eor v6.16b, v6.16b, v6.16b",
        "eor v7.16b, v7.16b, v7.16b",
        "eor v16.16b, v16.16b, v16.16b",
        "eor v17.16b, v17.16b, v17.16b",
        "eor v18.16b, v18.16b, v18.16b",
        "eor v19.16b, v19.16b, v19.16b",
        "eor v20.16b, v20.16b, v20.16b",
        "eor v21.16b, v21.16b, v21.16b",
        "mov x4, #0",
        "ret",
        sym_footer!("qsag_asm_gf2_128_mul_acc_pmull"),
    );

    unsafe extern "C" {
        pub(super) fn qsag_asm_transpose64x256_neon(rows: *mut u8);
        pub(super) fn qsag_asm_gf2_128_mul_acc_pmull(
            acc: *mut u8,
            a: *const u8,
            b: *const u8,
            n: usize,
        );
    }
}

#[cfg(test)]
mod tests {
    extern crate alloc;
    use super::*;
    use alloc::boxed::Box;
    use alloc::vec::Vec;

    /// Deterministic test stream (`xorshift64*`); test data only.
    struct TestStream(u64);

    impl TestStream {
        fn next_u64(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
    }

    const BACKENDS: [SimdBackend; 5] = [
        SimdBackend::Portable,
        SimdBackend::X86Avx2Pclmul,
        SimdBackend::X86Avx2GfniVpclmul,
        SimdBackend::X86Avx512GfniVpclmul,
        SimdBackend::Aarch64NeonSha3Pmull,
    ];

    #[test]
    fn transpose64x256_is_the_bit_matrix_transpose_on_every_backend() {
        let mut rng = TestStream(0x9E37_79B9_7F4A_7C15);
        let mut rows = [[0u64; 4]; 64];
        for row in &mut rows {
            for word in row.iter_mut() {
                *word = rng.next_u64();
            }
        }
        for backend in BACKENDS {
            let mut got = rows;
            transpose64x256_with_backend(&mut got, backend);
            for (r, row) in rows.iter().enumerate() {
                for (c, got_row) in got.iter().enumerate() {
                    for q in 0..4 {
                        assert_eq!(
                            (got_row[q] >> r) & 1,
                            (row[q] >> c) & 1,
                            "backend {backend:?} row {r} col {c} word {q}"
                        );
                    }
                }
            }
            // The transpose is an involution.
            transpose64x256_with_backend(&mut got, backend);
            assert_eq!(got, rows);
        }
    }

    #[test]
    #[allow(clippy::chunks_exact_to_as_chunks)]
    fn pack_and_unpack_256x200_match_the_bit_definition_and_round_trip() {
        let mut rng = TestStream(0xD1B5_4A32_D192_ED03);
        let mut states = Box::new([[0u8; KECCAK_STATE_BYTES]; BITSLICE_LANES]);
        for state in states.iter_mut() {
            for chunk in state.chunks_exact_mut(8) {
                chunk.copy_from_slice(&rng.next_u64().to_le_bytes());
            }
        }
        for backend in BACKENDS {
            let mut planes = Box::new([[0u64; 4]; KECCAK_STATE_BITS]);
            pack_256x200_bitslice_with_backend(&states, &mut planes, backend);
            for (i, plane) in planes.iter().enumerate() {
                for j in 0..BITSLICE_LANES {
                    let want = (states[j][i / 8] >> (i % 8)) & 1;
                    let got = ((plane[j / 64] >> (j % 64)) & 1) as u8;
                    assert_eq!(got, want, "backend {backend:?} plane {i} lane {j}");
                }
            }
            let mut back = Box::new([[0u8; KECCAK_STATE_BYTES]; BITSLICE_LANES]);
            unpack_256x200_bitslice_with_backend(&planes, &mut back, backend);
            assert_eq!(back, states);
        }
    }

    /// Schoolbook reference: carryless product, then reduction by repeated subtraction.
    fn gf2_128_mul_reference(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
        let mut wide = [0u64; 4];
        for i in 0..128 {
            if (a[i / 64] >> (i % 64)) & 1 == 1 {
                for j in 0..128 {
                    if (b[j / 64] >> (j % 64)) & 1 == 1 {
                        wide[(i + j) / 64] ^= 1u64 << ((i + j) % 64);
                    }
                }
            }
        }
        for bit in (128..255).rev() {
            if (wide[bit / 64] >> (bit % 64)) & 1 == 1 {
                wide[bit / 64] ^= 1u64 << (bit % 64);
                for tap in [0usize, 1, 2, 7] {
                    let t = bit - 128 + tap;
                    wide[t / 64] ^= 1u64 << (t % 64);
                }
            }
        }
        [wide[0], wide[1]]
    }

    #[test]
    fn polynomial_scale_xor_matches_schoolbook_and_preserves_boundaries() {
        let mut rng = TestStream(0x7523_1a09_ac48_3345);
        let mut src: Vec<u128> = (0..67)
            .map(|_| u128::from(rng.next_u64()) | (u128::from(rng.next_u64()) << 64))
            .collect();
        src[..4].copy_from_slice(&[0, 1, 1 << 127, u128::MAX]);
        let initial: Vec<u128> = (0..69)
            .map(|_| u128::from(rng.next_u64()) | (u128::from(rng.next_u64()) << 64))
            .collect();
        for scalar in [0, 1, 2, 1 << 127, u128::MAX, initial[0]] {
            let b = [scalar as u64, (scalar >> 64) as u64];
            for len in 0..=src.len() {
                let mut expected = initial.clone();
                for (dst, x) in expected[1..1 + len].iter_mut().zip(&src) {
                    let product = gf2_128_mul_reference([*x as u64, (*x >> 64) as u64], b);
                    *dst ^= u128::from(product[0]) | (u128::from(product[1]) << 64);
                }
                for backend in BACKENDS {
                    let mut actual = initial.clone();
                    gf2_128_scale_xor_with_backend(
                        &mut actual[1..1 + len],
                        &src[..len],
                        scalar,
                        backend,
                    );
                    assert_eq!(actual, expected, "{backend:?}, len={len}, scalar={scalar}");
                }
            }
        }
    }

    #[test]
    fn gf2_128_dot_matches_schoolbook_reference_on_every_backend() {
        let mut rng = TestStream(0x51ED_270B_9F3C_1A47);
        let mut wide = || u128::from(rng.next_u64()) | (u128::from(rng.next_u64()) << 64);
        let mut a: Vec<u128> = (0..67).map(|_| wide()).collect();
        let mut b: Vec<u128> = (0..67).map(|_| wide()).collect();
        a[..4].copy_from_slice(&[u128::MAX, 1 << 127, 2, 0]);
        b[..4].copy_from_slice(&[u128::MAX, 1 << 127, 1 << 127, u128::MAX]);
        let limbs = |v: u128| [v as u64, (v >> 64) as u64];
        // Odd and even lengths, the two-element kernel stride and its tails, and offsets
        // that put the slices at both 8- and 16-byte phases of the buffer.
        for start in [0usize, 1, 2] {
            for len in [0usize, 1, 2, 3, 4, 5, 16, 17, 31, 64, 65] {
                let (x, y) = (&a[start..start + len], &b[start..start + len]);
                let mut want = [0u64; 2];
                for (p, q) in x.iter().zip(y) {
                    let product = gf2_128_mul_reference(limbs(*p), limbs(*q));
                    want[0] ^= product[0];
                    want[1] ^= product[1];
                }
                let want = u128::from(want[0]) | (u128::from(want[1]) << 64);
                for backend in BACKENDS {
                    assert_eq!(
                        gf2_128_dot_with_backend(x, y, backend),
                        want,
                        "{backend:?}, start={start}, len={len}"
                    );
                }
            }
        }
        // x * x^127 = x^7 + x^2 + x + 1.
        assert_eq!(gf2_128_dot(&[2], &[1 << 127]), 0x87);
    }

    #[test]
    #[should_panic]
    fn gf2_128_dot_rejects_mismatched_lengths() {
        gf2_128_dot(&[0; 2], &[0]);
    }

    /// Bit-by-bit carryless product of a 64-bit word and a 64-bit limb.
    fn clmul64_reference(word: u64, limb: u64) -> u128 {
        let mut product = 0u128;
        for i in 0..64 {
            if (word >> i) & 1 == 1 {
                product ^= u128::from(limb) << i;
            }
        }
        product
    }

    #[test]
    fn clmul_64x128_acc_matches_bit_reference_and_preserves_boundaries() {
        let mut rng = TestStream(0x3C6E_F372_FE94_F82B);
        let mut words: Vec<u64> = (0..37).map(|_| rng.next_u64()).collect();
        words[..4].copy_from_slice(&[0, 1, 1 << 63, u64::MAX]);
        let initial: Vec<[u128; 2]> = (0..39)
            .map(|_| {
                [
                    u128::from(rng.next_u64()) | (u128::from(rng.next_u64()) << 64),
                    u128::from(rng.next_u64()) | (u128::from(rng.next_u64()) << 64),
                ]
            })
            .collect();
        for scalar in [0, 1, 1 << 63, 1 << 64, 1 << 127, u128::MAX, initial[0][0]] {
            for len in 0..=words.len() {
                let mut expected = initial.clone();
                for (slot, word) in expected[1..1 + len].iter_mut().zip(&words) {
                    slot[0] ^= clmul64_reference(*word, scalar as u64);
                    slot[1] ^= clmul64_reference(*word, (scalar >> 64) as u64);
                }
                for backend in BACKENDS {
                    let mut actual = initial.clone();
                    gf2_64x128_clmul_acc_with_backend(
                        &mut actual[1..1 + len],
                        &words[..len],
                        scalar,
                        backend,
                    );
                    assert_eq!(actual, expected, "{backend:?}, len={len}, scalar={scalar}");
                }
            }
        }
        // The two halves recombine to the field product after one reduction.
        let (word, scalar) = (words[5], initial[1][1]);
        let mut acc = [[0u128; 2]];
        gf2_64x128_clmul_acc(&mut acc, &[word], scalar);
        let low = acc[0][0] ^ (acc[0][1] << 64);
        let high = acc[0][1] >> 64;
        let reduced = low ^ high ^ (high << 1) ^ (high << 2) ^ (high << 7);
        let want = gf2_128_mul_reference([word, 0], [scalar as u64, (scalar >> 64) as u64]);
        assert_eq!(reduced, u128::from(want[0]) | (u128::from(want[1]) << 64));
    }

    #[test]
    #[should_panic]
    fn clmul_64x128_acc_rejects_mismatched_lengths() {
        gf2_64x128_clmul_acc(&mut [[0; 2]; 2], &[0], 1);
    }

    #[test]
    fn xor_combine_planes_match_row_by_row_reference_on_every_backend() {
        let mut rng = TestStream(0xD1B5_4A32_D192_ED03);
        for round in 0..6 {
            let mut rows = [[0u64; 4]; 64];
            for row in &mut rows {
                for word in row.iter_mut() {
                    *word = rng.next_u64();
                }
            }
            let mut pattern = [[0u8; XOR_COMBINE_NIBBLES]; XOR_COMBINE_PLANES];
            for nibbles in &mut pattern {
                for nibble in nibbles.iter_mut() {
                    // High bits are set in some rounds: only the low nibble may be read.
                    let high = if round % 2 == 0 { 0 } else { 0xF0 };
                    *nibble = (rng.next_u64() as u8 & 15) | high;
                }
            }
            // Empty, full and single-row combinations.
            pattern[0] = [0; XOR_COMBINE_NIBBLES];
            pattern[1] = [15; XOR_COMBINE_NIBBLES];
            pattern[127] = [0; XOR_COMBINE_NIBBLES];
            pattern[127][15] = 8;
            let mut want = [[[0u64; 4]; 64]; 2];
            for (k, nibbles) in pattern.iter().enumerate() {
                for (r, row) in rows.iter().enumerate() {
                    if (nibbles[r / 4] >> (r % 4)) & 1 == 1 {
                        for (dst, src) in want[k / 64][k % 64].iter_mut().zip(row) {
                            *dst ^= src;
                        }
                    }
                }
            }
            assert_eq!(want[1][63], rows[63]);
            for backend in BACKENDS {
                let mut planes = [[[u64::MAX; 4]; 64]; 2];
                gf2_xor_combine_planes_with_backend(&rows, &pattern, &mut planes, backend);
                assert_eq!(planes, want, "{backend:?}, round {round}");
            }
        }
    }

    #[test]
    #[should_panic]
    fn polynomial_scale_xor_rejects_mismatched_lengths() {
        gf2_128_scale_xor(&mut [0; 2], &[0], 1);
    }

    #[test]
    fn gf2_128_mul_acc_batch_matches_schoolbook_reference_on_every_backend() {
        let mut rng = TestStream(0xA076_1D64_78BD_642F);
        let mut a: Vec<[u64; 2]> = (0..41).map(|_| [rng.next_u64(), rng.next_u64()]).collect();
        let mut b: Vec<[u64; 2]> = (0..41).map(|_| [rng.next_u64(), rng.next_u64()]).collect();
        // Edge elements: all-ones, top-bit only, one, x, and zero.
        a[0] = [u64::MAX, u64::MAX];
        b[0] = [u64::MAX, u64::MAX];
        a[1] = [0, 1 << 63];
        b[1] = [0, 1 << 63];
        a[2] = [1, 0];
        a[3] = [2, 0];
        b[3] = [0, 1 << 63];
        a[4] = [0, 0];
        // x * x^127 = x^128 = x^7 + x^2 + x + 1.
        assert_eq!(gf2_128_mul_portable(a[3], b[3]), [0x87, 0]);
        for (x, y) in a.iter().zip(&b) {
            assert_eq!(gf2_128_mul_portable(*x, *y), gf2_128_mul_reference(*x, *y));
        }
        for len in [0usize, 1, 2, 3, 16, 17, 40, 41] {
            let seed = [rng.next_u64(), rng.next_u64()];
            let mut want = seed;
            for i in 0..len {
                let p = gf2_128_mul_reference(a[i], b[i]);
                want[0] ^= p[0];
                want[1] ^= p[1];
            }
            for backend in BACKENDS {
                let mut acc = seed;
                gf2_128_mul_acc_batch_with_backend(&mut acc, &a[..len], &b[..len], backend);
                assert_eq!(acc, want, "backend {backend:?} len {len}");
            }
        }
    }
}
