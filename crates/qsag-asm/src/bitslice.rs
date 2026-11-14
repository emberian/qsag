#![cfg_attr(not(test), deny(clippy::unwrap_used, clippy::expect_used))]
//! 256-way bitslice transpose and batched `GF(2^128)` multiply-accumulate kernels.
//!
//! * [`pack_256x200_bitslice`] / [`unpack_256x200_bitslice`] convert 256 `Keccak-f[1600]`
//!   states between byte form and 1600 bit planes of 256 lanes each. The conversion is a
//!   64x64 bit-matrix transpose applied to four columns at once ([`transpose64x256`]): six
//!   shift-and-mask butterfly stages, no branch, loop bound or address that depends on data.
//! * [`gf2_128_mul_acc_batch`] computes `acc ^= sum_i a[i] * b[i]` in
//!   `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)` with three carryless multiplications per
//!   product (Karatsuba) and one reduction for the whole batch.
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
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
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
        if backend == SimdBackend::X86Avx2GfniVpclmul && vpclmul_batch_supported(caps) {
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
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
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

    const BACKENDS: [SimdBackend; 4] = [
        SimdBackend::Portable,
        SimdBackend::X86Avx2Pclmul,
        SimdBackend::X86Avx2GfniVpclmul,
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
