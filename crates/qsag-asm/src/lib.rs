#![no_std]
//! # `qsag-asm` — SIMD & Platform Assembly Kernels with Scoped Verification
//!
//! Zero-dependency (`#![no_std]` + optional `std`) platform assembly kernels.
//! `ConstantTimeIsa.lean` proves ISA-model timing noninterference for AVX2 MPC chi,
//! SHA3 NEON chi, GFNI Shamir multiplication, VPCLMUL BDOZ MAC, and Goldilocks
//! multiplication and 32-byte equality on both ISAs. Functional results cover
//! Goldilocks and equality, GFNI one-block output, MPC chi lane-zero output and RSS
//! reconstruction, BCAX, and the carryless reduction degree bound. These are scoped
//! ISA-model theorems, not a proof of every exported kernel or compiled Rust wrapper.
//! `scripts/audit_elf_ct.py` checks all 16 x86 assembly symbols (plus the 3 [`bitslice`]
//! kernels, in the compiled ELF only), all 7 AArch64 kernels
//! in ELF and Mach-O, and compiled Rust crypto functions against its instruction
//! rules. `ct_dudect` statistically tests 10 dispatched operations (including
//! Goldilocks multiplication) on the selected backend; it is not a formal proof.
//!
//! Implemented kernel families:
//!
//! 1. **256-Way Parallel `Keccak-f[1600]` & Threshold MPC $\chi$-Layer:**
//!    - `x86_64` `AVX2` (`ymm0..ymm15`, 4 sponge instances $\times$ 64 bits = 256 wires/op),
//!    - `aarch64` `NEON` + `FEAT_SHA3` (`eor3.16b`, `rax1.2d`, `xar.2d`, `bcax.16b`).
//! 2. **32-Way `GF(2^8)` Shamir Multiplication & MAC (Wiedemann $\mathcal{T}_3$ Exact):**
//!    - `x86_64` `GFNI` (`vgf2p8affineqb` + `vgf2p8mulb` via proved basis isomorphism
//!      $\Phi : \mathcal{T}_3 \xrightarrow{\sim} \mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$),
//!    - `x86_64` `AVX2` fallback (`vpshufb` register-synthesized nibble LUT + branchless
//!      Russian-peasant arithmetic, zero memory table lookups).
//! 3. **2-Lane `Tower128` ($\mathcal{T}_7 = \mathbb{F}_{2^{128}}$) BDOZ MAC Inner Product:**
//!    - `x86_64` 256-bit `VPCLMULQDQ` (2 simultaneous 128-bit lanes) & 128-bit `PCLMULQDQ`,
//!    - `aarch64` `PMULL` / `PMULL2` with Lean-proved 2-step `0x87` degree bound
//!      (`clmul64_0x87_hi_degree_bound`) and compile-time verified $\mathcal{T}_7$
//!      Artin–Schreier basis isomorphism $\Psi$ (`T7_TO_POLY_BASIS` / `POLY_TO_T7_BASIS`).
//! 4. **Zero-Branch `Goldilocks` ($p = 2^{64} - 2^{32} + 1$) Field & $x^7$ S-Box:**
//!    - `x86_64` `BMI2`/`ADX` (`mulx`, `adcx`, `adox`, `sbb` masks — zero `jcc`, zero `cmov`),
//!    - `aarch64` (`mul`, `umulh`, `subs`/`sbc`, `adds`/`adc` masks — zero `b.cond`, zero `csel`).
//! 5. **Assembly Constant-Time Tag Verification, Volatile Memory Wipe & Hardware `DIT`/`DOIT`.**
//! 6. **256-Way Bitslice Transpose & Batched `GF(2^128)` Multiply-Accumulate ([`bitslice`]):**
//!    - `x86_64` `AVX2` shift-and-mask butterfly, `PCLMULQDQ` / 256-bit `VPCLMULQDQ` Karatsuba,
//!    - `aarch64` `NEON` butterfly, `PMULL` Karatsuba, and a branch-free portable reference.

#[cfg(feature = "std")]
extern crate std;

pub mod bitslice;
pub mod cpuid;
pub mod portable;

#[cfg(target_arch = "x86_64")]
pub mod x86_64_asm;

#[cfg(target_arch = "aarch64")]
pub mod aarch64_asm;

pub use bitslice::{
    BITSLICE_LANES, BitPlane256, KECCAK_STATE_BITS, KECCAK_STATE_BYTES, gf2_128_mul_acc_batch,
    gf2_128_mul_acc_batch_with_backend, gf2_128_mul_portable, pack_256x200_bitslice,
    pack_256x200_bitslice_with_backend, transpose64x256, transpose64x256_with_backend,
    unpack_256x200_bitslice, unpack_256x200_bitslice_with_backend,
};
pub use cpuid::{
    CpuCapabilities, DitRequirement, HardwareDitGuard, HardwareDitUnavailable, HardwareDitStatus, SimdBackend, detect_backend, enable_hardware_dit,
    probe_capabilities,
};
pub use portable::{
    GFNI_MAT_POLY_TO_T3, GFNI_MAT_T3_TO_POLY, GOLDILOCKS_EPSILON, GOLDILOCKS_PRIME,
    KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS, KeccakRow256, KeccakState4x,
    POLY_TO_T7_BASIS, T7_TO_POLY_BASIS, TOWER128_POLY_GENERATORS, poly128_to_tower128_ct,
    tower128_to_poly128_ct,
};

// ============================================================================
// Safe Runtime-Dispatched & Explicit-Backend Entrypoints
// ============================================================================

/// Execute 24-round `Keccak-f[1600]` across 4 parallel 1600-bit states (`256` bits per lane).
#[inline]
pub fn keccak_f1600_x4(state: &mut KeccakState4x) {
    keccak_f1600_x4_with_backend(state, detect_backend());
}

/// Execute `keccak_f1600_x4` on a specific [`SimdBackend`] (falling back safely if unsupported).
pub fn keccak_f1600_x4_with_backend(state: &mut KeccakState4x, backend: SimdBackend) {
    #[cfg(target_arch = "x86_64")]
    {
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
        ) && cpuid::probe_capabilities().avx2
        {
            // SAFETY: `probe_capabilities().avx2` verified both CPUID AVX2 and OS XCR0 YMM save.
            unsafe {
                x86_64_asm::run_keccak_f1600_avx2_4x(state);
            }
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        let caps = cpuid::probe_capabilities();
        if backend == SimdBackend::Aarch64NeonSha3Pmull && caps.aarch64_neon && caps.aarch64_sha3 && caps.aarch64_dit {
            let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
            // SAFETY: `probe_capabilities()` verified runtime `NEON` + `FEAT_SHA3` (`eor3`, `rax1`,
            // `xar`, `bcax`) before invoking `run_keccak_f1600_sha3_neon_4x`.
            unsafe {
                aarch64_asm::run_keccak_f1600_sha3_neon_4x(state);
            }
            return;
        }
    }
    let _ = backend;
    portable::keccak_f1600_4x_portable(state);
}

/// Execute 256-way bitsliced 3-party symmetric RSS MPC $\chi$-row gate:
/// `out[x] = s0[x] ^ s0[x+2] ^ (s0[x+1] & (s0[x+2] ^ s1[x+2])) ^ (s1[x+1] & s0[x+2]) ^ r_mask[x]`.
#[inline]
pub fn keccak_chi_mpc_row256(
    out: &mut KeccakRow256,
    s0: &KeccakRow256,
    s1: &KeccakRow256,
    r_mask: &KeccakRow256,
) {
    keccak_chi_mpc_row256_with_backend(out, s0, s1, r_mask, detect_backend());
}

/// Execute `keccak_chi_mpc_row256` on an explicit [`SimdBackend`].
pub fn keccak_chi_mpc_row256_with_backend(
    out: &mut KeccakRow256,
    s0: &KeccakRow256,
    s1: &KeccakRow256,
    r_mask: &KeccakRow256,
    backend: SimdBackend,
) {
    #[cfg(target_arch = "x86_64")]
    {
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
        ) && cpuid::probe_capabilities().avx2
        {
            // SAFETY: `avx2` + OS YMM verified; pointers derive from valid `&KeccakRow256` refs.
            unsafe {
                x86_64_asm::qsag_asm_keccak_chi_mpc_avx2(out, s0, s1, r_mask);
            }
            return;
        }
    }
    let _ = backend;
    portable::keccak_chi_mpc_4x_portable(out, s0, s1, r_mask);
}

/// Elementwise constant-time Shamir multiplication `dst[i] = a[i] * b[i]` in Wiedemann
/// $\mathcal{T}_3 = \mathbb{F}_{2^8}$ (`TowerGf256`), bit-exact across `GFNI`, `AVX2`, and `Portable`.
#[inline]
pub fn gf256_shamir_mul(dst: &mut [u8], a: &[u8], b: &[u8]) {
    gf256_shamir_mul_with_backend(dst, a, b, detect_backend());
}

/// Execute `gf256_shamir_mul` on an explicit [`SimdBackend`].
pub fn gf256_shamir_mul_with_backend(dst: &mut [u8], a: &[u8], b: &[u8], backend: SimdBackend) {
    assert_eq!(dst.len(), a.len());
    assert_eq!(dst.len(), b.len());
    if dst.is_empty() {
        return;
    }

    #[cfg(target_arch = "x86_64")]
    {
        let caps = cpuid::probe_capabilities();
        let blocks = dst.len() / 32;
        let rem = dst.len() % 32;

        if backend == SimdBackend::X86Avx2GfniVpclmul && caps.avx2 && caps.gfni {
            if blocks > 0 {
                // SAFETY: `avx2` + `gfni` verified; `blocks * 32 <= dst.len()`.
                unsafe {
                    x86_64_asm::qsag_asm_gf256_shamir_mul_gfni(
                        dst.as_mut_ptr(),
                        a.as_ptr(),
                        b.as_ptr(),
                        blocks,
                    );
                }
            }
            if rem > 0 {
                let off = blocks * 32;
                let mut ta = [0u8; 32];
                let mut tb = [0u8; 32];
                let mut td = [0u8; 32];
                ta[..rem].copy_from_slice(&a[off..]);
                tb[..rem].copy_from_slice(&b[off..]);
                unsafe {
                    x86_64_asm::qsag_asm_gf256_shamir_mul_gfni(
                        td.as_mut_ptr(),
                        ta.as_ptr(),
                        tb.as_ptr(),
                        1,
                    );
                }
                dst[off..].copy_from_slice(&td[..rem]);
                ct_memzero(&mut ta);
                ct_memzero(&mut tb);
                ct_memzero(&mut td);
            }
            return;
        }

        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
        ) && caps.avx2
        {
            if blocks > 0 {
                // SAFETY: `avx2` verified; `AVX2_GF256_ISO_LUTS` is 32-byte aligned static rodata.
                unsafe {
                    x86_64_asm::qsag_asm_gf256_shamir_mul_avx2(
                        dst.as_mut_ptr(),
                        a.as_ptr(),
                        b.as_ptr(),
                        blocks,
                        &x86_64_asm::AVX2_GF256_ISO_LUTS,
                    );
                }
            }
            if rem > 0 {
                let off = blocks * 32;
                let mut ta = [0u8; 32];
                let mut tb = [0u8; 32];
                let mut td = [0u8; 32];
                ta[..rem].copy_from_slice(&a[off..]);
                tb[..rem].copy_from_slice(&b[off..]);
                unsafe {
                    x86_64_asm::qsag_asm_gf256_shamir_mul_avx2(
                        td.as_mut_ptr(),
                        ta.as_ptr(),
                        tb.as_ptr(),
                        1,
                        &x86_64_asm::AVX2_GF256_ISO_LUTS,
                    );
                }
                dst[off..].copy_from_slice(&td[..rem]);
                ct_memzero(&mut ta);
                ct_memzero(&mut tb);
                ct_memzero(&mut td);
            }
            return;
        }
    }

    let _ = backend;
    portable::gf256_shamir_mul_portable(dst, a, b);
}

/// Constant-time Shamir multiply-accumulate `acc[i] ^= scalar * shares[i]` in Wiedemann
/// $\mathcal{T}_3 = \mathbb{F}_{2^8}$ (`TowerGf256`), constant-time even when `scalar` is secret!
#[inline]
pub fn gf256_shamir_mac(acc: &mut [u8], shares: &[u8], scalar: u8) {
    gf256_shamir_mac_with_backend(acc, shares, scalar, detect_backend());
}

/// Execute `gf256_shamir_mac` on an explicit [`SimdBackend`].
pub fn gf256_shamir_mac_with_backend(
    acc: &mut [u8],
    shares: &[u8],
    scalar: u8,
    backend: SimdBackend,
) {
    assert_eq!(acc.len(), shares.len());
    if acc.is_empty() {
        return;
    }

    #[cfg(target_arch = "x86_64")]
    {
        let caps = cpuid::probe_capabilities();
        let blocks = acc.len() / 32;
        let rem = acc.len() % 32;

        if backend == SimdBackend::X86Avx2GfniVpclmul && caps.avx2 && caps.gfni {
            if blocks > 0 {
                unsafe {
                    x86_64_asm::qsag_asm_gf256_shamir_mac_gfni(
                        acc.as_mut_ptr(),
                        shares.as_ptr(),
                        scalar as u32,
                        blocks,
                    );
                }
            }
            if rem > 0 {
                let off = blocks * 32;
                let mut ts = [0u8; 32];
                let mut ta = [0u8; 32];
                ts[..rem].copy_from_slice(&shares[off..]);
                ta[..rem].copy_from_slice(&acc[off..]);
                unsafe {
                    x86_64_asm::qsag_asm_gf256_shamir_mac_gfni(
                        ta.as_mut_ptr(),
                        ts.as_ptr(),
                        scalar as u32,
                        1,
                    );
                }
                acc[off..].copy_from_slice(&ta[..rem]);
                ct_memzero(&mut ts);
                ct_memzero(&mut ta);
            }
            return;
        }

        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
        ) && caps.avx2
        {
            if blocks > 0 {
                unsafe {
                    x86_64_asm::qsag_asm_gf256_shamir_mac_avx2(
                        acc.as_mut_ptr(),
                        shares.as_ptr(),
                        scalar as u32,
                        blocks,
                        &x86_64_asm::AVX2_GF256_ISO_LUTS,
                    );
                }
            }
            if rem > 0 {
                let off = blocks * 32;
                let mut ts = [0u8; 32];
                let mut ta = [0u8; 32];
                ts[..rem].copy_from_slice(&shares[off..]);
                ta[..rem].copy_from_slice(&acc[off..]);
                unsafe {
                    x86_64_asm::qsag_asm_gf256_shamir_mac_avx2(
                        ta.as_mut_ptr(),
                        ts.as_ptr(),
                        scalar as u32,
                        1,
                        &x86_64_asm::AVX2_GF256_ISO_LUTS,
                    );
                }
                acc[off..].copy_from_slice(&ta[..rem]);
                ct_memzero(&mut ts);
                ct_memzero(&mut ta);
            }
            return;
        }
    }

    let _ = backend;
    portable::gf256_shamir_mac_portable(acc, shares, scalar);
}

/// 2-lane simultaneous 128-bit BDOZ MAC inner product in polynomial basis
/// $\mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$ (`VPCLMULQDQ` / `PCLMULQDQ` / `PMULL`).
#[inline]
pub fn tower128_bdoz_2lane_poly_mac(lhs_pairs: &[[u128; 2]], rhs_pairs: &[[u128; 2]]) -> [u128; 2] {
    tower128_bdoz_2lane_poly_mac_with_backend(lhs_pairs, rhs_pairs, detect_backend())
}

/// Execute `tower128_bdoz_2lane_poly_mac` on an explicit [`SimdBackend`].
pub fn tower128_bdoz_2lane_poly_mac_with_backend(
    lhs_pairs: &[[u128; 2]],
    rhs_pairs: &[[u128; 2]],
    backend: SimdBackend,
) -> [u128; 2] {
    assert_eq!(lhs_pairs.len(), rhs_pairs.len());
    if lhs_pairs.is_empty() {
        return [0u128; 2];
    }

    #[cfg(target_arch = "x86_64")]
    {
        let caps = cpuid::probe_capabilities();
        // Pack little-endian bytes explicitly on small stack chunks (`16` pairs = 512 B) so
        // arbitrary host `u128` alignment/endianness is 100% platform-invariant.
        if backend == SimdBackend::X86Avx2GfniVpclmul && caps.avx2 && caps.vpclmulqdq {
            let mut total0 = 0u128;
            let mut total1 = 0u128;
            let mut lbuf = [0u8; 32 * 16];
            let mut rbuf = [0u8; 32 * 16];
            let mut obuf = [0u8; 32];
            let mut b0 = [0u8; 16];
            let mut b1 = [0u8; 16];
            for (lc, rc) in lhs_pairs.chunks(16).zip(rhs_pairs.chunks(16)) {
                let n = lc.len();
                for i in 0..n {
                    lbuf[32 * i..32 * i + 16].copy_from_slice(&lc[i][0].to_le_bytes());
                    lbuf[32 * i + 16..32 * i + 32].copy_from_slice(&lc[i][1].to_le_bytes());
                    rbuf[32 * i..32 * i + 16].copy_from_slice(&rc[i][0].to_le_bytes());
                    rbuf[32 * i + 16..32 * i + 32].copy_from_slice(&rc[i][1].to_le_bytes());
                }
                unsafe {
                    x86_64_asm::qsag_asm_tower128_bdoz_mac_vpclmul(
                        obuf.as_mut_ptr(),
                        lbuf.as_ptr(),
                        rbuf.as_ptr(),
                        n,
                    );
                }
                b0.copy_from_slice(&obuf[0..16]);
                b1.copy_from_slice(&obuf[16..32]);
                total0 ^= u128::from_le_bytes(b0);
                total1 ^= u128::from_le_bytes(b1);
            }
            ct_memzero(&mut b0);
            ct_memzero(&mut b1);
            ct_memzero(&mut lbuf);
            ct_memzero(&mut rbuf);
            ct_memzero(&mut obuf);
            return [total0, total1];
        }

        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
        ) && caps.avx2
            && caps.pclmulqdq
        {
            let mut total0 = 0u128;
            let mut total1 = 0u128;
            let mut lbuf = [0u8; 32 * 16];
            let mut rbuf = [0u8; 32 * 16];
            let mut obuf = [0u8; 32];
            let mut b0 = [0u8; 16];
            let mut b1 = [0u8; 16];
            for (lc, rc) in lhs_pairs.chunks(16).zip(rhs_pairs.chunks(16)) {
                let n = lc.len();
                for i in 0..n {
                    lbuf[32 * i..32 * i + 16].copy_from_slice(&lc[i][0].to_le_bytes());
                    lbuf[32 * i + 16..32 * i + 32].copy_from_slice(&lc[i][1].to_le_bytes());
                    rbuf[32 * i..32 * i + 16].copy_from_slice(&rc[i][0].to_le_bytes());
                    rbuf[32 * i + 16..32 * i + 32].copy_from_slice(&rc[i][1].to_le_bytes());
                }
                unsafe {
                    x86_64_asm::qsag_asm_tower128_bdoz_mac_pclmul(
                        obuf.as_mut_ptr(),
                        lbuf.as_ptr(),
                        rbuf.as_ptr(),
                        n,
                    );
                }
                b0.copy_from_slice(&obuf[0..16]);
                b1.copy_from_slice(&obuf[16..32]);
                total0 ^= u128::from_le_bytes(b0);
                total1 ^= u128::from_le_bytes(b1);
            }
            ct_memzero(&mut b0);
            ct_memzero(&mut b1);
            ct_memzero(&mut lbuf);
            ct_memzero(&mut rbuf);
            ct_memzero(&mut obuf);
            return [total0, total1];
        }
    }

    #[cfg(target_arch = "aarch64")]
    {
        let caps = cpuid::probe_capabilities();
        if backend == SimdBackend::Aarch64NeonSha3Pmull && caps.aarch64_neon && caps.aarch64_pmull {
            let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
            let mut total0 = 0u128;
            let mut total1 = 0u128;
            let mut lbuf = [0u8; 32 * 16];
            let mut rbuf = [0u8; 32 * 16];
            let mut obuf = [0u8; 32];
            let mut b0 = [0u8; 16];
            let mut b1 = [0u8; 16];
            for (lc, rc) in lhs_pairs.chunks(16).zip(rhs_pairs.chunks(16)) {
                let n = lc.len();
                for i in 0..n {
                    lbuf[32 * i..32 * i + 16].copy_from_slice(&lc[i][0].to_le_bytes());
                    lbuf[32 * i + 16..32 * i + 32].copy_from_slice(&lc[i][1].to_le_bytes());
                    rbuf[32 * i..32 * i + 16].copy_from_slice(&rc[i][0].to_le_bytes());
                    rbuf[32 * i + 16..32 * i + 32].copy_from_slice(&rc[i][1].to_le_bytes());
                }
                unsafe {
                    aarch64_asm::qsag_asm_tower128_bdoz_mac_pmull(
                        obuf.as_mut_ptr(),
                        lbuf.as_ptr(),
                        rbuf.as_ptr(),
                        n,
                    );
                }
                b0.copy_from_slice(&obuf[0..16]);
                b1.copy_from_slice(&obuf[16..32]);
                total0 ^= u128::from_le_bytes(b0);
                total1 ^= u128::from_le_bytes(b1);
            }
            ct_memzero(&mut b0);
            ct_memzero(&mut b1);
            ct_memzero(&mut lbuf);
            ct_memzero(&mut rbuf);
            ct_memzero(&mut obuf);
            return [total0, total1];
        }
    }

    let _ = backend;
    portable::tower128_bdoz_2lane_poly_mac_portable(lhs_pairs, rhs_pairs)
}

/// 2-lane BDOZ MAC inner product in **exact Wiedemann $\mathcal{T}_7$ (`Tower128`) coordinates**,
/// bit-for-bit identical to `qsag_core::field::tower::Tower128::mul` via the compile-time verified
/// field isomorphism $\Psi : \mathcal{T}_7 \xrightarrow{\sim} \mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$.
pub fn tower128_bdoz_2lane_mac(lhs_pairs: &[[u128; 2]], rhs_pairs: &[[u128; 2]]) -> [u128; 2] {
    tower128_bdoz_2lane_mac_with_backend(lhs_pairs, rhs_pairs, detect_backend())
}

/// Execute `tower128_bdoz_2lane_mac` on an explicit [`SimdBackend`].
pub fn tower128_bdoz_2lane_mac_with_backend(
    lhs_pairs: &[[u128; 2]],
    rhs_pairs: &[[u128; 2]],
    backend: SimdBackend,
) -> [u128; 2] {
    assert_eq!(lhs_pairs.len(), rhs_pairs.len());
    if lhs_pairs.is_empty() {
        return [0u128; 2];
    }
    if backend == SimdBackend::Portable {
        return portable::tower128_bdoz_2lane_mac_portable(lhs_pairs, rhs_pairs);
    }

    let mut poly_acc0 = 0u128;
    let mut poly_acc1 = 0u128;
    let mut conv_l = [[0u128; 2]; 16];
    let mut conv_r = [[0u128; 2]; 16];
    for (lc, rc) in lhs_pairs.chunks(16).zip(rhs_pairs.chunks(16)) {
        let n = lc.len();
        for i in 0..n {
            conv_l[i] = [tower128_to_poly128_ct(lc[i][0]), tower128_to_poly128_ct(lc[i][1])];
            conv_r[i] = [tower128_to_poly128_ct(rc[i][0]), tower128_to_poly128_ct(rc[i][1])];
        }
        let mut chunk_poly =
            tower128_bdoz_2lane_poly_mac_with_backend(&conv_l[..n], &conv_r[..n], backend);
        poly_acc0 ^= chunk_poly[0];
        poly_acc1 ^= chunk_poly[1];
        unsafe {
            core::ptr::write_volatile(&mut chunk_poly[0], 0);
            core::ptr::write_volatile(&mut chunk_poly[1], 0);
        }
    }
    // Zeroize stack-converted share buffers and polynomial-basis accumulators
    for pair in &mut conv_l {
        unsafe {
            core::ptr::write_volatile(&mut pair[0], 0);
            core::ptr::write_volatile(&mut pair[1], 0);
        }
    }
    for pair in &mut conv_r {
        unsafe {
            core::ptr::write_volatile(&mut pair[0], 0);
            core::ptr::write_volatile(&mut pair[1], 0);
        }
    }
    let out = [
        poly128_to_tower128_ct(poly_acc0),
        poly128_to_tower128_ct(poly_acc1),
    ];
    unsafe {
        core::ptr::write_volatile(&mut poly_acc0, 0);
        core::ptr::write_volatile(&mut poly_acc1, 0);
    }
    out
}

/// Zero-branch constant-time Goldilocks ($p = 2^{64} - 2^{32} + 1$) modular multiplication,
/// exact for ALL `(a, b) in [0, u64::MAX]^2`.
#[inline]
pub fn goldilocks_mul_ct(a: u64, b: u64) -> u64 {
    goldilocks_mul_ct_with_backend(a, b, detect_backend())
}

pub fn goldilocks_mul_ct_with_backend(a: u64, b: u64, backend: SimdBackend) -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
        ) && cpuid::probe_capabilities().bmi2
        {
            return unsafe { x86_64_asm::qsag_asm_goldilocks_mul_ct_x86_64(a, b) };
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if backend == SimdBackend::Aarch64NeonSha3Pmull {
            let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
            return unsafe { aarch64_asm::qsag_asm_goldilocks_mul_ct_aarch64(a, b) };
        }
    }
    let _ = backend;
    portable::goldilocks_mul_ct_portable(a, b)
}

/// Zero-branch constant-time Goldilocks modular addition `(a + b) mod p` (`[0, u64::MAX]^2`).
#[inline]
pub fn goldilocks_add_ct(a: u64, b: u64) -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        if detect_backend() != SimdBackend::Portable {
            return unsafe { x86_64_asm::qsag_asm_goldilocks_add_ct_x86_64(a, b) };
        }
    }
    portable::goldilocks_add_ct_portable(a, b)
}

/// Zero-branch constant-time Goldilocks modular subtraction `(a - b) mod p` (`[0, u64::MAX]^2`).
#[inline]
pub fn goldilocks_sub_ct(a: u64, b: u64) -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        if detect_backend() != SimdBackend::Portable {
            return unsafe { x86_64_asm::qsag_asm_goldilocks_sub_ct_x86_64(a, b) };
        }
    }
    portable::goldilocks_sub_ct_portable(a, b)
}

/// Zero-branch constant-time Goldilocks Poseidon2 S-box $x^7 \bmod p$ (`[0, u64::MAX]`).
#[inline]
pub fn goldilocks_pow7_ct(x: u64) -> u64 {
    goldilocks_pow7_ct_with_backend(x, detect_backend())
}

pub fn goldilocks_pow7_ct_with_backend(x: u64, backend: SimdBackend) -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        if matches!(
            backend,
            SimdBackend::X86Avx2Pclmul | SimdBackend::X86Avx2GfniVpclmul
        ) && cpuid::probe_capabilities().bmi2
        {
            return unsafe { x86_64_asm::qsag_asm_goldilocks_pow7_ct_x86_64(x) };
        }
    }
    let _ = backend;
    let x2 = goldilocks_mul_ct_with_backend(x, x, backend);
    let x3 = goldilocks_mul_ct_with_backend(x2, x, backend);
    let x6 = goldilocks_mul_ct_with_backend(x3, x3, backend);
    goldilocks_mul_ct_with_backend(x6, x, backend)
}

/// Zero-branch `BMI2 + ADX` (`mulx` + `adcx` + `adox`) 2-term Goldilocks inner product
/// `(a0 * b0 + a1 * b1) mod p`, exact for ALL `(a0, b0, a1, b1) in [0, u64::MAX]^4`.
#[inline]
pub fn goldilocks_dot2_ct(a0: u64, b0: u64, a1: u64, b1: u64) -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        let caps = cpuid::probe_capabilities();
        if caps.bmi2 && caps.adx {
            return unsafe { x86_64_asm::qsag_asm_goldilocks_dot2_adx_x86_64(a0, b0, a1, b1) };
        }
    }
    let p0 = goldilocks_mul_ct(a0, b0);
    let p1 = goldilocks_mul_ct(a1, b1);
    goldilocks_add_ct(p0, p1)
}

/// Constant-time 32-byte tag comparison backed by straight-line platform assembly (`0` branches).
#[inline]
pub fn ct_eq_32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        unsafe { x86_64_asm::qsag_asm_ct_eq_32_x86_64(a.as_ptr(), b.as_ptr()) == 1 }
    }
    #[cfg(target_arch = "aarch64")]
    {
        let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
        unsafe { aarch64_asm::qsag_asm_ct_eq_32_aarch64(a.as_ptr(), b.as_ptr()) == 1 }
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        portable::ct_eq_32_portable(a, b)
    }
}

/// Constant-time variable-length byte-slice comparison backed by platform assembly.
#[inline]
pub fn ct_eq_bytes(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    if a.is_empty() {
        return true;
    }
    #[cfg(target_arch = "x86_64")]
    {
        unsafe {
            x86_64_asm::qsag_asm_ct_eq_bytes_x86_64(a.as_ptr(), b.as_ptr(), a.len()) == 1
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        portable::ct_eq_bytes_portable(a, b)
    }
}

/// Hardware assembly memory wipe (`mfence` / `dmb ish`) immune to LLVM dead-store elimination.
#[inline]
pub fn ct_memzero(buf: &mut [u8]) {
    if buf.is_empty() {
        return;
    }
    #[cfg(target_arch = "x86_64")]
    {
        unsafe {
            x86_64_asm::qsag_asm_ct_memzero_x86_64(buf.as_mut_ptr(), buf.len());
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        let _dit_guard = cpuid::ensure_aarch64_dit_enabled();
        unsafe {
            aarch64_asm::qsag_asm_ct_memzero_aarch64(buf.as_mut_ptr(), buf.len());
        }
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        portable::ct_memzero_portable(buf);
    }
}

// ============================================================================
// Exhaustive Algebraic, Boundary & Cross-Backend Differential Unit Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Deterministic test-vector sponge stream backed directly by FIPS 202 `keccak_f1600_4x_portable`.
    struct KeccakTestStream {
        state: KeccakState4x,
        idx: usize,
    }

    impl KeccakTestStream {
        fn new(seed: u64) -> Self {
            let mut state = KeccakState4x::default();
            state.0[0] = [seed, seed ^ 0xA5A5_5A5A_F0F0_0F0F, seed.wrapping_add(1), 0x1F];
            state.0[16] = [0x8000_0000_0000_0000; 4];
            portable::keccak_f1600_4x_portable(&mut state);
            Self { state, idx: 0 }
        }

        fn next_u64(&mut self) -> u64 {
            if self.idx >= 68 {
                portable::keccak_f1600_4x_portable(&mut self.state);
                self.idx = 0;
            }
            let lane = self.idx / 4;
            let inst = self.idx % 4;
            self.idx += 1;
            self.state.0[lane][inst]
        }

        fn next_u128(&mut self) -> u128 {
            (self.next_u64() as u128) | ((self.next_u64() as u128) << 64)
        }
    }

    #[test]
    fn keccak_f1600_x4_matches_fips202_shake256_vectors() {
        // Test all 4 lanes simultaneously: lane 0 = SHAKE256(""), lane 1 = SHAKE256("abc"),
        // lane 2 & 3 = distinct multi-word states!
        let mut st_asm = KeccakState4x::default();
        // Sponge 0: empty input -> pad byte 0x1f at lane 0, 0x80 at byte 135 (lane 16 MSB)
        st_asm.0[0][0] = 0x1f;
        st_asm.0[16][0] = 0x8000_0000_0000_0000;
        // Sponge 1: "abc" -> 0x61, 0x62, 0x63, 0x1f at lane 0
        st_asm.0[0][1] = u64::from_le_bytes([0x61, 0x62, 0x63, 0x1f, 0, 0, 0, 0]);
        st_asm.0[16][1] = 0x8000_0000_0000_0000;
        // Sponge 2 & 3: nontrivial patterns across all 25 lanes
        for (l, lane) in st_asm.0.iter_mut().enumerate() {
            lane[2] = (l as u64).wrapping_mul(0x0123_4567_89AB_CDEF);
            lane[3] = !(l as u64).wrapping_mul(0xFEDC_BA98_7654_3210);
        }

        let mut st_port = st_asm;
        portable::keccak_f1600_4x_portable(&mut st_port);
        keccak_f1600_x4(&mut st_asm);
        assert_eq!(st_asm.0, st_port.0);

        // Check official NIST FIPS 202 SHAKE256("") first 32 bytes in sponge 0:
        let expected_empty: [u8; 32] = [
            0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e,
            0xeb, 0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64,
            0x6e, 0xd5, 0x76, 0x2f,
        ];
        let expected_abc: [u8; 32] = [
            0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77, 0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4,
            0x11, 0x4d, 0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee, 0x4f, 0x94, 0xea, 0x37,
            0xe7, 0x8b, 0x57, 0x39,
        ];
        let mut got_empty = [0u8; 32];
        let mut got_abc = [0u8; 32];
        for w in 0..4 {
            got_empty[8 * w..8 * w + 8].copy_from_slice(&st_asm.0[w][0].to_le_bytes());
            got_abc[8 * w..8 * w + 8].copy_from_slice(&st_asm.0[w][1].to_le_bytes());
        }
        assert_eq!(got_empty, expected_empty);
        assert_eq!(got_abc, expected_abc);
    }

    #[test]
    fn keccak_chi_mpc_3party_rss_reconstruction_and_asm_parity() {
        let mut rng = KeccakTestStream::new(0x1122_3344_5566_7788);
        let mut b0 = KeccakRow256::default();
        let mut b1 = KeccakRow256::default();
        let mut b2 = KeccakRow256::default();
        let mut r0 = KeccakRow256::default();
        let mut r1 = KeccakRow256::default();
        let mut r2 = KeccakRow256::default();

        for x in 0..5 {
            for lane in 0..4 {
                b0.0[x][lane] = rng.next_u64();
                b1.0[x][lane] = rng.next_u64();
                b2.0[x][lane] = rng.next_u64();
                r0.0[x][lane] = rng.next_u64();
                r1.0[x][lane] = rng.next_u64();
                r2.0[x][lane] = r0.0[x][lane] ^ r1.0[x][lane]; // correlated zero-share!
            }
        }

        let mut out0 = KeccakRow256::default();
        let mut out1 = KeccakRow256::default();
        let mut out2 = KeccakRow256::default();
        keccak_chi_mpc_row256(&mut out0, &b0, &b1, &r0);
        keccak_chi_mpc_row256(&mut out1, &b1, &b2, &r1);
        keccak_chi_mpc_row256(&mut out2, &b2, &b0, &r2);

        let mut out0_port = KeccakRow256::default();
        portable::keccak_chi_mpc_4x_portable(&mut out0_port, &b0, &b1, &r0);
        assert_eq!(out0.0, out0_port.0);

        // Verify exact reconstruction across all 5 * 256 = 1,280 Boolean Chi gates!
        for x in 0..5 {
            let x1 = (x + 1) % 5;
            let x2 = (x + 2) % 5;
            for lane in 0..4 {
                let bx = b0.0[x][lane] ^ b1.0[x][lane] ^ b2.0[x][lane];
                let bx1 = b0.0[x1][lane] ^ b1.0[x1][lane] ^ b2.0[x1][lane];
                let bx2 = b0.0[x2][lane] ^ b1.0[x2][lane] ^ b2.0[x2][lane];
                let expected = bx ^ ((!bx1) & bx2);
                let recon = out0.0[x][lane] ^ out1.0[x][lane] ^ out2.0[x][lane];
                assert_eq!(recon, expected);
            }
        }
    }

    #[test]
    fn exhaustive_65536_gf256_wiedemann_t3_mul_and_mac_across_all_backends() {
        // Test ALL 256 * 256 = 65,536 pairs (a, b) in chunks + odd tail lengths across
        // Portable, X86Avx2Pclmul, and X86Avx2GfniVpclmul!
        let mut a_all = [0u8; 512];
        let mut b_all = [0u8; 512];
        let mut exp_all = [0u8; 512];
        let mut out_gfni = [0u8; 512];
        let mut out_avx2 = [0u8; 512];

        for chunk_base in (0..65536usize).step_by(512) {
            for k in 0..512 {
                let idx = chunk_base + k;
                let a = (idx >> 8) as u8;
                let b = (idx & 0xFF) as u8;
                a_all[k] = a;
                b_all[k] = b;
            }
            gf256_shamir_mul_with_backend(&mut exp_all, &a_all, &b_all, SimdBackend::Portable);
            gf256_shamir_mul_with_backend(
                &mut out_avx2,
                &a_all,
                &b_all,
                SimdBackend::X86Avx2Pclmul,
            );
            gf256_shamir_mul_with_backend(
                &mut out_gfni,
                &a_all,
                &b_all,
                SimdBackend::X86Avx2GfniVpclmul,
            );
            assert_eq!(out_avx2, exp_all);
            assert_eq!(out_gfni, exp_all);
        }

        // Also test all 256 scalars on non-multiple-of-32 length (77 bytes) for Shamir MAC!
        let mut shares = [0u8; 77];
        for (i, share) in shares.iter_mut().enumerate() {
            *share = (i as u8).wrapping_mul(37).wrapping_add(13);
        }
        for scalar in 0..=255u8 {
            let mut acc_port = [0x5Au8; 77];
            let mut acc_avx2 = [0x5Au8; 77];
            let mut acc_gfni = [0x5Au8; 77];
            gf256_shamir_mac_with_backend(&mut acc_port, &shares, scalar, SimdBackend::Portable);
            gf256_shamir_mac_with_backend(
                &mut acc_avx2,
                &shares,
                scalar,
                SimdBackend::X86Avx2Pclmul,
            );
            gf256_shamir_mac_with_backend(
                &mut acc_gfni,
                &shares,
                scalar,
                SimdBackend::X86Avx2GfniVpclmul,
            );
            assert_eq!(acc_avx2, acc_port);
            assert_eq!(acc_gfni, acc_port);
        }
    }

    #[test]
    fn tower128_bdoz_2lane_mac_vpclmul_pclmul_wiedemann_parity() {
        let mut rng = KeccakTestStream::new(0xCAFE_BABE_DEAD_BEEF);
        let mut lhs = [[0u128; 2]; 37];
        let mut rhs = [[0u128; 2]; 37];
        for i in 0..37 {
            lhs[i] = [rng.next_u128(), rng.next_u128()];
            rhs[i] = [rng.next_u128(), rng.next_u128()];
        }
        // Include all-ones u128::MAX edge case in lane 0 & 1!
        lhs[0] = [u128::MAX, 1];
        rhs[0] = [u128::MAX, u128::MAX];

        let poly_port =
            tower128_bdoz_2lane_poly_mac_with_backend(&lhs, &rhs, SimdBackend::Portable);
        let poly_pclmul =
            tower128_bdoz_2lane_poly_mac_with_backend(&lhs, &rhs, SimdBackend::X86Avx2Pclmul);
        let poly_vpclmul =
            tower128_bdoz_2lane_poly_mac_with_backend(&lhs, &rhs, SimdBackend::X86Avx2GfniVpclmul);
        assert_eq!(poly_pclmul, poly_port);
        assert_eq!(poly_vpclmul, poly_port);

        let t7_port = tower128_bdoz_2lane_mac_with_backend(&lhs, &rhs, SimdBackend::Portable);
        let t7_pclmul =
            tower128_bdoz_2lane_mac_with_backend(&lhs, &rhs, SimdBackend::X86Avx2Pclmul);
        let t7_vpclmul =
            tower128_bdoz_2lane_mac_with_backend(&lhs, &rhs, SimdBackend::X86Avx2GfniVpclmul);
        assert_eq!(t7_pclmul, t7_port);
        assert_eq!(t7_vpclmul, t7_port);
    }

    #[test]
    fn goldilocks_asm_edge_cases_including_u64_max_and_dot2_adx() {
        let p = GOLDILOCKS_PRIME as u128;
        let edges: [u64; 14] = [
            0,
            1,
            2,
            7,
            (1u64 << 32) - 1,
            1u64 << 32,
            (1u64 << 32) + 1,
            GOLDILOCKS_PRIME - 2,
            GOLDILOCKS_PRIME - 1,
            GOLDILOCKS_PRIME,
            GOLDILOCKS_PRIME + 1,
            u64::MAX - (1u64 << 32),
            u64::MAX - 1,
            u64::MAX,
        ];
        for &a in &edges {
            let p7 = goldilocks_pow7_ct(a);
            assert!(p7 < GOLDILOCKS_PRIME);
            let a_m = (a as u128) % p;
            let exp_p7 = (((((((a_m * a_m) % p) * a_m) % p) * ((((a_m * a_m) % p) * a_m) % p))
                % p)
                * a_m)
                % p;
            assert_eq!(p7 as u128, exp_p7);

            for &b in &edges {
                let b_m = (b as u128) % p;
                let got_add = goldilocks_add_ct(a, b);
                let got_sub = goldilocks_sub_ct(a, b);
                let got_mul = goldilocks_mul_ct(a, b);
                assert!(got_add < GOLDILOCKS_PRIME);
                assert!(got_sub < GOLDILOCKS_PRIME);
                assert!(got_mul < GOLDILOCKS_PRIME);
                assert_eq!(got_add as u128, (a_m + b_m) % p);
                assert_eq!(got_sub as u128, (a_m + p - b_m) % p);
                assert_eq!(got_mul as u128, (a_m * b_m) % p);

                for &c in &[0u64, 1, GOLDILOCKS_PRIME - 1, u64::MAX] {
                    for &d in &[0u64, 7, GOLDILOCKS_PRIME - 1, u64::MAX] {
                        let c_m = (c as u128) % p;
                        let d_m = (d as u128) % p;
                        let got_dot = goldilocks_dot2_ct(a, b, c, d);
                        assert!(got_dot < GOLDILOCKS_PRIME);
                        assert_eq!(got_dot as u128, ((a_m * b_m) % p + (c_m * d_m) % p) % p);
                    }
                }
            }
        }
    }

    #[test]
    fn ct_eq_and_memzero_asm_verification() {
        let base = [0x3Cu8; 32];
        assert!(ct_eq_32(&base, &base));
        assert!(ct_eq_bytes(&base, &base));
        for byte_idx in 0..32 {
            for bit in 0..8 {
                let mut mutated = base;
                mutated[byte_idx] ^= 1u8 << bit;
                assert!(!ct_eq_32(&base, &mutated));
                assert!(!ct_eq_bytes(&base, &mutated));
            }
        }
        let mut secret = [0xAAu8; 93];
        ct_memzero(&mut secret);
        assert_eq!(secret, [0u8; 93]);
        let _ = enable_hardware_dit();
    }
}

/// Overwrite valid typed storage without allowing dead-store elimination.
#[inline(never)]
pub fn volatile_fill<T: Copy>(buf: &mut [T], value: T) {
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    for slot in buf.iter_mut() {
        // SAFETY: the exclusive reference is aligned and valid for a T write.
        unsafe { core::ptr::write_volatile(slot, value); }
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    core::hint::black_box(buf);
}

#[cfg(feature = "std")]
pub mod durable;

/// Permute independent states in four-state SIMD blocks, including a padded tail.
pub fn keccak_f1600_batch(states: &mut [[u64; 25]]) {
    let backend = detect_backend();
    for block in states.chunks_mut(4) {
        let mut packed = KeccakState4x::default();
        for (i, state) in block.iter().enumerate() {
            for (lane, value) in state.iter().enumerate() { packed.0[lane][i] = *value; }
        }
        keccak_f1600_x4_with_backend(&mut packed, backend);
        for (i, state) in block.iter_mut().enumerate() {
            for (lane, value) in state.iter_mut().enumerate() { *value = packed.0[lane][i]; }
        }
        volatile_fill(&mut packed.0, [0; 4]);
    }
}
