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
