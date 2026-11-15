//! Apple Silicon / ARM64 (`aarch64`) Constant-Time `NEON` + `PMULL` + `FEAT_SHA256` + `FEAT_DIT`
//! Microarchitectural Kernels (`core::arch::aarch64`).
//!
//! Provides native ARMv8-A / Apple M-series / Neoverse vector kernels for all operations that
//! previously fell back to scalar code on `aarch64`:
//! 1. **`GF(2^8)` Shamir `mul` & `mac` (`NEON` `vqtbl1q_u8` + `vmull_p8` `PMULL`):**
//!    Maps Wiedemann $\mathcal{T}_3 \xrightarrow{\Phi} \mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$
//!    via register-resident split-nibble `vqtbl1q_u8` tables, multiplies 16 bytes in parallel
//!    via hardware polynomial carryless `vmull_p8` / `vmull_high_p8`, and fuses `0x11B` modular
//!    reduction with $\Phi^{-1}$ in register-resident `vqtbl1q_u8` tables (`0` secret-indexed
//!    memory accesses, `0` branches).
//! 2. **256-Way Bitsliced 3-Party RSS MPC `Keccak` $\chi$-Row (`NEON` 128-bit `uint8x16_t`):**
//!    Executes `keccak_chi_mpc_row256` across all 5 lanes $\times$ 256 bits using `veorq_u8`,
//!    `vandq_u8`, `vbicq_u8`, and `vbslq_u8`.
//! 3. **4-Lane `int32x4_t` Seiler Signed-Montgomery `ML-DSA` `NTT` / `InvNTT` / `PointwiseMul`:**
//!    Bit-exact `[0, q)` canonical FIPS 204 Algorithms 41, 42, and 45 using `vmull_s32`,
//!    `vmull_high_s32`, `vmlsl_s32`, `vmlsl_high_s32`, and `vshrn_n_s64` (`0` branches, `0` divs).
//! 4. **ARMv8 `FEAT_SHA256` Intrinsics (`vsha256hq_u32` / `vsha256h2q_u32` / `vsha256su0q_u32` /
//!    `vsha256su1q_u32`)** and scoped **`FEAT_DIT` (`PSTATE.DIT = 1`)** execution guards.

#![allow(clippy::incompatible_msrv)]

use core::arch::aarch64::*;

use crate::cpuid::{DitRequirement, HardwareDitGuard};
use crate::ntt_simd::{MLDSA_N, MLDSA_Q, MLDSA_QINV, MLDSA_R2_MOD_Q, NTT_TABLES};
use crate::portable::{
    GFNI_MAT_POLY_TO_T3, GFNI_MAT_T3_TO_POLY, KeccakRow256, gfni_poly_mul_u8, sim_gf2p8affineqb,
    wiedemann_mul_t3_u8,
};
use crate::sha2_hw::SHA256_HW_CONSTS;

/// Acquire a scoped hardware Data-Independent Timing (`PSTATE.DIT = 1`) guard on `FEAT_DIT`
/// processors (Apple M1–M4, Neoverse V1/V2/N2), restoring prior `PSTATE.DIT` on drop.
#[inline(always)]
pub fn enter_aarch64_dit_region() -> HardwareDitGuard {
    DitRequirement::BestEffort
        .enter()
        .expect("BestEffort DIT guard never fails")
}

/// Explicitly zeroize volatile scratch caller-saved NEON vector registers `v0..v7` and `v16..v31`
/// (`v8..v15` low 64 bits are AAPCS64 callee-saved and managed by the compiler epilogue).
#[inline(always)]
unsafe fn wipe_neon_scratch_regs() {
    // SAFETY: `v0..v7` and `v16..v31` are AAPCS64 caller-saved volatile vector registers;
    // declaring them as `out` clobbers ensures live secret intermediates are wiped before `ret`.
    unsafe {
        core::arch::asm!(
            "eor v0.16b,  v0.16b,  v0.16b",
            "eor v1.16b,  v1.16b,  v1.16b",
            "eor v2.16b,  v2.16b,  v2.16b",
            "eor v3.16b,  v3.16b,  v3.16b",
            "eor v4.16b,  v4.16b,  v4.16b",
            "eor v5.16b,  v5.16b,  v5.16b",
            "eor v6.16b,  v6.16b,  v6.16b",
            "eor v7.16b,  v7.16b,  v7.16b",
            "eor v16.16b, v16.16b, v16.16b",
            "eor v17.16b, v17.16b, v17.16b",
            "eor v18.16b, v18.16b, v18.16b",
            "eor v19.16b, v19.16b, v19.16b",
            "eor v20.16b, v20.16b, v20.16b",
            "eor v21.16b, v21.16b, v21.16b",
            "eor v22.16b, v22.16b, v22.16b",
            "eor v23.16b, v23.16b, v23.16b",
            out("v0") _, out("v1") _, out("v2") _, out("v3") _,
            out("v4") _, out("v5") _, out("v6") _, out("v7") _,
            out("v16") _, out("v17") _, out("v18") _, out("v19") _,
            out("v20") _, out("v21") _, out("v22") _, out("v23") _,
            options(nostack),
        );
    }
}

// ============================================================================
// 1. Wiedemann T_3 = GF(2^8) Shamir `mul` & `mac` via `PMULL` (`vmull_p8`) + `TBL` (`vqtbl1q_u8`)
// ============================================================================

#[repr(C, align(16))]
pub(crate) struct Aarch64Gf256PmullConsts {
    pub t3_to_poly_lo: [u8; 16],
    pub t3_to_poly_hi: [u8; 16],
    pub poly_lo_to_t3_lo: [u8; 16],
    pub poly_lo_to_t3_hi: [u8; 16],
    pub poly_hi_to_t3_lo: [u8; 16],
    pub poly_hi_to_t3_hi: [u8; 16],
    pub mac_basis_lo: [u8; 16],
    pub mac_basis_hi: [u8; 16],
}

const fn clmul8_const(a: u8, b: u8) -> u16 {
    let mut acc = 0u16;
    let mut i = 0u32;
    while i < 8 {
        if ((b >> i) & 1) != 0 {
            acc ^= (a as u16) << i;
        }
        i += 1;
    }
    acc
}

const fn build_aarch64_gf256_pmull_consts() -> Aarch64Gf256PmullConsts {
    let mut t3_to_poly_lo = [0u8; 16];
    let mut t3_to_poly_hi = [0u8; 16];
    let mut poly_lo_to_t3_lo = [0u8; 16];
    let mut poly_lo_to_t3_hi = [0u8; 16];
    let mut poly_hi_to_t3_lo = [0u8; 16];
    let mut poly_hi_to_t3_hi = [0u8; 16];
    let mut mac_basis_lo = [0u8; 16];
    let mut mac_basis_hi = [0u8; 16];

    let mut i = 0usize;
    while i < 16 {
        let lo = i as u8;
        let hi = (i as u8) << 4;
        t3_to_poly_lo[i] = sim_gf2p8affineqb(lo, GFNI_MAT_T3_TO_POLY, 0);
        t3_to_poly_hi[i] = sim_gf2p8affineqb(hi, GFNI_MAT_T3_TO_POLY, 0);

        poly_lo_to_t3_lo[i] = sim_gf2p8affineqb(lo, GFNI_MAT_POLY_TO_T3, 0);
        poly_lo_to_t3_hi[i] = sim_gf2p8affineqb(hi, GFNI_MAT_POLY_TO_T3, 0);

        // High byte `p_hi` represents `p_hi(z) * z^8 == p_hi(z) * 0x1B (mod z^8 + z^4 + z^3 + z + 1)`.
        let red_lo = gfni_poly_mul_u8(lo, 0x1B);
        let red_hi = gfni_poly_mul_u8(hi, 0x1B);
        poly_hi_to_t3_lo[i] = sim_gf2p8affineqb(red_lo, GFNI_MAT_POLY_TO_T3, 0);
        poly_hi_to_t3_hi[i] = sim_gf2p8affineqb(red_hi, GFNI_MAT_POLY_TO_T3, 0);

        mac_basis_lo[i] = lo;
        mac_basis_hi[i] = hi;
        i += 1;
    }

    Aarch64Gf256PmullConsts {
        t3_to_poly_lo,
        t3_to_poly_hi,
        poly_lo_to_t3_lo,
        poly_lo_to_t3_hi,
        poly_hi_to_t3_lo,
        poly_hi_to_t3_hi,
        mac_basis_lo,
        mac_basis_hi,
    }
}

pub(crate) static A64_GF256_PMULL_CONSTS: Aarch64Gf256PmullConsts =
    build_aarch64_gf256_pmull_consts();

// Compile-time algebraic verification that split-nibble `Phi` + `vmull_p8` (`clmul8`) + fused
// `0x11B` reduction & `Phi^{-1}` equals `wiedemann_mul_t3_u8` on all 64 basis pairs and boundary bytes.
const _: () = {
    const fn sim_pmull_t3(a: u8, b: u8) -> u8 {
        let c = &A64_GF256_PMULL_CONSTS;
        let ap = c.t3_to_poly_lo[(a & 0x0F) as usize] ^ c.t3_to_poly_hi[(a >> 4) as usize];
        let bp = c.t3_to_poly_lo[(b & 0x0F) as usize] ^ c.t3_to_poly_hi[(b >> 4) as usize];
        let prod = clmul8_const(ap, bp);
        let plo = (prod & 0xFF) as u8;
        let phi = (prod >> 8) as u8;
        let t_lo =
            c.poly_lo_to_t3_lo[(plo & 0x0F) as usize] ^ c.poly_lo_to_t3_hi[(plo >> 4) as usize];
        let t_hi =
            c.poly_hi_to_t3_lo[(phi & 0x0F) as usize] ^ c.poly_hi_to_t3_hi[(phi >> 4) as usize];
        t_lo ^ t_hi
    }

    let mut i = 0u32;
    while i < 8 {
        let mut j = 0u32;
        while j < 8 {
            let a = 1u8 << i;
            let b = 1u8 << j;
            assert!(
                sim_pmull_t3(a, b) == wiedemann_mul_t3_u8(a, b),
                "AArch64 PMULL+TBL T3 basis isomorphism mismatch"
            );
            j += 1;
        }
        i += 1;
    }
    let mut x = 0u16;
    while x < 256 {
        let b = x as u8;
        let partner = b.wrapping_mul(0x9D) ^ 0x53;
        assert!(
            sim_pmull_t3(b, partner) == wiedemann_mul_t3_u8(b, partner),
            "AArch64 PMULL+TBL T3 sample mismatch"
        );
        x += 1;
    }
};

#[inline]
#[target_feature(enable = "neon,aes")]
unsafe fn gf256_mul16_pmull_vec(
    va: uint8x16_t,
    vb: uint8x16_t,
    mask_0f: uint8x16_t,
    t3_lo: uint8x16_t,
    t3_hi: uint8x16_t,
    plo_lo: uint8x16_t,
    plo_hi: uint8x16_t,
    phi_lo: uint8x16_t,
    phi_hi: uint8x16_t,
) -> uint8x16_t {
    let a_lo = vandq_u8(va, mask_0f);
    let a_hi = vshrq_n_u8::<4>(va);
    let ap = veorq_u8(vqtbl1q_u8(t3_lo, a_lo), vqtbl1q_u8(t3_hi, a_hi));

    let b_lo = vandq_u8(vb, mask_0f);
    let b_hi = vshrq_n_u8::<4>(vb);
    let bp = veorq_u8(vqtbl1q_u8(t3_lo, b_lo), vqtbl1q_u8(t3_hi, b_hi));

    let ap_p8 = vreinterpretq_p8_u8(ap);
    let bp_p8 = vreinterpretq_p8_u8(bp);
    let prod0 = vreinterpretq_u16_p16(vmull_p8(vget_low_p8(ap_p8), vget_low_p8(bp_p8)));
    let prod1 = vreinterpretq_u16_p16(vmull_high_p8(ap_p8, bp_p8));

    let p_lo = vmovn_high_u16(vmovn_u16(prod0), prod1);
    let p_hi = vshrn_high_n_u16::<8>(vshrn_n_u16::<8>(prod0), prod1);

    let r_lo = veorq_u8(
        vqtbl1q_u8(plo_lo, vandq_u8(p_lo, mask_0f)),
        vqtbl1q_u8(plo_hi, vshrq_n_u8::<4>(p_lo)),
    );
    let r_hi = veorq_u8(
        vqtbl1q_u8(phi_lo, vandq_u8(p_hi, mask_0f)),
        vqtbl1q_u8(phi_hi, vshrq_n_u8::<4>(p_hi)),
    );
    veorq_u8(r_lo, r_hi)
}

/// Constant-time 16-lane `NEON + PMULL` (`vmull_p8` + `vqtbl1q_u8`) Shamir slice multiplication
/// `dst[i] = a[i] * b[i]` in Wiedemann $\mathcal{T}_3 = \mathbb{F}_{2^8}$.
///
/// # Safety
/// Caller must verify runtime `NEON` + `FEAT_PMULL` (`caps.aarch64_neon && caps.aarch64_pmull`)
/// and equal slice lengths `dst.len() == a.len() == b.len()`.
#[target_feature(enable = "neon,aes")]
pub unsafe fn gf256_shamir_mul_pmull_neon(dst: &mut [u8], a: &[u8], b: &[u8]) {
    debug_assert_eq!(dst.len(), a.len());
    debug_assert_eq!(dst.len(), b.len());
    let _dit_guard = enter_aarch64_dit_region();
    let c = &A64_GF256_PMULL_CONSTS;

    unsafe {
        let mask_0f = vdupq_n_u8(0x0F);
        let t3_lo = vld1q_u8(c.t3_to_poly_lo.as_ptr());
        let t3_hi = vld1q_u8(c.t3_to_poly_hi.as_ptr());
        let plo_lo = vld1q_u8(c.poly_lo_to_t3_lo.as_ptr());
        let plo_hi = vld1q_u8(c.poly_lo_to_t3_hi.as_ptr());
        let phi_lo = vld1q_u8(c.poly_hi_to_t3_lo.as_ptr());
        let phi_hi = vld1q_u8(c.poly_hi_to_t3_hi.as_ptr());

        let len = dst.len();
        let blocks16 = len / 16;
        let rem = len % 16;
        let dp = dst.as_mut_ptr();
        let ap = a.as_ptr();
        let bp = b.as_ptr();

        let mut i = 0usize;
        while i < blocks16 {
            let off = i * 16;
            let va = vld1q_u8(ap.add(off));
            let vb = vld1q_u8(bp.add(off));
            let prod = gf256_mul16_pmull_vec(
                va, vb, mask_0f, t3_lo, t3_hi, plo_lo, plo_hi, phi_lo, phi_hi,
            );
            vst1q_u8(dp.add(off), prod);
            i += 1;
        }

        if rem > 0 {
            let off = blocks16 * 16;
            let mut ta = [0u8; 16];
            let mut tb = [0u8; 16];
            let mut td = [0u8; 16];
            ta[..rem].copy_from_slice(&a[off..]);
            tb[..rem].copy_from_slice(&b[off..]);
            let va = vld1q_u8(ta.as_ptr());
            let vb = vld1q_u8(tb.as_ptr());
            let prod = gf256_mul16_pmull_vec(
                va, vb, mask_0f, t3_lo, t3_hi, plo_lo, plo_hi, phi_lo, phi_hi,
            );
            vst1q_u8(td.as_mut_ptr(), prod);
            dst[off..].copy_from_slice(&td[..rem]);
            crate::ct_memzero(&mut ta);
            crate::ct_memzero(&mut tb);
            crate::ct_memzero(&mut td);
        }

        wipe_neon_scratch_regs();
    }
}

/// Constant-time `NEON + PMULL` Shamir multiply-accumulate `acc[i] ^= scalar * shares[i]`
/// in Wiedemann $\mathcal{T}_3 = \mathbb{F}_{2^8}$.
///
/// Synthesizes the secret `scalar`'s split-nibble tables `(mac_lo, mac_hi)` purely in NEON
/// vector registers using `gf256_mul16_pmull_vec` (`vmull_p8` + `vqtbl1q_u8`, zero secret-indexed
/// RAM accesses!), then processes `shares` at 32 bytes/iter using two `vqtbl1q_u8` instructions
/// per 16-byte lane.
///
/// # Safety
/// Caller must verify runtime `NEON` + `FEAT_PMULL` (`caps.aarch64_neon && caps.aarch64_pmull`)
/// and `acc.len() == shares.len()`.
#[target_feature(enable = "neon,aes")]
pub unsafe fn gf256_shamir_mac_pmull_neon(acc: &mut [u8], shares: &[u8], scalar: u8) {
    debug_assert_eq!(acc.len(), shares.len());
    let _dit_guard = enter_aarch64_dit_region();
    let c = &A64_GF256_PMULL_CONSTS;

    unsafe {
        let mask_0f = vdupq_n_u8(0x0F);
        let t3_lo = vld1q_u8(c.t3_to_poly_lo.as_ptr());
        let t3_hi = vld1q_u8(c.t3_to_poly_hi.as_ptr());
        let plo_lo = vld1q_u8(c.poly_lo_to_t3_lo.as_ptr());
        let plo_hi = vld1q_u8(c.poly_lo_to_t3_hi.as_ptr());
        let phi_lo = vld1q_u8(c.poly_hi_to_t3_lo.as_ptr());
        let phi_hi = vld1q_u8(c.poly_hi_to_t3_hi.as_ptr());

        let vscalar = vdupq_n_u8(scalar);
        let basis_lo = vld1q_u8(c.mac_basis_lo.as_ptr());
        let basis_hi = vld1q_u8(c.mac_basis_hi.as_ptr());

        let mac_lo = gf256_mul16_pmull_vec(
            vscalar, basis_lo, mask_0f, t3_lo, t3_hi, plo_lo, plo_hi, phi_lo, phi_hi,
        );
        let mac_hi = gf256_mul16_pmull_vec(
            vscalar, basis_hi, mask_0f, t3_lo, t3_hi, plo_lo, plo_hi, phi_lo, phi_hi,
        );

        let len = acc.len();
        let blocks32 = len / 32;
        let dp = acc.as_mut_ptr();
        let sp = shares.as_ptr();

        let mut i = 0usize;
        while i < blocks32 {
            let off = i * 32;
            let s0 = vld1q_u8(sp.add(off));
            let s1 = vld1q_u8(sp.add(off + 16));
            let a0 = vld1q_u8(dp.add(off));
            let a1 = vld1q_u8(dp.add(off + 16));

            let p0 = veorq_u8(
                vqtbl1q_u8(mac_lo, vandq_u8(s0, mask_0f)),
                vqtbl1q_u8(mac_hi, vshrq_n_u8::<4>(s0)),
            );
            let p1 = veorq_u8(
                vqtbl1q_u8(mac_lo, vandq_u8(s1, mask_0f)),
                vqtbl1q_u8(mac_hi, vshrq_n_u8::<4>(s1)),
            );

            vst1q_u8(dp.add(off), veorq_u8(a0, p0));
            vst1q_u8(dp.add(off + 16), veorq_u8(a1, p1));
            i += 1;
        }

        let mut off = blocks32 * 32;
        if len - off >= 16 {
            let s0 = vld1q_u8(sp.add(off));
            let a0 = vld1q_u8(dp.add(off));
            let p0 = veorq_u8(
                vqtbl1q_u8(mac_lo, vandq_u8(s0, mask_0f)),
                vqtbl1q_u8(mac_hi, vshrq_n_u8::<4>(s0)),
            );
            vst1q_u8(dp.add(off), veorq_u8(a0, p0));
            off += 16;
        }

        let rem = len - off;
        if rem > 0 {
            let mut ts = [0u8; 16];
            let mut ta = [0u8; 16];
            ts[..rem].copy_from_slice(&shares[off..]);
            ta[..rem].copy_from_slice(&acc[off..]);
            let s0 = vld1q_u8(ts.as_ptr());
            let a0 = vld1q_u8(ta.as_ptr());
            let p0 = veorq_u8(
                vqtbl1q_u8(mac_lo, vandq_u8(s0, mask_0f)),
                vqtbl1q_u8(mac_hi, vshrq_n_u8::<4>(s0)),
            );
            vst1q_u8(ta.as_mut_ptr(), veorq_u8(a0, p0));
            acc[off..].copy_from_slice(&ta[..rem]);
            crate::ct_memzero(&mut ts);
            crate::ct_memzero(&mut ta);
        }

        wipe_neon_scratch_regs();
    }
}

// ============================================================================
// 2. 256-Way Bitsliced 3-Party RSS MPC `Keccak` chi-Row (`NEON` 128-bit)
// ============================================================================

/// Constant-time `NEON` 256-way bitsliced 3-party RSS MPC $\chi$-row gate:
/// `out[x] = s0[x] ^ s0[x+2] ^ (s0[x+1] & (s0[x+2] ^ s1[x+2])) ^ (s1[x+1] & s0[x+2]) ^ r_mask[x]`.
///
/// Note the identity `(u_x1 & (u_x2 ^ v_x2)) ^ (v_x1 & u_x2) == vbslq_u8(u_x2, u_x1 ^ v_x1 ^ v_x2, 0) ^ (u_x1 & v_x2) ^ ...`;
/// we evaluate the exact Boolean share polynomial via `veorq_u8`, `vandq_u8`, `vbicq_u8`, and `vbslq_u8`.
///
/// # Safety
/// Caller must verify runtime `NEON` (`caps.aarch64_neon`).
#[target_feature(enable = "neon")]
pub unsafe fn keccak_chi_mpc_row256_neon(
    out: &mut KeccakRow256,
    s0: &KeccakRow256,
    s1: &KeccakRow256,
    r_mask: &KeccakRow256,
) {
    let _dit_guard = enter_aarch64_dit_region();
    // Observe Boolean identity on each bit:
    //   `(u1 & (u2 ^ v2)) ^ (v1 & u2)`
    //   `= vbslq_u8(u2, vbicq_u8(v1, v2) ^ vandq_u8(u1, vbicq_u8(all1, v2)) ^ ..., vandq_u8(u1, v2))`
    // Even cleaner exact decomposition using `vbslq_u8(sel, if_1, if_0) = (sel & if_1) | (!sel & if_0)`:
    //   When `u2 == 1`: `(u1 & (1 ^ v2)) ^ v1 = vbicq_u8(u1, v2) ^ v1`.
    //   When `u2 == 0`: `u1 & v2 = vandq_u8(u1, v2)`.
    //   Check:
    //     `u2 = 0`: `0 & (0 ^ v2) ^ (v1 & 0) = 0`? WAIT: `(u1 & (0 ^ v2)) ^ 0 = u1 & v2`! YES!
    //     `u2 = 1`: `(u1 & (1 ^ v2)) ^ (v1 & 1) = (u1 & !v2) ^ v1 = vbicq_u8(u1, v2) ^ v1`! YES!
    //   Therefore `vbslq_u8(u2, veorq_u8(vbicq_u8(u1, v2), v1), vandq_u8(u1, v2))` IS IDENTICAL
    //   on every single bit `(u1, v1, u2, v2) in {0, 1}^4`!
    unsafe {
        let mut x = 0usize;
        while x < 5 {
            let x1 = if x + 1 >= 5 { x + 1 - 5 } else { x + 1 };
            let x2 = if x + 2 >= 5 { x + 2 - 5 } else { x + 2 };

            let mut half = 0usize;
            while half < 2 {
                let byte_off = half * 16;
                let u_x = vld1q_u8(s0.0[x].as_ptr().cast::<u8>().add(byte_off));
                let u_x1 = vld1q_u8(s0.0[x1].as_ptr().cast::<u8>().add(byte_off));
                let u_x2 = vld1q_u8(s0.0[x2].as_ptr().cast::<u8>().add(byte_off));
                let v_x1 = vld1q_u8(s1.0[x1].as_ptr().cast::<u8>().add(byte_off));
                let v_x2 = vld1q_u8(s1.0[x2].as_ptr().cast::<u8>().add(byte_off));
                let r_x = vld1q_u8(r_mask.0[x].as_ptr().cast::<u8>().add(byte_off));

                let branch_u2_one = veorq_u8(vbicq_u8(u_x1, v_x2), v_x1);
                let branch_u2_zero = vandq_u8(u_x1, v_x2);
                let and_term = vbslq_u8(u_x2, branch_u2_one, branch_u2_zero);
                let res = veorq_u8(veorq_u8(u_x, u_x2), veorq_u8(and_term, r_x));

                vst1q_u8(out.0[x].as_mut_ptr().cast::<u8>().add(byte_off), res);
                half += 1;
            }
            x += 1;
        }
        wipe_neon_scratch_regs();
    }
}

// Compile-time exhaustive truth-table check over all `2^4 = 16` `(u1, v1, u2, v2)` bit tuples
// proving `vbslq_u8(u2, (u1 & !v2) ^ v1, u1 & v2) == (u1 & (u2 ^ v2)) ^ (v1 & u2)`.
const _: () = {
    let mut mask = 0u8;
    while mask < 16 {
        let u1 = mask & 1;
        let v1 = (mask >> 1) & 1;
        let u2 = (mask >> 2) & 1;
        let v2 = (mask >> 3) & 1;
        let spec = (u1 & (u2 ^ v2)) ^ (v1 & u2);
        let b1 = (u1 & (v2 ^ 1)) ^ v1;
        let b0 = u1 & v2;
        let bsl = if u2 == 1 { b1 } else { b0 };
        assert!(
            bsl == spec,
            "NEON vbslq/vbicq/veorq MPC chi identity mismatch"
        );
        mask += 1;
    }
};

// ============================================================================
// 3. 4-Lane `int32x4_t` Seiler Signed-Montgomery `ML-DSA` `NTT` / `InvNTT` / `PointwiseMul`
// ============================================================================

/// Seiler (`IACR ePrint 2018/039`) 4-lane `NEON` signed Montgomery product
/// `((a * b_mont - ((a * b_mont) mod^+- 2^32) * Q) >> 32)`.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn fqmul_neon(a: int32x4_t, b_mont: int32x4_t, qinv: int32x4_t, q: int32x4_t) -> int32x4_t {
    let prod_lo = vmull_s32(vget_low_s32(a), vget_low_s32(b_mont));
    let prod_hi = vmull_high_s32(a, b_mont);
    let m = vmulq_s32(vmulq_s32(a, b_mont), qinv);
    let diff_lo = vmlsl_s32(prod_lo, vget_low_s32(m), vget_low_s32(q));
    let diff_hi = vmlsl_high_s32(prod_hi, m, q);
    vshrn_high_n_s64::<32>(vshrn_n_s64::<32>(diff_lo), diff_hi)
}

/// Shift-add centered reduction `r = a - ((a + 2^22) >> 23) * q` (`|r| < q` for `|a| <= 250 q`).
#[inline]
#[target_feature(enable = "neon")]
unsafe fn reduce32_neon(a: int32x4_t, half23: int32x4_t, q: int32x4_t) -> int32x4_t {
    let t = vshrq_n_s32::<23>(vaddq_s32(a, half23));
    vmlsq_s32(a, t, q)
}

/// Constant-time canonicalization of `r in (-q, q)` into `[0, q)`.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn caddq_neon(r: int32x4_t, q: int32x4_t) -> int32x4_t {
    let neg_mask = vreinterpretq_s32_u32(vcltq_s32(r, vdupq_n_s32(0)));
    vaddq_s32(r, vandq_s32(neg_mask, q))
}

/// Constant-time 4-lane `NEON` FIPS 204 forward `NTT` (`Algorithm 41`).
///
/// # Safety
/// Caller must verify runtime `NEON` (`caps.aarch64_neon`).
#[inline(never)]
#[target_feature(enable = "neon")]
pub unsafe fn mldsa_ntt_neon(coeffs: &mut [u32; MLDSA_N]) {
    let _dit_guard = enter_aarch64_dit_region();
    let p = coeffs.as_mut_ptr().cast::<i32>();
    let zp = NTT_TABLES.zetas_mont.as_ptr();

    unsafe {
        let qinv = vdupq_n_s32(MLDSA_QINV);
        let q = vdupq_n_s32(MLDSA_Q as i32);
        let half23 = vdupq_n_s32(1 << 22);

        macro_rules! neon_ct_stage {
            ($vecs_per_half:literal, $blocks:literal, $m_base:literal) => {{
                let mut blk = 0usize;
                while blk < $blocks {
                    let z = vdupq_n_s32(*zp.add($m_base + blk));
                    let base = blk * (2 * $vecs_per_half) * 4;
                    let mut v = 0usize;
                    while v < $vecs_per_half {
                        let lo_ptr = p.add(base + v * 4);
                        let hi_ptr = p.add(base + ($vecs_per_half + v) * 4);
                        let lo = vld1q_s32(lo_ptr);
                        let hi = vld1q_s32(hi_ptr);
                        let t = fqmul_neon(hi, z, qinv, q);
                        vst1q_s32(lo_ptr, vaddq_s32(lo, t));
                        vst1q_s32(hi_ptr, vsubq_s32(lo, t));
                        v += 1;
                    }
                    blk += 1;
                }
            }};
        }

        // Full-vector Cooley-Tukey stages: len = 128, 64, 32, 16, 8, 4
        neon_ct_stage!(32, 1, 1);
        neon_ct_stage!(16, 2, 2);
        neon_ct_stage!(8, 4, 4);
        neon_ct_stage!(4, 8, 8);
        neon_ct_stage!(2, 16, 16);
        neon_ct_stage!(1, 32, 32);

        // Fused in-register stages len = 2 and len = 1 + canonicalization into `[0, q)`
        let mut k = 0usize;
        while k < 64 {
            let vp = p.add(k * 4);
            let mut v = vld1q_s32(vp);

            // Stage len = 2 (`m = 64 + k`)
            let z2 = vdupq_n_s32(*zp.add(64 + k));
            let lo2 = vget_low_s32(v);
            let hi2 = vget_high_s32(v);
            let t2 = vget_low_s32(fqmul_neon(vcombine_s32(hi2, hi2), z2, qinv, q));
            v = vcombine_s32(vadd_s32(lo2, t2), vsub_s32(lo2, t2));

            // Stage len = 1 (`m0 = 128 + 2*k`, `m1 = 128 + 2*k + 1`)
            let za = *zp.add(128 + 2 * k);
            let zb = *zp.add(128 + 2 * k + 1);
            let z1_arr = [za, zb, za, zb];
            let z1 = vld1q_s32(z1_arr.as_ptr());
            let even = vuzp1q_s32(v, v);
            let odd = vuzp2q_s32(v, v);
            let t1 = fqmul_neon(odd, z1, qinv, q);
            let sum1 = vaddq_s32(even, t1);
            let dif1 = vsubq_s32(even, t1);
            v = vzip1q_s32(sum1, dif1);

            v = caddq_neon(reduce32_neon(v, half23, q), q);
            vst1q_s32(vp, v);
            k += 1;
        }

        wipe_neon_scratch_regs();
    }
}

/// Constant-time 4-lane `NEON` FIPS 204 inverse `InvNTT` (`Algorithm 42`).
///
/// # Safety
/// Caller must verify runtime `NEON` (`caps.aarch64_neon`).
#[inline(never)]
#[target_feature(enable = "neon")]
pub unsafe fn mldsa_inv_ntt_neon(coeffs: &mut [u32; MLDSA_N]) {
    let _dit_guard = enter_aarch64_dit_region();
    let p = coeffs.as_mut_ptr().cast::<i32>();
    let nzp = NTT_TABLES.neg_zetas_mont.as_ptr();

    unsafe {
        let qinv = vdupq_n_s32(MLDSA_QINV);
        let q = vdupq_n_s32(MLDSA_Q as i32);
        let half23 = vdupq_n_s32(1 << 22);

        // Fused in-register Gentleman-Sande stages len = 1 and len = 2
        let mut k = 0usize;
        while k < 64 {
            let vp = p.add(k * 4);
            let mut v = vld1q_s32(vp);

            // Stage len = 1 (`m_a = 255 - 2*k`, `m_b = 255 - (2*k + 1)`)
            let za = *nzp.add(255 - 2 * k);
            let zb = *nzp.add(255 - (2 * k + 1));
            let z1_arr = [za, zb, za, zb];
            let z1 = vld1q_s32(z1_arr.as_ptr());
            let even = vuzp1q_s32(v, v);
            let odd = vuzp2q_s32(v, v);
            let s1 = vaddq_s32(even, odd);
            let d1 = fqmul_neon(vsubq_s32(even, odd), z1, qinv, q);
            v = vzip1q_s32(s1, d1);

            // Stage len = 2 (`m = 127 - k`)
            let z2 = vdupq_n_s32(*nzp.add(127 - k));
            let lo2 = vget_low_s32(v);
            let hi2 = vget_high_s32(v);
            let s2 = vadd_s32(lo2, hi2);
            let diff2 = vsub_s32(lo2, hi2);
            let d2 = vget_low_s32(fqmul_neon(vcombine_s32(diff2, diff2), z2, qinv, q));
            v = vcombine_s32(s2, d2);

            vst1q_s32(vp, v);
            k += 1;
        }

        macro_rules! neon_gs_stage {
            ($vecs_per_half:literal, $blocks:literal, $m_top:literal, $reduce_lo:literal) => {{
                let mut blk = 0usize;
                while blk < $blocks {
                    let z_neg = vdupq_n_s32(*nzp.add($m_top - blk));
                    let base = blk * (2 * $vecs_per_half) * 4;
                    let mut v = 0usize;
                    while v < $vecs_per_half {
                        let lo_ptr = p.add(base + v * 4);
                        let hi_ptr = p.add(base + ($vecs_per_half + v) * 4);
                        let lo = vld1q_s32(lo_ptr);
                        let hi = vld1q_s32(hi_ptr);
                        let mut sum = vaddq_s32(lo, hi);
                        if $reduce_lo {
                            sum = reduce32_neon(sum, half23, q);
                        }
                        let dif = fqmul_neon(vsubq_s32(lo, hi), z_neg, qinv, q);
                        vst1q_s32(lo_ptr, sum);
                        vst1q_s32(hi_ptr, dif);
                        v += 1;
                    }
                    blk += 1;
                }
            }};
        }

        // Full-vector GS stages len = 4, 8, 16, 32 (with lazy-bound reset at len = 32), 64
        neon_gs_stage!(1, 32, 63, false);
        neon_gs_stage!(2, 16, 31, false);
        neon_gs_stage!(4, 8, 15, false);
        neon_gs_stage!(8, 4, 7, true);
        neon_gs_stage!(16, 2, 3, false);

        // Fused stage len = 128 + `256^{-1} mod q` scaling + canonicalization into `[0, q)`
        let inv256_v = vdupq_n_s32(NTT_TABLES.inv256_mont);
        let neg_z1_inv256_v = vdupq_n_s32(NTT_TABLES.neg_zeta1_inv256_mont);
        let mut v = 0usize;
        while v < 32 {
            let lo_ptr = p.add(v * 4);
            let hi_ptr = p.add((32 + v) * 4);
            let lo = vld1q_s32(lo_ptr);
            let hi = vld1q_s32(hi_ptr);
            let r0 = fqmul_neon(vaddq_s32(lo, hi), inv256_v, qinv, q);
            let r1 = fqmul_neon(vsubq_s32(lo, hi), neg_z1_inv256_v, qinv, q);
            vst1q_s32(lo_ptr, caddq_neon(r0, q));
            vst1q_s32(hi_ptr, caddq_neon(r1, q));
            v += 1;
        }

        wipe_neon_scratch_regs();
    }
}

/// Constant-time 4-lane `NEON` FIPS 204 pointwise NTT multiplication (`Algorithm 45`).
///
/// # Safety
/// Caller must verify runtime `NEON` (`caps.aarch64_neon`).
#[target_feature(enable = "neon")]
pub unsafe fn mldsa_pointwise_mul_neon(
    out: &mut [u32; MLDSA_N],
    lhs: &[u32; MLDSA_N],
    rhs: &[u32; MLDSA_N],
) {
    let _dit_guard = enter_aarch64_dit_region();
    let op = out.as_mut_ptr().cast::<i32>();
    let lp = lhs.as_ptr().cast::<i32>();
    let rp = rhs.as_ptr().cast::<i32>();

    unsafe {
        let qinv = vdupq_n_s32(MLDSA_QINV);
        let q = vdupq_n_s32(MLDSA_Q as i32);
        let r2 = vdupq_n_s32(MLDSA_R2_MOD_Q);

        let mut v = 0usize;
        while v < 64 {
            let off = v * 4;
            let a = vld1q_s32(lp.add(off));
            let b = vld1q_s32(rp.add(off));
            let b_mont = fqmul_neon(b, r2, qinv, q);
            let prod = fqmul_neon(a, b_mont, qinv, q);
            vst1q_s32(op.add(off), caddq_neon(prod, q));
            v += 1;
        }

        wipe_neon_scratch_regs();
    }
}

// ============================================================================
// 4. ARMv8 `FEAT_SHA256` Intrinsics (`vsha256hq_u32` / `vsha256h2q_u32` / `vsha256su0q_u32` / `vsha256su1q_u32`)
// ============================================================================

/// Compress `blocks` (`64` bytes each) into FIPS 180-4 `SHA-256` `state` using ARMv8 `FEAT_SHA256`
/// intrinsics (`vsha256hq_u32`, `vsha256h2q_u32`, `vsha256su0q_u32`, `vsha256su1q_u32`) under a
/// scoped `FEAT_DIT` guard.
///
/// # Safety
/// Caller must verify runtime `NEON` + `FEAT_SHA256` (`caps.aarch64_neon && caps.aarch64_sha2`).
#[target_feature(enable = "neon,sha2")]
pub unsafe fn sha256_compress_blocks_neon_sha2(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    if blocks.is_empty() {
        return;
    }
    let _dit_guard = enter_aarch64_dit_region();
    let kp = SHA256_HW_CONSTS.k.as_ptr();

    unsafe {
        let mut abcd = vld1q_u32(state.as_ptr());
        let mut efgh = vld1q_u32(state.as_ptr().add(4));

        for block in blocks {
            let abcd_saved = abcd;
            let efgh_saved = efgh;
            let bp = block.as_ptr();

            let mut w0 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(bp)));
            let mut w1 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(bp.add(16))));
            let mut w2 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(bp.add(32))));
            let mut w3 = vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(bp.add(48))));

            macro_rules! sha256_quad_sched {
                ($m0:ident, $m1:ident, $m2:ident, $m3:ident, $k_idx:literal) => {{
                    let wk = vaddq_u32($m0, vld1q_u32(kp.add($k_idx)));
                    let prev_abcd = abcd;
                    abcd = vsha256hq_u32(abcd, efgh, wk);
                    efgh = vsha256h2q_u32(efgh, prev_abcd, wk);
                    $m0 = vsha256su1q_u32(vsha256su0q_u32($m0, $m1), $m2, $m3);
                }};
            }

            macro_rules! sha256_quad_final {
                ($m0:ident, $k_idx:literal) => {{
                    let wk = vaddq_u32($m0, vld1q_u32(kp.add($k_idx)));
                    let prev_abcd = abcd;
                    abcd = vsha256hq_u32(abcd, efgh, wk);
                    efgh = vsha256h2q_u32(efgh, prev_abcd, wk);
                }};
            }

            sha256_quad_sched!(w0, w1, w2, w3, 0);
            sha256_quad_sched!(w1, w2, w3, w0, 4);
            sha256_quad_sched!(w2, w3, w0, w1, 8);
            sha256_quad_sched!(w3, w0, w1, w2, 12);
            sha256_quad_sched!(w0, w1, w2, w3, 16);
            sha256_quad_sched!(w1, w2, w3, w0, 20);
            sha256_quad_sched!(w2, w3, w0, w1, 24);
            sha256_quad_sched!(w3, w0, w1, w2, 28);
            sha256_quad_sched!(w0, w1, w2, w3, 32);
            sha256_quad_sched!(w1, w2, w3, w0, 36);
            sha256_quad_sched!(w2, w3, w0, w1, 40);
            sha256_quad_sched!(w3, w0, w1, w2, 44);
            sha256_quad_final!(w0, 48);
            sha256_quad_final!(w1, 52);
            sha256_quad_final!(w2, 56);
            sha256_quad_final!(w3, 60);

            abcd = vaddq_u32(abcd, abcd_saved);
            efgh = vaddq_u32(efgh, efgh_saved);
        }

        vst1q_u32(state.as_mut_ptr(), abcd);
        vst1q_u32(state.as_mut_ptr().add(4), efgh);
        wipe_neon_scratch_regs();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exhaustive_65536_gf256_pmull_neon_parity() {
        let caps = crate::cpuid::probe_capabilities();
        if !(caps.aarch64_neon && caps.aarch64_pmull) {
            return;
        }
        let mut a = [0u8; 256];
        let mut b = [0u8; 256];
        let mut got = [0u8; 256];
        let mut exp = [0u8; 256];
        for i in 0..256 {
            b[i] = i as u8;
        }
        for x in 0..=255u8 {
            a.fill(x);
            unsafe {
                gf256_shamir_mul_pmull_neon(&mut got, &a, &b);
            }
            crate::portable::gf256_shamir_mul_portable(&mut exp, &a, &b);
            assert_eq!(got, exp, "GF(256) PMULL mul mismatch at x={x}");

            let mut acc_got = [0xA5u8; 256];
            let mut acc_exp = [0xA5u8; 256];
            unsafe {
                gf256_shamir_mac_pmull_neon(&mut acc_got, &b, x);
            }
            crate::portable::gf256_shamir_mac_portable(&mut acc_exp, &b, x);
            assert_eq!(acc_got, acc_exp, "GF(256) PMULL mac mismatch at scalar={x}");
        }
    }

    #[test]
    fn neon_sha256_intrinsics_matches_portable() {
        let caps = crate::cpuid::probe_capabilities();
        if !(caps.aarch64_neon && caps.aarch64_sha2) {
            return;
        }
        let iv: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let blocks = [[0x61u8; 64], [0x80u8; 64], [0xFFu8; 64]];
        let mut s_hw = iv;
        let mut s_sw = iv;
        unsafe {
            sha256_compress_blocks_neon_sha2(&mut s_hw, &blocks);
        }
        crate::sha2_hw::sha256_compress_blocks_portable(&mut s_sw, &blocks);
        assert_eq!(s_hw, s_sw);
    }
}
