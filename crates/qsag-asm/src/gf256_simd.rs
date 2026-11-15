//! Constant-time register-resident split-nibble `vpshufb` `GF(256)` Shamir kernels (`AVX2`)
//! for `x86_64` processors without `GFNI`.
//!
//! Instead of converting bytes between Wiedemann $\mathcal{T}_3$ and `Poly(0x11B)` and running an
//! 8-stage serial Russian-peasant shift-and-XOR dependency chain (`75` instructions / 32 B), we
//! exploit the native tower structure $\mathcal{T}_3 = \mathcal{T}_2[\alpha]/(\alpha^2 + x_1 \alpha + 1)$:
//!
//! - Every byte $a = a_0 + a_1 \alpha \in \mathcal{T}_3$ splits into two 4-bit nibbles
//!   $a_0, a_1 \in \mathcal{T}_2 = \mathbb{F}_{16}$.
//! - Because $|\mathcal{T}_2| = 16$, the entire multiplicative group $\mathcal{T}_2^\times \cong C_{15}$
//!   fits inside a single 16-byte `vpshufb` register lane (`0` memory table lookups!).
//! - Setting `LOG_T2[0] = 0x80` and using unsigned saturating byte addition (`vpaddusb`) sets
//!   bit 7 (`>= 0x80`) if and only if either nibble is zero; signed `vpcmpgtb(..., 14)` reduces
//!   non-zero exponent sums `[15, 28]` modulo `15` while leaving bit 7 intact so `vpshufb`
//!   hardware-zeroes any product by `0` in constant time.
//! - Compile-time `const` verification below exhaustively checks all `256 * 256 = 65,536` byte
//!   pairs against [`crate::portable::wiedemann_mul_t3_u8`].

use crate::portable::{tower_mul_t2, tower_scale_t2, wiedemann_mul_t3_u8};

#[repr(C, align(32))]
pub(crate) struct T3VpshufbConsts {
    pub log_t2: [u8; 32],
    pub exp_t2: [u8; 32],
    pub scale_exp_t2: [u8; 32],
    pub basis_nibbles: [u8; 32],
}

const fn build_t3_vpshufb_consts() -> T3VpshufbConsts {
    // Locate canonical primitive generator `g` of order 15 in Wiedemann `T_2 = GF(16)`.
    let mut g = 2u8;
    let gen = loop {
        let mut cur = 1u8;
        let mut step = 0usize;
        let mut ok = true;
        while step < 14 {
            cur = tower_mul_t2(cur, g);
            if cur == 1 {
                ok = false;
            }
            step += 1;
        }
        cur = tower_mul_t2(cur, g);
        if ok && cur == 1 {
            break g;
        }
        g += 1;
        assert!(g < 16, "T_2^x must have a cyclic generator of order 15");
    };

    let mut log16 = [0x80u8; 16];
    let mut exp16 = [0u8; 16];
    let mut sc_exp16 = [0u8; 16];
    let mut p = 1u8;
    let mut e = 0usize;
    while e < 15 {
        log16[p as usize] = e as u8;
        exp16[e] = p;
        sc_exp16[e] = p ^ tower_scale_t2(p);
        p = tower_mul_t2(p, gen);
        e += 1;
    }

    let mut log_t2 = [0u8; 32];
    let mut exp_t2 = [0u8; 32];
    let mut scale_exp_t2 = [0u8; 32];
    let mut basis_nibbles = [0u8; 32];
    let mut i = 0usize;
    while i < 16 {
        log_t2[i] = log16[i];
        log_t2[16 + i] = log16[i];
        exp_t2[i] = exp16[i];
        exp_t2[16 + i] = exp16[i];
        scale_exp_t2[i] = sc_exp16[i];
        scale_exp_t2[16 + i] = sc_exp16[i];
        basis_nibbles[i] = i as u8;
        basis_nibbles[16 + i] = (i as u8) << 4;
        i += 1;
    }

    T3VpshufbConsts {
        log_t2,
        exp_t2,
        scale_exp_t2,
        basis_nibbles,
    }
}

pub(crate) static T3_VPSHUFB_CONSTS: T3VpshufbConsts = build_t3_vpshufb_consts();

// Exhaustive compile-time proof over ALL 65,536 `(a, b)` pairs in `GF(256)` (`T_3`) that the
// exact `vpshufb` + `vpaddusb` + signed `vpcmpgtb` instruction semantics equal `wiedemann_mul_t3_u8`!
const _: () = {
    #[inline]
    const fn sim_vpshufb16(tbl: &[u8; 32], idx: u8) -> u8 {
        if (idx & 0x80) != 0 {
            0
        } else {
            tbl[(idx & 0x0F) as usize]
        }
    }

    #[inline]
    const fn sim_t2_reduce_exp(lu: u8, lv: u8) -> u8 {
        let s = lu.saturating_add(lv);
        let gt14 = if (s as i8) > 14 { 0xFFu8 } else { 0x00u8 };
        s.wrapping_sub(gt14 & 15)
    }

    let mut a = 0usize;
    while a < 256 {
        let mut b = 0usize;
        while b < 256 {
            let ab = a as u8;
            let bb = b as u8;
            let a0 = ab & 0x0F;
            let a1 = ab >> 4;
            let asum = a0 ^ a1;
            let b0 = bb & 0x0F;
            let b1 = bb >> 4;
            let bsum = b0 ^ b1;

            let sp = sim_t2_reduce_exp(
                sim_vpshufb16(&T3_VPSHUFB_CONSTS.log_t2, a0),
                sim_vpshufb16(&T3_VPSHUFB_CONSTS.log_t2, b0),
            );
            let sq = sim_t2_reduce_exp(
                sim_vpshufb16(&T3_VPSHUFB_CONSTS.log_t2, a1),
                sim_vpshufb16(&T3_VPSHUFB_CONSTS.log_t2, b1),
            );
            let sr = sim_t2_reduce_exp(
                sim_vpshufb16(&T3_VPSHUFB_CONSTS.log_t2, asum),
                sim_vpshufb16(&T3_VPSHUFB_CONSTS.log_t2, bsum),
            );

            let p = sim_vpshufb16(&T3_VPSHUFB_CONSTS.exp_t2, sp);
            let q = sim_vpshufb16(&T3_VPSHUFB_CONSTS.exp_t2, sq);
            let q_sc = sim_vpshufb16(&T3_VPSHUFB_CONSTS.scale_exp_t2, sq);
            let r = sim_vpshufb16(&T3_VPSHUFB_CONSTS.exp_t2, sr);

            let lo = p ^ q;
            let hi = r ^ p ^ q_sc;
            let got = lo | (hi << 4);
            let exp = wiedemann_mul_t3_u8(ab, bb);
            assert!(got == exp, "T3 vpshufb Karatsuba mismatch");
            b += 1;
        }
        a += 1;
    }
};

/// Constant-time register-only split-nibble `vpshufb` Shamir multiplication `dst[i] = a[i] * b[i]`
/// in Wiedemann $\mathcal{T}_3$ (`32` bytes/iter). Caller guarantees `blocks32 >= 1` and `caps.avx2`.
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn gf256_shamir_mul_vpshufb_avx2(
    dst: *mut u8,
    a: *const u8,
    b: *const u8,
    blocks32: usize,
) {
    let tbl_ptr = (&raw const T3_VPSHUFB_CONSTS).cast::<u8>();
    // SAFETY: caller verified `caps.avx2` and `blocks32 * 32` valid bytes; `T3_VPSHUFB_CONSTS` is
    // 32-byte aligned static `.rodata` (`128` bytes < 4 KiB). All touched YMM registers are wiped.
    unsafe {
        core::arch::asm!(
            "vmovdqa ymm13, ymmword ptr [{tbl} + 0]",
            "vmovdqa ymm14, ymmword ptr [{tbl} + 32]",
            "vmovdqa ymm15, ymmword ptr [{tbl} + 64]",
            "mov {tmp:e}, 0x0f",
            "vmovd xmm11, {tmp:e}",
            "vpbroadcastb ymm11, xmm11",
            "mov {tmp:e}, 0x0e",
            "vmovd xmm12, {tmp:e}",
            "vpbroadcastb ymm12, xmm12",
            "2:",
            "vmovdqu ymm0, ymmword ptr [{a}]",
            "vmovdqu ymm1, ymmword ptr [{b}]",
            "vpand ymm2, ymm0, ymm11",
            "vpsrlw ymm3, ymm0, 4",
            "vpand ymm3, ymm3, ymm11",
            "vpxor ymm4, ymm2, ymm3",
            "vpand ymm5, ymm1, ymm11",
            "vpsrlw ymm6, ymm1, 4",
            "vpand ymm6, ymm6, ymm11",
            "vpxor ymm7, ymm5, ymm6",

            "vpshufb ymm2, ymm13, ymm2",
            "vpshufb ymm5, ymm13, ymm5",
            "vpshufb ymm3, ymm13, ymm3",
            "vpshufb ymm6, ymm13, ymm6",
            "vpshufb ymm4, ymm13, ymm4",
            "vpshufb ymm7, ymm13, ymm7",

            "vpaddusb ymm2, ymm2, ymm5",
            "vpaddusb ymm3, ymm3, ymm6",
            "vpaddusb ymm4, ymm4, ymm7",

            "vpcmpgtb ymm5, ymm2, ymm12",
            "vpcmpgtb ymm6, ymm3, ymm12",
            "vpcmpgtb ymm7, ymm4, ymm12",
            "vpand ymm5, ymm5, ymm11",
            "vpand ymm6, ymm6, ymm11",
            "vpand ymm7, ymm7, ymm11",
            "vpsubb ymm2, ymm2, ymm5",
            "vpsubb ymm3, ymm3, ymm6",
            "vpsubb ymm4, ymm4, ymm7",

            "vpshufb ymm2, ymm14, ymm2",
            "vpshufb ymm5, ymm14, ymm3",
            "vpshufb ymm6, ymm15, ymm3",
            "vpshufb ymm4, ymm14, ymm4",

            "vpxor ymm5, ymm5, ymm2",
            "vpxor ymm4, ymm4, ymm2",
            "vpxor ymm4, ymm4, ymm6",
            "vpsllw ymm4, ymm4, 4",
            "vpor ymm5, ymm5, ymm4",
            "vmovdqu ymmword ptr [{dst}], ymm5",

            "add {a}, 32",
            "add {b}, 32",
            "add {dst}, 32",
            "dec rcx",
            "jnz 2b",

            "vpxor ymm0,  ymm0,  ymm0",
            "vpxor ymm1,  ymm1,  ymm1",
            "vpxor ymm2,  ymm2,  ymm2",
            "vpxor ymm3,  ymm3,  ymm3",
            "vpxor ymm4,  ymm4,  ymm4",
            "vpxor ymm5,  ymm5,  ymm5",
            "vpxor ymm6,  ymm6,  ymm6",
            "vpxor ymm7,  ymm7,  ymm7",
            "vpxor ymm11, ymm11, ymm11",
            "vpxor ymm12, ymm12, ymm12",
            "vpxor ymm13, ymm13, ymm13",
            "vpxor ymm14, ymm14, ymm14",
            "vpxor ymm15, ymm15, ymm15",
            "vzeroupper",
            dst = inout(reg) dst => _,
            a = inout(reg) a => _,
            b = inout(reg) b => _,
            inout("rcx") blocks32 => _,
            tbl = in(reg) tbl_ptr,
            tmp = out(reg) _,
            out("ymm0") _, out("ymm1") _, out("ymm2") _, out("ymm3") _,
            out("ymm4") _, out("ymm5") _, out("ymm6") _, out("ymm7") _,
            out("ymm11") _, out("ymm12") _, out("ymm13") _, out("ymm14") _,
            out("ymm15") _,
            options(nostack),
        );
    }
}

/// 2x-unrolled (`64` bytes/iter, 4 independent `vpshufb` lookups per iter) constant-time
/// Shamir MAC `acc[i] ^= scalar * shares[i]` in Wiedemann $\mathcal{T}_3$ (`AVX2`).
/// Caller guarantees `blocks64 >= 1` and `caps.avx2`.
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn gf256_shamir_mac_4vpshufb_avx2_x2(
    acc: *mut u8,
    shares: *const u8,
    scalar: u32,
    blocks64: usize,
) {
    let tbl_ptr = (&raw const T3_VPSHUFB_CONSTS).cast::<u8>();
    // SAFETY: caller verified `caps.avx2` and `blocks64 * 64` valid bytes; scalar nibble tables
    // are synthesized purely in YMM registers and wiped prior to `ret`.
    unsafe {
        core::arch::asm!(
            "vmovdqa ymm13, ymmword ptr [{tbl} + 0]",
            "vmovdqa ymm14, ymmword ptr [{tbl} + 32]",
            "vmovdqa ymm15, ymmword ptr [{tbl} + 64]",
            "vmovdqa ymm1,  ymmword ptr [{tbl} + 96]",
            "mov {tmp:e}, 0x0f",
            "vmovd xmm11, {tmp:e}",
            "vpbroadcastb ymm11, xmm11",
            "mov {tmp:e}, 0x0e",
            "vmovd xmm12, {tmp:e}",
            "vpbroadcastb ymm12, xmm12",

            // Synthesize `[scalar * (0..15), scalar * ((0..15) << 4)]` in 26 instructions (0 memory LUTs!)
            "vmovd xmm0, {scalar:e}",
            "vpbroadcastb ymm0, xmm0",
            "vpand ymm2, ymm0, ymm11",
            "vpsrlw ymm3, ymm0, 4",
            "vpand ymm3, ymm3, ymm11",
            "vpxor ymm4, ymm2, ymm3",
            "vpand ymm5, ymm1, ymm11",
            "vpsrlw ymm6, ymm1, 4",
            "vpand ymm6, ymm6, ymm11",
            "vpxor ymm7, ymm5, ymm6",
            "vpshufb ymm2, ymm13, ymm2",
            "vpshufb ymm5, ymm13, ymm5",
            "vpshufb ymm3, ymm13, ymm3",
            "vpshufb ymm6, ymm13, ymm6",
            "vpshufb ymm4, ymm13, ymm4",
            "vpshufb ymm7, ymm13, ymm7",
            "vpaddusb ymm2, ymm2, ymm5",
            "vpaddusb ymm3, ymm3, ymm6",
            "vpaddusb ymm4, ymm4, ymm7",
            "vpcmpgtb ymm5, ymm2, ymm12",
            "vpcmpgtb ymm6, ymm3, ymm12",
            "vpcmpgtb ymm7, ymm4, ymm12",
            "vpand ymm5, ymm5, ymm11",
            "vpand ymm6, ymm6, ymm11",
            "vpand ymm7, ymm7, ymm11",
            "vpsubb ymm2, ymm2, ymm5",
            "vpsubb ymm3, ymm3, ymm6",
            "vpsubb ymm4, ymm4, ymm7",
            "vpshufb ymm2, ymm14, ymm2",
            "vpshufb ymm5, ymm14, ymm3",
            "vpshufb ymm6, ymm15, ymm3",
            "vpshufb ymm4, ymm14, ymm4",
            "vpxor ymm5, ymm5, ymm2",
            "vpxor ymm4, ymm4, ymm2",
            "vpxor ymm4, ymm4, ymm6",
            "vpsllw ymm4, ymm4, 4",
            "vpor ymm5, ymm5, ymm4",
            "vperm2i128 ymm8, ymm5, ymm5, 0x00",
            "vperm2i128 ymm9, ymm5, ymm5, 0x11",

            // Hot 4-vpshufb inner loop processing 64 bytes per iteration across dual shuffle pipes
            "2:",
            "vmovdqu ymm0, ymmword ptr [{shares} + 0]",
            "vmovdqu ymm4, ymmword ptr [{shares} + 32]",
            "vmovdqu ymm1, ymmword ptr [{acc} + 0]",
            "vmovdqu ymm5, ymmword ptr [{acc} + 32]",
            "vpand ymm2, ymm0, ymm11",
            "vpsrlw ymm3, ymm0, 4",
            "vpand ymm3, ymm3, ymm11",
            "vpand ymm6, ymm4, ymm11",
            "vpsrlw ymm7, ymm4, 4",
            "vpand ymm7, ymm7, ymm11",
            "vpshufb ymm2, ymm8, ymm2",
            "vpshufb ymm3, ymm9, ymm3",
            "vpshufb ymm6, ymm8, ymm6",
            "vpshufb ymm7, ymm9, ymm7",
            "vpxor ymm1, ymm1, ymm2",
            "vpxor ymm5, ymm5, ymm6",
            "vpxor ymm1, ymm1, ymm3",
            "vpxor ymm5, ymm5, ymm7",
            "vmovdqu ymmword ptr [{acc} + 0],  ymm1",
            "vmovdqu ymmword ptr [{acc} + 32], ymm5",
            "add {shares}, 64",
            "add {acc}, 64",
            "dec rcx",
            "jnz 2b",

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
            "vpxor ymm11, ymm11, ymm11",
            "vpxor ymm12, ymm12, ymm12",
            "vpxor ymm13, ymm13, ymm13",
            "vpxor ymm14, ymm14, ymm14",
            "vpxor ymm15, ymm15, ymm15",
            "vzeroupper",
            acc = inout(reg) acc => _,
            shares = inout(reg) shares => _,
            scalar = in(reg) scalar,
            inout("rcx") blocks64 => _,
            tbl = in(reg) tbl_ptr,
            tmp = out(reg) _,
            out("ymm0") _, out("ymm1") _, out("ymm2") _, out("ymm3") _,
            out("ymm4") _, out("ymm5") _, out("ymm6") _, out("ymm7") _,
            out("ymm8") _, out("ymm9") _, out("ymm11") _, out("ymm12") _,
            out("ymm13") _, out("ymm14") _, out("ymm15") _,
            options(nostack),
        );
    }
}

/// Single-block (`32` bytes/iter) constant-time Shamir MAC using 26-insn $\mathcal{T}_3$ table
/// synthesis (`AVX2`). Caller guarantees `blocks32 >= 1` and `caps.avx2`.
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn gf256_shamir_mac_vpshufb_avx2_x1(
    acc: *mut u8,
    shares: *const u8,
    scalar: u32,
    blocks32: usize,
) {
    let tbl_ptr = (&raw const T3_VPSHUFB_CONSTS).cast::<u8>();
    unsafe {
        core::arch::asm!(
            "vmovdqa ymm13, ymmword ptr [{tbl} + 0]",
            "vmovdqa ymm14, ymmword ptr [{tbl} + 32]",
            "vmovdqa ymm15, ymmword ptr [{tbl} + 64]",
            "vmovdqa ymm1,  ymmword ptr [{tbl} + 96]",
            "mov {tmp:e}, 0x0f",
            "vmovd xmm11, {tmp:e}",
            "vpbroadcastb ymm11, xmm11",
            "mov {tmp:e}, 0x0e",
            "vmovd xmm12, {tmp:e}",
            "vpbroadcastb ymm12, xmm12",

            "vmovd xmm0, {scalar:e}",
            "vpbroadcastb ymm0, xmm0",
            "vpand ymm2, ymm0, ymm11",
            "vpsrlw ymm3, ymm0, 4",
            "vpand ymm3, ymm3, ymm11",
            "vpxor ymm4, ymm2, ymm3",
            "vpand ymm5, ymm1, ymm11",
            "vpsrlw ymm6, ymm1, 4",
            "vpand ymm6, ymm6, ymm11",
            "vpxor ymm7, ymm5, ymm6",
            "vpshufb ymm2, ymm13, ymm2",
            "vpshufb ymm5, ymm13, ymm5",
            "vpshufb ymm3, ymm13, ymm3",
            "vpshufb ymm6, ymm13, ymm6",
            "vpshufb ymm4, ymm13, ymm4",
            "vpshufb ymm7, ymm13, ymm7",
            "vpaddusb ymm2, ymm2, ymm5",
            "vpaddusb ymm3, ymm3, ymm6",
            "vpaddusb ymm4, ymm4, ymm7",
            "vpcmpgtb ymm5, ymm2, ymm12",
            "vpcmpgtb ymm6, ymm3, ymm12",
            "vpcmpgtb ymm7, ymm4, ymm12",
            "vpand ymm5, ymm5, ymm11",
            "vpand ymm6, ymm6, ymm11",
            "vpand ymm7, ymm7, ymm11",
            "vpsubb ymm2, ymm2, ymm5",
            "vpsubb ymm3, ymm3, ymm6",
            "vpsubb ymm4, ymm4, ymm7",
            "vpshufb ymm2, ymm14, ymm2",
            "vpshufb ymm5, ymm14, ymm3",
            "vpshufb ymm6, ymm15, ymm3",
            "vpshufb ymm4, ymm14, ymm4",
            "vpxor ymm5, ymm5, ymm2",
            "vpxor ymm4, ymm4, ymm2",
            "vpxor ymm4, ymm4, ymm6",
            "vpsllw ymm4, ymm4, 4",
            "vpor ymm5, ymm5, ymm4",
            "vperm2i128 ymm8, ymm5, ymm5, 0x00",
            "vperm2i128 ymm9, ymm5, ymm5, 0x11",

            "2:",
            "vmovdqu ymm0, ymmword ptr [{shares}]",
            "vmovdqu ymm1, ymmword ptr [{acc}]",
            "vpand ymm2, ymm0, ymm11",
            "vpsrlw ymm3, ymm0, 4",
            "vpand ymm3, ymm3, ymm11",
            "vpshufb ymm2, ymm8, ymm2",
            "vpshufb ymm3, ymm9, ymm3",
            "vpxor ymm1, ymm1, ymm2",
            "vpxor ymm1, ymm1, ymm3",
            "vmovdqu ymmword ptr [{acc}], ymm1",
            "add {shares}, 32",
            "add {acc}, 32",
            "dec rcx",
            "jnz 2b",

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
            "vpxor ymm11, ymm11, ymm11",
            "vpxor ymm12, ymm12, ymm12",
            "vpxor ymm13, ymm13, ymm13",
            "vpxor ymm14, ymm14, ymm14",
            "vpxor ymm15, ymm15, ymm15",
            "vzeroupper",
            acc = inout(reg) acc => _,
            shares = inout(reg) shares => _,
            scalar = in(reg) scalar,
            inout("rcx") blocks32 => _,
            tbl = in(reg) tbl_ptr,
            tmp = out(reg) _,
            out("ymm0") _, out("ymm1") _, out("ymm2") _, out("ymm3") _,
            out("ymm4") _, out("ymm5") _, out("ymm6") _, out("ymm7") _,
            out("ymm8") _, out("ymm9") _, out("ymm11") _, out("ymm12") _,
            out("ymm13") _, out("ymm14") _, out("ymm15") _,
            options(nostack),
        );
    }
}
