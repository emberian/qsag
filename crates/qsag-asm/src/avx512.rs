//! 512-bit `AVX-512` (`F/DQ/BW/VL`) + `GFNI` + `VPCLMULQDQ` constant-time kernels:
//!
//! 1. **Zero-spill 8-way `Keccak-f[1600]` (`keccak_f1600_avx512_8x`):**
//!    Keeps all 25 `8 x u64` state lanes (`zmm0..zmm24`) and 7 round temporaries (`zmm25..zmm31`)
//!    resident in registers across all 24 rounds (`0` stack loads/stores), using `vpternlogq`
//!    (`0x96` 3-way XOR and `0xD2` Boolean `chi` `a ^ ((~b) & c)`) and hardware `vprolq`.
//! 2. **64-byte/iter `EVEX` `GFNI` `GF(256)` Shamir `mul` & `mac` (Wiedemann $\mathcal{T}_3$).**
//! 3. **64-byte/iter (`4 x 128`-bit) `EVEX` `VPCLMULQDQ` Karatsuba BDOZ MAC, batch dot product,
//!    and scale-XOR.**
//!
//! Every kernel uses public trip-count loops (`dec rcx; jnz`), `base + immediate` addressing,
//! zero variable shifts/dividers, and explicit `vxorps zmmN, zmmN, zmmN` + `vzeroupper` wipes
//! prior to `ret`.

use crate::portable::{
    GFNI_MAT_POLY_TO_T3, GFNI_MAT_T3_TO_POLY, KECCAK_ROUND_CONSTANTS, KeccakState8x,
};

/// Execute 24-round `Keccak-f[1600]` across 8 independent 1600-bit sponge states in `zmm0..zmm31`
/// with zero stack spills.
///
/// # Safety
/// Caller must verify runtime `AVX512F + AVX512VL` and OS `XCR0[7:5] == 0b111` (`caps.avx512`).
#[target_feature(enable = "avx512f,avx512vl")]
pub(crate) unsafe fn keccak_f1600_avx512_8x(state: &mut KeccakState8x) {
    let st_ptr = state.0.as_mut_ptr().cast::<u8>();
    let rc_ptr = KECCAK_ROUND_CONSTANTS.as_ptr();
    // SAFETY: `state` holds `25 * 64 = 1600` writable bytes, `KECCAK_ROUND_CONSTANTS` holds
    // `24 * 8 = 192` readable bytes, and all 32 ZMM registers are wiped + `vzeroupper` before exit.
    unsafe {
        core::arch::asm!(
            "vmovdqu64 zmm0,  zmmword ptr [{st} + 0]",
            "vmovdqu64 zmm1,  zmmword ptr [{st} + 64]",
            "vmovdqu64 zmm2,  zmmword ptr [{st} + 128]",
            "vmovdqu64 zmm3,  zmmword ptr [{st} + 192]",
            "vmovdqu64 zmm4,  zmmword ptr [{st} + 256]",
            "vmovdqu64 zmm5,  zmmword ptr [{st} + 320]",
            "vmovdqu64 zmm6,  zmmword ptr [{st} + 384]",
            "vmovdqu64 zmm7,  zmmword ptr [{st} + 448]",
            "vmovdqu64 zmm8,  zmmword ptr [{st} + 512]",
            "vmovdqu64 zmm9,  zmmword ptr [{st} + 576]",
            "vmovdqu64 zmm10, zmmword ptr [{st} + 640]",
            "vmovdqu64 zmm11, zmmword ptr [{st} + 704]",
            "vmovdqu64 zmm12, zmmword ptr [{st} + 768]",
            "vmovdqu64 zmm13, zmmword ptr [{st} + 832]",
            "vmovdqu64 zmm14, zmmword ptr [{st} + 896]",
            "vmovdqu64 zmm15, zmmword ptr [{st} + 960]",
            "vmovdqu64 zmm16, zmmword ptr [{st} + 1024]",
            "vmovdqu64 zmm17, zmmword ptr [{st} + 1088]",
            "vmovdqu64 zmm18, zmmword ptr [{st} + 1152]",
            "vmovdqu64 zmm19, zmmword ptr [{st} + 1216]",
            "vmovdqu64 zmm20, zmmword ptr [{st} + 1280]",
            "vmovdqu64 zmm21, zmmword ptr [{st} + 1344]",
            "vmovdqu64 zmm22, zmmword ptr [{st} + 1408]",
            "vmovdqu64 zmm23, zmmword ptr [{st} + 1472]",
            "vmovdqu64 zmm24, zmmword ptr [{st} + 1536]",

            "2:",
            // Theta column parities C[0..4] -> zmm25..zmm29 via 3-input vpternlogq (0x96 = A ^ B ^ C)
            "vmovdqa64 zmm25, zmm0",
            "vpternlogq zmm25, zmm5, zmm10, 0x96",
            "vpternlogq zmm25, zmm15, zmm20, 0x96",

            "vmovdqa64 zmm26, zmm1",
            "vpternlogq zmm26, zmm6, zmm11, 0x96",
            "vpternlogq zmm26, zmm16, zmm21, 0x96",

            "vmovdqa64 zmm27, zmm2",
            "vpternlogq zmm27, zmm7, zmm12, 0x96",
            "vpternlogq zmm27, zmm17, zmm22, 0x96",

            "vmovdqa64 zmm28, zmm3",
            "vpternlogq zmm28, zmm8, zmm13, 0x96",
            "vpternlogq zmm28, zmm18, zmm23, 0x96",

            "vmovdqa64 zmm29, zmm4",
            "vpternlogq zmm29, zmm9, zmm14, 0x96",
            "vpternlogq zmm29, zmm19, zmm24, 0x96",

            // Theta D[0..4] and column XOR updates
            "vprolq zmm30, zmm26, 1",
            "vpxorq zmm30, zmm30, zmm29",
            "vpxorq zmm0,  zmm0,  zmm30",
            "vpxorq zmm5,  zmm5,  zmm30",
            "vpxorq zmm10, zmm10, zmm30",
            "vpxorq zmm15, zmm15, zmm30",
            "vpxorq zmm20, zmm20, zmm30",

            "vprolq zmm31, zmm27, 1",
            "vpxorq zmm31, zmm31, zmm25",
            "vpxorq zmm1,  zmm1,  zmm31",
            "vpxorq zmm6,  zmm6,  zmm31",
            "vpxorq zmm11, zmm11, zmm31",
            "vpxorq zmm16, zmm16, zmm31",
            "vpxorq zmm21, zmm21, zmm31",

            "vprolq zmm30, zmm28, 1",
            "vpxorq zmm30, zmm30, zmm26",
            "vpxorq zmm2,  zmm2,  zmm30",
            "vpxorq zmm7,  zmm7,  zmm30",
            "vpxorq zmm12, zmm12, zmm30",
            "vpxorq zmm17, zmm17, zmm30",
            "vpxorq zmm22, zmm22, zmm30",

            "vprolq zmm31, zmm29, 1",
            "vpxorq zmm31, zmm31, zmm27",
            "vpxorq zmm3,  zmm3,  zmm31",
            "vpxorq zmm8,  zmm8,  zmm31",
            "vpxorq zmm13, zmm13, zmm31",
            "vpxorq zmm18, zmm18, zmm31",
            "vpxorq zmm23, zmm23, zmm31",

            "vprolq zmm30, zmm25, 1",
            "vpxorq zmm30, zmm30, zmm28",
            "vpxorq zmm4,  zmm4,  zmm30",
            "vpxorq zmm9,  zmm9,  zmm30",
            "vpxorq zmm14, zmm14, zmm30",
            "vpxorq zmm19, zmm19, zmm30",
            "vpxorq zmm24, zmm24, zmm30",

            // Rho + Pi in-place 24-cycle permutation via hardware 64-bit lane rotate `vprolq`
            "vprolq zmm25, zmm1,  1",
            "vprolq zmm1,  zmm6,  44",
            "vprolq zmm6,  zmm9,  20",
            "vprolq zmm9,  zmm22, 61",
            "vprolq zmm22, zmm14, 39",
            "vprolq zmm14, zmm20, 18",
            "vprolq zmm20, zmm2,  62",
            "vprolq zmm2,  zmm12, 43",
            "vprolq zmm12, zmm13, 25",
            "vprolq zmm13, zmm19, 8",
            "vprolq zmm19, zmm23, 56",
            "vprolq zmm23, zmm15, 41",
            "vprolq zmm15, zmm4,  27",
            "vprolq zmm4,  zmm24, 14",
            "vprolq zmm24, zmm21, 2",
            "vprolq zmm21, zmm8,  55",
            "vprolq zmm8,  zmm16, 45",
            "vprolq zmm16, zmm5,  36",
            "vprolq zmm5,  zmm3,  28",
            "vprolq zmm3,  zmm18, 21",
            "vprolq zmm18, zmm17, 15",
            "vprolq zmm17, zmm11, 10",
            "vprolq zmm11, zmm7,  6",
            "vprolq zmm7,  zmm10, 3",
            "vmovdqa64 zmm10, zmm25",

            // Chi row-by-row via single-instruction `vpternlogq dst, b, c, 0xD2` (`dst ^ ((~b) & c)`)
            // Row y = 0 (lanes 0..4)
            "vmovdqa64 zmm25, zmm0",
            "vmovdqa64 zmm26, zmm1",
            "vpternlogq zmm0, zmm1, zmm2, 0xd2",
            "vpternlogq zmm1, zmm2, zmm3, 0xd2",
            "vpternlogq zmm2, zmm3, zmm4, 0xd2",
            "vpternlogq zmm3, zmm4, zmm25, 0xd2",
            "vpternlogq zmm4, zmm25, zmm26, 0xd2",

            // Row y = 1 (lanes 5..9)
            "vmovdqa64 zmm25, zmm5",
            "vmovdqa64 zmm26, zmm6",
            "vpternlogq zmm5, zmm6, zmm7, 0xd2",
            "vpternlogq zmm6, zmm7, zmm8, 0xd2",
            "vpternlogq zmm7, zmm8, zmm9, 0xd2",
            "vpternlogq zmm8, zmm9, zmm25, 0xd2",
            "vpternlogq zmm9, zmm25, zmm26, 0xd2",

            // Row y = 2 (lanes 10..14)
            "vmovdqa64 zmm25, zmm10",
            "vmovdqa64 zmm26, zmm11",
            "vpternlogq zmm10, zmm11, zmm12, 0xd2",
            "vpternlogq zmm11, zmm12, zmm13, 0xd2",
            "vpternlogq zmm12, zmm13, zmm14, 0xd2",
            "vpternlogq zmm13, zmm14, zmm25, 0xd2",
            "vpternlogq zmm14, zmm25, zmm26, 0xd2",

            // Row y = 3 (lanes 15..19)
            "vmovdqa64 zmm25, zmm15",
            "vmovdqa64 zmm26, zmm16",
            "vpternlogq zmm15, zmm16, zmm17, 0xd2",
            "vpternlogq zmm16, zmm17, zmm18, 0xd2",
            "vpternlogq zmm17, zmm18, zmm19, 0xd2",
            "vpternlogq zmm18, zmm19, zmm25, 0xd2",
            "vpternlogq zmm19, zmm25, zmm26, 0xd2",

            // Row y = 4 (lanes 20..24)
            "vmovdqa64 zmm25, zmm20",
            "vmovdqa64 zmm26, zmm21",
            "vpternlogq zmm20, zmm21, zmm22, 0xd2",
            "vpternlogq zmm21, zmm22, zmm23, 0xd2",
            "vpternlogq zmm22, zmm23, zmm24, 0xd2",
            "vpternlogq zmm23, zmm24, zmm25, 0xd2",
            "vpternlogq zmm24, zmm25, zmm26, 0xd2",

            // Iota
            "vpbroadcastq zmm25, qword ptr [{rc}]",
            "vpxorq zmm0, zmm0, zmm25",
            "add {rc}, 8",
            "dec rcx",
            "jnz 2b",

            "vmovdqu64 zmmword ptr [{st} + 0],    zmm0",
            "vmovdqu64 zmmword ptr [{st} + 64],   zmm1",
            "vmovdqu64 zmmword ptr [{st} + 128],  zmm2",
            "vmovdqu64 zmmword ptr [{st} + 192],  zmm3",
            "vmovdqu64 zmmword ptr [{st} + 256],  zmm4",
            "vmovdqu64 zmmword ptr [{st} + 320],  zmm5",
            "vmovdqu64 zmmword ptr [{st} + 384],  zmm6",
            "vmovdqu64 zmmword ptr [{st} + 448],  zmm7",
            "vmovdqu64 zmmword ptr [{st} + 512],  zmm8",
            "vmovdqu64 zmmword ptr [{st} + 576],  zmm9",
            "vmovdqu64 zmmword ptr [{st} + 640],  zmm10",
            "vmovdqu64 zmmword ptr [{st} + 704],  zmm11",
            "vmovdqu64 zmmword ptr [{st} + 768],  zmm12",
            "vmovdqu64 zmmword ptr [{st} + 832],  zmm13",
            "vmovdqu64 zmmword ptr [{st} + 896],  zmm14",
            "vmovdqu64 zmmword ptr [{st} + 960],  zmm15",
            "vmovdqu64 zmmword ptr [{st} + 1024], zmm16",
            "vmovdqu64 zmmword ptr [{st} + 1088], zmm17",
            "vmovdqu64 zmmword ptr [{st} + 1152], zmm18",
            "vmovdqu64 zmmword ptr [{st} + 1216], zmm19",
            "vmovdqu64 zmmword ptr [{st} + 1280], zmm20",
            "vmovdqu64 zmmword ptr [{st} + 1344], zmm21",
            "vmovdqu64 zmmword ptr [{st} + 1408], zmm22",
            "vmovdqu64 zmmword ptr [{st} + 1472], zmm23",
            "vmovdqu64 zmmword ptr [{st} + 1536], zmm24",

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
            st = in(reg) st_ptr,
            rc = inout(reg) rc_ptr => _,
            inout("rcx") 24usize => _,
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

/// 64-byte/iter `AVX-512` + `GFNI` elementwise Shamir multiplication `dst[i] = a[i] * b[i]`
/// in Wiedemann $\mathcal{T}_3$. Caller guarantees `blocks64 >= 1`.
#[target_feature(enable = "avx512f,avx512bw,avx512vl,gfni")]
pub(crate) unsafe fn gf256_shamir_mul_avx512_gfni(
    dst: *mut u8,
    a: *const u8,
    b: *const u8,
    blocks64: usize,
) {
    // SAFETY: caller verified `caps.avx512 && caps.gfni` and `blocks64 * 64 <= len`.
    unsafe {
        core::arch::asm!(
            "vpbroadcastq zmm4, {mat_fwd}",
            "vpbroadcastq zmm5, {mat_inv}",
            "2:",
            "vmovdqu64 zmm0, zmmword ptr [{a}]",
            "vmovdqu64 zmm1, zmmword ptr [{b}]",
            "vgf2p8affineqb zmm0, zmm0, zmm4, 0",
            "vgf2p8affineqb zmm1, zmm1, zmm4, 0",
            "vgf2p8mulb zmm0, zmm0, zmm1",
            "vgf2p8affineqb zmm0, zmm0, zmm5, 0",
            "vmovdqu64 zmmword ptr [{dst}], zmm0",
            "add {a}, 64",
            "add {b}, 64",
            "add {dst}, 64",
            "dec rcx",
            "jnz 2b",
            "vxorps zmm0, zmm0, zmm0",
            "vxorps zmm1, zmm1, zmm1",
            "vxorps zmm4, zmm4, zmm4",
            "vxorps zmm5, zmm5, zmm5",
            "vzeroupper",
            dst = inout(reg) dst => _,
            a = inout(reg) a => _,
            b = inout(reg) b => _,
            inout("rcx") blocks64 => _,
            mat_fwd = in(reg) GFNI_MAT_T3_TO_POLY,
            mat_inv = in(reg) GFNI_MAT_POLY_TO_T3,
            out("zmm0") _, out("zmm1") _, out("zmm4") _, out("zmm5") _,
            options(nostack),
        );
    }
}

/// 64-byte/iter `AVX-512` + `GFNI` Shamir multiply-accumulate `acc[i] ^= scalar * shares[i]`
/// in Wiedemann $\mathcal{T}_3$. Caller guarantees `blocks64 >= 1`.
#[target_feature(enable = "avx512f,avx512bw,avx512vl,gfni")]
pub(crate) unsafe fn gf256_shamir_mac_avx512_gfni(
    acc: *mut u8,
    shares: *const u8,
    scalar: u32,
    blocks64: usize,
) {
    // SAFETY: caller verified `caps.avx512 && caps.gfni` and `blocks64 * 64 <= len`.
    unsafe {
        core::arch::asm!(
            "vpbroadcastq zmm4, {mat_fwd}",
            "vpbroadcastq zmm5, {mat_inv}",
            "vpbroadcastb zmm2, {scalar:e}",
            "vgf2p8affineqb zmm2, zmm2, zmm4, 0",
            "2:",
            "vmovdqu64 zmm0, zmmword ptr [{shares}]",
            "vmovdqu64 zmm1, zmmword ptr [{acc}]",
            "vgf2p8affineqb zmm0, zmm0, zmm4, 0",
            "vgf2p8mulb zmm0, zmm0, zmm2",
            "vgf2p8affineqb zmm0, zmm0, zmm5, 0",
            "vpxorq zmm1, zmm1, zmm0",
            "vmovdqu64 zmmword ptr [{acc}], zmm1",
            "add {shares}, 64",
            "add {acc}, 64",
            "dec rcx",
            "jnz 2b",
            "vxorps zmm0, zmm0, zmm0",
            "vxorps zmm1, zmm1, zmm1",
            "vxorps zmm2, zmm2, zmm2",
            "vxorps zmm4, zmm4, zmm4",
            "vxorps zmm5, zmm5, zmm5",
            "vzeroupper",
            acc = inout(reg) acc => _,
            shares = inout(reg) shares => _,
            scalar = in(reg) scalar,
            inout("rcx") blocks64 => _,
            mat_fwd = in(reg) GFNI_MAT_T3_TO_POLY,
            mat_inv = in(reg) GFNI_MAT_POLY_TO_T3,
            out("zmm0") _, out("zmm1") _, out("zmm2") _, out("zmm4") _, out("zmm5") _,
            options(nostack),
        );
    }
}

/// 512-bit `VPCLMULQDQ` 2-lane BDOZ MAC inner product processing 2 pairs (`4 x 128`-bit = 64 B)
/// per iteration and XOR-accumulating into `[out32 + 0..32]`. Caller guarantees `blocks64 >= 1`.
#[target_feature(enable = "avx512f,avx512dq,avx512vl,vpclmulqdq")]
pub(crate) unsafe fn tower128_bdoz_mac_avx512_evex(
    out32: *mut u8,
    lhs64: *const u8,
    rhs64: *const u8,
    blocks64: usize,
) {
    // SAFETY: caller verified `caps.avx512 && caps.vpclmulqdq`, `blocks64 * 64` readable bytes in
    // `lhs64`/`rhs64`, and `32` readable/writable bytes in `out32`.
    unsafe {
        core::arch::asm!(
            "vxorps zmm0, zmm0, zmm0",
            "vxorps zmm1, zmm1, zmm1",
            "vxorps zmm2, zmm2, zmm2",
            "2:",
            "vmovdqu64 zmm3, zmmword ptr [{lhs}]",
            "vmovdqu64 zmm4, zmmword ptr [{rhs}]",
            "vpclmulqdq zmm5, zmm3, zmm4, 0x00",
            "vpclmulqdq zmm6, zmm3, zmm4, 0x11",
            "vpshufd zmm7, zmm3, 0x4e",
            "vpxorq zmm7, zmm7, zmm3",
            "vpshufd zmm8, zmm4, 0x4e",
            "vpxorq zmm8, zmm8, zmm4",
            "vpclmulqdq zmm7, zmm7, zmm8, 0x00",
            "vpxorq zmm0, zmm0, zmm5",
            "vpxorq zmm1, zmm1, zmm6",
            "vpxorq zmm2, zmm2, zmm7",
            "add {lhs}, 64",
            "add {rhs}, 64",
            "dec rcx",
            "jnz 2b",

            // Fold high 256-bit pair (pair 1) into low 256-bit pair (pair 0)
            "vextracti64x4 ymm3, zmm0, 1",
            "vpxor ymm0, ymm0, ymm3",
            "vextracti64x4 ymm4, zmm1, 1",
            "vpxor ymm1, ymm1, ymm4",
            "vextracti64x4 ymm5, zmm2, 1",
            "vpxor ymm2, ymm2, ymm5",

            // Karatsuba middle combine + single 2-lane 0x87 reduction in YMM
            "vpxor ymm2, ymm2, ymm0",
            "vpxor ymm2, ymm2, ymm1",
            "vpslldq ymm3, ymm2, 8",
            "vpsrldq ymm2, ymm2, 8",
            "vpxor ymm0, ymm0, ymm3",
            "vpxor ymm1, ymm1, ymm2",
            "mov {poly:e}, 0x87",
            "vmovq xmm6, {poly}",
            "vpbroadcastq ymm6, xmm6",
            "vpclmulqdq ymm3, ymm1, ymm6, 0x01",
            "vpslldq ymm4, ymm3, 8",
            "vpsrldq ymm5, ymm3, 8",
            "vpxor ymm0, ymm0, ymm4",
            "vpxor ymm1, ymm1, ymm5",
            "vpclmulqdq ymm3, ymm1, ymm6, 0x00",
            "vpxor ymm0, ymm0, ymm3",
            "vpxor ymm0, ymm0, ymmword ptr [{out32}]",
            "vmovdqu ymmword ptr [{out32}], ymm0",

            "vxorps zmm0, zmm0, zmm0",
            "vxorps zmm1, zmm1, zmm1",
            "vxorps zmm2, zmm2, zmm2",
            "vxorps zmm3, zmm3, zmm3",
            "vxorps zmm4, zmm4, zmm4",
            "vxorps zmm5, zmm5, zmm5",
            "vxorps zmm6, zmm6, zmm6",
            "vxorps zmm7, zmm7, zmm7",
            "vxorps zmm8, zmm8, zmm8",
            "vzeroupper",
            out32 = in(reg) out32,
            lhs = inout(reg) lhs64 => _,
            rhs = inout(reg) rhs64 => _,
            inout("rcx") blocks64 => _,
            poly = out(reg) _,
            out("zmm0") _, out("zmm1") _, out("zmm2") _, out("zmm3") _,
            out("zmm4") _, out("zmm5") _, out("zmm6") _, out("zmm7") _,
            out("zmm8") _,
            options(nostack),
        );
    }
}

/// 512-bit `VPCLMULQDQ` batched `GF(2^128)` multiply-accumulate (`4 x 128`-bit = 64 B per iter)
/// XORing the reduced sum into `[acc16]`. Caller guarantees `quads >= 1`.
#[target_feature(enable = "avx512f,avx512dq,avx512vl,vpclmulqdq")]
pub(crate) unsafe fn gf2_128_mul_acc_avx512_evex(
    acc16: *mut u8,
    a64: *const u8,
    b64: *const u8,
    quads: usize,
) {
    // SAFETY: caller verified `caps.avx512 && caps.vpclmulqdq` and `quads * 64` readable bytes.
    unsafe {
        core::arch::asm!(
            "vxorps zmm0, zmm0, zmm0",
            "vxorps zmm1, zmm1, zmm1",
            "vxorps zmm2, zmm2, zmm2",
            "2:",
            "vmovdqu64 zmm3, zmmword ptr [{a}]",
            "vmovdqu64 zmm4, zmmword ptr [{b}]",
            "vpclmulqdq zmm5, zmm3, zmm4, 0x00",
            "vpclmulqdq zmm6, zmm3, zmm4, 0x11",
            "vpshufd zmm7, zmm3, 0x4e",
            "vpxorq zmm7, zmm7, zmm3",
            "vpshufd zmm8, zmm4, 0x4e",
            "vpxorq zmm8, zmm8, zmm4",
            "vpclmulqdq zmm7, zmm7, zmm8, 0x00",
            "vpxorq zmm0, zmm0, zmm5",
            "vpxorq zmm1, zmm1, zmm6",
            "vpxorq zmm2, zmm2, zmm7",
            "add {a}, 64",
            "add {b}, 64",
            "dec rcx",
            "jnz 2b",

            // Fold 512 -> 256 -> 128 bits prior to a single `0x87` reduction
            "vextracti64x4 ymm3, zmm0, 1",
            "vpxor ymm0, ymm0, ymm3",
            "vextracti64x4 ymm4, zmm1, 1",
            "vpxor ymm1, ymm1, ymm4",
            "vextracti64x4 ymm5, zmm2, 1",
            "vpxor ymm2, ymm2, ymm5",

            "vextracti128 xmm3, ymm0, 1",
            "vpxor xmm0, xmm0, xmm3",
            "vextracti128 xmm4, ymm1, 1",
            "vpxor xmm1, xmm1, xmm4",
            "vextracti128 xmm5, ymm2, 1",
            "vpxor xmm2, xmm2, xmm5",

            "vpxor xmm2, xmm2, xmm0",
            "vpxor xmm2, xmm2, xmm1",
            "vpslldq xmm3, xmm2, 8",
            "vpsrldq xmm2, xmm2, 8",
            "vpxor xmm0, xmm0, xmm3",
            "vpxor xmm1, xmm1, xmm2",
            "mov {poly:e}, 0x87",
            "vmovq xmm6, {poly}",
            "vpclmulqdq xmm3, xmm1, xmm6, 0x01",
            "vpslldq xmm4, xmm3, 8",
            "vpsrldq xmm5, xmm3, 8",
            "vpxor xmm0, xmm0, xmm4",
            "vpxor xmm1, xmm1, xmm5",
            "vpclmulqdq xmm3, xmm1, xmm6, 0x00",
            "vpxor xmm0, xmm0, xmm3",
            "vpxor xmm0, xmm0, xmmword ptr [{acc}]",
            "vmovdqu xmmword ptr [{acc}], xmm0",

            "vxorps zmm0, zmm0, zmm0",
            "vxorps zmm1, zmm1, zmm1",
            "vxorps zmm2, zmm2, zmm2",
            "vxorps zmm3, zmm3, zmm3",
            "vxorps zmm4, zmm4, zmm4",
            "vxorps zmm5, zmm5, zmm5",
            "vxorps zmm6, zmm6, zmm6",
            "vxorps zmm7, zmm7, zmm7",
            "vxorps zmm8, zmm8, zmm8",
            "vzeroupper",
            acc = in(reg) acc16,
            a = inout(reg) a64 => _,
            b = inout(reg) b64 => _,
            inout("rcx") quads => _,
            poly = out(reg) _,
            out("zmm0") _, out("zmm1") _, out("zmm2") _, out("zmm3") _,
            out("zmm4") _, out("zmm5") _, out("zmm6") _, out("zmm7") _,
            out("zmm8") _,
            options(nostack),
        );
    }
}

/// 512-bit `VPCLMULQDQ` elementwise scale-XOR `dst[i] ^= src[i] * scalar` in
/// `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)` (`4 x 128`-bit = 64 B per iter).
/// Caller guarantees `quads >= 1`. The 512-bit `vpslldq`/`vpsrldq` byte shifts are `AVX512BW`.
#[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vl,vpclmulqdq")]
pub(crate) unsafe fn poly_scale_xor_avx512_evex(
    dst64: *mut u8,
    src64: *const u8,
    scalar_lo: u64,
    scalar_hi: u64,
    quads: usize,
) {
    // SAFETY: caller verified `caps.avx512 && caps.vpclmulqdq` and `quads * 64` valid bytes.
    unsafe {
        core::arch::asm!(
            "vmovq xmm5, {slo}",
            "vpinsrq xmm5, xmm5, {shi}, 1",
            "vshufi64x2 zmm5, zmm5, zmm5, 0x00",
            "vpshufd zmm9, zmm5, 0x4e",
            "vpxorq zmm9, zmm9, zmm5",
            "mov {poly:e}, 0x87",
            "vpbroadcastq zmm10, {poly}",
            "2:",
            "vmovdqu64 zmm4, zmmword ptr [{src}]",
            "vpclmulqdq zmm0, zmm4, zmm5, 0x00",
            "vpclmulqdq zmm1, zmm4, zmm5, 0x11",
            "vpshufd zmm8, zmm4, 0x4e",
            "vpxorq zmm8, zmm8, zmm4",
            "vpclmulqdq zmm2, zmm8, zmm9, 0x00",
            "vpxorq zmm2, zmm2, zmm0",
            "vpxorq zmm2, zmm2, zmm1",
            "vpslldq zmm3, zmm2, 8",
            "vpsrldq zmm2, zmm2, 8",
            "vpxorq zmm0, zmm0, zmm3",
            "vpxorq zmm1, zmm1, zmm2",
            "vpclmulqdq zmm6, zmm1, zmm10, 0x01",
            "vpslldq zmm7, zmm6, 8",
            "vpsrldq zmm8, zmm6, 8",
            "vpxorq zmm0, zmm0, zmm7",
            "vpxorq zmm1, zmm1, zmm8",
            "vpclmulqdq zmm6, zmm1, zmm10, 0x00",
            "vpxorq zmm0, zmm0, zmm6",
            "vpxorq zmm0, zmm0, zmmword ptr [{dst}]",
            "vmovdqu64 zmmword ptr [{dst}], zmm0",
            "add {src}, 64",
            "add {dst}, 64",
            "dec rcx",
            "jnz 2b",
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
            "vzeroupper",
            dst = inout(reg) dst64 => _,
            src = inout(reg) src64 => _,
            slo = in(reg) scalar_lo,
            shi = in(reg) scalar_hi,
            inout("rcx") quads => _,
            poly = out(reg) _,
            out("zmm0") _, out("zmm1") _, out("zmm2") _, out("zmm3") _,
            out("zmm4") _, out("zmm5") _, out("zmm6") _, out("zmm7") _,
            out("zmm8") _, out("zmm9") _, out("zmm10") _,
            options(nostack),
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::cpuid::SimdBackend;
    use crate::portable::{self, KeccakState4x};

    const X86_BACKENDS: [SimdBackend; 4] = [
        SimdBackend::Portable,
        SimdBackend::X86Avx2Pclmul,
        SimdBackend::X86Avx2GfniVpclmul,
        SimdBackend::X86Avx512GfniVpclmul,
    ];

    fn stream(seed: u64) -> impl FnMut() -> u64 {
        let mut s = seed;
        move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        }
    }

    /// Every pair count crosses the 16-pair packing chunk and the odd-pair 256-bit tail.
    #[test]
    fn bdoz_mac_matches_portable_at_every_length_and_chunk_boundary() {
        let mut next = stream(0xBD02_0512);
        let mut word = || u128::from(next()) | (u128::from(next()) << 64);
        let lhs: [[u128; 2]; 50] = core::array::from_fn(|i| match i {
            0 => [u128::MAX, u128::MAX],
            1 => [1u128 << 127, 1],
            _ => [word(), word()],
        });
        let rhs: [[u128; 2]; 50] = core::array::from_fn(|i| match i {
            0 => [u128::MAX, u128::MAX],
            _ => [word(), word()],
        });
        for len in 0..=50 {
            let poly = portable::tower128_bdoz_2lane_poly_mac_portable(&lhs[..len], &rhs[..len]);
            let t7 = portable::tower128_bdoz_2lane_mac_portable(&lhs[..len], &rhs[..len]);
            for backend in X86_BACKENDS {
                let (l, r) = (&lhs[..len], &rhs[..len]);
                let got = crate::tower128_bdoz_2lane_poly_mac_with_backend(l, r, backend);
                assert_eq!(got, poly, "poly len={len} {backend:?}");
                let got = crate::tower128_bdoz_2lane_mac_with_backend(l, r, backend);
                assert_eq!(got, t7, "t7 len={len} {backend:?}");
            }
        }
    }

    /// Batches of `1..=19` states on every explicit backend, including the zero-padded
    /// 8-way block for `5..=7` trailing states.
    #[test]
    fn keccak_batch_matches_single_state_portable_on_every_backend_and_length() {
        let mut next = stream(0x1600_8888);
        let input: [[u64; 25]; 19] = core::array::from_fn(|_| core::array::from_fn(|_| next()));
        let expected: [[u64; 25]; 19] = core::array::from_fn(|i| {
            let mut one = KeccakState4x(core::array::from_fn(|j| [input[i][j]; 4]));
            portable::keccak_f1600_4x_portable(&mut one);
            core::array::from_fn(|j| one.0[j][0])
        });
        for backend in X86_BACKENDS {
            for len in 0..=19 {
                let mut states = input;
                crate::keccak_f1600_batch_with_backend(&mut states[..len], backend);
                assert_eq!(&states[..len], &expected[..len], "len={len} {backend:?}");
                assert_eq!(&states[len..], &input[len..], "tail touched len={len} {backend:?}");
            }
        }
    }
}
