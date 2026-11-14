//! Hand-crafted, zero-secret-branch `x86_64` SIMD & scalar assembly kernels (`AVX2`, `GFNI`,
//! `VPCLMULQDQ`, `PCLMULQDQ`, `BMI2`/`ADX`).
//!
//! ### ABI & Microarchitectural Side-Channel Invariants
//! 1. **Zero Secret Branches:** Every exported `qsag_asm_*` function contains zero data-dependent
//!    conditional jumps; the only control-flow edges are bottom-tested `dec` + `jnz` loops over
//!    public buffer lengths / fixed protocol round counts (`24` for `Keccak-f[1600]`).
//! 2. **Zero Secret Memory Indexing:** All loads/stores address sequential caller buffers or
//!    fixed-offset stack slots; LUTs (`vpshufb`) live strictly in `ymm` vector registers.
//! 3. **Zero Variable-Latency Dividers:** Zero `div`/`idiv` instructions anywhere.
//! 4. **Register & Stack Zeroization + `vzeroupper`:** Every `AVX2` kernel explicitly zeroes all
//!    secret-bearing `ymm` registers (and stack scratch frames in `Keccak-f[1600]`) and executes
//!    `vzeroupper` before `ret`, preserving System V AMD64 callee-saved registers.

use core::arch::global_asm;

use crate::portable::{
    GFNI_MAT_POLY_TO_T3, GFNI_MAT_T3_TO_POLY, KECCAK_ROUND_CONSTANTS, KeccakRow256, KeccakState4x,
    sim_gf2p8affineqb,
};

/// 32-byte aligned precomputed nibble tables (duplicated across both 128-bit lanes of each `ymm`
/// slot) for `AVX2` `vpshufb` Wiedemann $\mathcal{T}_3 \leftrightarrow \text{GFNI(0x11B)}$ conversion.
#[repr(C, align(32))]
pub struct Avx2Gf256IsoLuts {
    pub t3_to_poly_lo: [u8; 32],
    pub t3_to_poly_hi: [u8; 32],
    pub poly_to_t3_lo: [u8; 32],
    pub poly_to_t3_hi: [u8; 32],
    pub basis_nibbles_32: [u8; 32],
}

pub static AVX2_GF256_ISO_LUTS: Avx2Gf256IsoLuts = {
    let mut t3_to_poly_lo = [0u8; 32];
    let mut t3_to_poly_hi = [0u8; 32];
    let mut poly_to_t3_lo = [0u8; 32];
    let mut poly_to_t3_hi = [0u8; 32];
    let mut basis_nibbles_32 = [0u8; 32];
    let mut nib = 0usize;
    while nib < 16 {
        let f_lo = sim_gf2p8affineqb(nib as u8, GFNI_MAT_T3_TO_POLY, 0);
        let f_hi = sim_gf2p8affineqb((nib << 4) as u8, GFNI_MAT_T3_TO_POLY, 0);
        let i_lo = sim_gf2p8affineqb(nib as u8, GFNI_MAT_POLY_TO_T3, 0);
        let i_hi = sim_gf2p8affineqb((nib << 4) as u8, GFNI_MAT_POLY_TO_T3, 0);
        t3_to_poly_lo[nib] = f_lo;
        t3_to_poly_lo[nib + 16] = f_lo;
        t3_to_poly_hi[nib] = f_hi;
        t3_to_poly_hi[nib + 16] = f_hi;
        poly_to_t3_lo[nib] = i_lo;
        poly_to_t3_lo[nib + 16] = i_lo;
        poly_to_t3_hi[nib] = i_hi;
        poly_to_t3_hi[nib + 16] = i_hi;
        basis_nibbles_32[nib] = nib as u8;
        basis_nibbles_32[nib + 16] = (nib << 4) as u8;
        nib += 1;
    }
    Avx2Gf256IsoLuts {
        t3_to_poly_lo,
        t3_to_poly_hi,
        poly_to_t3_lo,
        poly_to_t3_hi,
        basis_nibbles_32,
    }
};

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
    // =========================================================================
    // 1. qsag_asm_keccak_f1600_avx2_4x(state: *mut [[u64;4];25], rcs: *const u64)
    //    256-way parallel bitsliced / 4-sponge AVX2 24-round Keccak-f[1600]
    // =========================================================================
    sym_header!("qsag_asm_keccak_f1600_avx2_4x"),
    "push rbp",
    "mov rbp, rsp",
    "and rsp, -32",
    "sub rsp, 832",
    "mov ecx, 24",
    "2:",
    // Theta C[0..4] -> ymm0..ymm4
    "vmovdqu ymm0, ymmword ptr [rdi + 0]",
    "vpxor ymm0, ymm0, ymmword ptr [rdi + 160]",
    "vpxor ymm0, ymm0, ymmword ptr [rdi + 320]",
    "vpxor ymm0, ymm0, ymmword ptr [rdi + 480]",
    "vpxor ymm0, ymm0, ymmword ptr [rdi + 640]",

    "vmovdqu ymm1, ymmword ptr [rdi + 32]",
    "vpxor ymm1, ymm1, ymmword ptr [rdi + 192]",
    "vpxor ymm1, ymm1, ymmword ptr [rdi + 352]",
    "vpxor ymm1, ymm1, ymmword ptr [rdi + 512]",
    "vpxor ymm1, ymm1, ymmword ptr [rdi + 672]",

    "vmovdqu ymm2, ymmword ptr [rdi + 64]",
    "vpxor ymm2, ymm2, ymmword ptr [rdi + 224]",
    "vpxor ymm2, ymm2, ymmword ptr [rdi + 384]",
    "vpxor ymm2, ymm2, ymmword ptr [rdi + 544]",
    "vpxor ymm2, ymm2, ymmword ptr [rdi + 704]",

    "vmovdqu ymm3, ymmword ptr [rdi + 96]",
    "vpxor ymm3, ymm3, ymmword ptr [rdi + 256]",
    "vpxor ymm3, ymm3, ymmword ptr [rdi + 416]",
    "vpxor ymm3, ymm3, ymmword ptr [rdi + 576]",
    "vpxor ymm3, ymm3, ymmword ptr [rdi + 736]",

    "vmovdqu ymm4, ymmword ptr [rdi + 128]",
    "vpxor ymm4, ymm4, ymmword ptr [rdi + 288]",
    "vpxor ymm4, ymm4, ymmword ptr [rdi + 448]",
    "vpxor ymm4, ymm4, ymmword ptr [rdi + 608]",
    "vpxor ymm4, ymm4, ymmword ptr [rdi + 768]",

    // Theta D[0..4] -> ymm5..ymm9
    "vpsllq ymm10, ymm1, 1",
    "vpsrlq ymm11, ymm1, 63",
    "vpor ymm10, ymm10, ymm11",
    "vpxor ymm5, ymm4, ymm10",

    "vpsllq ymm10, ymm2, 1",
    "vpsrlq ymm11, ymm2, 63",
    "vpor ymm10, ymm10, ymm11",
    "vpxor ymm6, ymm0, ymm10",

    "vpsllq ymm10, ymm3, 1",
    "vpsrlq ymm11, ymm3, 63",
    "vpor ymm10, ymm10, ymm11",
    "vpxor ymm7, ymm1, ymm10",

    "vpsllq ymm10, ymm4, 1",
    "vpsrlq ymm11, ymm4, 63",
    "vpor ymm10, ymm10, ymm11",
    "vpxor ymm8, ymm2, ymm10",

    "vpsllq ymm10, ymm0, 1",
    "vpsrlq ymm11, ymm0, 63",
    "vpor ymm10, ymm10, ymm11",
    "vpxor ymm9, ymm3, ymm10",

    // Theta XOR + Rho + Pi -> [rsp + 32*target]
    // src=0 (x=0 -> dst=0, rot=0)
    "vpxor ymm0, ymm5, ymmword ptr [rdi + 0]",
    "vmovdqa ymmword ptr [rsp + 0], ymm0",
    // src=1 (x=1 -> dst=10, rot=1)
    "vpxor ymm0, ymm6, ymmword ptr [rdi + 32]",
    "vpsllq ymm1, ymm0, 1",
    "vpsrlq ymm2, ymm0, 63",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 320], ymm0",
    // src=2 (x=2 -> dst=20, rot=62)
    "vpxor ymm0, ymm7, ymmword ptr [rdi + 64]",
    "vpsllq ymm1, ymm0, 62",
    "vpsrlq ymm2, ymm0, 2",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 640], ymm0",
    // src=3 (x=3 -> dst=5, rot=28)
    "vpxor ymm0, ymm8, ymmword ptr [rdi + 96]",
    "vpsllq ymm1, ymm0, 28",
    "vpsrlq ymm2, ymm0, 36",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 160], ymm0",
    // src=4 (x=4 -> dst=15, rot=27)
    "vpxor ymm0, ymm9, ymmword ptr [rdi + 128]",
    "vpsllq ymm1, ymm0, 27",
    "vpsrlq ymm2, ymm0, 37",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 480], ymm0",
    // src=5 (x=0 -> dst=16, rot=36)
    "vpxor ymm0, ymm5, ymmword ptr [rdi + 160]",
    "vpsllq ymm1, ymm0, 36",
    "vpsrlq ymm2, ymm0, 28",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 512], ymm0",
    // src=6 (x=1 -> dst=1, rot=44)
    "vpxor ymm0, ymm6, ymmword ptr [rdi + 192]",
    "vpsllq ymm1, ymm0, 44",
    "vpsrlq ymm2, ymm0, 20",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 32], ymm0",
    // src=7 (x=2 -> dst=11, rot=6)
    "vpxor ymm0, ymm7, ymmword ptr [rdi + 224]",
    "vpsllq ymm1, ymm0, 6",
    "vpsrlq ymm2, ymm0, 58",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 352], ymm0",
    // src=8 (x=3 -> dst=21, rot=55)
    "vpxor ymm0, ymm8, ymmword ptr [rdi + 256]",
    "vpsllq ymm1, ymm0, 55",
    "vpsrlq ymm2, ymm0, 9",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 672], ymm0",
    // src=9 (x=4 -> dst=6, rot=20)
    "vpxor ymm0, ymm9, ymmword ptr [rdi + 288]",
    "vpsllq ymm1, ymm0, 20",
    "vpsrlq ymm2, ymm0, 44",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 192], ymm0",
    // src=10 (x=0 -> dst=7, rot=3)
    "vpxor ymm0, ymm5, ymmword ptr [rdi + 320]",
    "vpsllq ymm1, ymm0, 3",
    "vpsrlq ymm2, ymm0, 61",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 224], ymm0",
    // src=11 (x=1 -> dst=17, rot=10)
    "vpxor ymm0, ymm6, ymmword ptr [rdi + 352]",
    "vpsllq ymm1, ymm0, 10",
    "vpsrlq ymm2, ymm0, 54",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 544], ymm0",
    // src=12 (x=2 -> dst=2, rot=43)
    "vpxor ymm0, ymm7, ymmword ptr [rdi + 384]",
    "vpsllq ymm1, ymm0, 43",
    "vpsrlq ymm2, ymm0, 21",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 64], ymm0",
    // src=13 (x=3 -> dst=12, rot=25)
    "vpxor ymm0, ymm8, ymmword ptr [rdi + 416]",
    "vpsllq ymm1, ymm0, 25",
    "vpsrlq ymm2, ymm0, 39",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 384], ymm0",
    // src=14 (x=4 -> dst=22, rot=39)
    "vpxor ymm0, ymm9, ymmword ptr [rdi + 448]",
    "vpsllq ymm1, ymm0, 39",
    "vpsrlq ymm2, ymm0, 25",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 704], ymm0",
    // src=15 (x=0 -> dst=23, rot=41)
    "vpxor ymm0, ymm5, ymmword ptr [rdi + 480]",
    "vpsllq ymm1, ymm0, 41",
    "vpsrlq ymm2, ymm0, 23",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 736], ymm0",
    // src=16 (x=1 -> dst=8, rot=45)
    "vpxor ymm0, ymm6, ymmword ptr [rdi + 512]",
    "vpsllq ymm1, ymm0, 45",
    "vpsrlq ymm2, ymm0, 19",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 256], ymm0",
    // src=17 (x=2 -> dst=18, rot=15)
    "vpxor ymm0, ymm7, ymmword ptr [rdi + 544]",
    "vpsllq ymm1, ymm0, 15",
    "vpsrlq ymm2, ymm0, 49",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 576], ymm0",
    // src=18 (x=3 -> dst=3, rot=21)
    "vpxor ymm0, ymm8, ymmword ptr [rdi + 576]",
    "vpsllq ymm1, ymm0, 21",
    "vpsrlq ymm2, ymm0, 43",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 96], ymm0",
    // src=19 (x=4 -> dst=13, rot=8)
    "vpxor ymm0, ymm9, ymmword ptr [rdi + 608]",
    "vpsllq ymm1, ymm0, 8",
    "vpsrlq ymm2, ymm0, 56",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 416], ymm0",
    // src=20 (x=0 -> dst=14, rot=18)
    "vpxor ymm0, ymm5, ymmword ptr [rdi + 640]",
    "vpsllq ymm1, ymm0, 18",
    "vpsrlq ymm2, ymm0, 46",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 448], ymm0",
    // src=21 (x=1 -> dst=24, rot=2)
    "vpxor ymm0, ymm6, ymmword ptr [rdi + 672]",
    "vpsllq ymm1, ymm0, 2",
    "vpsrlq ymm2, ymm0, 62",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 768], ymm0",
    // src=22 (x=2 -> dst=9, rot=61)
    "vpxor ymm0, ymm7, ymmword ptr [rdi + 704]",
    "vpsllq ymm1, ymm0, 61",
    "vpsrlq ymm2, ymm0, 3",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 288], ymm0",
    // src=23 (x=3 -> dst=19, rot=56)
    "vpxor ymm0, ymm8, ymmword ptr [rdi + 736]",
    "vpsllq ymm1, ymm0, 56",
    "vpsrlq ymm2, ymm0, 8",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 608], ymm0",
    // src=24 (x=4 -> dst=4, rot=14)
    "vpxor ymm0, ymm9, ymmword ptr [rdi + 768]",
    "vpsllq ymm1, ymm0, 14",
    "vpsrlq ymm2, ymm0, 50",
    "vpor ymm0, ymm1, ymm2",
    "vmovdqa ymmword ptr [rsp + 128], ymm0",

    // Chi + Iota row 0 (offsets 0..128)
    "vmovdqa ymm0, ymmword ptr [rsp + 0]",
    "vmovdqa ymm1, ymmword ptr [rsp + 32]",
    "vmovdqa ymm2, ymmword ptr [rsp + 64]",
    "vmovdqa ymm3, ymmword ptr [rsp + 96]",
    "vmovdqa ymm4, ymmword ptr [rsp + 128]",
    "vpandn ymm5, ymm1, ymm2",
    "vpxor ymm5, ymm0, ymm5",
    "vpbroadcastq ymm10, qword ptr [rsi]",
    "vpxor ymm5, ymm5, ymm10",
    "vmovdqu ymmword ptr [rdi + 0], ymm5",
    "vpandn ymm6, ymm2, ymm3",
    "vpxor ymm6, ymm1, ymm6",
    "vmovdqu ymmword ptr [rdi + 32], ymm6",
    "vpandn ymm7, ymm3, ymm4",
    "vpxor ymm7, ymm2, ymm7",
    "vmovdqu ymmword ptr [rdi + 64], ymm7",
    "vpandn ymm8, ymm4, ymm0",
    "vpxor ymm8, ymm3, ymm8",
    "vmovdqu ymmword ptr [rdi + 96], ymm8",
    "vpandn ymm9, ymm0, ymm1",
    "vpxor ymm9, ymm4, ymm9",
    "vmovdqu ymmword ptr [rdi + 128], ymm9",

    // Chi row 1 (offsets 160..288)
    "vmovdqa ymm0, ymmword ptr [rsp + 160]",
    "vmovdqa ymm1, ymmword ptr [rsp + 192]",
    "vmovdqa ymm2, ymmword ptr [rsp + 224]",
    "vmovdqa ymm3, ymmword ptr [rsp + 256]",
    "vmovdqa ymm4, ymmword ptr [rsp + 288]",
    "vpandn ymm5, ymm1, ymm2",
    "vpxor ymm5, ymm0, ymm5",
    "vmovdqu ymmword ptr [rdi + 160], ymm5",
    "vpandn ymm6, ymm2, ymm3",
    "vpxor ymm6, ymm1, ymm6",
    "vmovdqu ymmword ptr [rdi + 192], ymm6",
    "vpandn ymm7, ymm3, ymm4",
    "vpxor ymm7, ymm2, ymm7",
    "vmovdqu ymmword ptr [rdi + 224], ymm7",
    "vpandn ymm8, ymm4, ymm0",
    "vpxor ymm8, ymm3, ymm8",
    "vmovdqu ymmword ptr [rdi + 256], ymm8",
    "vpandn ymm9, ymm0, ymm1",
    "vpxor ymm9, ymm4, ymm9",
    "vmovdqu ymmword ptr [rdi + 288], ymm9",

    // Chi row 2 (offsets 320..448)
    "vmovdqa ymm0, ymmword ptr [rsp + 320]",
    "vmovdqa ymm1, ymmword ptr [rsp + 352]",
    "vmovdqa ymm2, ymmword ptr [rsp + 384]",
    "vmovdqa ymm3, ymmword ptr [rsp + 416]",
    "vmovdqa ymm4, ymmword ptr [rsp + 448]",
    "vpandn ymm5, ymm1, ymm2",
    "vpxor ymm5, ymm0, ymm5",
    "vmovdqu ymmword ptr [rdi + 320], ymm5",
    "vpandn ymm6, ymm2, ymm3",
    "vpxor ymm6, ymm1, ymm6",
    "vmovdqu ymmword ptr [rdi + 352], ymm6",
    "vpandn ymm7, ymm3, ymm4",
    "vpxor ymm7, ymm2, ymm7",
    "vmovdqu ymmword ptr [rdi + 384], ymm7",
    "vpandn ymm8, ymm4, ymm0",
    "vpxor ymm8, ymm3, ymm8",
    "vmovdqu ymmword ptr [rdi + 416], ymm8",
    "vpandn ymm9, ymm0, ymm1",
    "vpxor ymm9, ymm4, ymm9",
    "vmovdqu ymmword ptr [rdi + 448], ymm9",

    // Chi row 3 (offsets 480..608)
    "vmovdqa ymm0, ymmword ptr [rsp + 480]",
    "vmovdqa ymm1, ymmword ptr [rsp + 512]",
    "vmovdqa ymm2, ymmword ptr [rsp + 544]",
    "vmovdqa ymm3, ymmword ptr [rsp + 576]",
    "vmovdqa ymm4, ymmword ptr [rsp + 608]",
    "vpandn ymm5, ymm1, ymm2",
    "vpxor ymm5, ymm0, ymm5",
    "vmovdqu ymmword ptr [rdi + 480], ymm5",
    "vpandn ymm6, ymm2, ymm3",
    "vpxor ymm6, ymm1, ymm6",
    "vmovdqu ymmword ptr [rdi + 512], ymm6",
    "vpandn ymm7, ymm3, ymm4",
    "vpxor ymm7, ymm2, ymm7",
    "vmovdqu ymmword ptr [rdi + 544], ymm7",
    "vpandn ymm8, ymm4, ymm0",
    "vpxor ymm8, ymm3, ymm8",
    "vmovdqu ymmword ptr [rdi + 576], ymm8",
    "vpandn ymm9, ymm0, ymm1",
    "vpxor ymm9, ymm4, ymm9",
    "vmovdqu ymmword ptr [rdi + 608], ymm9",

    // Chi row 4 (offsets 640..768)
    "vmovdqa ymm0, ymmword ptr [rsp + 640]",
    "vmovdqa ymm1, ymmword ptr [rsp + 672]",
    "vmovdqa ymm2, ymmword ptr [rsp + 704]",
    "vmovdqa ymm3, ymmword ptr [rsp + 736]",
    "vmovdqa ymm4, ymmword ptr [rsp + 768]",
    "vpandn ymm5, ymm1, ymm2",
    "vpxor ymm5, ymm0, ymm5",
    "vmovdqu ymmword ptr [rdi + 640], ymm5",
    "vpandn ymm6, ymm2, ymm3",
    "vpxor ymm6, ymm1, ymm6",
    "vmovdqu ymmword ptr [rdi + 672], ymm6",
    "vpandn ymm7, ymm3, ymm4",
    "vpxor ymm7, ymm2, ymm7",
    "vmovdqu ymmword ptr [rdi + 704], ymm7",
    "vpandn ymm8, ymm4, ymm0",
    "vpxor ymm8, ymm3, ymm8",
    "vmovdqu ymmword ptr [rdi + 736], ymm8",
    "vpandn ymm9, ymm0, ymm1",
    "vpxor ymm9, ymm4, ymm9",
    "vmovdqu ymmword ptr [rdi + 768], ymm9",

    "add rsi, 8",
    "dec ecx",
    "jnz 2b",

    // Zeroize 800-byte stack scratch frame & all YMM registers before exit!
    "vpxor ymm0, ymm0, ymm0",
    "mov ecx, 25",
    "mov rax, rsp",
    "3:",
    "vmovdqa ymmword ptr [rax], ymm0",
    "add rax, 32",
    "dec ecx",
    "jnz 3b",
    "vpxor ymm1, ymm1, ymm1",
    "vpxor ymm2, ymm2, ymm2",
    "vpxor ymm3, ymm3, ymm3",
    "vpxor ymm4, ymm4, ymm4",
    "vpxor ymm5, ymm5, ymm5",
    "vpxor ymm6, ymm6, ymm6",
    "vpxor ymm7, ymm7, ymm7",
    "vpxor ymm8, ymm8, ymm8",
    "vpxor ymm9, ymm9, ymm9",
    "vpxor ymm10, ymm10, ymm10",
    "vpxor ymm11, ymm11, ymm11",
    "vzeroall",
    "vzeroupper",
    "mov rsp, rbp",
    "pop rbp",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "xor eax, eax",
    "ret",
    sym_footer!("qsag_asm_keccak_f1600_avx2_4x"),

    // =========================================================================
    // 2. qsag_asm_keccak_chi_mpc_avx2(out, s0, s1, r_mask)
    //    Straight-line 256-way bitsliced 3-party RSS MPC Chi row (ZERO branches!)
    // =========================================================================
    sym_header!("qsag_asm_keccak_chi_mpc_avx2"),
    "vmovdqu ymm0, ymmword ptr [rsi + 0]",
    "vmovdqu ymm1, ymmword ptr [rsi + 32]",
    "vmovdqu ymm2, ymmword ptr [rsi + 64]",
    "vmovdqu ymm3, ymmword ptr [rsi + 96]",
    "vmovdqu ymm4, ymmword ptr [rsi + 128]",
    "vmovdqu ymm5, ymmword ptr [rdx + 0]",
    "vmovdqu ymm6, ymmword ptr [rdx + 32]",
    "vmovdqu ymm7, ymmword ptr [rdx + 64]",
    "vmovdqu ymm8, ymmword ptr [rdx + 96]",
    "vmovdqu ymm9, ymmword ptr [rdx + 128]",

    // Lane x = 0 (x1 = 1, x2 = 2)
    "vpxor ymm10, ymm2, ymm7",
    "vpand ymm10, ymm1, ymm10",
    "vpand ymm11, ymm6, ymm2",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm11, ymm0, ymm2",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm10, ymm10, ymmword ptr [rcx + 0]",
    "vmovdqu ymmword ptr [rdi + 0], ymm10",

    // Lane x = 1 (x1 = 2, x2 = 3)
    "vpxor ymm10, ymm3, ymm8",
    "vpand ymm10, ymm2, ymm10",
    "vpand ymm11, ymm7, ymm3",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm11, ymm1, ymm3",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm10, ymm10, ymmword ptr [rcx + 32]",
    "vmovdqu ymmword ptr [rdi + 32], ymm10",

    // Lane x = 2 (x1 = 3, x2 = 4)
    "vpxor ymm10, ymm4, ymm9",
    "vpand ymm10, ymm3, ymm10",
    "vpand ymm11, ymm8, ymm4",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm11, ymm2, ymm4",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm10, ymm10, ymmword ptr [rcx + 64]",
    "vmovdqu ymmword ptr [rdi + 64], ymm10",

    // Lane x = 3 (x1 = 4, x2 = 0)
    "vpxor ymm10, ymm0, ymm5",
    "vpand ymm10, ymm4, ymm10",
    "vpand ymm11, ymm9, ymm0",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm11, ymm3, ymm0",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm10, ymm10, ymmword ptr [rcx + 96]",
    "vmovdqu ymmword ptr [rdi + 96], ymm10",

    // Lane x = 4 (x1 = 0, x2 = 1)
    "vpxor ymm10, ymm1, ymm6",
    "vpand ymm10, ymm0, ymm10",
    "vpand ymm11, ymm5, ymm1",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm11, ymm4, ymm1",
    "vpxor ymm10, ymm10, ymm11",
    "vpxor ymm10, ymm10, ymmword ptr [rcx + 128]",
    "vmovdqu ymmword ptr [rdi + 128], ymm10",

    // Wipe secret share registers & upper YMM state
    "vpxor ymm0, ymm0, ymm0",
    "vpxor ymm1, ymm1, ymm1",
    "vpxor ymm2, ymm2, ymm2",
    "vpxor ymm3, ymm3, ymm3",
    "vpxor ymm4, ymm4, ymm4",
    "vpxor ymm5, ymm5, ymm5",
    "vpxor ymm6, ymm6, ymm6",
    "vpxor ymm7, ymm7, ymm7",
    "vpxor ymm8, ymm8, ymm8",
    "vpxor ymm9, ymm9, ymm9",
    "vpxor ymm10, ymm10, ymm10",
    "vpxor ymm11, ymm11, ymm11",
    "vzeroall",
    "vzeroupper",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "xor eax, eax",
    "ret",
    sym_footer!("qsag_asm_keccak_chi_mpc_avx2"),

    // =========================================================================
    // 3. qsag_asm_gf256_shamir_mul_gfni(dst: *mut u8, a: *const u8, b: *const u8, blocks32: usize)
    //    32-way GFNI Shamir Wiedemann T_3 multiplication via vgf2p8affineqb + vgf2p8mulb
    //    Caller guarantees `blocks32 >= 1`.
    // =========================================================================
    sym_header!("qsag_asm_gf256_shamir_mul_gfni"),
    "mov rax, 0x71500a8a86be78ce",
    "vmovq xmm14, rax",
    "vpbroadcastq ymm14, xmm14",
    "mov rax, 0xa1e4f8e072a2700c",
    "vmovq xmm15, rax",
    "vpbroadcastq ymm15, xmm15",
    "2:",
    "vmovdqu ymm0, ymmword ptr [rsi]",
    "vmovdqu ymm1, ymmword ptr [rdx]",
    "vgf2p8affineqb ymm0, ymm0, ymm14, 0",
    "vgf2p8affineqb ymm1, ymm1, ymm14, 0",
    "vgf2p8mulb ymm2, ymm0, ymm1",
    "vgf2p8affineqb ymm2, ymm2, ymm15, 0",
    "vmovdqu ymmword ptr [rdi], ymm2",
    "add rsi, 32",
    "add rdx, 32",
    "add rdi, 32",
    "dec rcx",
    "jnz 2b",
    "vpxor ymm0, ymm0, ymm0",
    "vpxor ymm1, ymm1, ymm1",
    "vpxor ymm2, ymm2, ymm2",
    "vpxor ymm14, ymm14, ymm14",
    "vpxor ymm15, ymm15, ymm15",
    "vzeroall",
    "vzeroupper",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "xor eax, eax",
    "ret",
    sym_footer!("qsag_asm_gf256_shamir_mul_gfni"),

    // =========================================================================
    // 4. qsag_asm_gf256_shamir_mac_gfni(acc: *mut u8, shares: *const u8, scalar: u8, blocks32: usize)
    //    32-way GFNI Shamir Wiedemann T_3 multiply-accumulate `acc[i] ^= scalar * shares[i]`
    //    Caller guarantees `blocks32 >= 1`.
    // =========================================================================
    sym_header!("qsag_asm_gf256_shamir_mac_gfni"),
    "mov rax, 0x71500a8a86be78ce",
    "vmovq xmm14, rax",
    "vpbroadcastq ymm14, xmm14",
    "mov rax, 0xa1e4f8e072a2700c",
    "vmovq xmm15, rax",
    "vpbroadcastq ymm15, xmm15",
    "vmovd xmm3, edx",
    "vpbroadcastb ymm3, xmm3",
    "vgf2p8affineqb ymm3, ymm3, ymm14, 0",
    "2:",
    "vmovdqu ymm0, ymmword ptr [rsi]",
    "vmovdqu ymm1, ymmword ptr [rdi]",
    "vgf2p8affineqb ymm0, ymm0, ymm14, 0",
    "vgf2p8mulb ymm2, ymm0, ymm3",
    "vgf2p8affineqb ymm2, ymm2, ymm15, 0",
    "vpxor ymm1, ymm1, ymm2",
    "vmovdqu ymmword ptr [rdi], ymm1",
    "add rsi, 32",
    "add rdi, 32",
    "dec rcx",
    "jnz 2b",
    "vpxor ymm0, ymm0, ymm0",
    "vpxor ymm1, ymm1, ymm1",
    "vpxor ymm2, ymm2, ymm2",
    "vpxor ymm3, ymm3, ymm3",
    "vpxor ymm14, ymm14, ymm14",
    "vpxor ymm15, ymm15, ymm15",
    "xor eax, eax",
    "xor edx, edx",
    "vzeroall",
    "vzeroupper",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "xor eax, eax",
    "ret",
    sym_footer!("qsag_asm_gf256_shamir_mac_gfni"),

    // =========================================================================
    // 5. qsag_asm_gf256_shamir_mul_avx2(dst, a, b, blocks32, luts_ptr /* r8 */)
    //    32-way pure-AVX2 fallback (for AMD EPYC-Milan (Zen 3) without GFNI!)
    //    Register-resident nibble basis conversion + 8-step branchless Russian-peasant mul.
    // =========================================================================
    sym_header!("qsag_asm_gf256_shamir_mul_avx2"),
    "vmovdqa ymm12, ymmword ptr [r8 + 0]",
    "vmovdqa ymm13, ymmword ptr [r8 + 32]",
    "vmovdqa ymm14, ymmword ptr [r8 + 64]",
    "vmovdqa ymm15, ymmword ptr [r8 + 96]",
    "mov eax, 0x0f",
    "vmovd xmm10, eax",
    "vpbroadcastb ymm10, xmm10",
    "mov eax, 0x1b",
    "vmovd xmm11, eax",
    "vpbroadcastb ymm11, xmm11",
    "vpxor ymm9, ymm9, ymm9",
    "2:",
    "vmovdqu ymm0, ymmword ptr [rsi]",
    "vmovdqu ymm1, ymmword ptr [rdx]",
    // Map a (ymm0): T_3 -> Poly(0x11B)
    "vpand ymm3, ymm0, ymm10",
    "vpsrlw ymm4, ymm0, 4",
    "vpand ymm4, ymm4, ymm10",
    "vpshufb ymm3, ymm12, ymm3",
    "vpshufb ymm4, ymm13, ymm4",
    "vpxor ymm0, ymm3, ymm4",
    // Map b (ymm1): T_3 -> Poly(0x11B)
    "vpand ymm3, ymm1, ymm10",
    "vpsrlw ymm4, ymm1, 4",
    "vpand ymm4, ymm4, ymm10",
    "vpshufb ymm3, ymm12, ymm3",
    "vpshufb ymm4, ymm13, ymm4",
    "vpxor ymm1, ymm3, ymm4",

    // Step k = 7 (MSB of b): acc = a & (b_bit7 ? 0xFF : 0x00)
    "vpcmpgtb ymm2, ymm9, ymm1",
    "vpand ymm2, ymm0, ymm2",
    "vpaddb ymm1, ymm1, ymm1",
    // Step k = 6
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    // Step k = 5
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    // Step k = 4
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    // Step k = 3
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    // Step k = 2
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    // Step k = 1
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    // Step k = 0
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",

    // Map acc (ymm2): Poly(0x11B) -> T_3
    "vpand ymm3, ymm2, ymm10",
    "vpsrlw ymm4, ymm2, 4",
    "vpand ymm4, ymm4, ymm10",
    "vpshufb ymm3, ymm14, ymm3",
    "vpshufb ymm4, ymm15, ymm4",
    "vpxor ymm2, ymm3, ymm4",
    "vmovdqu ymmword ptr [rdi], ymm2",

    "add rsi, 32",
    "add rdx, 32",
