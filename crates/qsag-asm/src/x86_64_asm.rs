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
    "add rdi, 32",
    "dec rcx",
    "jnz 2b",
    "vpxor ymm0, ymm0, ymm0",
    "vpxor ymm1, ymm1, ymm1",
    "vpxor ymm2, ymm2, ymm2",
    "vpxor ymm3, ymm3, ymm3",
    "vpxor ymm4, ymm4, ymm4",
    "vpxor ymm5, ymm5, ymm5",
    "vpxor ymm6, ymm6, ymm6",
    "vpxor ymm10, ymm10, ymm10",
    "vpxor ymm11, ymm11, ymm11",
    "vpxor ymm12, ymm12, ymm12",
    "vpxor ymm13, ymm13, ymm13",
    "vpxor ymm14, ymm14, ymm14",
    "vpxor ymm15, ymm15, ymm15",
    "xor eax, eax",
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
    sym_footer!("qsag_asm_gf256_shamir_mul_avx2"),
    // =========================================================================
    // 5b. qsag_asm_gf256_shamir_mac_avx2(acc, shares, scalar, blocks32, luts_ptr /* r8 */)
    //     Constant-time register-synthesized nibble LUT Shamir MAC on AVX2!
    // =========================================================================
    sym_header!("qsag_asm_gf256_shamir_mac_avx2"),
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
    // Synthesize [scalar *_{T_3} (0..15), scalar *_{T_3} (0,16..240)] in registers (0 memory LUTs!)
    "vmovd xmm0, edx",
    "vpbroadcastb ymm0, xmm0",
    "vmovdqa ymm1, ymmword ptr [r8 + 128]",
    // Map scalar (ymm0) and basis_nibbles (ymm1): T_3 -> Poly(0x11B)
    "vpand ymm3, ymm0, ymm10",
    "vpsrlw ymm4, ymm0, 4",
    "vpand ymm4, ymm4, ymm10",
    "vpshufb ymm3, ymm12, ymm3",
    "vpshufb ymm4, ymm13, ymm4",
    "vpxor ymm0, ymm3, ymm4",
    "vpand ymm3, ymm1, ymm10",
    "vpsrlw ymm4, ymm1, 4",
    "vpand ymm4, ymm4, ymm10",
    "vpshufb ymm3, ymm12, ymm3",
    "vpshufb ymm4, ymm13, ymm4",
    "vpxor ymm1, ymm3, ymm4",
    // 8-step branchless Russian-peasant mul in Poly(0x11B)
    "vpcmpgtb ymm2, ymm9, ymm1",
    "vpand ymm2, ymm0, ymm2",
    "vpaddb ymm1, ymm1, ymm1",
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    "vpaddb ymm1, ymm1, ymm1",
    "vpcmpgtb ymm5, ymm9, ymm2",
    "vpaddb ymm2, ymm2, ymm2",
    "vpand ymm5, ymm5, ymm11",
    "vpxor ymm2, ymm2, ymm5",
    "vpcmpgtb ymm6, ymm9, ymm1",
    "vpand ymm6, ymm0, ymm6",
    "vpxor ymm2, ymm2, ymm6",
    // Map Poly(0x11B) -> T_3 and broadcast lane0 -> ymm7 (lo LUT), lane1 -> ymm8 (hi LUT)
    "vpand ymm3, ymm2, ymm10",
    "vpsrlw ymm4, ymm2, 4",
    "vpand ymm4, ymm4, ymm10",
    "vpshufb ymm3, ymm14, ymm3",
    "vpshufb ymm4, ymm15, ymm4",
    "vpxor ymm2, ymm3, ymm4",
    "vperm2i128 ymm7, ymm2, ymm2, 0x00",
    "vperm2i128 ymm8, ymm2, ymm2, 0x11",
    // Hot inner loop: 10 AVX2 instructions per 32 Shamir multiplies!
    "2:",
    "vmovdqu ymm0, ymmword ptr [rsi]",
    "vmovdqu ymm1, ymmword ptr [rdi]",
    "vpand ymm2, ymm0, ymm10",
    "vpsrlw ymm3, ymm0, 4",
    "vpand ymm3, ymm3, ymm10",
    "vpshufb ymm2, ymm7, ymm2",
    "vpshufb ymm3, ymm8, ymm3",
    "vpxor ymm1, ymm1, ymm2",
    "vpxor ymm1, ymm1, ymm3",
    "vmovdqu ymmword ptr [rdi], ymm1",
    "add rsi, 32",
    "add rdi, 32",
    "dec rcx",
    "jnz 2b",
    "vpxor ymm0, ymm0, ymm0",
    "vpxor ymm1, ymm1, ymm1",
    "vpxor ymm2, ymm2, ymm2",
    "vpxor ymm3, ymm3, ymm3",
    "vpxor ymm4, ymm4, ymm4",
    "vpxor ymm5, ymm5, ymm5",
    "vpxor ymm6, ymm6, ymm6",
    "vpxor ymm7, ymm7, ymm7",
    "vpxor ymm8, ymm8, ymm8",
    "vpxor ymm10, ymm10, ymm10",
    "vpxor ymm11, ymm11, ymm11",
    "vpxor ymm12, ymm12, ymm12",
    "vpxor ymm13, ymm13, ymm13",
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
    sym_footer!("qsag_asm_gf256_shamir_mac_avx2"),
    // =========================================================================
    // 6. qsag_asm_tower128_bdoz_mac_vpclmul(out32: *mut u8, lhs32: *const u8, rhs32: *const u8, count: usize)
    //    2-lane simultaneous 128-bit BDOZ MAC inner product via 256-bit VPCLMULQDQ + 0x87 reduction!
    //    Caller guarantees `count >= 1`.
    // =========================================================================
    sym_header!("qsag_asm_tower128_bdoz_mac_vpclmul"),
    "vpxor ymm0, ymm0, ymm0", // accumulated lo128 across both 128-bit lanes
    "vpxor ymm1, ymm1, ymm1", // accumulated hi128 across both 128-bit lanes
    "2:",
    "vmovdqu ymm2, ymmword ptr [rsi]",
    "vmovdqu ymm3, ymmword ptr [rdx]",
    "vpclmulqdq ymm4, ymm2, ymm3, 0x00", // a0 * b0
    "vpclmulqdq ymm5, ymm2, ymm3, 0x11", // a1 * b1
    "vpclmulqdq ymm6, ymm2, ymm3, 0x01", // a1 * b0
    "vpclmulqdq ymm7, ymm2, ymm3, 0x10", // a0 * b1
    "vpxor ymm6, ymm6, ymm7",            // mid = a1*b0 ^ a0*b1
    "vpslldq ymm7, ymm6, 8",             // mid << 64 per 128b lane
    "vpsrldq ymm6, ymm6, 8",             // mid >> 64 per 128b lane
    "vpxor ymm4, ymm4, ymm7",            // prod_lo
    "vpxor ymm5, ymm5, ymm6",            // prod_hi
    "vpxor ymm0, ymm0, ymm4",
    "vpxor ymm1, ymm1, ymm5",
    "add rsi, 32",
    "add rdx, 32",
    "dec rcx",
    "jnz 2b",
    // Final 2-step reduction modulo z^128 + z^7 + z^2 + z + 1 (0x87) in BOTH 128-bit lanes!
    "mov eax, 0x87",
    "vmovq xmm8, rax",
    "vpbroadcastq ymm8, xmm8",
    "vpclmulqdq ymm4, ymm1, ymm8, 0x01", // T = C3 * 0x87
    "vpslldq ymm5, ymm4, 8",
    "vpsrldq ymm6, ymm4, 8",
    "vpxor ymm0, ymm0, ymm5",            // C1' = C1 ^ T_lo
    "vpxor ymm1, ymm1, ymm6",            // C2' = C2 ^ T_hi
    "vpclmulqdq ymm4, ymm1, ymm8, 0x00", // U = C2' * 0x87
    "vpxor ymm0, ymm0, ymm4",            // canonical 128-bit remainder in both lanes!
    "vmovdqu ymmword ptr [rdi], ymm0",
    "vpxor ymm0, ymm0, ymm0",
    "vpxor ymm1, ymm1, ymm1",
    "vpxor ymm2, ymm2, ymm2",
    "vpxor ymm3, ymm3, ymm3",
    "vpxor ymm4, ymm4, ymm4",
    "vpxor ymm5, ymm5, ymm5",
    "vpxor ymm6, ymm6, ymm6",
    "vpxor ymm7, ymm7, ymm7",
    "vpxor ymm8, ymm8, ymm8",
    "xor eax, eax",
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
    sym_footer!("qsag_asm_tower128_bdoz_mac_vpclmul"),
    // =========================================================================
    // 7. qsag_asm_tower128_bdoz_mac_pclmul(out32: *mut u8, lhs32: *const u8, rhs32: *const u8, count: usize)
    //    128-bit PCLMULQDQ fallback (for AMD EPYC-Milan (Zen 3) without VPCLMULQDQ!)
    //    Caller guarantees `count >= 1`.
    // =========================================================================
    sym_header!("qsag_asm_tower128_bdoz_mac_pclmul"),
    "vpxor xmm0, xmm0, xmm0", // lane0 lo128
    "vpxor xmm1, xmm1, xmm1", // lane0 hi128
    "vpxor xmm2, xmm2, xmm2", // lane1 lo128
    "vpxor xmm3, xmm3, xmm3", // lane1 hi128
    "2:",
    // Lane 0 (offset 0)
    "vmovdqu xmm4, xmmword ptr [rsi + 0]",
    "vmovdqu xmm5, xmmword ptr [rdx + 0]",
    "vpclmulqdq xmm6, xmm4, xmm5, 0x00",
    "vpclmulqdq xmm7, xmm4, xmm5, 0x11",
    "vpclmulqdq xmm8, xmm4, xmm5, 0x01",
    "vpclmulqdq xmm9, xmm4, xmm5, 0x10",
    "vpxor xmm8, xmm8, xmm9",
    "vpslldq xmm9, xmm8, 8",
    "vpsrldq xmm8, xmm8, 8",
    "vpxor xmm6, xmm6, xmm9",
    "vpxor xmm7, xmm7, xmm8",
    "vpxor xmm0, xmm0, xmm6",
    "vpxor xmm1, xmm1, xmm7",
    // Lane 1 (offset 16)
    "vmovdqu xmm4, xmmword ptr [rsi + 16]",
    "vmovdqu xmm5, xmmword ptr [rdx + 16]",
    "vpclmulqdq xmm6, xmm4, xmm5, 0x00",
    "vpclmulqdq xmm7, xmm4, xmm5, 0x11",
    "vpclmulqdq xmm8, xmm4, xmm5, 0x01",
    "vpclmulqdq xmm9, xmm4, xmm5, 0x10",
    "vpxor xmm8, xmm8, xmm9",
    "vpslldq xmm9, xmm8, 8",
    "vpsrldq xmm8, xmm8, 8",
    "vpxor xmm6, xmm6, xmm9",
    "vpxor xmm7, xmm7, xmm8",
    "vpxor xmm2, xmm2, xmm6",
    "vpxor xmm3, xmm3, xmm7",
    "add rsi, 32",
    "add rdx, 32",
    "dec rcx",
    "jnz 2b",
    "mov eax, 0x87",
    "vmovq xmm10, rax",
    // Reduce Lane 0
    "vpclmulqdq xmm6, xmm1, xmm10, 0x01",
    "vpslldq xmm7, xmm6, 8",
    "vpsrldq xmm8, xmm6, 8",
    "vpxor xmm0, xmm0, xmm7",
    "vpxor xmm1, xmm1, xmm8",
    "vpclmulqdq xmm6, xmm1, xmm10, 0x00",
    "vpxor xmm0, xmm0, xmm6",
    "vmovdqu xmmword ptr [rdi + 0], xmm0",
    // Reduce Lane 1
    "vpclmulqdq xmm6, xmm3, xmm10, 0x01",
    "vpslldq xmm7, xmm6, 8",
    "vpsrldq xmm8, xmm6, 8",
    "vpxor xmm2, xmm2, xmm7",
    "vpxor xmm3, xmm3, xmm8",
    "vpclmulqdq xmm6, xmm3, xmm10, 0x00",
    "vpxor xmm2, xmm2, xmm6",
    "vmovdqu xmmword ptr [rdi + 16], xmm2",
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
    sym_footer!("qsag_asm_tower128_bdoz_mac_pclmul"),
    // =========================================================================
    // 8. qsag_asm_goldilocks_mul_ct_x86_64(a: u64, b: u64) -> u64
    //    Zero-branch BMI2 `mulx` + `sbb` canonical Goldilocks multiplication
    //    Exact over ALL (a, b) in [0, 2^64 - 1]^2!
    // =========================================================================
    sym_header!("qsag_asm_goldilocks_mul_ct_x86_64"),
    "mov rdx, rdi",
    "mulx rcx, rax, rsi",
    "mov rdx, rcx",
    "shr rcx, 32",
    "mov edx, edx",
    "sub rax, rcx",
    "sbb r8d, r8d",
    "sub rax, r8",
    "mov r9, rdx",
    "shl r9, 32",
    "sub r9, rdx",
    "add rax, r9",
    "sbb r8d, r8d",
    "add rax, r8",
    "mov r9d, 0xffffffff",
    "mov r8, rax",
    "add r8, r9",
    "sbb rcx, rcx",
    "and rcx, r9",
    "add rax, rcx",
    "xor ecx, ecx",
    "xor edx, edx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "ret",
    sym_footer!("qsag_asm_goldilocks_mul_ct_x86_64"),
    // =========================================================================
    // 9. qsag_asm_goldilocks_add_ct_x86_64(a: u64, b: u64) -> u64
    //    Zero-branch Goldilocks addition exact over ALL (a, b) in [0, 2^64 - 1]^2!
    // =========================================================================
    sym_header!("qsag_asm_goldilocks_add_ct_x86_64"),
    "mov rax, rdi",
    "add rax, rsi",
    "sbb r8d, r8d",
    "add rax, r8",
    "sbb r10d, r10d",
    "add rax, r10",
    "mov r9d, 0xffffffff",
    "mov r8, rax",
    "add r8, r9",
    "sbb rcx, rcx",
    "and rcx, r9",
    "add rax, rcx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "ret",
    sym_footer!("qsag_asm_goldilocks_add_ct_x86_64"),
    // =========================================================================
    // 10. qsag_asm_goldilocks_sub_ct_x86_64(a: u64, b: u64) -> u64
    //     Zero-branch Goldilocks subtraction exact over ALL (a, b) in [0, 2^64 - 1]^2!
    // =========================================================================
    sym_header!("qsag_asm_goldilocks_sub_ct_x86_64"),
    "mov r9d, 0xffffffff",
    // Canonicalize a -> rax
    "mov rax, rdi",
    "mov r8, rax",
    "add r8, r9",
    "sbb rcx, rcx",
    "and rcx, r9",
    "add rax, rcx",
    // Canonicalize b -> rsi
    "mov r8, rsi",
    "add r8, r9",
    "sbb rcx, rcx",
    "and rcx, r9",
    "add rsi, rcx",
    // Subtract ac - bc + (borrow ? p : 0)
    "sub rax, rsi",
    "sbb r8, r8",
    "mov r10, 0xffffffff00000001",
    "and r8, r10",
    "add rax, r8",
    "xor ecx, ecx",
    "xor esi, esi",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "ret",
    sym_footer!("qsag_asm_goldilocks_sub_ct_x86_64"),
    // =========================================================================
    // 11. qsag_asm_goldilocks_pow7_ct_x86_64(x: u64) -> u64
    //     Zero-branch Poseidon2 x^7 mod p S-box (x -> x^2 -> x^3 -> x^6 -> x^7)
    // =========================================================================
    sym_header!("qsag_asm_goldilocks_pow7_ct_x86_64"),
    "mov r11, rdi",
    "mov r10d, 0xffffffff",
    // x2 = x * x mod p -> rax
    "mov rdx, r11",
    "mulx rcx, rax, r11",
    "mov rdx, rcx",
    "shr rcx, 32",
    "mov edx, edx",
    "sub rax, rcx",
    "sbb r8d, r8d",
    "sub rax, r8",
    "mov r9, rdx",
    "shl r9, 32",
    "sub r9, rdx",
    "add rax, r9",
    "sbb r8d, r8d",
    "add rax, r8",
    "mov r8, rax",
    "add r8, r10",
    "sbb rcx, rcx",
    "and rcx, r10",
    "add rax, rcx",
    // x3 = x2 * x mod p -> rax
    "mov rdx, rax",
    "mulx rcx, rax, r11",
    "mov rdx, rcx",
    "shr rcx, 32",
    "mov edx, edx",
    "sub rax, rcx",
    "sbb r8d, r8d",
    "sub rax, r8",
    "mov r9, rdx",
    "shl r9, 32",
    "sub r9, rdx",
    "add rax, r9",
    "sbb r8d, r8d",
    "add rax, r8",
    "mov r8, rax",
    "add r8, r10",
    "sbb rcx, rcx",
    "and rcx, r10",
    "add rax, rcx",
    // x6 = x3 * x3 mod p -> rax
    "mov rdx, rax",
    "mulx rcx, rax, rax",
    "mov rdx, rcx",
    "shr rcx, 32",
    "mov edx, edx",
    "sub rax, rcx",
    "sbb r8d, r8d",
    "sub rax, r8",
    "mov r9, rdx",
    "shl r9, 32",
    "sub r9, rdx",
    "add rax, r9",
    "sbb r8d, r8d",
    "add rax, r8",
    "mov r8, rax",
    "add r8, r10",
    "sbb rcx, rcx",
    "and rcx, r10",
    "add rax, rcx",
    // x7 = x6 * x mod p -> rax
    "mov rdx, rax",
    "mulx rcx, rax, r11",
    "mov rdx, rcx",
    "shr rcx, 32",
    "mov edx, edx",
    "sub rax, rcx",
    "sbb r8d, r8d",
    "sub rax, r8",
    "mov r9, rdx",
    "shl r9, 32",
    "sub r9, rdx",
    "add rax, r9",
    "sbb r8d, r8d",
    "add rax, r8",
    "mov r8, rax",
    "add r8, r10",
    "sbb rcx, rcx",
    "and rcx, r10",
    "add rax, rcx",
    "xor ecx, ecx",
    "xor edx, edx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "ret",
    sym_footer!("qsag_asm_goldilocks_pow7_ct_x86_64"),
    // =========================================================================
    // 12. qsag_asm_goldilocks_dot2_adx_x86_64(a0, b0, a1, b1) -> u64
    //     BMI2 + ADX (`mulx` + `adcx` + `adox`) dual-carry Goldilocks inner product
    //     `(a0 * b0 + a1 * b1) mod p` with zero branches!
    // =========================================================================
    sym_header!("qsag_asm_goldilocks_dot2_adx_x86_64"),
    "mov r10, rdx", // save a1 before rdx is overwritten
    "xor eax, eax", // clears both CF = 0 and OF = 0 for adcx / adox!
    "mov rdx, rdi",
    "mulx r9, r8, rsi", // r9:r8 = a0 * b0
    "mov rdx, r10",
    "mulx r11, r10, rcx", // r11:r10 = a1 * b1
    "adcx r8, r10",       // CF chain: lo = lo0 + lo1
    "adcx r9, r11",       // CF chain: hi = hi0 + hi1 + CF0, CF = carry128
    "adox rax, rax",      // OF chain stays 0 (demonstrating independent CF/OF pipelines)
    "adcx rax, rax",      // rax = carry128 in {0, 1}
    // Fold carry128 * (2^128 mod p): 2^128 == (2^32 - 1)^2 = p - 2^32 = 0xfffffffe00000001 (mod p)!
    "neg rax", // rax = carry128 ? -1 : 0
    "mov r11, 0xfffffffe00000001",
    "and r11, rax", // r11 = carry128 ? (2^128 mod p) : 0
    // Reduce r9:r8 (128-bit) -> rax
    "mov rax, r8",
    "mov rdx, r9",
    "shr r9, 32",
    "mov edx, edx",
    "sub rax, r9",
    "sbb r8d, r8d",
    "sub rax, r8",
    "mov r9, rdx",
    "shl r9, 32",
    "sub r9, rdx",
    "add rax, r9",
    "sbb r8d, r8d",
    "add rax, r8",
    // Add r11 = carry128 * (2^128 mod p)
    "add rax, r11",
    "sbb r8d, r8d",
    "add rax, r8",
    "sbb r10d, r10d",
    "add rax, r10",
    // Canonicalize into [0, p - 1]
    "mov r9d, 0xffffffff",
    "mov r8, rax",
    "add r8, r9",
    "sbb rcx, rcx",
    "and rcx, r9",
    "add rax, rcx",
    "xor ecx, ecx",
    "xor edx, edx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "ret",
    sym_footer!("qsag_asm_goldilocks_dot2_adx_x86_64"),
    // =========================================================================
    // 13. qsag_asm_ct_eq_32_x86_64(a: *const u8, b: *const u8) -> u64
    //     Straight-line 32-byte tag equality (returns 1 iff equal, 0 otherwise; 0 jumps!)
    // =========================================================================
    sym_header!("qsag_asm_ct_eq_32_x86_64"),
    "mov rax, qword ptr [rdi + 0]",
    "xor rax, qword ptr [rsi + 0]",
    "mov rcx, qword ptr [rdi + 8]",
    "xor rcx, qword ptr [rsi + 8]",
    "mov rdx, qword ptr [rdi + 16]",
    "xor rdx, qword ptr [rsi + 16]",
    "mov r8, qword ptr [rdi + 24]",
    "xor r8, qword ptr [rsi + 24]",
    "or rax, rcx",
    "or rdx, r8",
    "or rax, rdx",
    "mov rcx, rax",
    "neg rcx",
    "or rax, rcx",
    "shr rax, 63",
    "xor eax, 1",
    "xor ecx, ecx",
    "xor edx, edx",
    "xor r8d, r8d",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "ret",
    sym_footer!("qsag_asm_ct_eq_32_x86_64"),
    // =========================================================================
    // 14. qsag_asm_ct_eq_bytes_x86_64(a: *const u8, b: *const u8, len: usize) -> u64
    //     Constant-time byte-slice tag comparison (`len >= 1`).
    // =========================================================================
    sym_header!("qsag_asm_ct_eq_bytes_x86_64"),
    "xor eax, eax",
    "mov rcx, rdx",
    "2:",
    "movzx r8d, byte ptr [rdi]",
    "movzx r9d, byte ptr [rsi]",
    "xor r8d, r9d",
    "or eax, r8d",
    "inc rdi",
    "inc rsi",
    "dec rcx",
    "jnz 2b",
    "sub eax, 1",
    "shr eax, 31",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor edi, edi",
    "xor esi, esi",
    "xor edx, edx",
    "xor ecx, ecx",
    "xor r8d, r8d",
    "xor r9d, r9d",
    "xor r10d, r10d",
    "xor r11d, r11d",
    "ret",
    sym_footer!("qsag_asm_ct_eq_bytes_x86_64"),
    // =========================================================================
    // 15. qsag_asm_ct_memzero_x86_64(ptr: *mut u8, len: usize)
    //     Byte-granular memory wipe followed by mfence (`len >= 1`), immune to LLVM DSE!
    // =========================================================================
    sym_header!("qsag_asm_ct_memzero_x86_64"),
    "mov rcx, rsi",
    "xor eax, eax",
    "2:",
    "mov byte ptr [rdi], al",
    "inc rdi",
    "dec rcx",
    "jnz 2b",
    "mfence",
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
    sym_footer!("qsag_asm_ct_memzero_x86_64"),
);

// Explicit `extern "sysv64"` ABI declaration guarantees System V AMD64 register/callee-save
// conventions (`rdi, rsi, rdx, rcx, r8`, caller-saved `xmm6..xmm15`) even if compiled on
// `x86_64-pc-windows-*`. Raw entrypoints are `pub(crate)` so external callers
// always pass through `lib.rs` CPUID/XCR0 and `blocks32 >= 1` / `count >= 1` guards.
unsafe extern "sysv64" {
    pub(crate) fn qsag_asm_keccak_f1600_avx2_4x(state: *mut KeccakState4x, rcs: *const u64);
    pub(crate) fn qsag_asm_keccak_chi_mpc_avx2(
        out: *mut KeccakRow256,
        s0: *const KeccakRow256,
        s1: *const KeccakRow256,
        r_mask: *const KeccakRow256,
    );
    pub(crate) fn qsag_asm_gf256_shamir_mul_gfni(
        dst: *mut u8,
        a: *const u8,
        b: *const u8,
        blocks32: usize,
    );
    pub(crate) fn qsag_asm_gf256_shamir_mac_gfni(
        acc: *mut u8,
        shares: *const u8,
        scalar: u32,
        blocks32: usize,
    );
    pub(crate) fn qsag_asm_gf256_shamir_mul_avx2(
        dst: *mut u8,
        a: *const u8,
        b: *const u8,
        blocks32: usize,
        luts: *const Avx2Gf256IsoLuts,
    );
    pub(crate) fn qsag_asm_gf256_shamir_mac_avx2(
        acc: *mut u8,
        shares: *const u8,
        scalar: u32,
        blocks32: usize,
        luts: *const Avx2Gf256IsoLuts,
    );
    pub(crate) fn qsag_asm_tower128_bdoz_mac_vpclmul(
        out32: *mut u8,
        lhs32: *const u8,
        rhs32: *const u8,
        count: usize,
    );
    pub(crate) fn qsag_asm_tower128_bdoz_mac_pclmul(
        out32: *mut u8,
        lhs32: *const u8,
        rhs32: *const u8,
        count: usize,
    );
    pub(crate) fn qsag_asm_goldilocks_mul_ct_x86_64(a: u64, b: u64) -> u64;
    pub(crate) fn qsag_asm_goldilocks_add_ct_x86_64(a: u64, b: u64) -> u64;
    pub(crate) fn qsag_asm_goldilocks_sub_ct_x86_64(a: u64, b: u64) -> u64;
    pub(crate) fn qsag_asm_goldilocks_pow7_ct_x86_64(x: u64) -> u64;
    pub(crate) fn qsag_asm_goldilocks_dot2_adx_x86_64(a0: u64, b0: u64, a1: u64, b1: u64) -> u64;
    pub(crate) fn qsag_asm_ct_eq_32_x86_64(a: *const u8, b: *const u8) -> u64;
    pub(crate) fn qsag_asm_ct_eq_bytes_x86_64(a: *const u8, b: *const u8, len: usize) -> u64;
    pub(crate) fn qsag_asm_ct_memzero_x86_64(ptr: *mut u8, len: usize);
}

#[inline]
pub(crate) unsafe fn run_keccak_f1600_avx2_4x(state: &mut KeccakState4x) {
    unsafe {
        qsag_asm_keccak_f1600_avx2_4x(state as *mut KeccakState4x, KECCAK_ROUND_CONSTANTS.as_ptr());
    }
}
