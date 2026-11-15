//! 100% branchless, table-free portable constant-time reference kernels and compile-time verified
//! algebraic basis-isomorphism tables (`Wiedemann T_3 <-> GFNI 0x11B` and
//! `Wiedemann T_7 <-> GF(2)[z]/(z^128 + z^7 + z^2 + z + 1)`).

use core::hint::black_box;
use core::sync::atomic::{Ordering, compiler_fence};

/// Goldilocks prime $p = 2^{64} - 2^{32} + 1$.
pub const GOLDILOCKS_PRIME: u64 = 0xFFFF_FFFF_0000_0001;

/// Goldilocks reduction constant $\epsilon = 2^{32} - 1 = 2^{64} - p$.
pub const GOLDILOCKS_EPSILON: u64 = 0x0000_0000_FFFF_FFFF;

/// Standard 24 FIPS 202 `Keccak-f[1600]` round constants.
pub const KECCAK_ROUND_CONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// FIPS 202 $\rho$ rotation offsets indexed by `x + 5 * y`.
pub const KECCAK_ROTATION_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// 32-byte aligned 4-way (`256`-bit per lane) `Keccak-f[1600]` state (`4` parallel sponges, or
/// `256` parallel Boolean Keccak wires when bitsliced).
/// Intentionally omits `#[derive(PartialEq, Eq)]` so no early-exit comparison symbol is emitted.
#[derive(Clone, Copy, Debug)]
#[repr(C, align(32))]
#[derive(Default)]
pub struct KeccakState4x(pub [[u64; 4]; 25]);

/// 64-byte aligned 8-way (`512`-bit per lane) `Keccak-f[1600]` state (`8` parallel sponges, or
/// `512` parallel Boolean Keccak wires when bitsliced).
/// Intentionally omits `#[derive(PartialEq, Eq)]` so no early-exit comparison symbol is emitted.
#[derive(Clone, Copy, Debug)]
#[repr(C, align(64))]
#[derive(Default)]
pub struct KeccakState8x(pub [[u64; 8]; 25]);

/// 32-byte aligned 5-lane row of 256-bit registers (`5 × 256 = 1,280` parallel bits) for MPC $\chi$.
/// Intentionally omits `#[derive(PartialEq, Eq)]` so no early-exit comparison symbol is emitted.
#[derive(Clone, Copy, Debug)]
#[repr(C, align(32))]
#[derive(Default)]
pub struct KeccakRow256(pub [[u64; 4]; 5]);

/// Intel `VGF2P8AFFINEQB` 64-bit matrix mapping Wiedemann $\mathcal{T}_3$ (`TowerGf256`)
/// $\to \mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$ (`0x11B`), sending generator $z \leftrightarrow \text{0x30} \in \mathcal{T}_3$.
pub const GFNI_MAT_T3_TO_POLY: u64 = 0x7150_0A8A_86BE_78CE;

/// Inverse Intel `VGF2P8AFFINEQB` 64-bit matrix mapping $\mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$
/// (`0x11B`) $\to$ Wiedemann $\mathcal{T}_3$ (`TowerGf256`).
pub const GFNI_MAT_POLY_TO_T3: u64 = 0xA1E4_F8E0_72A2_700C;

/// Exact Artin–Schreier roots $X_0, X_1, \dots, X_6 \in \mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$
/// satisfying $X_0^2 + X_0 + 1 = 0$ and $X_k^2 + X_{k-1} X_k + 1 = 0$ ($1 \le k \le 6$), defining
/// the canonical field isomorphism $\Psi : \mathcal{T}_7 \xrightarrow{\sim} \mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$.
pub const TOWER128_POLY_GENERATORS: [u128; 7] = [
    0x295a_c0b1_f473_1af9_676a_ac9f_a4b2_0b08,
    0x5003_17bd_159d_73bb_34d2_f7fb_a603_e341,
    0x8724_30dc_df13_5bcc_433f_5364_0b5a_b39a,
    0x08ee_6d05_a2af_a6e5_f848_729a_9637_483a,
    0x6167_c15a_e3f2_5159_51c6_5cff_fdd0_9b94,
    0x11bf_2ae0_0eef_b745_8f19_90f8_ffd4_b9bc,
    0x8845_a6b7_8c9f_ffc3_6a2a_7460_0cfa_98de,
];

// ============================================================================
// 1. Wiedemann Binary Tower (T_3 and T_7) & Polynomial Basis Algebra
// ============================================================================

macro_rules! def_tower_level {
    ($mul_fn:ident, $scale_fn:ident, $prev_mul:ident, $prev_scale:ident, $ty:ty, $half:literal, $mask:literal) => {
        #[inline]
        pub const fn $scale_fn(a: $ty) -> $ty {
            let lo = a & $mask;
            let hi = (a >> $half) & $mask;
            hi | ((lo ^ $prev_scale(hi)) << $half)
        }

        #[inline]
        pub const fn $mul_fn(a: $ty, b: $ty) -> $ty {
            let a_lo = a & $mask;
            let a_hi = (a >> $half) & $mask;
            let b_lo = b & $mask;
            let b_hi = (b >> $half) & $mask;
            let p = $prev_mul(a_lo, b_lo);
            let q = $prev_mul(a_hi, b_hi);
            let r = $prev_mul(a_lo ^ a_hi, b_lo ^ b_hi);
            let lo = p ^ q;
            let hi = r ^ p ^ q ^ $prev_scale(q);
            lo | (hi << $half)
        }
    };
}

#[inline]
const fn tower_scale_t0(a: u8) -> u8 {
    a & 1
}

#[inline]
const fn tower_mul_t0(a: u8, b: u8) -> u8 {
    (a & 1) & (b & 1)
}

def_tower_level!(
    tower_mul_t1,
    tower_scale_t1,
    tower_mul_t0,
    tower_scale_t0,
    u8,
    1,
    0x01
);
def_tower_level!(
    tower_mul_t2,
    tower_scale_t2,
    tower_mul_t1,
    tower_scale_t1,
    u8,
    2,
    0x03
);
def_tower_level!(
    wiedemann_mul_t3_u8,
    tower_scale_t3,
    tower_mul_t2,
    tower_scale_t2,
    u8,
    4,
    0x0F
);

#[inline]
const fn tower_scale_t3_u16(a: u16) -> u16 {
    tower_scale_t3(a as u8) as u16
}

#[inline]
const fn tower_mul_t3_u16(a: u16, b: u16) -> u16 {
    wiedemann_mul_t3_u8(a as u8, b as u8) as u16
}

def_tower_level!(
    tower_mul_t4,
    tower_scale_t4,
    tower_mul_t3_u16,
    tower_scale_t3_u16,
    u16,
    8,
    0x00FF
);

#[inline]
const fn tower_scale_t4_u32(a: u32) -> u32 {
    tower_scale_t4(a as u16) as u32
}

#[inline]
const fn tower_mul_t4_u32(a: u32, b: u32) -> u32 {
    tower_mul_t4(a as u16, b as u16) as u32
}

def_tower_level!(
    tower_mul_t5,
    tower_scale_t5,
    tower_mul_t4_u32,
    tower_scale_t4_u32,
    u32,
    16,
    0x0000_FFFF
);

#[inline]
const fn tower_scale_t5_u64(a: u64) -> u64 {
    tower_scale_t5(a as u32) as u64
}

#[inline]
const fn tower_mul_t5_u64(a: u64, b: u64) -> u64 {
    tower_mul_t5(a as u32, b as u32) as u64
}

def_tower_level!(
    tower_mul_t6,
    tower_scale_t6,
    tower_mul_t5_u64,
    tower_scale_t5_u64,
    u64,
    32,
    0x0000_0000_FFFF_FFFF
);

#[inline]
const fn tower_scale_t6_u128(a: u128) -> u128 {
    tower_scale_t6(a as u64) as u128
}

#[inline]
const fn tower_mul_t6_u128(a: u128, b: u128) -> u128 {
    tower_mul_t6(a as u64, b as u64) as u128
}

def_tower_level!(
    wiedemann_mul_t7_u128,
    tower_scale_t7,
    tower_mul_t6_u128,
    tower_scale_t6_u128,
    u128,
    64,
    0x0000_0000_0000_0000_FFFF_FFFF_FFFF_FFFF
);

/// Exact GFNI (`0x11B`) byte multiplication for compile-time verification.
#[inline]
pub const fn gfni_poly_mul_u8(mut a: u8, mut b: u8) -> u8 {
    let mut acc = 0u8;
    let mut i = 0;
    while i < 8 {
        let mask = 0u8.wrapping_sub(b & 1);
        acc ^= a & mask;
        let hi = 0u8.wrapping_sub((a >> 7) & 1);
        a = (a << 1) ^ (0x1Bu8 & hi);
        b >>= 1;
        i += 1;
    }
    acc
}

/// Exact software model of Intel `VGF2P8AFFINEQB(x, matrix_qword, imm8)`.
#[inline]
pub const fn sim_gf2p8affineqb(x: u8, matrix_qword: u64, imm8: u8) -> u8 {
    let mut out = 0u8;
    let mut i = 0u32;
    while i < 8 {
        let row_byte = ((matrix_qword >> (8 * (7 - i))) & 0xFF) as u8;
        let prod = x & row_byte;
        let parity = (prod.count_ones() & 1) as u8;
        out |= (parity ^ ((imm8 >> i) & 1)) << i;
        i += 1;
    }
    out
}

/// Constant-time polynomial multiplication in $\mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$.
#[inline]
pub const fn poly128_mul_const(mut a: u128, mut b: u128) -> u128 {
    let mut acc = 0u128;
    let mut i = 0;
    while i < 128 {
        let b_mask = 0u128.wrapping_sub(b & 1);
        acc ^= a & b_mask;
        let hi_mask = 0u128.wrapping_sub((a >> 127) & 1);
        a = (a << 1) ^ (0x87u128 & hi_mask);
        b >>= 1;
        i += 1;
    }
    acc
}

macro_rules! unroll_64 {
    ($m:ident, $a:expr, $b:expr, $acc:expr) => {{
        $m!(
            $a, $b, $acc, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
        );
        $m!(
            $a, $b, $acc, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31
        );
        $m!(
            $a, $b, $acc, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47
        );
        $m!(
            $a, $b, $acc, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63
        );
    }};
}

macro_rules! clmul_bits {
    ($a128:expr, $b:expr, $acc:expr, $($i:literal),+) => {
        $(
            let mask = 0u128.wrapping_sub((($b >> $i) & 1) as u128);
            $acc ^= ($a128 << $i) & mask;
        )+
    };
}

/// Carryless $64 \times 64 \to 128$ polynomial multiplication in portable constant-time code
/// (`0` branches, `0` variable-count `cl` shifts!).
#[inline]
pub const fn clmul64_portable(a: u64, b: u64) -> u128 {
    let mut acc = 0u128;
    let a128 = a as u128;
    unroll_64!(clmul_bits, a128, b, acc);
    acc
}

/// Carryless $128 \times 128 \to 256$-bit (`(lo128, hi128)`) multiplication via Karatsuba.
#[inline]
pub const fn clmul128_wide_portable(a: u128, b: u128) -> (u128, u128) {
    let a0 = a as u64;
    let a1 = (a >> 64) as u64;
    let b0 = b as u64;
    let b1 = (b >> 64) as u64;
    let z0 = clmul64_portable(a0, b0);
    let z2 = clmul64_portable(a1, b1);
    let z1 = clmul64_portable(a0 ^ a1, b0 ^ b1) ^ z0 ^ z2;
    let lo = z0 ^ (z1 << 64);
    let hi = z2 ^ (z1 >> 64);
    (lo, hi)
}

/// Exact 2-step reduction of a 256-bit polynomial `(lo128, hi128)` modulo $z^{128} + z^7 + z^2 + z + 1$ (`0x87`),
/// matching our `vpclmulqdq` / `pclmulqdq` / `pmull` hardware instruction sequence 1-to-1!
#[inline]
pub const fn clmul256_reduce_0x87(lo128: u128, hi128: u128) -> u128 {
    let c2 = hi128 as u64;
    let c3 = (hi128 >> 64) as u64;
    // Step 1: C3 * z^192 == (C3 * 0x87) * z^64
    let t = clmul64_portable(c3, 0x87);
    let lo1 = lo128 ^ (t << 64);
    let c2_prime = c2 ^ ((t >> 64) as u64);
    // Step 2: C2' * z^128 == C2' * 0x87 (deg <= 70 < 128)
    let u = clmul64_portable(c2_prime, 0x87);
    lo1 ^ u
}

/// Compact `128`-word (`2 KiB` per direction, `0` 16 KiB nibble LUTs!) $\mathbb{F}_2$-linear basis
/// matrices between Wiedemann $\mathcal{T}_7$ and $\mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$.
const fn build_tower128_basis_pair() -> ([u128; 128], [u128; 128]) {
    // Verify Artin-Schreier defining equations at compile time!
    let mut k = 0usize;
    while k < 7 {
        let xk = if k == 0 {
            1u128
        } else {
            TOWER128_POLY_GENERATORS[k - 1]
        };
        let gk = TOWER128_POLY_GENERATORS[k];
        let lhs = poly128_mul_const(gk, gk) ^ poly128_mul_const(xk, gk);
        assert!(
            lhs == 1,
            "TOWER128_POLY_GENERATORS failed Artin-Schreier equation"
        );
        k += 1;
    }

    // 1. Columns of Psi: T_7 -> Poly128
    let mut t7_cols = [0u128; 128];
    let mut m = 0usize;
    while m < 128 {
        let mut prod = 1u128;
        let mut bit = 0usize;
        while bit < 7 {
            if ((m >> bit) & 1) == 1 {
                prod = poly128_mul_const(prod, TOWER128_POLY_GENERATORS[bit]);
            }
            bit += 1;
        }
        t7_cols[m] = prod;
        m += 1;
    }

    // 2. Invert 128x128 binary matrix over GF(2) at compile time to obtain Psi^{-1}: Poly128 -> T_7!
    let mut rows_lhs = [0u128; 128];
    let mut rows_rhs = [0u128; 128];
    let mut r = 0usize;
    while r < 128 {
        let mut row_val = 0u128;
        let mut c = 0usize;
        while c < 128 {
            if ((t7_cols[c] >> r) & 1) == 1 {
                row_val |= 1u128 << c;
            }
            c += 1;
        }
        rows_lhs[r] = row_val;
        rows_rhs[r] = 1u128 << r;
        r += 1;
    }

    let mut col = 0usize;
    while col < 128 {
        let mut piv = col;
        while piv < 128 && ((rows_lhs[piv] >> col) & 1) == 0 {
            piv += 1;
        }
        assert!(
            piv < 128,
            "T_7 -> Poly128 basis matrix must be non-singular"
        );
        if piv != col {
            let tmp_l = rows_lhs[col];
            rows_lhs[col] = rows_lhs[piv];
            rows_lhs[piv] = tmp_l;
            let tmp_r = rows_rhs[col];
            rows_rhs[col] = rows_rhs[piv];
            rows_rhs[piv] = tmp_r;
        }
        let mut row = 0usize;
        while row < 128 {
            if row != col && ((rows_lhs[row] >> col) & 1) == 1 {
                rows_lhs[row] ^= rows_lhs[col];
                rows_rhs[row] ^= rows_rhs[col];
            }
            row += 1;
        }
        col += 1;
    }

    let mut poly_cols = [0u128; 128];
    let mut out_bit = 0usize;
    while out_bit < 128 {
        let inv_row = rows_rhs[out_bit];
        let mut in_bit = 0usize;
        while in_bit < 128 {
            if ((inv_row >> in_bit) & 1) == 1 {
                poly_cols[in_bit] |= 1u128 << out_bit;
            }
            in_bit += 1;
        }
        out_bit += 1;
    }

    (t7_cols, poly_cols)
}

const TOWER128_BASIS_PAIR: ([u128; 128], [u128; 128]) = build_tower128_basis_pair();

/// 128 basis columns of $\Psi : \mathcal{T}_7 \to \mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$.
pub const T7_TO_POLY_BASIS: [u128; 128] = TOWER128_BASIS_PAIR.0;

/// 128 basis columns of $\Psi^{-1} : \mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1) \to \mathcal{T}_7$.
pub const POLY_TO_T7_BASIS: [u128; 128] = TOWER128_BASIS_PAIR.1;

// Compile-time check of GFNI_MAT_T3_TO_POLY and GFNI_MAT_POLY_TO_T3 roundtrip on basis bits!
const _: () = {
    let mut b = 0u32;
    while b < 8 {
        let e = 1u8 << b;
        let fwd = sim_gf2p8affineqb(e, GFNI_MAT_T3_TO_POLY, 0);
        let rev = sim_gf2p8affineqb(fwd, GFNI_MAT_POLY_TO_T3, 0);
        assert!(rev == e, "GFNI <-> T_3 matrices must be exact inverses");
        b += 1;
    }
};

macro_rules! linear128_step {
    ($w:expr, $basis:ident, $base:literal, $acc:expr, $($b:literal),+) => {
        $(
            let mask = 0u128.wrapping_sub((($w >> $b) & 1) as u128);
            $acc ^= $basis[$base + $b] & mask;
        )+
    };
}

/// Constant-time linear basis map $\Psi : \mathcal{T}_7 \to \mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$
/// (`0` branches, `0` variable shifts, `0` 16 KiB table scans — pure constant-shift bit-matrix XOR!).
#[inline]
pub fn tower128_to_poly128_ct(x: u128) -> u128 {
    let x = black_box(x);
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let mut acc = 0u128;
    linear128_step!(
        lo,
        T7_TO_POLY_BASIS,
        0,
        acc,
        0,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15
    );
    linear128_step!(
        lo,
        T7_TO_POLY_BASIS,
        0,
        acc,
        16,
        17,
        18,
        19,
        20,
        21,
        22,
        23,
        24,
        25,
        26,
        27,
        28,
        29,
        30,
        31
    );
    linear128_step!(
        lo,
        T7_TO_POLY_BASIS,
        0,
        acc,
        32,
        33,
        34,
        35,
        36,
        37,
        38,
        39,
        40,
        41,
        42,
        43,
        44,
        45,
        46,
        47
    );
    linear128_step!(
        lo,
        T7_TO_POLY_BASIS,
        0,
        acc,
        48,
        49,
        50,
        51,
        52,
        53,
        54,
        55,
        56,
        57,
        58,
        59,
        60,
        61,
        62,
        63
    );
    linear128_step!(
        hi,
        T7_TO_POLY_BASIS,
        64,
        acc,
        0,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15
    );
    linear128_step!(
        hi,
        T7_TO_POLY_BASIS,
        64,
        acc,
        16,
        17,
        18,
        19,
        20,
        21,
        22,
        23,
        24,
        25,
        26,
        27,
        28,
        29,
        30,
        31
    );
    linear128_step!(
        hi,
        T7_TO_POLY_BASIS,
        64,
        acc,
        32,
        33,
        34,
        35,
        36,
        37,
        38,
        39,
        40,
        41,
        42,
        43,
        44,
        45,
        46,
        47
    );
    linear128_step!(
        hi,
        T7_TO_POLY_BASIS,
        64,
        acc,
        48,
        49,
        50,
        51,
        52,
        53,
        54,
        55,
        56,
        57,
        58,
        59,
        60,
        61,
        62,
        63
    );
    acc
}

/// Constant-time inverse linear basis map $\Psi^{-1} : \mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1) \to \mathcal{T}_7$
/// (`0` branches, `0` variable shifts, `0` 16 KiB table scans!).
#[inline]
pub fn poly128_to_tower128_ct(y: u128) -> u128 {
    let y = black_box(y);
    let lo = y as u64;
    let hi = (y >> 64) as u64;
    let mut acc = 0u128;
    linear128_step!(
        lo,
        POLY_TO_T7_BASIS,
        0,
        acc,
        0,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15
    );
    linear128_step!(
        lo,
        POLY_TO_T7_BASIS,
        0,
        acc,
        16,
        17,
        18,
        19,
        20,
        21,
        22,
        23,
        24,
        25,
        26,
        27,
        28,
        29,
        30,
        31
    );
    linear128_step!(
        lo,
        POLY_TO_T7_BASIS,
        0,
        acc,
        32,
        33,
        34,
        35,
        36,
        37,
        38,
        39,
        40,
        41,
        42,
        43,
        44,
        45,
        46,
        47
    );
    linear128_step!(
        lo,
        POLY_TO_T7_BASIS,
        0,
        acc,
        48,
        49,
        50,
        51,
        52,
        53,
        54,
        55,
        56,
        57,
        58,
        59,
        60,
        61,
        62,
        63
    );
    linear128_step!(
        hi,
        POLY_TO_T7_BASIS,
        64,
        acc,
        0,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15
    );
    linear128_step!(
        hi,
        POLY_TO_T7_BASIS,
        64,
        acc,
        16,
        17,
        18,
        19,
        20,
        21,
        22,
        23,
        24,
        25,
        26,
        27,
        28,
        29,
        30,
        31
    );
    linear128_step!(
        hi,
        POLY_TO_T7_BASIS,
        64,
        acc,
        32,
        33,
        34,
        35,
        36,
        37,
        38,
        39,
        40,
        41,
        42,
        43,
        44,
        45,
        46,
        47
    );
    linear128_step!(
        hi,
        POLY_TO_T7_BASIS,
        64,
        acc,
        48,
        49,
        50,
        51,
        52,
        53,
        54,
        55,
        56,
        57,
        58,
        59,
        60,
        61,
        62,
        63
    );
    acc
}

// ============================================================================
// 2. Portable Constant-Time Kernels (Matching Hardware SIMD Kernels Bit-for-Bit)
// ============================================================================

macro_rules! keccak_rho_pi_lanes {
    ($s:expr, $b:expr, $(($src:literal, $tgt:literal, $rot:literal)),+ $(,)?) => {
        $(
            for lane in 0..4 {
                $b[$tgt][lane] = $s[$src][lane].rotate_left($rot);
            }
        )+
    };
}

/// Portable 4-way (`256`-bit per lane) `Keccak-f[1600]` 24-round permutation
/// (`0` variable-count rotations, `0` integer divisions, volatile scratch zeroization).
pub fn keccak_f1600_4x_portable(state: &mut KeccakState4x) {
    let s = &mut state.0;
    let mut c = [[0u64; 4]; 5];
    let mut d = [[0u64; 4]; 5];
    let mut b = [[0u64; 4]; 25];

    for &rc in &KECCAK_ROUND_CONSTANTS {
        for x in 0..5 {
            for lane in 0..4 {
                c[x][lane] = s[x][lane]
                    ^ s[x + 5][lane]
                    ^ s[x + 10][lane]
                    ^ s[x + 15][lane]
                    ^ s[x + 20][lane];
            }
        }
        for lane in 0..4 {
            d[0][lane] = c[4][lane] ^ c[1][lane].rotate_left(1);
            d[1][lane] = c[0][lane] ^ c[2][lane].rotate_left(1);
            d[2][lane] = c[1][lane] ^ c[3][lane].rotate_left(1);
            d[3][lane] = c[2][lane] ^ c[4][lane].rotate_left(1);
            d[4][lane] = c[3][lane] ^ c[0][lane].rotate_left(1);
        }
        for y in 0..5 {
            for x in 0..5 {
                for lane in 0..4 {
                    s[x + 5 * y][lane] ^= d[x][lane];
                }
            }
        }
        keccak_rho_pi_lanes!(
            s,
            b,
            (0, 0, 0),
            (1, 10, 1),
            (2, 20, 62),
            (3, 5, 28),
            (4, 15, 27),
            (5, 16, 36),
            (6, 1, 44),
            (7, 11, 6),
            (8, 21, 55),
            (9, 6, 20),
            (10, 7, 3),
            (11, 17, 10),
            (12, 2, 43),
            (13, 12, 25),
            (14, 22, 39),
            (15, 23, 41),
            (16, 8, 45),
            (17, 18, 15),
            (18, 3, 21),
            (19, 13, 8),
            (20, 14, 18),
            (21, 24, 2),
            (22, 9, 61),
            (23, 19, 56),
            (24, 4, 14),
        );
        for y in 0..5 {
            let row = 5 * y;
            for lane in 0..4 {
                s[row][lane] = b[row][lane] ^ ((!b[row + 1][lane]) & b[row + 2][lane]);
                s[row + 1][lane] = b[row + 1][lane] ^ ((!b[row + 2][lane]) & b[row + 3][lane]);
                s[row + 2][lane] = b[row + 2][lane] ^ ((!b[row + 3][lane]) & b[row + 4][lane]);
                s[row + 3][lane] = b[row + 3][lane] ^ ((!b[row + 4][lane]) & b[row][lane]);
                s[row + 4][lane] = b[row + 4][lane] ^ ((!b[row][lane]) & b[row + 1][lane]);
            }
        }
        for value in &mut s[0] {
            *value ^= rc;
        }
    }

    // Volatile wipe of all stack scratch arrays
    for row in &mut c {
        for word in row {
            unsafe { core::ptr::write_volatile(word, 0) };
        }
    }
    for row in &mut d {
        for word in row {
            unsafe { core::ptr::write_volatile(word, 0) };
        }
    }
    for row in &mut b {
        for word in row {
            unsafe { core::ptr::write_volatile(word, 0) };
        }
    }
    compiler_fence(Ordering::SeqCst);
}

/// Portable 8-way (`512`-bit per lane) `Keccak-f[1600]` 24-round permutation.
pub fn keccak_f1600_8x_portable(state: &mut KeccakState8x) {
    let mut lo = KeccakState4x::default();
    let mut hi = KeccakState4x::default();
    for (lane, words) in state.0.iter().enumerate() {
        lo.0[lane] = [words[0], words[1], words[2], words[3]];
        hi.0[lane] = [words[4], words[5], words[6], words[7]];
    }
    keccak_f1600_4x_portable(&mut lo);
    keccak_f1600_4x_portable(&mut hi);
    for (lane, words) in state.0.iter_mut().enumerate() {
        *words = [
            lo.0[lane][0],
            lo.0[lane][1],
            lo.0[lane][2],
            lo.0[lane][3],
            hi.0[lane][0],
            hi.0[lane][1],
            hi.0[lane][2],
            hi.0[lane][3],
        ];
    }
    for row in &mut lo.0 {
        for word in row {
            unsafe { core::ptr::write_volatile(word, 0) };
        }
    }
    for row in &mut hi.0 {
        for word in row {
            unsafe { core::ptr::write_volatile(word, 0) };
        }
    }
    compiler_fence(Ordering::SeqCst);
}

/// Portable 256-way bitsliced symmetric 3-party RSS MPC $\chi$-row gate:
/// `out[x] = s0[x] ^ s0[x+2] ^ (s0[x+1] & s0[x+2]) ^ (s0[x+1] & s1[x+2]) ^ (s1[x+1] & s0[x+2]) ^ r_mask[x]`.
///
/// Summing `out` across all 3 parties with `r_mask^(0) ^ r_mask^(1) ^ r_mask^(2) == 0` yields
/// `b[x] ^ b[x+2] ^ (b[x+1] & b[x+2]) == b[x] ^ ((!b[x+1]) & b[x+2])` across 256 parallel sponges!
pub fn keccak_chi_mpc_4x_portable(
    out: &mut KeccakRow256,
    s0: &KeccakRow256,
    s1: &KeccakRow256,
    r_mask: &KeccakRow256,
) {
    const NEXT1: [usize; 5] = [1, 2, 3, 4, 0];
    const NEXT2: [usize; 5] = [2, 3, 4, 0, 1];
    for x in 0..5 {
        let x1 = NEXT1[x];
        let x2 = NEXT2[x];
        for lane in 0..4 {
            let u_x = s0.0[x][lane];
            let u_x1 = s0.0[x1][lane];
            let u_x2 = s0.0[x2][lane];
            let v_x1 = s1.0[x1][lane];
            let v_x2 = s1.0[x2][lane];
            let and_term = (u_x1 & (u_x2 ^ v_x2)) ^ (v_x1 & u_x2);
            out.0[x][lane] = u_x ^ u_x2 ^ and_term ^ r_mask.0[x][lane];
        }
    }
}

/// Portable constant-time elementwise Wiedemann $\mathcal{T}_3$ (`TowerGf256`) slice multiply:
/// `dst[i] = a[i] * b[i]` in $\mathcal{T}_3$.
pub fn gf256_shamir_mul_portable(dst: &mut [u8], a: &[u8], b: &[u8]) {
    assert_eq!(dst.len(), a.len());
    assert_eq!(dst.len(), b.len());
    for i in 0..dst.len() {
        dst[i] = wiedemann_mul_t3_u8(black_box(a[i]), black_box(b[i]));
    }
}

/// Portable constant-time Wiedemann $\mathcal{T}_3$ (`TowerGf256`) Shamir multiply-accumulate:
/// `acc[i] ^= scalar * shares[i]` in $\mathcal{T}_3$ (constant-time even when `scalar` is secret).
pub fn gf256_shamir_mac_portable(acc: &mut [u8], shares: &[u8], scalar: u8) {
    assert_eq!(acc.len(), shares.len());
    let s = black_box(scalar);
    for i in 0..acc.len() {
        acc[i] ^= wiedemann_mul_t3_u8(s, black_box(shares[i]));
    }
}

/// Portable 2-lane polynomial-basis BDOZ MAC inner product over $\mathbb{F}_2[z]/(z^{128}+z^7+z^2+z+1)$:
/// computes `(acc0, acc1) = (\bigoplus_i a_lane0[i] * b_lane0[i], \bigoplus_i a_lane1[i] * b_lane1[i])`
/// using delayed 256-bit carryless accumulation + single `0x87` reduction at the end!
pub fn tower128_bdoz_2lane_poly_mac_portable(
    lhs_pairs: &[[u128; 2]],
    rhs_pairs: &[[u128; 2]],
) -> [u128; 2] {
    assert_eq!(lhs_pairs.len(), rhs_pairs.len());
    let mut lo0 = 0u128;
    let mut hi0 = 0u128;
    let mut lo1 = 0u128;
    let mut hi1 = 0u128;
    for i in 0..lhs_pairs.len() {
        let (p_lo0, p_hi0) = clmul128_wide_portable(lhs_pairs[i][0], rhs_pairs[i][0]);
        let (p_lo1, p_hi1) = clmul128_wide_portable(lhs_pairs[i][1], rhs_pairs[i][1]);
        lo0 ^= p_lo0;
        hi0 ^= p_hi0;
        lo1 ^= p_lo1;
        hi1 ^= p_hi1;
    }
    let out = [
        clmul256_reduce_0x87(lo0, hi0),
        clmul256_reduce_0x87(lo1, hi1),
    ];
    unsafe {
        core::ptr::write_volatile(&mut lo0, 0);
        core::ptr::write_volatile(&mut hi0, 0);
        core::ptr::write_volatile(&mut lo1, 0);
        core::ptr::write_volatile(&mut hi1, 0);
    }
    out
}

/// Portable 2-lane Wiedemann $\mathcal{T}_7$ (`Tower128`) BDOZ MAC inner product, bit-exact with
/// `qsag_core::field::tower::Tower128::mul`.
pub fn tower128_bdoz_2lane_mac_portable(
    lhs_pairs: &[[u128; 2]],
    rhs_pairs: &[[u128; 2]],
) -> [u128; 2] {
    assert_eq!(lhs_pairs.len(), rhs_pairs.len());
    let mut acc0 = 0u128;
    let mut acc1 = 0u128;
    for i in 0..lhs_pairs.len() {
        acc0 ^= wiedemann_mul_t7_u128(lhs_pairs[i][0], rhs_pairs[i][0]);
        acc1 ^= wiedemann_mul_t7_u128(lhs_pairs[i][1], rhs_pairs[i][1]);
    }
    let out = [acc0, acc1];
    unsafe {
        core::ptr::write_volatile(&mut acc0, 0);
        core::ptr::write_volatile(&mut acc1, 0);
    }
    out
}

/// Branchless Goldilocks canonicalizer `x mod p` for arbitrary `u64` (`0 ..= u64::MAX`).
#[inline]
pub const fn goldilocks_canonicalize_ct(x: u64) -> u64 {
    let (_, carry) = x.overflowing_add(GOLDILOCKS_EPSILON);
    let adj = (0u64.wrapping_sub(carry as u64)) & GOLDILOCKS_EPSILON;
    x.wrapping_add(adj)
}

/// Branchless Goldilocks modular addition `(a + b) mod p` exact for ALL `(a, b) in [0, u64::MAX]^2`.
#[inline]
pub const fn goldilocks_add_ct_portable(a: u64, b: u64) -> u64 {
    let (s1, c1) = a.overflowing_add(b);
    let adj1 = (0u64.wrapping_sub(c1 as u64)) & GOLDILOCKS_EPSILON;
    let (s2, c2) = s1.overflowing_add(adj1);
    let adj2 = (0u64.wrapping_sub(c2 as u64)) & GOLDILOCKS_EPSILON;
    goldilocks_canonicalize_ct(s2.wrapping_add(adj2))
}

/// Branchless Goldilocks modular subtraction `(a - b) mod p` exact for ALL `(a, b) in [0, u64::MAX]^2`.
#[inline]
pub const fn goldilocks_sub_ct_portable(a: u64, b: u64) -> u64 {
    let ac = goldilocks_canonicalize_ct(a);
    let bc = goldilocks_canonicalize_ct(b);
    let (diff, borrow) = ac.overflowing_sub(bc);
    let adj = (0u64.wrapping_sub(borrow as u64)) & GOLDILOCKS_PRIME;
    diff.wrapping_add(adj)
}

/// Branchless Goldilocks 128-to-64 reduction `x mod p` exact for ALL `x in [0, u128::MAX]`.
#[inline]
pub const fn goldilocks_reduce128_ct_portable(x: u128) -> u64 {
    let x0 = x as u64;
    let hi = (x >> 64) as u64;
    let x1 = hi & GOLDILOCKS_EPSILON;
    let x2 = hi >> 32;

    let (t1, b1) = x0.overflowing_sub(x2);
    let adj1 = (0u64.wrapping_sub(b1 as u64)) & GOLDILOCKS_EPSILON;
    let u1 = t1.wrapping_sub(adj1);

    let m = (x1 << 32).wrapping_sub(x1);
    let (t2, c2) = u1.overflowing_add(m);
    let adj2 = (0u64.wrapping_sub(c2 as u64)) & GOLDILOCKS_EPSILON;
    let u2 = t2.wrapping_add(adj2);

    goldilocks_canonicalize_ct(u2)
}

/// Branchless Goldilocks modular multiplication `(a * b) mod p` exact for ALL `(a, b) in [0, u64::MAX]^2`.
#[inline]
pub const fn goldilocks_mul_ct_portable(a: u64, b: u64) -> u64 {
    goldilocks_reduce128_ct_portable((a as u128) * (b as u128))
}

/// Branchless Goldilocks Poseidon2 S-box $x^7 \bmod p$ exact for ALL `x in [0, u64::MAX]`.
#[inline]
pub const fn goldilocks_pow7_ct_portable(x: u64) -> u64 {
    let x2 = goldilocks_mul_ct_portable(x, x);
    let x3 = goldilocks_mul_ct_portable(x2, x);
    let x6 = goldilocks_mul_ct_portable(x3, x3);
    goldilocks_mul_ct_portable(x6, x)
}

/// Constant-time 32-byte tag equality (`true` iff `a == b`).
#[inline]
pub fn ct_eq_32_portable(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let mut diff = 0u64;
    for chunk in 0..4 {
        let o = 8 * chunk;
        let wa = u64::from_le_bytes([
            a[o],
            a[o + 1],
            a[o + 2],
            a[o + 3],
            a[o + 4],
            a[o + 5],
            a[o + 6],
            a[o + 7],
        ]);
        let wb = u64::from_le_bytes([
            b[o],
            b[o + 1],
            b[o + 2],
            b[o + 3],
            b[o + 4],
            b[o + 5],
            b[o + 6],
            b[o + 7],
        ]);
        diff |= black_box(wa ^ wb);
    }
    let folded = (diff | diff.wrapping_neg()) >> 63;
    folded == 0
}

/// Constant-time arbitrary byte-slice equality.
#[inline]
pub fn ct_eq_bytes_portable(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for i in 0..a.len() {
        diff |= black_box(a[i] ^ b[i]);
    }
    let diff = black_box(diff);
    (((diff as u16).wrapping_sub(1)) >> 15) == 1
}

/// Volatile-fenced memory zeroization immune to dead-store elimination.
#[inline(never)]
pub fn ct_memzero_portable(buf: &mut [u8]) {
    for byte in buf.iter_mut() {
        // SAFETY: `byte` is a valid aligned mutable `u8` reference inside `buf`.
        unsafe {
            core::ptr::write_volatile(byte, 0u8);
        }
    }
    compiler_fence(Ordering::SeqCst);
    black_box(buf);
}

// Pin the Wiedemann T_3 generators: X0² + X0 = 1; Xk² + X(k-1)Xk = 1.
// The alternative Xk² + Xk relations describe a different tower basis.
const _: () = {
    let x0 = sim_gf2p8affineqb(0x02, GFNI_MAT_T3_TO_POLY, 0);
    let x1 = sim_gf2p8affineqb(0x04, GFNI_MAT_T3_TO_POLY, 0);
    let x2 = sim_gf2p8affineqb(0x10, GFNI_MAT_T3_TO_POLY, 0);
    assert!(gfni_poly_mul_u8(x0, x0) ^ x0 == 1);
    assert!(gfni_poly_mul_u8(x1, x1) ^ gfni_poly_mul_u8(x0, x1) == 1);
    assert!(gfni_poly_mul_u8(x2, x2) ^ gfni_poly_mul_u8(x1, x2) == 1);
};
