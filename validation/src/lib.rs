// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Shared reference-oracle helpers, basis isomorphisms, and algebraic inverse
//! utilities for QSAG external differential validation and property-based testing.

use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractExtensionField, AbstractField, Field, PrimeField64};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use qsag_asm::SimdBackend;

pub mod poseidon2_ref;
pub mod spec_ref;

/// Goldilocks prime `p = 2^64 - 2^32 + 1`.
pub const GOLDILOCKS_P: u64 = poseidon2_ref::P;

/// Every `qsag-asm` dispatch tier; tiers the host lacks fall back inside `qsag-asm`.
pub const ALL_SIMD_BACKENDS: [SimdBackend; 4] = [
    SimdBackend::Portable,
    SimdBackend::X86Avx2Pclmul,
    SimdBackend::X86Avx2GfniVpclmul,
    SimdBackend::X86Avx512GfniVpclmul,
];

type P3Ext2 = BinomialExtensionField<P3Goldilocks, 2>;

/// Plonky3 Goldilocks element of `raw mod p`.
#[inline]
pub fn p3_gl(raw: u64) -> P3Goldilocks {
    P3Goldilocks::from_canonical_u64(raw % GOLDILOCKS_P)
}

/// Limbs `[c00, c01, c10, c11]` of `(c00 + c01 u) + (c10 + c11 u) v` with `u^2 = 7`, `v^2 = u`,
/// as the pair of Plonky3 quadratic-extension coefficients of `1` and `v`.
fn p3_ext4_split(a: [u64; 4]) -> (P3Ext2, P3Ext2) {
    (
        P3Ext2::from_base_slice(&[p3_gl(a[0]), p3_gl(a[1])]),
        P3Ext2::from_base_slice(&[p3_gl(a[2]), p3_gl(a[3])]),
    )
}

fn p3_ext4_join(c0: P3Ext2, c1: P3Ext2) -> [u64; 4] {
    let (c0, c1): (&[P3Goldilocks], &[P3Goldilocks]) = (c0.as_base_slice(), c1.as_base_slice());
    [c0[0], c0[1], c1[0], c1[1]].map(|x| x.as_canonical_u64())
}

/// Reference `GoldilocksExt4` product over Plonky3's quadratic extension:
/// `(a0 + a1 v)(b0 + b1 v) = (a0 b0 + u a1 b1) + (a0 b1 + a1 b0) v`.
pub fn p3_ext4_mul(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let u = P3Ext2::from_base_slice(&[P3Goldilocks::zero(), P3Goldilocks::one()]);
    let ((a0, a1), (b0, b1)) = (p3_ext4_split(a), p3_ext4_split(b));
    p3_ext4_join(a0 * b0 + u * a1 * b1, a0 * b1 + a1 * b0)
}

/// Reference `GoldilocksExt4` inverse through the norm to the quadratic extension (`0 -> 0`).
pub fn p3_ext4_inv(a: [u64; 4]) -> [u64; 4] {
    let u = P3Ext2::from_base_slice(&[P3Goldilocks::zero(), P3Goldilocks::one()]);
    let (a0, a1) = p3_ext4_split(a);
    match (a0 * a0 - u * a1 * a1).try_inverse() {
        Some(norm_inv) => p3_ext4_join(a0 * norm_inv, -(a1 * norm_inv)),
        None => [0; 4],
    }
}

/// Reference `GoldilocksExt4` power by square-and-multiply; `exp = p` is the Frobenius map.
pub fn p3_ext4_pow(mut base: [u64; 4], mut exp: u64) -> [u64; 4] {
    let mut acc = [1, 0, 0, 0];
    while exp > 0 {
        if exp & 1 == 1 {
            acc = p3_ext4_mul(acc, base);
        }
        base = p3_ext4_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// Reference AES / Rijndael $\mathbb{F}_{2}[x]/(x^8 + x^4 + x^3 + x + 1)$ (`0x11B`) byte multiplication.
#[inline]
pub const fn gf256_poly11b_mul(mut a: u8, mut b: u8) -> u8 {
    let mut p = 0u8;
    let mut i = 0;
    while i < 8 {
        if (b & 1) != 0 {
            p ^= a;
        }
        let hi = a & 0x80;
        a <<= 1;
        if hi != 0 {
            a ^= 0x1B;
        }
        b >>= 1;
        i += 1;
    }
    p
}

/// Multiplicative inverse in $\mathbb{F}_{2}[x]/(x^8 + x^4 + x^3 + x + 1)$ via $a^{254}$ (`0 -> 0`).
#[inline]
pub const fn gf256_poly11b_inv(a: u8) -> u8 {
    let mut acc = 1u8;
    let mut base = a;
    let mut exp = 254u8;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = gf256_poly11b_mul(acc, base);
        }
        base = gf256_poly11b_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// Intel `GF2P8AFFINEQB` byte map (`mat` is row-major MSB-to-LSB `u64` matching `GFNI_MAT_*`):
/// output bit `i` (`0..8`, LSB-first) is `parity(((mat >> (8 * (7 - i))) as u8) & x) ^ ((imm8 >> i) & 1)`.
#[inline]
pub const fn gfni_affine_byte(mat: u64, x: u8, imm8: u8) -> u8 {
    let mut out = 0u8;
    let mut i = 0usize;
    while i < 8 {
        let row = ((mat >> (8 * (7 - i))) & 0xFF) as u8;
        let parity = ((row & x).count_ones() & 1) as u8;
        out |= parity << i;
        i += 1;
    }
    out ^ imm8
}

/// Reference multiplication in $\mathbb{F}_2[z]/(z^{128} + z^7 + z^2 + z + 1)$ (`0x87`, LSB = coeff of $z^0$).
#[inline]
pub const fn gf2_128_poly87_mul_ref(mut a: u128, mut b: u128) -> u128 {
    let mut acc = 0u128;
    let mut i = 0;
    while i < 128 {
        if (b & 1) != 0 {
            acc ^= a;
        }
        let carry = (a >> 127) & 1;
        a <<= 1;
        if carry != 0 {
            a ^= 0x87;
        }
        b >>= 1;
        i += 1;
    }
    acc
}

/// Reference schoolbook negacyclic polynomial multiplication in $\mathbb{Z}_q[X]/(X^{256} + 1)$
/// for NIST FIPS 204 ML-DSA ($q = 8{,}380{,}417$).
pub fn mldsa_poly_mul_negacyclic_ref(a: &[i32; 256], b: &[i32; 256]) -> [i32; 256] {
    const Q: i64 = 8_380_417;
    let mut out = [0i64; 256];
    for i in 0..256 {
        let ai = (a[i] as i64).rem_euclid(Q);
        for j in 0..256 {
            let bj = (b[j] as i64).rem_euclid(Q);
            let prod = (ai * bj) % Q;
            if i + j < 256 {
                out[i + j] = (out[i + j] + prod).rem_euclid(Q);
            } else {
                out[i + j - 256] = (out[i + j - 256] - prod).rem_euclid(Q);
            }
        }
    }
    let mut res = [0i32; 256];
    for (dst, &v) in res.iter_mut().zip(out.iter()) {
        *dst = v as i32;
    }
    res
}

/// Reference Goldilocks multiplication in `u128` -> canonical `[0, p)`.
#[inline]
pub const fn goldilocks_mul_u128_ref(a: u64, b: u64) -> u64 {
    (((a as u128) * (b as u128)) % (GOLDILOCKS_P as u128)) as u64
}

/// NIST SP 800-185 §2.3.1 `left_encode(x)` integer encoding.
pub fn nist_left_encode(x: usize) -> Vec<u8> {
    if x == 0 {
        return vec![1u8, 0u8];
    }
    let be = (x as u64).to_be_bytes();
    let first_nz = be.iter().position(|&b| b != 0).unwrap_or(7);
    let slice = &be[first_nz..];
    let mut out = Vec::with_capacity(1 + slice.len());
    out.push(slice.len() as u8);
    out.extend_from_slice(slice);
    out
}

/// Unpadded NIST SP 800-185 §2.3.3 `bytepad` prefix `left_encode(136) || encode_string(N) || encode_string(S)`.
///
/// Note: upstream `tiny-keccak 2.0.2` has a known `fill_block()` bug (`debris/tiny-keccak#48`)
/// whenever this unpadded prefix is an exact multiple of `rate = 136` (e.g. `N = ""` and
/// `S.len() == 129` -> `2 + 2 + 3 + 129 = 136`, or `S.len() == 265` -> `272`), absorbing an
/// extraneous 136-byte zero block. Use [`cshake256_nist_sp800_185_ref`] for exact NIST SP 800-185
/// reference evaluation across all customization lengths.
pub fn cshake256_unpadded_prefix(name: &[u8], custom: &[u8]) -> Vec<u8> {
    let mut z = nist_left_encode(136);
    z.extend_from_slice(&nist_left_encode(name.len() * 8));
    z.extend_from_slice(name);
    z.extend_from_slice(&nist_left_encode(custom.len() * 8));
    z.extend_from_slice(custom);
    z
}

/// Exact NIST SP 800-185 §3.3 `cSHAKE256(X, L, N, S)` reference oracle built atop
/// `sha3::Shake256` (when `N` and `S` are both empty) and `tiny_keccak::keccakf` with strict
/// §2.3.3 `bytepad` (`while (len(z)/8) mod w != 0`).
pub fn cshake256_nist_sp800_185_ref(
    name: &[u8],
    custom: &[u8],
    input: &[u8],
    out_len: usize,
) -> Vec<u8> {
    const RATE: usize = 136;
    if name.is_empty() && custom.is_empty() {
        use sha3::digest::{ExtendableOutput, Update, XofReader};
        let mut s = sha3::Shake256::default();
        s.update(input);
        let mut out = vec![0u8; out_len];
        s.finalize_xof().read(&mut out);
        return out;
    }

    let mut stream = cshake256_unpadded_prefix(name, custom);
    if !stream.len().is_multiple_of(RATE) {
        let pad = RATE - (stream.len() % RATE);
        stream.resize(stream.len() + pad, 0u8);
    }
    stream.extend_from_slice(input);

    let mut state = [0u64; 25];
    let full_blocks = stream.len() / RATE;
    for blk in 0..full_blocks {
        let chunk = &stream[blk * RATE..(blk + 1) * RATE];
        for (lane, word_slot) in state.iter_mut().take(17).enumerate() {
            let word = u64::from_le_bytes(chunk[lane * 8..(lane + 1) * 8].try_into().unwrap());
            *word_slot ^= word;
        }
        tiny_keccak::keccakf(&mut state);
    }

    let rem = &stream[full_blocks * RATE..];
    let mut last_block = [0u8; RATE];
    last_block[..rem.len()].copy_from_slice(rem);
    last_block[rem.len()] ^= 0x04;
    last_block[RATE - 1] ^= 0x80;
    for (lane, word_slot) in state.iter_mut().take(17).enumerate() {
        let word = u64::from_le_bytes(last_block[lane * 8..(lane + 1) * 8].try_into().unwrap());
        *word_slot ^= word;
    }
    tiny_keccak::keccakf(&mut state);

    let mut out = Vec::with_capacity(out_len);
    while out.len() < out_len {
        for &lane_word in state.iter().take(17) {
            let bytes = lane_word.to_le_bytes();
            let take = (out_len - out.len()).min(8);
            out.extend_from_slice(&bytes[..take]);
            if out.len() == out_len {
                break;
            }
        }
        if out.len() < out_len {
            tiny_keccak::keccakf(&mut state);
        }
    }
    out
}
