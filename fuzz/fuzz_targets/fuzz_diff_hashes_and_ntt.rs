// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided differential fuzzer cross-checking `qsag-asm`, `qsag-accel`, `qsag-core`,
//! and `qsag-agg` hardware/SIMD kernels (`AVX-512` 8-way Keccak, `SHA-NI` SHA-256, `GFNI`
//! `GF(2^8)`, `VPCLMULQDQ` `GF(2^128)`, `AVX-512` Seiler `ML-DSA` NTT, and `BMI2/ADX`
//! `Goldilocks`) against independent references on arbitrary fuzzer-synthesized inputs and
//! slice alignments.
//!
//! References: `sha2`, `sha3`, `tiny-keccak`, `ghash` and `p3-goldilocks`, plus three written
//! here from the specifications: an SP 800-185 `cSHAKE256` over the raw Keccak permutation
//! (`tiny-keccak` 2.0.2 double-permutes when the `bytepad` header is a multiple of the rate),
//! a schoolbook product in `Z_q[X]/(X^256 + 1)`, and `u128` arithmetic for Goldilocks and its
//! quadratic and quartic extensions, written as `F_p[u]/(u^2 - 7)` and `F_p[v]/(v^4 - 7)`.

use arbitrary::Arbitrary;
use ghash::universal_hash::{KeyInit, UniversalHash};
use libfuzzer_sys::fuzz_target;
use p3_field::{AbstractField, Field as P3Field, PrimeField64};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use qsag_accel::goldilocks as accel_gl;
use qsag_accel::keccak::{cshake256_framed_xof, keccak256, sha3_256, shake256_xof};
use qsag_accel::sha2::sha256;
use qsag_agg::field::GoldilocksExt4;
use qsag_asm::{
    SimdBackend, detect_backend, gf2_128_dot_with_backend, gf256_shamir_mac_with_backend,
    goldilocks_add_ct, goldilocks_dot2_ct, goldilocks_mul_ct, goldilocks_mul_ct_with_backend,
    goldilocks_pow7_ct, goldilocks_pow7_ct_with_backend, goldilocks_sub_ct, keccak_f1600_batch,
    mldsa_inv_ntt_with_backend, mldsa_ntt_with_backend, mldsa_pointwise_mul_with_backend,
    sha256_compress_blocks,
};
use qsag_core::field::goldilocks::{Goldilocks as CoreGl, GoldilocksExt2};
use qsag_core::field::tower::TowerGf256;
use sha2::Digest as _;
use tiny_keccak::{CShake, Hasher as _, Shake as TinyShake, Xof as _};

const MLDSA_Q: u32 = 8_380_417;
const P: u64 = 0xFFFF_FFFF_0000_0001;
const P128: u128 = P as u128;

/// Operand values at which a 64-bit Goldilocks implementation changes behaviour.
const GL_EDGES: [u64; 16] = [
    0,
    1,
    2,
    7,
    (1 << 32) - 1,
    1 << 32,
    (1 << 32) + 1,
    P - 2,
    P - 1,
    P,
    P + 1,
    P + 2,
    u64::MAX - (1 << 32),
    u64::MAX - 1,
    u64::MAX,
    1 << 63,
];

/// One raw 64-bit operand. `class` steers it into the alias band `[p, 2^64)`, which a
/// uniform word reaches with probability `2^-32`, or onto an edge value.
#[derive(Arbitrary, Debug, Clone, Copy)]
struct GlWord {
    raw: u64,
    class: u8,
}

impl GlWord {
    fn value(self) -> u64 {
        match self.class & 3 {
            0 => self.raw,
            // `2^64 - p = 2^32 - 1` aliases.
            1 => P + self.raw % ((1 << 32) - 1),
            2 => GL_EDGES[(self.raw % GL_EDGES.len() as u64) as usize],
            _ => self.raw % P,
        }
    }
}

#[derive(Arbitrary, Debug)]
struct DiffFuzzInput {
    poly_a: [u32; 256],
    poly_b: [u32; 256],
    unalign_pad: u8,
    shake_out_len: u16,
    gf_scalar: u8,
    custom_len_class: u8,
    gl_words: Vec<[GlWord; 4]>,
    gf128_pairs: Vec<([u8; 16], [u8; 16])>,
    custom: Vec<u8>,
    payload: Vec<u8>,
}

// ---------------------------------------------------------------------------------------
// SP 800-185 cSHAKE256 over the raw Keccak-f[1600] permutation
// ---------------------------------------------------------------------------------------

const RATE: usize = 136;

/// `left_encode(x)`: the minimal big-endian bytes of `x`, preceded by their count.
fn left_encode(x: u64) -> Vec<u8> {
    let be = x.to_be_bytes();
    let skip = be.iter().take_while(|&&b| b == 0).count().min(7);
    let mut out = vec![(8 - skip) as u8];
    out.extend_from_slice(&be[skip..]);
    out
}

/// `encode_string(s) = left_encode(bit length of s) || s`.
fn encode_string(s: &[u8]) -> Vec<u8> {
    let mut out = left_encode(8 * s.len() as u64);
    out.extend_from_slice(s);
    out
}

fn xor_block(state: &mut [u64; 25], block: &[u8]) {
    for (lane, chunk) in state.iter_mut().zip(block.chunks(8)) {
        let mut word = [0u8; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        *lane ^= u64::from_le_bytes(word);
    }
}

/// Sponge with rate 136 over `tiny_keccak::keccakf`, final `suffix` byte and `0x80`.
fn keccak_sponge_256(input: &[u8], suffix: u8, out: &mut [u8]) {
    let mut state = [0u64; 25];
    let mut blocks = input.chunks_exact(RATE);
    for block in &mut blocks {
        xor_block(&mut state, block);
        tiny_keccak::keccakf(&mut state);
    }
    let mut last = [0u8; RATE];
    let tail = blocks.remainder();
    last[..tail.len()].copy_from_slice(tail);
    last[tail.len()] ^= suffix;
    last[RATE - 1] ^= 0x80;
    xor_block(&mut state, &last);
    tiny_keccak::keccakf(&mut state);
    let mut squeezed = out.chunks_mut(RATE).peekable();
    while let Some(chunk) = squeezed.next() {
        for (bytes, lane) in chunk.chunks_mut(8).zip(&state) {
            bytes.copy_from_slice(&lane.to_le_bytes()[..bytes.len()]);
        }
        if squeezed.peek().is_some() {
            tiny_keccak::keccakf(&mut state);
        }
    }
}

/// `cSHAKE256(X, L, N = "", S)`. With both strings empty it is `SHAKE256(X, L)`.
fn cshake256_sp800_185(customization: &[u8], x: &[u8], out: &mut [u8]) {
    if customization.is_empty() {
        return keccak_sponge_256(x, 0x1F, out);
    }
    let mut input = left_encode(RATE as u64);
    input.extend_from_slice(&encode_string(b""));
    input.extend_from_slice(&encode_string(customization));
    input.resize(input.len().next_multiple_of(RATE), 0);
    input.extend_from_slice(x);
    keccak_sponge_256(&input, 0x04, out);
}

// ---------------------------------------------------------------------------------------
// Goldilocks references in `u128`
// ---------------------------------------------------------------------------------------

fn r_add(a: u64, b: u64) -> u64 {
    ((a as u128 + b as u128) % P128) as u64
}
fn r_sub(a: u64, b: u64) -> u64 {
    ((a as u128 % P128 + P128 - b as u128 % P128) % P128) as u64
}
fn r_mul(a: u64, b: u64) -> u64 {
    ((a as u128 % P128) * (b as u128 % P128) % P128) as u64
}
fn r_pow7(a: u64) -> u64 {
    (0..6).fold(a % P, |acc, _| r_mul(acc, a))
}

/// Product in `F_p[x]/(x^N - 7)`: `N = 2` is the quadratic extension in basis `(1, u)`,
/// `N = 4` the quartic extension in basis `(1, v, v^2, v^3)`.
fn r_binomial_mul<const N: usize>(a: [u64; N], b: [u64; N]) -> [u64; N] {
    let mut out = [0u64; N];
    for i in 0..N {
        for j in 0..N {
            let term = r_mul(a[i], b[j]);
            if i + j < N {
                out[i + j] = r_add(out[i + j], term);
            } else {
                out[i + j - N] = r_add(out[i + j - N], r_mul(7, term));
            }
        }
    }
    out
}

/// Tower limbs `(c0.c0, c0.c1, c1.c0, c1.c1)` hold `l0 + l1 u + l2 v + l3 u v` with
/// `u = v^2`: the coefficients of `1, v, v^2, v^3` are `l0, l2, l1, l3`.
fn tower_to_powers(l: [u64; 4]) -> [u64; 4] {
    [l[0], l[2], l[1], l[3]]
}

fn ext4_of(l: [u64; 4]) -> GoldilocksExt4 {
    GoldilocksExt4::from_limbs(l.map(CoreGl::from_u64_reduced))
}

fn ext4_powers(x: GoldilocksExt4) -> [u64; 4] {
    tower_to_powers(x.to_limbs().map(CoreGl::to_canonical_u64))
}

fn ext2_of(l: [u64; 2]) -> GoldilocksExt2 {
    GoldilocksExt2::new(CoreGl::from_u64_reduced(l[0]), CoreGl::from_u64_reduced(l[1]))
}

fn ext2_limbs(x: GoldilocksExt2) -> [u64; 2] {
    [x.c0.to_canonical_u64(), x.c1.to_canonical_u64()]
}

fn check_goldilocks_base(a: u64, b: u64, backend: SimdBackend) {
    let (sum, diff, prod, seventh) = (r_add(a, b), r_sub(a, b), r_mul(a, b), r_pow7(a));

    // Plonky3 on the reduced operands agrees with the `u128` reference.
    let (pa, pb) = (
        P3Goldilocks::from_canonical_u64(a % P),
        P3Goldilocks::from_canonical_u64(b % P),
    );
    assert_eq!((pa + pb).as_canonical_u64(), sum);
    assert_eq!((pa - pb).as_canonical_u64(), diff);
    assert_eq!((pa * pb).as_canonical_u64(), prod);
    assert_eq!(pa.exp_u64(7).as_canonical_u64(), seventh);

    // `qsag-asm` kernels take the raw words.
    assert_eq!(goldilocks_add_ct(a, b), sum, "asm add {a:#x} {b:#x}");
    assert_eq!(goldilocks_sub_ct(a, b), diff, "asm sub {a:#x} {b:#x}");
    assert_eq!(goldilocks_mul_ct(a, b), prod, "asm mul {a:#x} {b:#x}");
    assert_eq!(goldilocks_pow7_ct(a), seventh, "asm pow7 {a:#x}");
    for be in [backend, SimdBackend::Portable] {
        assert_eq!(goldilocks_mul_ct_with_backend(a, b, be), prod, "{be:?}");
        assert_eq!(goldilocks_pow7_ct_with_backend(a, be), seventh, "{be:?}");
    }

    // `qsag-accel` scalar field, documented canonical for every `u64` input.
    assert_eq!(accel_gl::gl_reduce_u64(a), a % P);
    assert_eq!(accel_gl::gl_is_canonical(a), a < P);
    assert_eq!(accel_gl::gl_add(a, b), sum);
    assert_eq!(accel_gl::gl_sub(a, b), diff);
    assert_eq!(accel_gl::gl_neg(a), r_sub(0, a));
    assert_eq!(accel_gl::gl_mul(a, b), prod);
    assert_eq!(accel_gl::gl_sq(a), r_mul(a, a));
    assert_eq!(accel_gl::gl_reduce128((a as u128) << 64 | b as u128), {
        (((a as u128) << 64 | b as u128) % P128) as u64
    });
    let accel_inv = accel_gl::gl_inv_or_zero(a);
    assert!(accel_inv < P);
    assert_eq!(r_mul(a, accel_inv), u64::from(a % P != 0));

    // `qsag-core` field element built from the raw word.
    let (qa, qb) = (CoreGl::from_u64_reduced(a), CoreGl::from_u64_reduced(b));
    assert_eq!(qa.to_canonical_u64(), a % P);
    assert_eq!(CoreGl::from_canonical(a).is_ok(), a < P);
    assert_eq!((qa + qb).to_canonical_u64(), sum);
    assert_eq!((qa - qb).to_canonical_u64(), diff);
    assert_eq!((qa * qb).to_canonical_u64(), prod);
    assert_eq!((-qa).to_canonical_u64(), r_sub(0, a));
    assert_eq!(qa.pow(7).to_canonical_u64(), seventh);
    assert_eq!(qa.square().to_canonical_u64(), r_mul(a, a));
    assert_eq!(qa.mul_by_7().to_canonical_u64(), r_mul(7, a));
    let wide = (a as u128) << 64 | b as u128;
    assert_eq!(CoreGl::reduce128(wide).to_canonical_u64(), (wide % P128) as u64);
    assert_eq!(CoreGl::from_u128_reduced(wide).to_canonical_u64(), (wide % P128) as u64);
    let core_inv = qa.inv().to_canonical_u64();
    assert_eq!(r_mul(a, core_inv), u64::from(a % P != 0));
    assert_eq!(
        core_inv,
        pa.try_inverse().map_or(0, |v| v.as_canonical_u64())
    );
}

fn check_goldilocks_extensions(w: [u64; 4], x: [u64; 4]) {
    // `a0 * b0 + a1 * b1` on raw words.
    assert_eq!(
        goldilocks_dot2_ct(w[0], x[0], w[1], x[1]),
        r_add(r_mul(w[0], x[0]), r_mul(w[1], x[1])),
        "asm dot2 {w:#x?} {x:#x?}"
    );

    // Quadratic extension: `qsag-core` type and `qsag-accel` limb pairs.
    let (a2, b2) = ([w[0], w[1]], [x[0], x[1]]);
    let (ra2, rb2) = (a2.map(|v| v % P), b2.map(|v| v % P));
    let (ea, eb) = (ext2_of(a2), ext2_of(b2));
    let prod2 = r_binomial_mul(ra2, rb2);
    let sum2 = [r_add(a2[0], b2[0]), r_add(a2[1], b2[1])];
    let diff2 = [r_sub(a2[0], b2[0]), r_sub(a2[1], b2[1])];
    assert_eq!(ext2_limbs(ea + eb), sum2);
    assert_eq!(ext2_limbs(ea - eb), diff2);
    assert_eq!(ext2_limbs(ea * eb), prod2);
    assert_eq!(ext2_limbs(ea.square()), r_binomial_mul(ra2, ra2));
    assert_eq!(ext2_limbs(ea.mul_base(CoreGl::from_u64_reduced(x[2]))), {
        [r_mul(a2[0], x[2]), r_mul(a2[1], x[2])]
    });
    let is_zero2 = ra2 == [0, 0];
    match ea.inv() {
        Some(inv) => {
            assert!(!is_zero2);
            assert_eq!(r_binomial_mul(ra2, ext2_limbs(inv)), [1, 0]);
        }
        None => assert!(is_zero2),
    }
    assert_eq!(accel_gl::ext2_add(a2, b2), sum2);
    assert_eq!(accel_gl::ext2_sub(a2, b2), diff2);
    assert_eq!(accel_gl::ext2_mul(a2, b2), prod2);
    assert_eq!(accel_gl::ext2_neg(a2), [r_sub(0, a2[0]), r_sub(0, a2[1])]);
    let accel_inv2 = accel_gl::ext2_inv_or_zero(a2);
    assert_eq!(
        r_binomial_mul(ra2, accel_inv2),
        [u64::from(!is_zero2), 0]
    );

    // Quartic extension against the schoolbook product in `F_p[v]/(v^4 - 7)`.
    let (a4, b4) = (ext4_of(w), ext4_of(x));
    let (pa4, pb4) = (
        tower_to_powers(w.map(|v| v % P)),
        tower_to_powers(x.map(|v| v % P)),
    );
    let prod4 = r_binomial_mul(pa4, pb4);
    assert_eq!(ext4_powers(a4 + b4), core::array::from_fn(|i| r_add(pa4[i], pb4[i])));
    assert_eq!(ext4_powers(a4 - b4), core::array::from_fn(|i| r_sub(pa4[i], pb4[i])));
    assert_eq!(ext4_powers(-a4), pa4.map(|v| r_sub(0, v)));
    assert_eq!(ext4_powers(a4 * b4), prod4);
    assert_eq!(ext4_powers(a4.square()), r_binomial_mul(pa4, pa4));
    assert_eq!(
        ext4_powers(a4.mul_add(b4, a4)),
        core::array::from_fn(|i| r_add(prod4[i], pa4[i]))
    );
    assert_eq!(
        ext4_powers(a4.mul_base(CoreGl::from_u64_reduced(x[0]))),
        pa4.map(|v| r_mul(v, x[0]))
    );
    let seventh4 = (0..6).fold(pa4, |acc, _| r_binomial_mul(acc, pa4));
    assert_eq!(ext4_powers(a4.pow(7)), seventh4);
    let is_zero4 = pa4 == [0; 4];
    assert_eq!(a4.is_zero(), is_zero4);
    assert_eq!(
        r_binomial_mul(pa4, ext4_powers(a4.inv())),
        [u64::from(!is_zero4), 0, 0, 0]
    );
    // Canonical 32-byte codec of the element.
    assert_eq!(GoldilocksExt4::from_le_bytes_canonical(a4.to_le_bytes()), Some(a4));
}

/// `a * b` in `Z_q[X]/(X^256 + 1)`.
fn negacyclic_product(a: &[u32; 256], b: &[u32; 256]) -> [u32; 256] {
    let q = u64::from(MLDSA_Q);
    let mut out = [0u64; 256];
    for i in 0..256 {
        for j in 0..256 {
            let term = u64::from(a[i]) * u64::from(b[j]) % q;
            if i + j < 256 {
                out[i + j] = (out[i + j] + term) % q;
            } else {
                out[i + j - 256] = (out[i + j - 256] + q - term) % q;
            }
        }
    }
    out.map(|v| v as u32)
}

fuzz_target!(|input: DiffFuzzInput| {
    // 1. Unaligned buffer slice for sponges & SHA-NI
    let pad = (input.unalign_pad as usize) & 15;
    let payload_cap = input.payload.len().min(4096);
    let mut aligned_buf = vec![0xA5u8; pad + payload_cap];
    aligned_buf[pad..pad + payload_cap].copy_from_slice(&input.payload[..payload_cap]);
    let msg = &aligned_buf[pad..pad + payload_cap];

    // 2. SHA-256 (`SHA-NI`) vs RustCrypto `sha2::Sha256`
    let exp_sha256: [u8; 32] = sha2::Sha256::digest(msg).into();
    assert_eq!(sha256(msg), exp_sha256);
    if msg.len() >= 64 {
        let n_blocks = msg.len() / 64;
        let blocks: &[[u8; 64]] = msg[..n_blocks * 64].as_chunks::<64>().0;
        let mut st_hw = [
            0x6a09e667u32,
            0xbb67ae85,
            0x3c6ef372,
            0xa54ff53a,
            0x510e527f,
            0x9b05688c,
            0x1f83d9ab,
            0x5be0cd19,
        ];
        let mut st_port = st_hw;
        sha256_compress_blocks(&mut st_hw, blocks);
        qsag_asm::sha256_compress_blocks_portable(&mut st_port, blocks);
        assert_eq!(st_hw, st_port);
    }

    // 3. `SHA3-256`, `Keccak-256`, `SHAKE256`, and `cSHAKE256` vs `sha3` & `tiny-keccak`
    let exp_sha3: [u8; 32] = sha3::Sha3_256::digest(msg).into();
    let exp_keccak: [u8; 32] = sha3::Keccak256::digest(msg).into();
    assert_eq!(sha3_256(msg), exp_sha3);
    assert_eq!(keccak256(msg), exp_keccak);

    let out_len = (input.shake_out_len as usize) % 545;
    let mut q_shake = vec![0u8; out_len];
    shake256_xof(msg, &mut q_shake);
    let mut tk_shake = TinyShake::v256();
    tk_shake.update(msg);
    let mut u_shake = vec![0u8; out_len];
    tk_shake.squeeze(&mut u_shake);
    assert_eq!(q_shake, u_shake);

    // Customization string of up to 300 bytes. Two classes pin its length to 129 and 265,
    // where the unpadded `bytepad` header is exactly one and two rate blocks.
    let mut custom = input.custom[..input.custom.len().min(300)].to_vec();
    let pinned_len = match input.custom_len_class & 3 {
        1 => Some(129),
        2 => Some(265),
        _ => None,
    };
    if let Some(len) = pinned_len {
        let filler = msg.iter().copied().chain(core::iter::repeat(0x3C));
        custom.extend(filler.take(len.saturating_sub(custom.len())));
        custom.truncate(len);
    }
    let custom = custom.as_slice();
    let mut q_cshake = vec![0u8; out_len];
    cshake256_framed_xof(custom, &[msg], &mut q_cshake);
    let mut framed_u64 = Vec::with_capacity(16 + msg.len());
    framed_u64.extend_from_slice(&(1u64).to_le_bytes());
    framed_u64.extend_from_slice(&(msg.len() as u64).to_le_bytes());
    framed_u64.extend_from_slice(msg);
    assert_eq!(
        qsag_core::sponge::keccak::cshake256_xof(out_len, custom, &framed_u64),
        q_cshake
    );
    // Every customization length, including 129 and 265, against SP 800-185 assembled here.
    let mut spec_cshake = vec![0u8; out_len];
    cshake256_sp800_185(custom, &framed_u64, &mut spec_cshake);
    assert_eq!(q_cshake, spec_cshake, "cSHAKE256, |S| = {}", custom.len());
    // Verify multi-lane Keccak batch (`1..=17`) agrees with `tiny_keccak::keccakf`
    let batch_n = 1 + (pad % 17);
    let mut states = vec![[0u64; 25]; batch_n];
    for (idx, st) in states.iter_mut().enumerate() {
        for (lane, w) in st.iter_mut().enumerate() {
            let b = msg.get((idx * 25 + lane) % msg.len().max(1)).copied().unwrap_or(0);
            *w = (b as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ ((idx * 31 + lane) as u64);
        }
    }
    let mut ref_states = states.clone();
    keccak_f1600_batch(&mut states);
    for st in &mut ref_states {
        tiny_keccak::keccakf(st);
    }
    assert_eq!(states, ref_states);
    // Upstream `tiny-keccak 2.0.2` has a known `fill_block()` double-permutation bug
    // (`debris/tiny-keccak#48`) when the unpadded `bytepad` header is an exact multiple of 136
    // (`custom.len() == 129` -> 136B, `custom.len() == 265` -> 272B). Those two lengths are
    // covered by the SP 800-185 reference above; `tiny-keccak` is a second witness elsewhere.
    let s_hdr_len = if custom.len() * 8 < 256 { 2 } else { 3 };
    let unpadded_bytepad_len = 2 + 2 + s_hdr_len + custom.len();
    if custom.is_empty() || !unpadded_bytepad_len.is_multiple_of(136) {
        let mut tk_cs = CShake::v256(b"", custom);
        tk_cs.update(&framed_u64);
        let mut exp_cshake = vec![0u8; out_len];
        tk_cs.squeeze(&mut exp_cshake);
        assert_eq!(q_cshake, exp_cshake);
    }

    // 4. `GFNI` / `vpshufb` `GF(2^8)` SIMD MAC vs `TowerGf256` scalar algebra
    let backend = detect_backend();
    let mut dst_simd = msg.to_vec();
    let mut dst_ref = msg.to_vec();
    let src: Vec<u8> = msg.iter().map(|&b| b.wrapping_mul(17) ^ 0x5A).collect();
    gf256_shamir_mac_with_backend(&mut dst_simd, &src, input.gf_scalar, backend);
    for (d, &s) in dst_ref.iter_mut().zip(&src) {
        *d ^= TowerGf256(s).mul(TowerGf256(input.gf_scalar)).0;
    }
    assert_eq!(dst_simd, dst_ref);

    // 5. `VPCLMULQDQ` `GF(2^128)` dot product vs RustCrypto `ghash::GHash`
    let n128 = input.gf128_pairs.len().min(33);
    let mut vec_a = Vec::with_capacity(n128);
    let mut vec_b = Vec::with_capacity(n128);
    let mut exp_dot = 0u128;
    for &(ab, bb) in &input.gf128_pairs[..n128] {
        let a = u128::from_le_bytes(ab);
        let b = u128::from_le_bytes(bb);
        vec_a.push(a);
        vec_b.push(b);
        let mut gh = ghash::GHash::new(&a.reverse_bits().to_be_bytes().into());
        gh.update(&[b.reverse_bits().to_be_bytes().into()]);
        let prod_be: [u8; 16] = gh.finalize().into();
        exp_dot ^= u128::from_be_bytes(prod_be).reverse_bits();
    }
    assert_eq!(gf2_128_dot_with_backend(&vec_a, &vec_b, backend), exp_dot);
    assert_eq!(
        gf2_128_dot_with_backend(&vec_a, &vec_b, SimdBackend::Portable),
        exp_dot
    );

    // 6. `AVX-512` Seiler `ML-DSA` NTT: all 256 coefficients of both operands come from the
    //    input. Backends agree with each other, the transform inverts, and the transform-domain
    //    product is the schoolbook product in `Z_q[X]/(X^256 + 1)`.
    let mut pa = input.poly_a.map(|c| c % MLDSA_Q);
    let mut pb = input.poly_b.map(|c| c % MLDSA_Q);
    let (orig_a, orig_b) = (pa, pb);
    let mut pa_port = pa;
    let mut pb_port = pb;
    mldsa_ntt_with_backend(&mut pa, backend);
    mldsa_ntt_with_backend(&mut pb, backend);
    mldsa_ntt_with_backend(&mut pa_port, SimdBackend::Portable);
    mldsa_ntt_with_backend(&mut pb_port, SimdBackend::Portable);
    assert_eq!(pa, pa_port);
    assert_eq!(pb, pb_port);

    let mut prod_simd = [0u32; 256];
    let mut prod_port = [0u32; 256];
    mldsa_pointwise_mul_with_backend(&mut prod_simd, &pa, &pb, backend);
    mldsa_pointwise_mul_with_backend(&mut prod_port, &pa_port, &pb_port, SimdBackend::Portable);
    mldsa_inv_ntt_with_backend(&mut prod_simd, backend);
    mldsa_inv_ntt_with_backend(&mut prod_port, SimdBackend::Portable);
    assert_eq!(prod_simd, prod_port);
    assert_eq!(prod_simd, negacyclic_product(&orig_a, &orig_b));

    mldsa_inv_ntt_with_backend(&mut pa, backend);
    assert_eq!(pa, orig_a);
    mldsa_inv_ntt_with_backend(&mut pb_port, SimdBackend::Portable);
    assert_eq!(pb_port, orig_b);

    // 7. Goldilocks and its extensions on raw 64-bit words, including `[p, 2^64)`.
    for (i, &edge) in GL_EDGES.iter().enumerate() {
        check_goldilocks_base(edge, GL_EDGES[(i + pad) % GL_EDGES.len()], backend);
    }
    for words in input.gl_words.iter().take(48) {
        let w = words.map(GlWord::value);
        check_goldilocks_base(w[0], w[1], backend);
        check_goldilocks_base(w[2], w[3], backend);
        let x = [w[2], w[3], w[0] ^ w[3], w[1].wrapping_add(w[2])];
        check_goldilocks_extensions(w, x);
        check_goldilocks_extensions(x, w);
    }
});
