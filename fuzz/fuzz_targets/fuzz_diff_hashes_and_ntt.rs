// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided differential fuzzer cross-checking `qsag-asm`, `qsag-accel`, `qsag-core`,
//! and `qsag-agg` hardware/SIMD kernels (`AVX-512` 8-way Keccak, `SHA-NI` SHA-256, `GFNI`
//! `GF(2^8)`, `VPCLMULQDQ` `GF(2^128)`, `AVX-512` Seiler `ML-DSA` NTT, and `BMI2/ADX`
//! `Goldilocks`) against independent upstream crates (`sha3`, `tiny-keccak`, `sha2`, `ghash`,
//! and `p3-goldilocks`) on arbitrary fuzzer-synthesized inputs and slice alignments.

use arbitrary::Arbitrary;
use ghash::universal_hash::{KeyInit, UniversalHash};
use libfuzzer_sys::fuzz_target;
use p3_field::{AbstractField, Field as P3Field, PrimeField64};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use qsag_accel::keccak::{cshake256_framed_xof, keccak256, sha3_256, shake256_xof};
use qsag_accel::sha2::sha256;
use qsag_asm::{
    SimdBackend, detect_backend, gf2_128_dot_with_backend, gf256_shamir_mac_with_backend,
    goldilocks_mul_ct, keccak_f1600_batch, mldsa_inv_ntt_with_backend, mldsa_ntt_with_backend,
    mldsa_pointwise_mul_with_backend, sha256_compress_blocks,
};
use qsag_core::field::goldilocks::Goldilocks as CoreGl;
use qsag_core::field::tower::TowerGf256;
use sha2::Digest as _;
use tiny_keccak::{CShake, Hasher as _, Shake as TinyShake, Xof as _};

const MLDSA_Q: u32 = 8_380_417;

#[derive(Arbitrary, Debug)]
struct DiffFuzzInput {
    unalign_pad: u8,
    shake_out_len: u16,
    gf_scalar: u8,
    custom: Vec<u8>,
    payload: Vec<u8>,
    poly_a: [u32; 32],
    poly_b: [u32; 32],
    gl_pairs: Vec<(u64, u64)>,
    gf128_pairs: Vec<([u8; 16], [u8; 16])>,
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

    let custom = &input.custom[..input.custom.len().min(300)];
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
    // (`custom.len() == 129` -> 136B, `custom.len() == 265` -> 272B). Cross-check `tiny-keccak`
    // everywhere outside those two buggy upstream lengths.
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

    // 6. `AVX-512` Seiler `ML-DSA` NTT roundtrip + convolution vs portable backend
    let mut pa = [0u32; 256];
    let mut pb = [0u32; 256];
    for i in 0..256 {
        pa[i] = input.poly_a[i % 32].wrapping_add((i as u32) * 1021) % MLDSA_Q;
        pb[i] = input.poly_b[i % 32].wrapping_add((i as u32) * 4093) % MLDSA_Q;
    }
    let orig_a = pa;
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

    mldsa_inv_ntt_with_backend(&mut pa, backend);
    assert_eq!(pa, orig_a);

    // 7. `BMI2/ADX` Goldilocks vs Plonky3 `p3-goldilocks`
    for &(a_raw, b_raw) in input.gl_pairs.iter().take(64) {
        let qa = CoreGl::from_u64_reduced(a_raw);
        let qb = CoreGl::from_u64_reduced(b_raw);
        let pa_gl = P3Goldilocks::from_canonical_u64(a_raw % 0xFFFF_FFFF_0000_0001);
        let pb_gl = P3Goldilocks::from_canonical_u64(b_raw % 0xFFFF_FFFF_0000_0001);
        let q_mul = (qa * qb).to_canonical_u64();
        let asm_mul = goldilocks_mul_ct(qa.to_canonical_u64(), qb.to_canonical_u64());
        let p3_mul = (pa_gl * pb_gl).as_canonical_u64();
        assert_eq!(q_mul, p3_mul);
        assert_eq!(asm_mul, p3_mul);
        assert_eq!(
            qa.inv().to_canonical_u64(),
            pa_gl.try_inverse().map_or(0, |v| v.as_canonical_u64())
        );
    }
});
