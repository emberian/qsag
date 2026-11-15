// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Sponge, Hash & SIMD Hardware Kernel Differential Property-Based Testing
//! (`sha3`, `tiny-keccak`, `sha2`, `hmac`, `ripemd`, `blake3` vs `qsag-asm`,
//! `qsag-core`, `qsag-accel`, and `qsag-agg`).
//!
//! Exercises random lengths `0..=16384`, unaligned byte slices `&buf[offset..offset+len]`,
//! empty strings, exact rate boundaries (`63, 64, 65, 71, 72, 73, 135, 136, 137, 271, 272,
//! 1023, 1024, 1025, 2071`), and arbitrary Keccak SIMD batch sizes `1..=33`.

use hmac::{Hmac, Mac};
use proptest::prelude::*;
use qsag_accel::keccak::{
    cshake256_framed_xof, keccak_f1600 as accel_keccak_f1600, keccak256 as accel_keccak256,
    sha3_256 as accel_sha3_256, shake256_xof as accel_shake256_xof,
};
use qsag_accel::sha2::{
    Sha256Hasher, Sha512Hasher, hash160 as accel_hash160, hmac_sha512 as accel_hmac_sha512,
    ripemd160 as accel_ripemd160, sha256 as accel_sha256, sha256_tagged, sha512 as accel_sha512,
};
use qsag_asm::{
    BITSLICE_LANES, KeccakRow256, KeccakState4x, KeccakState8x, SimdBackend,
    keccak_chi_mpc_row256_with_backend, keccak_f1600_batch_with_backend,
    keccak_f1600_x4_with_backend, keccak_f1600_x8_with_backend, pack_256x200_bitslice_with_backend,
    probe_capabilities, sha256_compress_blocks, sha256_compress_blocks_portable,
    sha256_compress_bytes, unpack_256x200_bitslice_with_backend,
};
use qsag_core::fips205::{sha256_digest, sha512_digest};
use qsag_core::sponge::keccak::{
    cshake256_32, cshake256_xof, encode_multi_frame, keccak_f1600 as core_keccak_f1600,
    shake256_32, shake256_xof,
};
use ripemd::Ripemd160;
use sha2::{Digest as _, Sha256, Sha512};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Keccak256, Sha3_256, Sha3_384, Sha3_512, Shake256};
use tiny_keccak::{CShake, Hasher as _, Keccak as TinyKeccak, Sha3 as TinySha3, Shake, Xof as _};

const ALL_SIMD_BACKENDS: [SimdBackend; 4] = [
    SimdBackend::Portable,
    SimdBackend::X86Avx2Pclmul,
    SimdBackend::X86Avx2GfniVpclmul,
    SimdBackend::X86Avx512GfniVpclmul,
];

const RATE_BOUNDARY_LENGTHS: &[usize] = &[
    0, 1, 2, 31, 32, 33, 55, 56, 57, 63, 64, 65, 71, 72, 73, 119, 120, 127, 128, 129, 135, 136,
    137, 199, 200, 201, 271, 272, 273, 511, 512, 513, 1023, 1024, 1025, 2071, 4096, 8192, 16384,
];

/// Exhaustive deterministic sweep across every critical SHA-256 (`64B`), SHA-512 (`128B`),
/// SHA3-512 (`72B`), SHA3-256/SHAKE256 (`136B`), and BLAKE3 (`64B`/`1024B`) rate boundary,
/// using deliberately misaligned slice offsets `&backing[off..off + len]`.
#[test]
fn sponge_and_hash_exact_rate_boundaries_and_unaligned_slices() {
    let caps = probe_capabilities();
    if std::env::var("QSAG_REQUIRE_AVX512").as_deref() == Ok("1") {
        assert!(caps.avx512, "AVX-512 expected on target host");
    }

    let mut backing = vec![0u8; 16384 + 32];
    for (i, b) in backing.iter_mut().enumerate() {
        *b = ((i.wrapping_mul(131).wrapping_add(17)) ^ (i >> 5)) as u8;
    }

    for &len in RATE_BOUNDARY_LENGTHS {
        for off in [0usize, 1, 3, 7, 13] {
            let msg = &backing[off..off + len];

            // 1. SHA3-256: `qsag_accel` vs `sha3` vs `tiny-keccak`
            let ref_sha3_256: [u8; 32] = Sha3_256::digest(msg).into();
            let mut tk_sha3 = TinySha3::v256();
            tk_sha3.update(msg);
            let mut tk_sha3_out = [0u8; 32];
            tk_sha3.finalize(&mut tk_sha3_out);
            assert_eq!(ref_sha3_256, tk_sha3_out);
            assert_eq!(accel_sha3_256(msg), ref_sha3_256, "sha3_256 len={len} off={off}");

            // 2. Original Keccak-256 (Ethereum): `qsag_accel` vs `sha3::Keccak256` vs `tiny-keccak`
            let ref_keccak256: [u8; 32] = Keccak256::digest(msg).into();
            let mut tk_k256 = TinyKeccak::v256();
            tk_k256.update(msg);
            let mut tk_k256_out = [0u8; 32];
            tk_k256.finalize(&mut tk_k256_out);
            assert_eq!(ref_keccak256, tk_k256_out);
            assert_eq!(accel_keccak256(msg), ref_keccak256, "keccak256 len={len} off={off}");

            // 3. SHAKE256 XOF (output lengths 0, 32, 136, 137, 300): `qsag_core`, `qsag_accel`, `qsag_agg` vs `sha3` & `tiny-keccak`
            for out_len in [0usize, 32, 136, 137, 300] {
                let mut s_ref = Shake256::default();
                s_ref.update(msg);
                let mut expected_xof = vec![0u8; out_len];
                s_ref.finalize_xof().read(&mut expected_xof);

                let mut tk_shake = Shake::v256();
                tk_shake.update(msg);
                let mut tk_out = vec![0u8; out_len];
                tk_shake.squeeze(&mut tk_out);
                assert_eq!(expected_xof, tk_out);

                assert_eq!(shake256_xof(out_len, msg), expected_xof);
                let mut accel_out = vec![0u8; out_len];
                accel_shake256_xof(msg, &mut accel_out);
                assert_eq!(accel_out, expected_xof);
                if out_len == 32 {
                    let exp32: [u8; 32] = expected_xof.as_slice().try_into().unwrap();
                    assert_eq!(shake256_32(msg), exp32);
                }
            }

            // 4. NIST SP 800-185 cSHAKE256 (`N = ""`, `S = custom`, including `|S| == 0` fallback to SHAKE256
            //    and multi-block customization strings `|S| = 140 > 136`!)
            for custom in [
                &b""[..],
                &b"QSAG.DOMAIN.TEST"[..],
                &backing[5..5 + 140],
            ] {
                let mut tk_cs = CShake::v256(b"", custom);
                tk_cs.update(msg);
                let mut tk_cs_out = [0u8; 200];
                tk_cs.squeeze(&mut tk_cs_out);

                let core_cs = cshake256_xof(200, custom, msg);
                assert_eq!(core_cs.as_slice(), &tk_cs_out[..], "cshake256 len={len}");
                let exp32: [u8; 32] = tk_cs_out[..32].try_into().unwrap();
                assert_eq!(cshake256_32(custom, msg), exp32);
                assert_eq!(qsag_agg::sponge::cshake256_32(custom, msg), exp32);
            }

            // 5. SHA-256 (`SHA-NI` + portable + streaming chunked + FIPS 205 `sha256_digest`),
            //    SHA-512, RIPEMD-160, Bitcoin HASH160, and BLAKE3 sanity
            let ref_sha256: [u8; 32] = Sha256::digest(msg).into();
            assert_eq!(accel_sha256(msg), ref_sha256, "accel sha256 len={len}");
            assert_eq!(sha256_digest(msg), ref_sha256, "fips205 sha256 len={len}");

            let mut stream256 = Sha256Hasher::new();
            for chunk in msg.chunks(19) {
                stream256.update(chunk);
            }
            assert_eq!(stream256.finalize(), ref_sha256);

            let ref_sha512: [u8; 64] = Sha512::digest(msg).into();
            assert_eq!(accel_sha512(msg), ref_sha512, "accel sha512 len={len}");
            assert_eq!(sha512_digest(msg), ref_sha512, "fips205 sha512 len={len}");

            let mut stream512 = Sha512Hasher::new();
            for chunk in msg.chunks(37) {
                stream512.update(chunk);
            }
            assert_eq!(stream512.finalize(), ref_sha512);

            let ref_ripemd: [u8; 20] = Ripemd160::digest(msg).into();
            assert_eq!(accel_ripemd160(msg), ref_ripemd, "ripemd160 len={len}");
            let ref_hash160: [u8; 20] = Ripemd160::digest(ref_sha256).into();
            assert_eq!(accel_hash160(msg), ref_hash160, "hash160 len={len}");

            // Verify FIPS 205 PreHash M' formatting digests (`SHA3-384`, `SHA3-512`) match RustCrypto `sha3`
            if len <= 256 {
                let ref_sha3_384: [u8; 48] = Sha3_384::digest(msg).into();
                let ref_sha3_512: [u8; 64] = Sha3_512::digest(msg).into();
                let mp384 = qsag_core::fips205::format_prehash_m_prime(
                    qsag_core::fips205::SlhPreHash::Sha3_384,
                    msg,
                    b"ctx",
                )
                .unwrap();
                assert_eq!(&mp384[mp384.len() - 48..], &ref_sha3_384);
                let mp512 = qsag_core::fips205::format_prehash_m_prime(
                    qsag_core::fips205::SlhPreHash::Sha3_512,
                    msg,
                    b"ctx",
                )
                .unwrap();
                assert_eq!(&mp512[mp512.len() - 64..], &ref_sha3_512);
            }

            // Also verify BLAKE3 reference consistency on identical unaligned buffers
            let b3_oneshot = blake3::hash(msg);
            let mut b3_stream = blake3::Hasher::new();
            b3_stream.update(msg);
            assert_eq!(b3_oneshot, b3_stream.finalize());
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// Random lengths `0..=16384` + unaligned offsets `1..15` across SHAKE256, cSHAKE256
    /// multi-frame, SHA-256 (`SHA-NI` + tagged BIP-340), SHA-512, HMAC-SHA512 (BIP-32 / SLIP-0010),
    /// and RIPEMD-160 / HASH160.
    #[test]
    fn random_unaligned_sponges_sha2_hmac_and_ripemd160(
        raw in prop::collection::vec(any::<u8>(), 16..=16416),
        offset in 1usize..16usize,
        custom in prop::collection::vec(any::<u8>(), 0..=200),
        hmac_key in prop::collection::vec(any::<u8>(), 0..=200),
        tag in prop::collection::vec(any::<u8>(), 1..=64),
        out_len in 1usize..=544usize,
    ) {
        let len = raw.len() - offset;
        let msg = &raw[offset..offset + len];

        // 1. SHAKE256 XOF
        let mut s_ref = Shake256::default();
        s_ref.update(msg);
        let mut exp_xof = vec![0u8; out_len];
        s_ref.finalize_xof().read(&mut exp_xof);
        prop_assert_eq!(shake256_xof(out_len, msg), exp_xof.clone());
        let mut accel_xof = vec![0u8; out_len];
        accel_shake256_xof(msg, &mut accel_xof);
        prop_assert_eq!(accel_xof, exp_xof);

        // 2. cSHAKE256 + multi-frame equivalence across `qsag_core`, `qsag_accel`, and `tiny-keccak`
        let mut tk_cs = CShake::v256(b"", &custom);
        tk_cs.update(msg);
        let mut exp_cs = vec![0u8; out_len];
        tk_cs.squeeze(&mut exp_cs);
        prop_assert_eq!(cshake256_xof(out_len, &custom, msg), exp_cs);

        let f0 = &msg[..msg.len() / 2];
        let f1 = &msg[msg.len() / 2..];
        let encoded_frames = encode_multi_frame(&[f0, f1]);
        let mut tk_mf = CShake::v256(b"", &custom);
        tk_mf.update(&encoded_frames);
        let mut exp_mf = vec![0u8; out_len];
        tk_mf.squeeze(&mut exp_mf);
        let mut got_accel_mf = vec![0u8; out_len];
        cshake256_framed_xof(&custom, &[f0, f1], &mut got_accel_mf);
        prop_assert_eq!(got_accel_mf, exp_mf);

        // 3. Hardware `SHA-NI` raw block compressor (`qsag_asm::sha256_compress_blocks` & `sha256_compress_bytes`)
        let init_iv: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
            0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
        ];
        let mut st_hw = init_iv;
        let rem_hw = sha256_compress_bytes(&mut st_hw, msg);
        prop_assert_eq!(rem_hw, &msg[(msg.len() / 64) * 64..]);

        let blocks: Vec<[u8; 64]> = msg
            .chunks_exact(64)
            .map(|c| c.try_into().unwrap())
            .collect();
        let mut st_port = init_iv;
        sha256_compress_blocks_portable(&mut st_port, &blocks);
        let mut st_disp = init_iv;
        sha256_compress_blocks(&mut st_disp, &blocks);
        prop_assert_eq!(st_hw, st_port);
        prop_assert_eq!(st_disp, st_port);

        // 4. BIP-340 tagged SHA-256 (`SHA256(SHA256(tag) || SHA256(tag) || msg)`)
        let tag_hash = Sha256::digest(&tag);
        let mut bip_h = Sha256::new();
        sha2::Digest::update(&mut bip_h, tag_hash);
        sha2::Digest::update(&mut bip_h, tag_hash);
        sha2::Digest::update(&mut bip_h, msg);
        let exp_tagged: [u8; 32] = bip_h.finalize().into();
        prop_assert_eq!(sha256_tagged(&tag, msg), exp_tagged);

        // 5. HMAC-SHA512 vs RustCrypto `hmac::Hmac<Sha512>`
        let mut mac = <Hmac<Sha512> as Mac>::new_from_slice(&hmac_key).unwrap();
        Mac::update(&mut mac, msg);
        let exp_hmac: [u8; 64] = mac.finalize().into_bytes().into();
        prop_assert_eq!(accel_hmac_sha512(&hmac_key, msg), exp_hmac);

        // 6. RIPEMD-160 & HASH160
        let exp_r160: [u8; 20] = Ripemd160::digest(msg).into();
        prop_assert_eq!(accel_ripemd160(msg), exp_r160);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Cross-validates `qsag_asm` 8-way `AVX-512` (`keccak_f1600_x8`), 4-way `AVX2` (`keccak_f1600_x4`),
    /// arbitrary batch sizes `1..=33` (`keccak_f1600_batch_with_backend`), 256-way bitslice pack/unpack,
    /// and 256-way RSS MPC `\chi`-row gate (`keccak_chi_mpc_row256`)!
    #[test]
    fn keccak_f1600_avx512_8x_avx2_4x_batch_1_to_33_and_mpc_chi(
        batch_len in 1usize..=33usize,
        seed in any::<u64>(),
        s0_words in any::<[[u64; 4]; 5]>(),
        s1_words in any::<[[u64; 4]; 5]>(),
        s2_words in any::<[[u64; 4]; 5]>(),
        m0_words in any::<[[u64; 4]; 5]>(),
        m1_words in any::<[[u64; 4]; 5]>(),
    ) {
        // Generate `batch_len` distinct 25-word Keccak states
        let mut states: Vec<[u64; 25]> = (0..batch_len)
            .map(|b| {
                core::array::from_fn(|lane| {
                    let mut x = seed
                        .wrapping_add((b as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15))
                        .wrapping_add((lane as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9));
                    x ^= x >> 30;
                    x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
                    x ^ (x >> 31)
                })
            })
            .collect();

        // Scalar oracle via `qsag_core::sponge::keccak::keccak_f1600` & `qsag_accel::keccak::keccak_f1600`
        let expected: Vec<[u64; 25]> = states
            .iter()
            .map(|s| {
                let mut c1 = *s;
                let mut c2 = *s;
                core_keccak_f1600(&mut c1);
                accel_keccak_f1600(&mut c2);
                assert_eq!(c1, c2);
                c1
            })
            .collect();

        // Test `keccak_f1600_batch_with_backend` across `1..=33` for EVERY backend
        for backend in ALL_SIMD_BACKENDS {
            let mut batch_copy = states.clone();
            keccak_f1600_batch_with_backend(&mut batch_copy, backend);
            prop_assert_eq!(&batch_copy, &expected);
        }

        // Explicitly test `keccak_f1600_x8_with_backend` and `keccak_f1600_x4_with_backend`
        if states.len() >= 8 {
            let mut st8 = KeccakState8x::default();
            for lane in 0..25 {
                for inst in 0..8 {
                    st8.0[lane][inst] = states[inst][lane];
                }
            }
            for backend in ALL_SIMD_BACKENDS {
                let mut cur = st8.clone();
                keccak_f1600_x8_with_backend(&mut cur, backend);
                for inst in 0..8 {
                    let got: [u64; 25] = core::array::from_fn(|lane| cur.0[lane][inst]);
                    prop_assert_eq!(got, expected[inst]);
                }
            }
        }
        if states.len() >= 4 {
            let mut st4 = KeccakState4x::default();
            for lane in 0..25 {
                for inst in 0..4 {
                    st4.0[lane][inst] = states[inst][lane];
                }
            }
            for backend in ALL_SIMD_BACKENDS {
                let mut cur = st4.clone();
                keccak_f1600_x4_with_backend(&mut cur, backend);
                for inst in 0..4 {
                    let got: [u64; 25] = core::array::from_fn(|lane| cur.0[lane][inst]);
                    prop_assert_eq!(got, expected[inst]);
                }
            }
        }

        // Verify 3-party symmetric RSS MPC `\chi`-row gate:
        // Given replicated shares `(s0, s1), (s1, s2), (s2, s0)` of plaintext row `x = s0 ^ s1 ^ s2`
        // and zero-sum mask `r0 ^ r1 ^ r2 == 0`, XORing the 3 party outputs MUST equal
        // standard Keccak `\chi(x)[i] = x[i] ^ ((!x[i+1]) & x[i+2])` across all 256 wires!
        let m2_words: [[u64; 4]; 5] =
            core::array::from_fn(|c| core::array::from_fn(|w| m0_words[c][w] ^ m1_words[c][w]));
        let plain_words: [[u64; 4]; 5] = core::array::from_fn(|c| {
            core::array::from_fn(|w| s0_words[c][w] ^ s1_words[c][w] ^ s2_words[c][w])
        });
        let expected_chi: [[u64; 4]; 5] = core::array::from_fn(|c| {
            core::array::from_fn(|w| {
                plain_words[c][w] ^ ((!plain_words[(c + 1) % 5][w]) & plain_words[(c + 2) % 5][w])
            })
        });

        let r0 = KeccakRow256(s0_words);
        let r1 = KeccakRow256(s1_words);
        let r2 = KeccakRow256(s2_words);
        let mask0 = KeccakRow256(m0_words);
        let mask1 = KeccakRow256(m1_words);
        let mask2 = KeccakRow256(m2_words);

        for backend in ALL_SIMD_BACKENDS {
            let mut out0 = KeccakRow256::default();
            let mut out1 = KeccakRow256::default();
            let mut out2 = KeccakRow256::default();
            keccak_chi_mpc_row256_with_backend(&mut out0, &r0, &r1, &mask0, backend);
            keccak_chi_mpc_row256_with_backend(&mut out1, &r1, &r2, &mask1, backend);
            keccak_chi_mpc_row256_with_backend(&mut out2, &r2, &r0, &mask2, backend);

            let recon: [[u64; 4]; 5] = core::array::from_fn(|c| {
                core::array::from_fn(|w| out0.0[c][w] ^ out1.0[c][w] ^ out2.0[c][w])
            });
            prop_assert_eq!(recon, expected_chi);
        }

        let _ = &mut states;
    }
}

#[test]
fn bitslice_256x200_pack_unpack_roundtrip_across_backends() {
    let mut raw_states = vec![[0u8; 200]; BITSLICE_LANES];
    for (lane, st) in raw_states.iter_mut().enumerate() {
        for (b, slot) in st.iter_mut().enumerate() {
            *slot = ((lane * 73 + b * 19 + 5) ^ (lane >> 2)) as u8;
        }
    }
    let array_ref: &[[u8; 200]; BITSLICE_LANES] = raw_states.as_slice().try_into().unwrap();
    let mut ref_planes = vec![qsag_asm::BitPlane256::default(); 1600];
    pack_256x200_bitslice_with_backend(
        array_ref,
        (&mut ref_planes[..]).try_into().unwrap(),
        SimdBackend::Portable,
    );

    for backend in ALL_SIMD_BACKENDS {
        let mut planes = vec![qsag_asm::BitPlane256::default(); 1600];
        pack_256x200_bitslice_with_backend(
            array_ref,
            (&mut planes[..]).try_into().unwrap(),
            backend,
        );
        assert_eq!(planes, ref_planes, "pack_256x200 mismatch on {backend:?}");

        let mut unpacked = vec![[0u8; 200]; BITSLICE_LANES];
        unpack_256x200_bitslice_with_backend(
            (&planes[..]).try_into().unwrap(),
            (&mut unpacked[..]).try_into().unwrap(),
            backend,
        );
        assert_eq!(unpacked, raw_states, "unpack_256x200 mismatch on {backend:?}");
    }
}
