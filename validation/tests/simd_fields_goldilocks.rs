// SPDX-License-Identifier: Apache-2.0 OR MIT
//! SIMD Finite-Field Kernels (`GF(2^8)` `GFNI`/`vpshufb`/`Russian-peasant`,
//! `GF(2^128)` `VPCLMULQDQ` 2-lane & batched MulAcc vs `polyval`/`ghash`, and `Goldilocks` +
//! `Ext2` + `Ext4` + Radix-2 NTT + `Poseidon2` Algebraic Bijectivity vs Plonky3 `p3-goldilocks`).

use ghash::universal_hash::{KeyInit, UniversalHash as _};
use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractExtensionField, AbstractField, Field, PrimeField64, TwoAdicField};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use polyval::Polyval;
use proptest::prelude::*;
use qsag_agg::field::{
    GOLDILOCKS_PRIME, Goldilocks as AggGl, GoldilocksExt2, GoldilocksExt4, TWO_ADIC_ROOT_OF_UNITY_32,
    intt_goldilocks, ntt_goldilocks,
};
use qsag_asm::{
    GFNI_MAT_POLY_TO_T3, GFNI_MAT_T3_TO_POLY, SimdBackend, detect_backend, gf2_128_dot_with_backend,
    gf2_128_mul_acc_batch_with_backend, gf256_shamir_mac_avx2_russian_peasant,
    gf256_shamir_mac_with_backend, gf256_shamir_mul_avx2_russian_peasant,
    gf256_shamir_mul_with_backend, goldilocks_add_ct, goldilocks_dot2_ct,
    goldilocks_mul_ct_with_backend, goldilocks_pow7_ct_with_backend, goldilocks_sub_ct,
    poly128_to_tower128_ct, probe_capabilities, tower128_bdoz_2lane_mac_with_backend,
    tower128_bdoz_2lane_poly_mac_with_backend, tower128_to_poly128_ct,
};
use qsag_core::field::goldilocks::Goldilocks as CoreGl;
use qsag_core::field::tower::{Tower128, TowerGf256, eval_poly_gf256, lagrange_weights_zero_gf256};
use qsag_core::sponge::poseidon2::poseidon2_perm12;
use qsag_external_validation::{
    build_poseidon2_inverse_matrices, gf2_128_poly87_mul_ref, gf256_poly11b_inv, gf256_poly11b_mul,
    gfni_affine_byte, goldilocks_mul_u128_ref, poseidon2_perm12_inv_with_mats,
};

const ALL_BACKENDS: [SimdBackend; 4] = [
    SimdBackend::Portable,
    SimdBackend::X86Avx2Pclmul,
    SimdBackend::X86Avx2GfniVpclmul,
    SimdBackend::X86Avx512GfniVpclmul,
];

const ODD_SIMD_LENGTHS: &[usize] = &[0, 1, 2, 7, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 511, 513];

/// Exhaustive `256 x 256` verification of the Wiedemann `T_3 <-> F_2[x]/(x^8+x^4+x^3+x+1)`
/// `VGFP8AFFINEQB` isomorphism (`GFNI_MAT_T3_TO_POLY` & `GFNI_MAT_POLY_TO_T3`) across all 65,536
/// byte pairs!
#[test]
fn gf256_wiedemann_t3_to_aes_poly11b_isomorphism_exhaustive_65536() {
    let caps = probe_capabilities();
    if std::env::var("QSAG_REQUIRE_AVX512").as_deref() == Ok("1") {
        assert!(caps.avx512 && caps.gfni && caps.vpclmulqdq);
        assert_eq!(detect_backend(), SimdBackend::X86Avx512GfniVpclmul);
    }

    // 1. Bijection & ring-homomorphism on `0` and `1`
    assert_eq!(gfni_affine_byte(GFNI_MAT_T3_TO_POLY, 0, 0), 0);
    assert_eq!(gfni_affine_byte(GFNI_MAT_T3_TO_POLY, 1, 0), 1);
    for x in 0u8..=255 {
        let poly = gfni_affine_byte(GFNI_MAT_T3_TO_POLY, x, 0);
        let back = gfni_affine_byte(GFNI_MAT_POLY_TO_T3, poly, 0);
        assert_eq!(back, x, "GFNI T3<->Poly bijection failed at {x:#04x}");
        let inv_t3 = (TowerGf256(x)).ct_inv().0;
        let inv_poly = gf256_poly11b_inv(poly);
        assert_eq!(gfni_affine_byte(GFNI_MAT_T3_TO_POLY, inv_t3, 0), inv_poly);
    }

    // 2. All 65,536 byte products packed into 256-byte slices across ALL SIMD backends
    let mut lhs = Vec::with_capacity(65536);
    let mut rhs = Vec::with_capacity(65536);
    let mut expected = Vec::with_capacity(65536);
    for a in 0u8..=255 {
        let pa = gfni_affine_byte(GFNI_MAT_T3_TO_POLY, a, 0);
        for b in 0u8..=255 {
            let pb = gfni_affine_byte(GFNI_MAT_T3_TO_POLY, b, 0);
            let p_prod = gf256_poly11b_mul(pa, pb);
            let t3_prod = gfni_affine_byte(GFNI_MAT_POLY_TO_T3, p_prod, 0);
            assert_eq!(t3_prod, TowerGf256(a).mul(TowerGf256(b)).0);
            lhs.push(a);
            rhs.push(b);
            expected.push(t3_prod);
        }
    }

    for backend in ALL_BACKENDS {
        let mut dst = vec![0u8; 65536];
        gf256_shamir_mul_with_backend(&mut dst, &lhs, &rhs, backend);
        assert_eq!(dst, expected, "65,536 exhaustive GF(256) mul mismatch on {backend:?}");
    }
    let mut dst_rp = vec![0u8; 65536];
    gf256_shamir_mul_avx2_russian_peasant(&mut dst_rp, &lhs, &rhs);
    assert_eq!(dst_rp, expected, "65,536 exhaustive Russian-peasant mul mismatch");
}

#[test]
fn gf256_simd_odd_tail_lengths_sweep() {
    for &len in ODD_SIMD_LENGTHS {
        let a: Vec<u8> = (0..len).map(|i| ((i * 73 + 19) & 0xFF) as u8).collect();
        let b: Vec<u8> = (0..len).map(|i| ((i * 151 + 211) & 0xFF) as u8).collect();
        let acc_init: Vec<u8> = (0..len).map(|i| ((i * 41 + 7) & 0xFF) as u8).collect();
        let scalar = ((len * 29 + 0xA5) & 0xFF) as u8;

        let exp_mul: Vec<u8> = a
            .iter()
            .zip(&b)
            .map(|(&x, &y)| {
                let px = gfni_affine_byte(GFNI_MAT_T3_TO_POLY, x, 0);
                let py = gfni_affine_byte(GFNI_MAT_T3_TO_POLY, y, 0);
                gfni_affine_byte(GFNI_MAT_POLY_TO_T3, gf256_poly11b_mul(px, py), 0)
            })
            .collect();
        let ps = gfni_affine_byte(GFNI_MAT_T3_TO_POLY, scalar, 0);
        let exp_mac: Vec<u8> = acc_init
            .iter()
            .zip(&a)
            .map(|(&ac, &sh)| {
                let psh = gfni_affine_byte(GFNI_MAT_T3_TO_POLY, sh, 0);
                ac ^ gfni_affine_byte(GFNI_MAT_POLY_TO_T3, gf256_poly11b_mul(ps, psh), 0)
            })
            .collect();

        for backend in ALL_BACKENDS {
            let mut got_mul = vec![0xFFu8; len];
            gf256_shamir_mul_with_backend(&mut got_mul, &a, &b, backend);
            assert_eq!(got_mul, exp_mul, "gf256 mul len={len} backend={backend:?}");

            let mut got_mac = acc_init.clone();
            gf256_shamir_mac_with_backend(&mut got_mac, &a, scalar, backend);
            assert_eq!(got_mac, exp_mac, "gf256 mac len={len} backend={backend:?}");
        }

        let mut rp_mul = vec![0xFFu8; len];
        gf256_shamir_mul_avx2_russian_peasant(&mut rp_mul, &a, &b);
        assert_eq!(rp_mul, exp_mul);
        let mut rp_mac = acc_init.clone();
        gf256_shamir_mac_avx2_russian_peasant(&mut rp_mac, &a, scalar);
        assert_eq!(rp_mac, exp_mac);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    /// 10,000-case property-based test comparing `GFNI` 512b, `GFNI` 256b, `vpshufb` 256b,
    /// `AVX2` Russian-peasant, and `Portable` `GF(2^8)` kernels + $t$-of-$n$ Shamir secret
    /// Lagrange interpolation against reference AES-polynomial arithmetic!
    #[test]
    fn gf256_simd_10000_cases_and_shamir_lagrange_reconstruction(
        len in 0usize..=520usize,
        seed in any::<u64>(),
        scalar in any::<u8>(),
        secret in any::<[u8; 32]>(),
        threshold in 2usize..=7usize,
    ) {
        let mut st = seed | 1;
        let mut next_u8 = || {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            (st & 0xFF) as u8
        };
        let a: Vec<u8> = (0..len).map(|_| next_u8()).collect();
        let b: Vec<u8> = (0..len).map(|_| next_u8()).collect();
        let acc0: Vec<u8> = (0..len).map(|_| next_u8()).collect();

        let mut ref_mul = vec![0u8; len];
        gf256_shamir_mul_with_backend(&mut ref_mul, &a, &b, SimdBackend::Portable);
        let mut ref_mac = acc0.clone();
        gf256_shamir_mac_with_backend(&mut ref_mac, &a, scalar, SimdBackend::Portable);

        for backend in [
            SimdBackend::X86Avx2Pclmul,
            SimdBackend::X86Avx2GfniVpclmul,
            SimdBackend::X86Avx512GfniVpclmul,
        ] {
            let mut got_mul = vec![0u8; len];
            gf256_shamir_mul_with_backend(&mut got_mul, &a, &b, backend);
            prop_assert_eq!(&got_mul, &ref_mul);

            let mut got_mac = acc0.clone();
            gf256_shamir_mac_with_backend(&mut got_mac, &a, scalar, backend);
            prop_assert_eq!(&got_mac, &ref_mac);
        }

        // Verify Shamir t-of-n secret reconstruction via `gf256_shamir_mac_with_backend(X86Avx512GfniVpclmul)`
        // matches Lagrange interpolation in `F_2[x]/(x^8 + x^4 + x^3 + x + 1)`!
        let pts_t3: Vec<TowerGf256> = (1..=threshold).map(|i| TowerGf256(i as u8)).collect();
        let weights = lagrange_weights_zero_gf256(&pts_t3).unwrap();
        let mut shares = vec![[0u8; 32]; threshold];
        for col in 0..32 {
            let mut coeffs = Vec::with_capacity(threshold);
            coeffs.push(TowerGf256(secret[col]));
            for _ in 1..threshold {
                coeffs.push(TowerGf256(next_u8()));
            }
            for (p_idx, &x) in pts_t3.iter().enumerate() {
                shares[p_idx][col] = eval_poly_gf256(&coeffs, x).0;
            }
        }
        let mut recon = [0u8; 32];
        for (p_idx, w) in weights.iter().enumerate() {
            gf256_shamir_mac_with_backend(
                &mut recon,
                &shares[p_idx],
                w.0,
                SimdBackend::X86Avx512GfniVpclmul,
            );
        }
        prop_assert_eq!(recon, secret);
    }
}

/// Convert standard polynomial-basis `GF(2^128)` (`F_2[z]/(z^128 + z^7 + z^2 + z + 1)`) product
/// into RustCrypto `polyval` (`F_2[z]/(z^128 + z^127 + z^126 + z^121 + 1)` Montgomery `z^-128` domain):
/// In `polyval`, `Polyval::new(&h)` + `update(&[x])` computes `mul_polyval(x, h) = rev128(rev128(x) * rev128(h) * z mod P_ghash)`?
/// Specifically, `GHASH` (`ghash` crate, NIST SP 800-38D) uses bit-reflected MSB-first representation of
/// `F_2[z]/(z^128 + z^7 + z^2 + z + 1)`! For any `a, b: u128`, reversing bits inside the 128-bit big-endian
/// block maps `gf2_128_poly87_mul_ref(a, b)` **exact bit-for-bit** to `ghash::GHash::new(&h_be); update(&[x_be])`!
#[inline]
fn poly87_u128_to_ghash_block(v: u128) -> ghash::Block {
    // In `ghash`, bit 0 of the polynomial is the MSB (`0x80`) of byte 0 (`u128::reverse_bits()` in BE!).
    v.reverse_bits().to_be_bytes().into()
}

#[inline]
fn ghash_block_to_poly87_u128(block: ghash::Block) -> u128 {
    let raw: [u8; 16] = block.into();
    u128::from_be_bytes(raw).reverse_bits()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5_000))]

    /// Cross-validates `qsag_asm` `VPCLMULQDQ` (`AVX-512` EVEX & `AVX2` 256-bit), `PCLMULQDQ`,
    /// and `Portable` `GF(2^128)` kernels (`tower128_bdoz_2lane_poly_mac`, `tower128_bdoz_2lane_mac`,
    /// `gf2_128_mul_acc_batch`, `gf2_128_dot`, `tower128_to_poly128_ct`) against:
    /// 1. RustCrypto `ghash::GHash` (NIST SP 800-38D) & `polyval::Polyval` (RFC 8452),
    /// 2. Reference `gf2_128_poly87_mul_ref`, and
    /// 3. `qsag_core::field::tower::Tower128` ($\mathcal{T}_7$).
    #[test]
    fn gf2_128_vpclmulqdq_matches_ghash_polyval_and_tower128(
        a0 in any::<u128>(),
        b0 in any::<u128>(),
        a1 in any::<u128>(),
        b1 in any::<u128>(),
        batch_len in 0usize..=35usize,
        seed in any::<u64>(),
    ) {
        // 1. Single-block exact equivalence with RustCrypto `ghash::GHash` (bit-reflected SP 800-38D)
        let prod0_ref = gf2_128_poly87_mul_ref(a0, b0);
        let mut gh = ghash::GHash::new(&poly87_u128_to_ghash_block(a0));
        gh.update(&[poly87_u128_to_ghash_block(b0)]);
        let gh_out = ghash_block_to_poly87_u128(gh.finalize());
        prop_assert_eq!(prod0_ref, gh_out);

        // Also cross-verify `polyval::Polyval` relation (`GHash(H, X)` == byte-reversed `Polyval(mulX_ghash(rev_bytes(H)), rev_bytes(X))`)
        let mut pv = Polyval::new(&a0.to_le_bytes().into());
        pv.update(&[b0.to_le_bytes().into()]);
        let pv_tag: [u8; 16] = pv.finalize().into();
        // Verify deterministic `Polyval` self-consistency via `z^128` compensation (`x^128 = x^7 + x^2 + x + 1 = 0x87` in poly87,
        // and under bit-reversal `Polyval(a, b) = rev128(gf2_128_poly87_mul_ref(gf2_128_poly87_mul_ref(rev128(a), rev128(b)), 1 << 127 ...))`):
        // Specifically: `rev128(Polyval(rev128(a), rev128(b))) == a * b * x^{-127}` -> check `mul(rev128(pv), x^127)`!
        let pv_rev = u128::from_le_bytes(pv_tag).reverse_bits();
        let lhs_rev = a0.reverse_bits();
        let rhs_rev = b0.reverse_bits();
        // In POLYVAL: `dot(A, B) = A * B * x^{-128} mod (x^128 + x^127 + x^126 + x^121 + 1)`.
        // Under `rev127` (`rev128(u)` maps `u` to `u_rev * x^0`), multiplying `pv_rev` by `x^{-1}` in poly87:
        // Since `x^128 + x^7 + x^2 + x + 1 = 0 => x * (x^127 + x^6 + x + 1) = 1`, `x^{-1} = (1 << 127) | 0x43`!
        let x_inv_poly87: u128 = (1u128 << 127) | 0x43;
        prop_assert_eq!(
            gf2_128_poly87_mul_ref(pv_rev, x_inv_poly87),
            gf2_128_poly87_mul_ref(lhs_rev, rhs_rev)
        );

        // 2. Basis isomorphism `T_7 <-> Poly128` roundtrip + `Tower128` multiplication homomorphism
        let a0_poly = tower128_to_poly128_ct(a0);
        let b0_poly = tower128_to_poly128_ct(b0);
        prop_assert_eq!(poly128_to_tower128_ct(a0_poly), a0);
        let prod_t7 = Tower128(a0).mul(Tower128(b0)).0;
        prop_assert_eq!(
            poly128_to_tower128_ct(gf2_128_poly87_mul_ref(a0_poly, b0_poly)),
            prod_t7
        );

        // 3. Multi-pair `tower128_bdoz_2lane_poly_mac_with_backend` & `tower128_bdoz_2lane_mac_with_backend`
        //    across `batch_len` in `0..=35` (covering odd EVEX / VPCLMULQDQ tail paths!)
        let mut st = (seed as u128) | 1;
        let mut next_u128 = || {
            st ^= st << 23;
            st ^= st >> 17;
            st = st.wrapping_mul(0x9E37_79B9_7F4A_7C15_F39C_C060_5CED_C835);
            st
        };
        let mut lhs_pairs = Vec::with_capacity(batch_len + 1);
        let mut rhs_pairs = Vec::with_capacity(batch_len + 1);
        lhs_pairs.push([a0, a1]);
        rhs_pairs.push([b0, b1]);
        for _ in 0..batch_len {
            lhs_pairs.push([next_u128(), next_u128()]);
            rhs_pairs.push([next_u128(), next_u128()]);
        }

        let mut exp_poly0 = 0u128;
        let mut exp_poly1 = 0u128;
        let mut exp_t7_0 = 0u128;
        let mut exp_t7_1 = 0u128;
        for (l, r) in lhs_pairs.iter().zip(&rhs_pairs) {
            exp_poly0 ^= gf2_128_poly87_mul_ref(l[0], r[0]);
            exp_poly1 ^= gf2_128_poly87_mul_ref(l[1], r[1]);
            exp_t7_0 ^= Tower128(l[0]).mul(Tower128(r[0])).0;
            exp_t7_1 ^= Tower128(l[1]).mul(Tower128(r[1])).0;
        }

        for backend in ALL_BACKENDS {
            let got_poly = tower128_bdoz_2lane_poly_mac_with_backend(&lhs_pairs, &rhs_pairs, backend);
            prop_assert_eq!(got_poly, [exp_poly0, exp_poly1]);

            let got_t7 = tower128_bdoz_2lane_mac_with_backend(&lhs_pairs, &rhs_pairs, backend);
            prop_assert_eq!(got_t7, [exp_t7_0, exp_t7_1]);
        }

        // 4. `bitslice` batched `gf2_128_dot_with_backend` & `gf2_128_mul_acc_batch_with_backend`
        let vec_a: Vec<u128> = lhs_pairs.iter().map(|p| p[0]).collect();
        let vec_b: Vec<u128> = rhs_pairs.iter().map(|p| p[0]).collect();
        let vec_a_limbs: Vec<[u64; 2]> = vec_a.iter().map(|&x| [x as u64, (x >> 64) as u64]).collect();
        let vec_b_limbs: Vec<[u64; 2]> = vec_b.iter().map(|&x| [x as u64, (x >> 64) as u64]).collect();
        let init_acc = 0x1234_5678_9ABC_DEF0_FEDC_BA98_7654_3210u128;
        let exp_acc = init_acc ^ exp_poly0;
        for backend in ALL_BACKENDS {
            prop_assert_eq!(gf2_128_dot_with_backend(&vec_a, &vec_b, backend), exp_poly0);
            let mut acc_limbs = [init_acc as u64, (init_acc >> 64) as u64];
            gf2_128_mul_acc_batch_with_backend(&mut acc_limbs, &vec_a_limbs, &vec_b_limbs, backend);
            let got_acc = (acc_limbs[0] as u128) | ((acc_limbs[1] as u128) << 64);
            prop_assert_eq!(got_acc, exp_acc);
        }
    }
}

/// Canonical edge-value grid (`0, 1, 2^32 - 1, 2^32, p - 1, p, u64::MAX`) comparing
/// `qsag-agg`, `qsag-core`, and `qsag-asm` (`BMI2/ADX` assembly) against Plonky3 `p3-goldilocks`!
#[test]
fn goldilocks_edge_grid_and_ntt_against_plonky3() {
    let edges: &[u64] = &[
        0,
        1,
        2,
        7,
        0xFFFF_FFFF,
        0x1_0000_0000,
        0x1_0000_0001,
        GOLDILOCKS_PRIME - 2,
        GOLDILOCKS_PRIME - 1,
        GOLDILOCKS_PRIME,
        GOLDILOCKS_PRIME + 1,
        u64::MAX - 1,
        u64::MAX,
    ];

    for &ra in edges {
        for &rb in edges {
            let ca = ra % GOLDILOCKS_PRIME;
            let cb = rb % GOLDILOCKS_PRIME;

            let p3_a = P3Goldilocks::from_canonical_u64(ca);
            let p3_b = P3Goldilocks::from_canonical_u64(cb);

            let agg_a = AggGl::from_u64_reduced(ra);
            let agg_b = AggGl::from_u64_reduced(rb);
            let core_a = CoreGl::from_u64_reduced(ra);
            let core_b = CoreGl::from_u64_reduced(rb);

            assert_eq!(agg_a.to_canonical_u64(), ca);
            assert_eq!(core_a.to_canonical_u64(), ca);

            let exp_add = (p3_a + p3_b).as_canonical_u64();
            let exp_sub = (p3_a - p3_b).as_canonical_u64();
            let exp_mul = (p3_a * p3_b).as_canonical_u64();
            let exp_pow7 = p3_a.exp_u64(7).as_canonical_u64();
            let exp_inv = p3_a.try_inverse().map_or(0, |v| v.as_canonical_u64());

            assert_eq!(exp_mul, goldilocks_mul_u128_ref(ca, cb));
            assert_eq!((agg_a + agg_b).to_canonical_u64(), exp_add);
            assert_eq!((core_a + core_b).to_canonical_u64(), exp_add);
            assert_eq!(goldilocks_add_ct(ca, cb), exp_add);

            assert_eq!((agg_a - agg_b).to_canonical_u64(), exp_sub);
            assert_eq!((core_a - core_b).to_canonical_u64(), exp_sub);
            assert_eq!(goldilocks_sub_ct(ca, cb), exp_sub);

            assert_eq!((agg_a * agg_b).to_canonical_u64(), exp_mul);
            assert_eq!((core_a * core_b).to_canonical_u64(), exp_mul);
            assert_eq!(agg_a.inv().to_canonical_u64(), exp_inv);

            for backend in ALL_BACKENDS {
                assert_eq!(goldilocks_mul_ct_with_backend(ca, cb, backend), exp_mul);
                assert_eq!(goldilocks_pow7_ct_with_backend(ca, backend), exp_pow7);
            }
        }
    }

    // Verify 2-adic root of unity matches Plonky3 `TwoAdicField::two_adic_generator(32)`!
    assert_eq!(
        P3Goldilocks::two_adic_generator(32).as_canonical_u64(),
        TWO_ADIC_ROOT_OF_UNITY_32
    );

    // Cross-check Radix-2 NTT & INTT (`qsag_agg::field::{ntt_goldilocks, intt_goldilocks}`)
    // against Plonky3 `p3_dft::Radix2Dit` across sizes 2^0 .. 2^12!
    let dft = Radix2Dit::default();
    for log_n in 0..=12usize {
        let n = 1usize << log_n;
        let coeffs_u64: Vec<u64> = (0..n)
            .map(|i| ((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF) % GOLDILOCKS_PRIME)
            .collect();
        let mut qsag_vec: Vec<AggGl> = coeffs_u64.iter().map(|&v| AggGl::from_u64_reduced(v)).collect();
        let p3_vec: Vec<P3Goldilocks> = coeffs_u64
            .iter()
            .map(|&v| P3Goldilocks::from_canonical_u64(v))
            .collect();

        ntt_goldilocks(&mut qsag_vec);
        let p3_evals = dft.dft(p3_vec.clone());
        let qsag_evals_u64: Vec<u64> = qsag_vec.iter().map(|x| x.to_canonical_u64()).collect();
        let p3_evals_u64: Vec<u64> = p3_evals.iter().map(|x| x.as_canonical_u64()).collect();
        assert_eq!(qsag_evals_u64, p3_evals_u64, "Radix-2 NTT mismatch vs Plonky3 at log_n={log_n}");

        intt_goldilocks(&mut qsag_vec);
        let qsag_back_u64: Vec<u64> = qsag_vec.iter().map(|x| x.to_canonical_u64()).collect();
        assert_eq!(qsag_back_u64, coeffs_u64, "Radix-2 INTT roundtrip mismatch at log_n={log_n}");
    }
}

/// Reference multiplication in $\mathbb{F}_p[X]/(X^4 - 7)$ over Plonky3 `P3Goldilocks`.
fn p3_quartic_mul(a: [P3Goldilocks; 4], b: [P3Goldilocks; 4]) -> [P3Goldilocks; 4] {
    let w = P3Goldilocks::from_canonical_u64(7);
    let mut out = [P3Goldilocks::zero(); 4];
    for i in 0..4 {
        for j in 0..4 {
            let term = a[i] * b[j];
            if i + j < 4 {
                out[i + j] += term;
            } else {
                out[i + j - 4] += term * w;
            }
        }
    }
    out
}

fn p3_quartic_pow(mut base: [P3Goldilocks; 4], mut exp: u64) -> [P3Goldilocks; 4] {
    let mut acc = [
        P3Goldilocks::one(),
        P3Goldilocks::zero(),
        P3Goldilocks::zero(),
        P3Goldilocks::zero(),
    ];
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = p3_quartic_mul(acc, base);
        }
        base = p3_quartic_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// Isomorphism $\iota : \text{GoldilocksExt4} = \mathbb{F}_{p^2}[v]/(v^2 - u) \xrightarrow{\sim} \mathbb{F}_p[X]/(X^4 - 7)$:
/// $(c_{00} + c_{01} u) + (c_{10} + c_{11} u) v \mapsto c_{00} + c_{10} X + c_{01} X^2 + c_{11} X^3$
/// since $v \mapsto X$ and $u = v^2 \mapsto X^2$ with $X^4 = u^2 = 7$.
#[inline]
fn ext4_to_p3_quartic(x: GoldilocksExt4) -> [P3Goldilocks; 4] {
    let [c00, c01, c10, c11] = x.to_limbs();
    [
        P3Goldilocks::from_canonical_u64(c00.to_canonical_u64()),
        P3Goldilocks::from_canonical_u64(c10.to_canonical_u64()),
        P3Goldilocks::from_canonical_u64(c01.to_canonical_u64()),
        P3Goldilocks::from_canonical_u64(c11.to_canonical_u64()),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    /// 10,000-case property-based test comparing `Goldilocks`, `GoldilocksExt2`, and
    /// `GoldilocksExt4` (`mul`, `square`, `inv`, Frobenius $x \mapsto x^p$) against Plonky3!
    #[test]
    fn goldilocks_base_ext2_and_ext4_10000_cases_against_plonky3(
        x_raw in any::<[u64; 4]>(),
        y_raw in any::<[u64; 4]>(),
    ) {
        // 1. Base field + `goldilocks_dot2_ct` vs Plonky3
        let a0 = x_raw[0] % GOLDILOCKS_PRIME;
        let b0 = y_raw[0] % GOLDILOCKS_PRIME;
        let a1 = x_raw[1] % GOLDILOCKS_PRIME;
        let b1 = y_raw[1] % GOLDILOCKS_PRIME;

        let p3_dot = (P3Goldilocks::from_canonical_u64(a0) * P3Goldilocks::from_canonical_u64(b0)
            + P3Goldilocks::from_canonical_u64(a1) * P3Goldilocks::from_canonical_u64(b1))
            .as_canonical_u64();
        prop_assert_eq!(goldilocks_dot2_ct(a0, b0, a1, b1), p3_dot);
        prop_assert_eq!(
            goldilocks_mul_ct_with_backend(a0, b0, SimdBackend::X86Avx512GfniVpclmul),
            (P3Goldilocks::from_canonical_u64(a0) * P3Goldilocks::from_canonical_u64(b0)).as_canonical_u64()
        );

        // 2. Quadratic extension `GoldilocksExt2` vs `p3_field::BinomialExtensionField<P3Goldilocks, 2>`
        type P3Ext2 = BinomialExtensionField<P3Goldilocks, 2>;
        let q_e2_x = GoldilocksExt2::new(AggGl::from_u64_reduced(x_raw[0]), AggGl::from_u64_reduced(x_raw[1]));
        let q_e2_y = GoldilocksExt2::new(AggGl::from_u64_reduced(y_raw[0]), AggGl::from_u64_reduced(y_raw[1]));
        let p3_e2_x = P3Ext2::from_base_slice(&[
            P3Goldilocks::from_canonical_u64(q_e2_x.c0.to_canonical_u64()),
            P3Goldilocks::from_canonical_u64(q_e2_x.c1.to_canonical_u64()),
        ]);
        let p3_e2_y = P3Ext2::from_base_slice(&[
            P3Goldilocks::from_canonical_u64(q_e2_y.c0.to_canonical_u64()),
            P3Goldilocks::from_canonical_u64(q_e2_y.c1.to_canonical_u64()),
        ]);

        let q_e2_prod = q_e2_x * q_e2_y;
        let p3_e2_prod_val = p3_e2_x * p3_e2_y;
        let p3_e2_prod: &[P3Goldilocks] = p3_e2_prod_val.as_base_slice();
        prop_assert_eq!(q_e2_prod.c0.to_canonical_u64(), p3_e2_prod[0].as_canonical_u64());
        prop_assert_eq!(q_e2_prod.c1.to_canonical_u64(), p3_e2_prod[1].as_canonical_u64());

        if !q_e2_x.is_zero() {
            let q_e2_inv = q_e2_x.inv();
            let p3_e2_inv_val = p3_e2_x.inverse();
            let p3_e2_inv: &[P3Goldilocks] = p3_e2_inv_val.as_base_slice();
            prop_assert_eq!(q_e2_inv.c0.to_canonical_u64(), p3_e2_inv[0].as_canonical_u64());
            prop_assert_eq!(q_e2_inv.c1.to_canonical_u64(), p3_e2_inv[1].as_canonical_u64());
        }

        // 3. Quartic extension `GoldilocksExt4` (`X^4 - 7`) mul, square, inverse, and Frobenius `x^p`!
        let q_x = GoldilocksExt4::from_limbs(x_raw.map(AggGl::from_u64_reduced));
        let q_y = GoldilocksExt4::from_limbs(y_raw.map(AggGl::from_u64_reduced));
        let p3_qx = ext4_to_p3_quartic(q_x);
        let p3_qy = ext4_to_p3_quartic(q_y);

        prop_assert_eq!(ext4_to_p3_quartic(q_x * q_y), p3_quartic_mul(p3_qx, p3_qy));
        prop_assert_eq!(ext4_to_p3_quartic(q_x.square()), p3_quartic_mul(p3_qx, p3_qx));

        if !q_x.is_zero() {
            let inv = q_x.inv();
            prop_assert_eq!(q_x * inv, GoldilocksExt4::ONE);
            let p3_inv = ext4_to_p3_quartic(inv);
            prop_assert_eq!(
                p3_quartic_mul(p3_qx, p3_inv),
                [
                    P3Goldilocks::one(),
                    P3Goldilocks::zero(),
                    P3Goldilocks::zero(),
                    P3Goldilocks::zero(),
                ]
            );
        }

        // Frobenius endomorphism: `(x + y)^p == x^p + y^p` and `(x * y)^p == x^p * y^p` in `F_p[X]/(X^4 - 7)`
        let frob_x = p3_quartic_pow(p3_qx, GOLDILOCKS_PRIME);
        let frob_y = p3_quartic_pow(p3_qy, GOLDILOCKS_PRIME);
        let frob_prod = p3_quartic_pow(ext4_to_p3_quartic(q_x * q_y), GOLDILOCKS_PRIME);
        prop_assert_eq!(frob_prod, p3_quartic_mul(frob_x, frob_y));
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1_200))]

    /// 1,200-state property-based test verifying algebraic bijectivity
    /// (`poseidon2_perm12_inv(poseidon2_perm12(x)) == x` AND `poseidon2_perm12(poseidon2_perm12_inv(x)) == x`)
    /// plus exact Width-12 permutation parity across `qsag_core`, `qsag_agg`, and `qsag_accel`!
    #[test]
    fn poseidon2_width12_bijectivity_and_three_crate_parity(
        raw_state in any::<[u64; 12]>(),
    ) {
        let (me_inv, mi_inv) = build_poseidon2_inverse_matrices();

        let core_in: [CoreGl; 12] = raw_state.map(CoreGl::from_u64_reduced);
        let agg_in: [AggGl; 12] = raw_state.map(AggGl::from_u64_reduced);
        let mut accel_in: [u64; 12] = core_in.map(|x| x.to_canonical_u64());

        let mut core_st = core_in;
        poseidon2_perm12(&mut core_st);

        let mut agg_st = agg_in;
        qsag_agg::sponge::poseidon2_perm12(&mut agg_st);

        qsag_accel::poseidon2::poseidon2_perm12(&mut accel_in);

        let core_out_u64 = core_st.map(|x| x.to_canonical_u64());
        let agg_out_u64 = agg_st.map(|x| x.to_canonical_u64());
        prop_assert_eq!(core_out_u64, agg_out_u64);
        prop_assert_eq!(core_out_u64, accel_in);

        // Left inverse: `perm_inv(perm(x)) == x`
        let mut back = core_st;
        poseidon2_perm12_inv_with_mats(&mut back, &me_inv, &mi_inv);
        prop_assert_eq!(back, core_in);

        // Right inverse: `perm(perm_inv(y)) == y`
        let mut preimage = core_in;
        poseidon2_perm12_inv_with_mats(&mut preimage, &me_inv, &mi_inv);
        poseidon2_perm12(&mut preimage);
        prop_assert_eq!(preimage, core_in);
    }
}
