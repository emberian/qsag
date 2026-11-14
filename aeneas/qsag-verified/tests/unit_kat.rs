//! Comprehensive KAT, algebraic, and adversarial security unit tests for `qsag-verified`
//! (`#![no_std]`, `#![forbid(unsafe_code)]`, 0 external deps).

use qsag_verified::{
    bdoz_commit_masked_tag, bdoz_fold_masked_value, cshake256_32, ct_eq_bytes32,
    decode_fips205_adrs, derive_jorts_det_r_rand, dkg_beaver_frobenius_eval_gf256,
    dkg_beaver_frobenius_share_shamir_gf256, dkg_verify_key_shares_boolean_bdoz_gf256,
    dkg_verify_shamir_2of3_key_bit_gf256, embed_gf256_to_tower128, encode_fips205_adrs,
    epoch_latch_advance, fips205_f, fips205_wots_chain, fips205_wots_checksum, gf16_add, gf16_mul,
    gf256_add, gf256_frobenius_residual, gf256_inv, gf256_inv_or_zero, gf256_is_boolean_frobenius,
    gf256_mul, goldilocks_add, goldilocks_canon, goldilocks_ext2_add, goldilocks_ext2_mul,
    goldilocks_ext2_sub, goldilocks_from_canonical, goldilocks_inv, goldilocks_inv_or_zero,
    goldilocks_mul, goldilocks_pow7, goldilocks_sub, keccak_f1600, rss_and_gate,
    rss_keccak_chi_lane, rss_not, rss_reconstruct, rss_xor, shake256_32,
    shamir_degree_reduce_2of3_gf256, shamir_eval_poly_gf256, shamir_eval_poly_goldilocks,
    shamir_lagrange_at_zero_gf256, shamir_lagrange_at_zero_goldilocks, shamir_validate_points_gf256,
    tower128_add, tower128_mul, tower256_add, tower256_mul, tsw_canonical_target_sum,
    tsw_check_target_sum, verify_mac_2lane, verify_mac_2lane_with_burn, wots_checksum_base16,
    wots_extract_base16_digits, BdozCommittedBatchOpening2Lane, BdozVerifierSession2Lane,
    BdozWireOpening2Lane, EpochLatch, EpochLatchError, EpochRequest,
    EpochSignRequest, Fips205Adrs, Fips205AdrsType, Gf16, Gf256, Goldilocks, GoldilocksExt2,
    LastBoundEpoch, RssShare64, RssZeroSeeds64, Shake256Sponge, Tower128, Tower256,
    GOLDILOCKS_PRIME,
};

fn make_honest_bdoz_batch(
    alpha: [Tower128; 2],
    session_id: [u8; 32],
    round_id: u64,
    mask_value: Tower128,
    mask_key_lanes: [Tower128; 2],
    open_nonce: [u8; 32],
    openings: &[BdozWireOpening2Lane],
) -> BdozCommittedBatchOpening2Lane {
    let masked_sum = bdoz_fold_masked_value(mask_value, openings);
    let mut folded_key0 = mask_key_lanes[0];
    let mut folded_key1 = mask_key_lanes[1];
    for w in openings {
        folded_key0 = tower128_add(folded_key0, tower128_mul(w.chal_weight, w.key_lanes[0]));
        folded_key1 = tower128_add(folded_key1, tower128_mul(w.chal_weight, w.key_lanes[1]));
    }
    let peer_masked_mac_lanes = [
        tower128_add(folded_key0, tower128_mul(alpha[0], masked_sum)),
        tower128_add(folded_key1, tower128_mul(alpha[1], masked_sum)),
    ];
    let tag_commitment = bdoz_commit_masked_tag(
        &session_id,
        round_id,
        masked_sum,
        peer_masked_mac_lanes,
        &open_nonce,
    );
    BdozCommittedBatchOpening2Lane {
        session_id,
        round_id,
        mask_value,
        mask_key_lanes,
        peer_masked_mac_lanes,
        open_nonce,
        tag_commitment,
    }
}

#[test]
fn test_cshake256_nist_sp800_185_kat() {
    // NIST cSHAKE sample #3: N = "", S = "Email Signature", X = 00010203.
    // First 32 bytes of the official 512-bit output (cSHAKE output is prefix-consistent).
    // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/cSHAKE_samples.pdf
    let expected = [
        0xd0, 0x08, 0x82, 0x8e, 0x2b, 0x80, 0xac, 0x9d,
        0x22, 0x18, 0xff, 0xee, 0x1d, 0x07, 0x0c, 0x48,
        0xb8, 0xe4, 0xc8, 0x7b, 0xff, 0x32, 0xc9, 0x69,
        0x9d, 0x5b, 0x68, 0x96, 0xee, 0xe0, 0xed, 0xd1,
    ];
    assert_eq!(cshake256_32(b"Email Signature", &[0, 1, 2, 3]), expected);
}

#[test]
fn test_shake256_nist_fips202_kats() {
    // NIST FIPS 202 SHAKE256 empty-message 256-bit output.
    let expected_empty: [u8; 32] = [
        0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb,
        0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5,
        0x76, 0x2f,
    ];
    assert_eq!(shake256_32(b""), expected_empty);
    assert_eq!(cshake256_32(b"", b""), expected_empty);

    let expected_abc: [u8; 32] = [
        0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77, 0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4, 0x11,
        0x4d, 0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee, 0x4f, 0x94, 0xea, 0x37, 0xe7, 0x8b,
        0x57, 0x39,
    ];
    assert_eq!(shake256_32(b"abc"), expected_abc);

    let mut msg = [0u8; 300];
    for (idx, b) in msg.iter_mut().enumerate() {
        *b = (idx as u8).wrapping_mul(37).wrapping_add(11);
    }
    let oneshot = shake256_32(&msg);
    let mut sp = Shake256Sponge::new_shake256();
    sp.absorb(&msg[..73]);
    sp.absorb(&msg[73..211]);
    sp.absorb(&msg[211..]);
    let mut streamed = [0u8; 32];
    sp.squeeze(&mut streamed);
    assert_eq!(oneshot, streamed);

    assert_ne!(cshake256_32(b"QSAG-DOMAIN-A", b"abc"), expected_abc);
    assert_ne!(
        cshake256_32(b"QSAG-DOMAIN-A", b"abc"),
        cshake256_32(b"QSAG-DOMAIN-B", b"abc")
    );

    let mut st = [0u64; 25];
    keccak_f1600(&mut st);
    assert_eq!(st[0], 0xF125_8F79_40E1_DDE7);
}

#[test]
fn test_goldilocks_branchless_and_ext2_field_laws() {
    assert!(goldilocks_from_canonical(GOLDILOCKS_PRIME - 1).is_ok());
    assert!(goldilocks_from_canonical(GOLDILOCKS_PRIME).is_err());
    assert!(goldilocks_from_canonical(u64::MAX).is_err());
    assert_eq!(goldilocks_canon(0), Goldilocks(0));
    assert_eq!(goldilocks_canon(GOLDILOCKS_PRIME - 1), Goldilocks(GOLDILOCKS_PRIME - 1));
    assert_eq!(goldilocks_canon(GOLDILOCKS_PRIME), Goldilocks(0));
    assert_eq!(goldilocks_canon(GOLDILOCKS_PRIME + 1), Goldilocks(1));
    assert_eq!(
        goldilocks_canon(u64::MAX),
        Goldilocks(u64::MAX - GOLDILOCKS_PRIME)
    );
    assert_eq!(goldilocks_inv_or_zero(Goldilocks(0)), Goldilocks(0));
    assert_eq!(goldilocks_inv_or_zero(Goldilocks(GOLDILOCKS_PRIME)), Goldilocks(0));

    let samples = [
        0u64,
        1,
        2,
        7,
        0xFFFF_FFFF,
        0x1_0000_0000,
        GOLDILOCKS_PRIME - 2,
        GOLDILOCKS_PRIME - 1,
    ];
    for &ra in &samples {
        let a = Goldilocks(ra);
        if ra != 0 {
            let inv = goldilocks_inv(a).expect("non-zero element invertible");
            assert_eq!(inv, goldilocks_inv_or_zero(a));
            assert_eq!(goldilocks_mul(a, inv), Goldilocks(1));
        } else {
            assert_eq!(goldilocks_inv(a), None);
        }
        let a2 = goldilocks_mul(a, a);
        let a4 = goldilocks_mul(a2, a2);
        let a7 = goldilocks_mul(goldilocks_mul(a4, a2), a);
        assert_eq!(goldilocks_pow7(a), a7);
        for &rb in &samples {
            let b = Goldilocks(rb);
            assert!(goldilocks_add(a, b).0 < GOLDILOCKS_PRIME);
            assert!(goldilocks_sub(a, b).0 < GOLDILOCKS_PRIME);
            assert!(goldilocks_mul(a, b).0 < GOLDILOCKS_PRIME);
            assert_eq!(goldilocks_sub(goldilocks_add(a, b), b), a);
        }
    }

    let u = GoldilocksExt2 {
        c0: Goldilocks(0),
        c1: Goldilocks(1),
    };
    assert_eq!(
        goldilocks_ext2_mul(u, u),
        GoldilocksExt2 {
            c0: Goldilocks(7),
            c1: Goldilocks(0)
        }
    );
    let x = GoldilocksExt2 {
        c0: Goldilocks(GOLDILOCKS_PRIME - 5),
        c1: Goldilocks(123456789),
    };
    let y = GoldilocksExt2 {
        c0: Goldilocks(987654321),
        c1: Goldilocks(GOLDILOCKS_PRIME - 3),
    };
    assert_eq!(goldilocks_ext2_sub(goldilocks_ext2_add(x, y), y), x);
}

#[test]
fn test_wiedemann_tower_frobenius_and_committed_bdoz_mac() {
    for x in 1u8..16 {
        let mut acc = Gf16(1);
        for _ in 0..15 {
            acc = gf16_mul(acc, Gf16(x));
        }
        assert_eq!(acc, Gf16(1));
        assert_eq!(gf16_add(Gf16(x), Gf16(x)), Gf16(0));
    }

    // Exhaustive Gf256 branchless Fermat inversion AND Frobenius Booleanity check
    assert_eq!(gf256_inv_or_zero(Gf256(0)), Gf256(0));
    assert_eq!(gf256_inv(Gf256(0)), None);
    for x in 0u16..=255 {
        let xu = x as u8;
        let elem = Gf256(xu);
        assert_eq!(gf256_is_boolean_frobenius(elem), xu == 0 || xu == 1);
        if xu != 0 {
            let inv = gf256_inv(elem).expect("non-zero Gf256 invertible");
            assert_eq!(inv, gf256_inv_or_zero(elem));
            assert_eq!(gf256_mul(elem, inv), Gf256(1));
        }
    }

    let a8 = Gf256(0xA7);
    let b8 = Gf256(0x5D);
    assert_eq!(
        embed_gf256_to_tower128(gf256_mul(a8, b8)),
        tower128_mul(embed_gf256_to_tower128(a8), embed_gf256_to_tower128(b8))
    );

    let t0 = Tower256 {
        lo: 0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210,
        hi: 0xCAFEF00D_DEADBEEF_11223344_55667788,
    };
    let t1 = Tower256 {
        lo: 0xAAAA_5555_FFFF_0000_1234_5678_9ABC_DEF0,
        hi: 0x0F0E_0D0C_0B0A_0908_0706_0504_0302_0100,
    };
    let t2 = Tower256 {
        lo: 7,
        hi: 0x8000_0000_0000_0000_0000_0000_0000_0001,
    };
    assert_eq!(
        tower256_mul(t0, tower256_add(t1, t2)),
        tower256_add(tower256_mul(t0, t1), tower256_mul(t0, t2))
    );

    // Committed & random-masked 2-lane BDOZ MAC verification + single-abort key burn
    let alpha = [
        Tower128(0xDEAD_BEEF_CAFE_BABE_0123_4567_89AB_CDEF),
        Tower128(0x1357_9BDF_2468_ACE0_FEDC_BA98_7654_3210),
    ];
    let w0 = BdozWireOpening2Lane {
        opened_value: Gf256(0x7B),
        chal_weight: Tower128(0x9988_7766_5544_3322_1100_AA55_CC33_F00D),
        key_lanes: [
            Tower128(0x1111_2222_3333_4444),
            Tower128(0x9999_AAAA_BBBB_CCCC),
        ],
    };
    let w1 = BdozWireOpening2Lane {
        opened_value: Gf256(0xE3),
        chal_weight: Tower128(0x0102_0304_0506_0708_090A_0B0C_0D0E_0F10),
        key_lanes: [
            Tower128(0x5555_6666_7777_8888),
            Tower128(0xDDDD_EEEE_FFFF_1234),
        ],
    };
    let wires = [w0, w1];
    let batch = make_honest_bdoz_batch(
        alpha,
        [0xAAu8; 32],
        7,
        Tower128(0xCAFE_BABE_1234_5678_9ABC_DEF0_4242_1337),
        [Tower128(0xA1B2_C3D4), Tower128(0xE5F6_0718)],
        [0x55u8; 32],
        &wires,
    );

    // Empty slice MUST reject!
    assert!(!verify_mac_2lane(alpha, &batch, &[]));
    // Honest committed + masked opening succeeds
    assert!(verify_mac_2lane(alpha, &batch, &wires));

    // Tampered wire value MUST reject
    let mut bad_wires = wires;
    bad_wires[0].opened_value = Gf256(0x7A);
    assert!(!verify_mac_2lane(alpha, &batch, &bad_wires));

    // Zero challenge weight MUST reject
    let mut zero_chal_wires = wires;
    zero_chal_wires[1].chal_weight = Tower128(0);
    let zero_chal_batch = make_honest_bdoz_batch(
        alpha,
        [0xAAu8; 32],
        7,
        Tower128(0xCAFE),
        [Tower128(1), Tower128(2)],
        [0x55u8; 32],
        &zero_chal_wires,
    );
    assert!(!verify_mac_2lane(alpha, &zero_chal_batch, &zero_chal_wires));

    // Tampered pre-open commitment MUST reject even if algebraic MAC holds!
    let mut bad_commit_batch = batch;
    bad_commit_batch.tag_commitment[0] ^= 0x01;
    assert!(!verify_mac_2lane(alpha, &bad_commit_batch, &wires));

    // Single-abort key burn permanently zeroes alpha_lanes and rejects subsequent calls!
    let sess0 = BdozVerifierSession2Lane::new(alpha);
    let (sess1, ok1) = verify_mac_2lane_with_burn(sess0, &batch, &wires);
    assert!(ok1 && !sess1.is_burned());
    let (sess2, ok2) = verify_mac_2lane_with_burn(sess1, &bad_commit_batch, &wires);
    assert!(!ok2 && sess2.is_burned());
    // Even a valid batch MUST be rejected after burn!
    let (sess3, ok3) = verify_mac_2lane_with_burn(sess2, &batch, &wires);
    assert!(!ok3 && sess3.is_burned());
}

#[test]
fn test_fips205_adrs_wots_and_tsw() {
    let adrs = Fips205Adrs::from_tree_u96(
        7,
        (0x1234_5678u128 << 64) | 0x9ABC_DEF0_1122_3344u128,
        Fips205AdrsType::WotsHash,
        9,
        14,
        3,
    );
    let bytes = encode_fips205_adrs(adrs);
    assert_eq!(decode_fips205_adrs(&bytes), Some(adrs));

    let z = fips205_wots_checksum(&[0u8; 16]);
    assert_eq!(&z[..32], &[0u8; 32]);
    assert_eq!(&z[32..35], &[1, 14, 0]);

    let f = fips205_wots_checksum(&[0xFFu8; 16]);
    assert_eq!(&f[..32], &[15u8; 32]);
    assert_eq!(&f[32..35], &[0, 0, 0]);

    let mut m1 = [0x88u8; 16];
    let d1 = wots_extract_base16_digits(&m1);
    m1[5] = 0x87;
    let d2 = wots_extract_base16_digits(&m1);
    assert!(wots_checksum_base16(&d2) > wots_checksum_base16(&d1));

    let x0 = [0x42u8; 16];
    let pk_seed = [0xA5u8; 16];
    let step1 = fips205_wots_chain(x0, 2, 5, &pk_seed, adrs).unwrap();
    let step2 = fips205_wots_chain(step1, 7, 4, &pk_seed, adrs).unwrap();
    let direct = fips205_wots_chain(x0, 2, 9, &pk_seed, adrs).unwrap();
    assert_eq!(step2, direct);
    assert_eq!(fips205_wots_chain(x0, 12, 4, &pk_seed, adrs), None);
    let _ = fips205_f(&pk_seed, &adrs, &x0);

    let target = tsw_canonical_target_sum(16, 32).unwrap();
    assert_eq!(target, 240);
    let mut digits = [7u32; 32];
    for d in digits.iter_mut().take(16) {
        *d = 8;
    }
    assert!(tsw_check_target_sum(16, 32, target, &digits));
    digits[0] = 9;
    assert!(!tsw_check_target_sum(16, 32, target, &digits));
}

#[test]
fn test_dkg_frobenius_booleanity_and_crash_retry_epoch_latch() {
    // Full-set 0..n Shamir point validation
    assert!(shamir_validate_points_gf256(&[Gf256(1), Gf256(2), Gf256(3), Gf256(4)]));
    assert!(!shamir_validate_points_gf256(&[]));
    assert!(!shamir_validate_points_gf256(&[Gf256(1), Gf256(2), Gf256(0)]));
    assert!(!shamir_validate_points_gf256(&[Gf256(1), Gf256(2), Gf256(2)]));

    // Exhaustive 2-of-3 Shamir DKG Frobenius Booleanity check over ALL 256 secrets!
    let pts3 = [Gf256(1), Gf256(2), Gf256(3)];
    for secret_raw in 0u16..=255 {
        let s = Gf256(secret_raw as u8);
        let poly = [s, Gf256(0x73)];
        let sh = [
            shamir_eval_poly_gf256(&poly, pts3[0]),
            shamir_eval_poly_gf256(&poly, pts3[1]),
            shamir_eval_poly_gf256(&poly, pts3[2]),
        ];
        let accepted = dkg_verify_shamir_2of3_key_bit_gf256(pts3, sh);
        assert_eq!(accepted, secret_raw == 0 || secret_raw == 1);

        // Beaver Frobenius evaluation identity: matches s^2 ^ s across all 256 values!
        let a = Gf256(0x5B);
        let b = Gf256(0xC9);
        let c = gf256_mul(a, b);
        assert_eq!(
            dkg_beaver_frobenius_eval_gf256(a, b, c, s),
            gf256_frobenius_residual(s)
        );
    }

    // Degree-2 corrupted Shamir shares MUST be rejected even if f_01(0) == 1
    assert!(!dkg_verify_shamir_2of3_key_bit_gf256(
        pts3,
        [Gf256(1), Gf256(1), Gf256(2)]
    ));

    // Beaver Shamir share linearity + BDOZ DKG batch Booleanity check
    let a_poly = [Gf256(0x3A), Gf256(0x11)];
    let b_poly = [Gf256(0x9E), Gf256(0x22)];
    let c_val = gf256_mul(a_poly[0], b_poly[0]);
    let c_poly = [c_val, Gf256(0x7F)];
    let s_poly_ok = [Gf256(1), Gf256(0x4D)];
    let eps = gf256_add(s_poly_ok[0], a_poly[0]);
    let delta = gf256_add(s_poly_ok[0], b_poly[0]);
    let z_sh0 = dkg_beaver_frobenius_share_shamir_gf256(
        shamir_eval_poly_gf256(&s_poly_ok, pts3[0]),
        shamir_eval_poly_gf256(&a_poly, pts3[0]),
        shamir_eval_poly_gf256(&b_poly, pts3[0]),
        shamir_eval_poly_gf256(&c_poly, pts3[0]),
        eps,
        delta,
    );
    let z_sh1 = dkg_beaver_frobenius_share_shamir_gf256(
        shamir_eval_poly_gf256(&s_poly_ok, pts3[1]),
        shamir_eval_poly_gf256(&a_poly, pts3[1]),
        shamir_eval_poly_gf256(&b_poly, pts3[1]),
        shamir_eval_poly_gf256(&c_poly, pts3[1]),
        eps,
        delta,
    );
    let z_rec = shamir_lagrange_at_zero_gf256(&pts3[..2], &[z_sh0, z_sh1]).unwrap();
    assert_eq!(z_rec, Gf256(0));

    let alpha = [Tower128(0x1234_5678), Tower128(0x9ABC_DEF0)];
    let ok_res_wire = [BdozWireOpening2Lane {
        opened_value: z_rec,
        chal_weight: Tower128(7),
        key_lanes: [Tower128(0x11), Tower128(0x22)],
    }];
    let ok_batch = make_honest_bdoz_batch(
        alpha,
        [0xCCu8; 32],
        1,
        Tower128(0x9999),
        [Tower128(3), Tower128(4)],
        [0x77u8; 32],
        &ok_res_wire,
    );
    assert!(dkg_verify_key_shares_boolean_bdoz_gf256(
        alpha,
        &ok_batch,
        &ok_res_wire
    ));

    // Poisoned non-Boolean share (s = 0x02 -> s^2 ^ s != 0) MUST be rejected even with valid BDOZ MAC!
    let bad_res_wire = [BdozWireOpening2Lane {
        opened_value: gf256_frobenius_residual(Gf256(0x02)),
        chal_weight: Tower128(7),
        key_lanes: [Tower128(0x11), Tower128(0x22)],
    }];
    let bad_batch = make_honest_bdoz_batch(
        alpha,
        [0xCCu8; 32],
        2,
        Tower128(0x8888),
        [Tower128(5), Tower128(6)],
        [0x66u8; 32],
        &bad_res_wire,
    );
    assert!(!dkg_verify_key_shares_boolean_bdoz_gf256(
        alpha,
        &bad_batch,
        &bad_res_wire
    ));

    // Shamir Goldilocks & 2-of-3 RSS gates
    let poly_gf = [Gf256(0x9C), Gf256(0x31), Gf256(0xF4)];
    let pts_gf = [Gf256(1), Gf256(2), Gf256(5)];
    let sh_gf = [
        shamir_eval_poly_gf256(&poly_gf, pts_gf[0]),
        shamir_eval_poly_gf256(&poly_gf, pts_gf[1]),
        shamir_eval_poly_gf256(&poly_gf, pts_gf[2]),
    ];
    assert_eq!(shamir_lagrange_at_zero_gf256(&pts_gf, &sh_gf), Some(poly_gf[0]));

    let poly_a = [Gf256(0x13), Gf256(0x77)];
    let poly_b = [Gf256(0x29), Gf256(0xB4)];
    let prod_shares = [
        gf256_mul(
            shamir_eval_poly_gf256(&poly_a, pts3[0]),
            shamir_eval_poly_gf256(&poly_b, pts3[0]),
        ),
        gf256_mul(
            shamir_eval_poly_gf256(&poly_a, pts3[1]),
            shamir_eval_poly_gf256(&poly_b, pts3[1]),
        ),
        gf256_mul(
            shamir_eval_poly_gf256(&poly_a, pts3[2]),
            shamir_eval_poly_gf256(&poly_b, pts3[2]),
        ),
    ];
    let slopes = [Gf256(0x41), Gf256(0x82), Gf256(0xC3)];
    let red = [
        shamir_degree_reduce_2of3_gf256(pts3, prod_shares, slopes, pts3[0]).unwrap(),
        shamir_degree_reduce_2of3_gf256(pts3, prod_shares, slopes, pts3[1]).unwrap(),
    ];
    assert_eq!(
        shamir_lagrange_at_zero_gf256(&pts3[..2], &red),
        Some(gf256_mul(poly_a[0], poly_b[0]))
    );

    let poly_gl = [
        Goldilocks(GOLDILOCKS_PRIME - 42),
        Goldilocks(1234567),
        Goldilocks(9999991),
    ];
    let pts_gl = [Goldilocks(1), Goldilocks(2), Goldilocks(3)];
    let sh_gl = [
        shamir_eval_poly_goldilocks(&poly_gl, pts_gl[0]),
        shamir_eval_poly_goldilocks(&poly_gl, pts_gl[1]),
        shamir_eval_poly_goldilocks(&poly_gl, pts_gl[2]),
    ];
    assert_eq!(
        shamir_lagrange_at_zero_goldilocks(&pts_gl, &sh_gl),
        Some(poly_gl[0])
    );

    let x = 0xDEAD_BEEF_CAFE_BABEu64;
    let y = 0x0123_4567_89AB_CDEFu64;
    let z = 0xF0E1_D2C3_B4A5_9687u64;
    let sa = RssShare64 {
        x0: 0x1111_2222_3333_4444,
        x1: 0x5555_6666_7777_8888,
        x2: x ^ 0x1111_2222_3333_4444 ^ 0x5555_6666_7777_8888,
    };
    let sb = RssShare64 {
        x0: 0xAAAA_BBBB_CCCC_DDDD,
        x1: 0x9999_8888_7777_6666,
        x2: y ^ 0xAAAA_BBBB_CCCC_DDDD ^ 0x9999_8888_7777_6666,
    };
    let sc = RssShare64 {
        x0: 0x1357_9BDF_2468_ACE0,
        x1: 0x0246_8ACE_1357_9BDF,
        x2: z ^ 0x1357_9BDF_2468_ACE0 ^ 0x0246_8ACE_1357_9BDF,
    };
    let seeds = RssZeroSeeds64 {
        r0: 0xCAFE_F00D_1234_5678,
        r1: 0x8765_4321_DEAD_BEEF,
        r2: 0xFEDC_BA98_7654_3210,
    };
    assert_eq!(rss_reconstruct(rss_and_gate(sa, sb, seeds)), x & y);
    assert_eq!(rss_reconstruct(rss_xor(sa, sb)), x ^ y);
    assert_eq!(rss_reconstruct(rss_not(sa)), !x);
    assert_eq!(
        rss_reconstruct(rss_keccak_chi_lane(sa, sb, sc, seeds)),
        x ^ ((!y) & z)
    );

    // Stateful Jorts crash-retry-safe WAL EpochLatch::acquire_or_retry
    let key_id = [0x3Cu8; 32];
    let sk_prf = [0x91u8; 32];
    let msg_a = [0xA1u8; 32];
    let msg_b = [0xB2u8; 32];
    assert!(ct_eq_bytes32(&key_id, &key_id));
    let mut bad_key = key_id;
    bad_key[31] ^= 1;
    assert!(!ct_eq_bytes32(&key_id, &bad_key));

    let r0 = derive_jorts_det_r_rand(&sk_prf, &key_id, 0, &msg_a);
    assert_eq!(r0, derive_jorts_det_r_rand(&sk_prf, &key_id, 0, &msg_a));
    assert_ne!(r0, derive_jorts_det_r_rand(&sk_prf, &key_id, 1, &msg_a));

    let st0 = EpochLatch::new(2, key_id);
    // 1. Acquire epoch 0 fresh
    let req0 = EpochSignRequest {
        requested_epoch: 0,
        key_epoch_id: key_id,
        msg_digest: msg_a,
        deterministic_r_rand: r0,
    };
    let (st1, g0) = st0.acquire_or_retry(req0).unwrap();
    assert_eq!(g0.authorized_epoch, 0);
    assert!(!g0.is_idempotent_retry);
    assert_eq!(st1.next_epoch(), 1);

    // 2. Honest crash-retry with identical (epoch, msg_digest, r_rand) succeeds idempotently!
    let (st1_retry, g0_retry) = st1.acquire_or_retry(req0).unwrap();
    assert_eq!(st1_retry.next_epoch(), 1);
    assert_eq!(st1_retry.max_epoch(), 2);
    assert_eq!(st1_retry.key_epoch_id(), key_id);
    match st1_retry.last_bound() {
        LastBoundEpoch::Bound(record) => {
            assert_eq!(record.epoch, 0);
            assert_eq!(record.msg_digest, msg_a);
            assert_eq!(record.r_rand, r0);
        }
        LastBoundEpoch::Unset => panic!("retry lost its binding"),
    }

    // Independent adversarial cases reconstruct their fixture through valid transitions.
    let bound_epoch0 = || EpochLatch::new(2, key_id).acquire_or_retry(req0).unwrap().0;
    assert_eq!(g0_retry.authorized_epoch, 0);
    assert_eq!(g0_retry.msg_digest, msg_a);
    assert_eq!(g0_retry.r_rand, r0);
    assert!(g0_retry.is_idempotent_retry);

    // 3. Crash-retry with fresh/drifted r_rand' MUST fail!
    let mut drifted_r = r0;
    drifted_r[0] ^= 1;
    assert_eq!(
        bound_epoch0().acquire_or_retry(EpochSignRequest {
            requested_epoch: 0,
            key_epoch_id: key_id,
            msg_digest: msg_a,
            deterministic_r_rand: drifted_r,
        }).err(),
        Some(EpochLatchError::RetryRandomizerMismatch { epoch: 0 })
    );

    // 4. Equivocation attempt on epoch 0 with msg_b MUST fail!
    let r0_b = derive_jorts_det_r_rand(&sk_prf, &key_id, 0, &msg_b);
    assert_eq!(
        bound_epoch0().acquire_or_retry(EpochSignRequest {
            requested_epoch: 0,
            key_epoch_id: key_id,
            msg_digest: msg_b,
            deterministic_r_rand: r0_b,
        }).err(),
        Some(EpochLatchError::EpochEquivocationAttempt { epoch: 0 })
    );

    // 5. Advance to epoch 1 on msg_b
    let r1 = derive_jorts_det_r_rand(&sk_prf, &key_id, 1, &msg_b);
    let (st2, g1) = st1_retry
        .acquire_or_retry(EpochSignRequest {
            requested_epoch: 1,
            key_epoch_id: key_id,
            msg_digest: msg_b,
            deterministic_r_rand: r1,
        })
        .unwrap();
    assert_eq!(g1.authorized_epoch, 1);
    assert!(!g1.is_idempotent_retry);
    assert_eq!(st2.next_epoch(), 2);

    let bound_epoch1 = || bound_epoch0().acquire_or_retry(EpochSignRequest {
        requested_epoch: 1,
        key_epoch_id: key_id,
        msg_digest: msg_b,
        deterministic_r_rand: r1,
    }).unwrap().0;

    // 6. Replay of sealed epoch 0 MUST fail once epoch 1 is active!
    assert_eq!(
        st2.acquire_or_retry(req0).err(),
        Some(EpochLatchError::NonSequentialEpoch {
            expected: 2,
            requested: 0,
        })
    );

    // 7. Tree exhaustion at epoch 2 (max_epoch = 2)
    let r2 = derive_jorts_det_r_rand(&sk_prf, &key_id, 2, &msg_a);
    assert_eq!(
        bound_epoch1().acquire_or_retry(EpochSignRequest {
            requested_epoch: 2,
            key_epoch_id: key_id,
            msg_digest: msg_a,
            deterministic_r_rand: r2,
        }).err(),
        Some(EpochLatchError::TreeExhausted { max_epoch: 2 })
    );

    // Fresh epoch-only advance preserves an empty retry slot.
    let (st_fresh_adv, adv0) = epoch_latch_advance(
        EpochLatch::new(2, key_id),
        EpochRequest {
            requested_epoch: 0,
            key_epoch_id: key_id,
        },
