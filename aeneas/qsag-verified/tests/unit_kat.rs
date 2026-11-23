//! Comprehensive KAT, algebraic, and adversarial security unit tests for `qsag-verified`
//! (`#![no_std]`, `#![forbid(unsafe_code)]`, 0 external deps).

use qsag_verified::{
    EpochLatch, EpochLatchError, EpochRequest, EpochSignRequest, Fips205Adrs, Fips205AdrsType,
    GOLDILOCKS_PRIME, Gf16, Gf256, Goldilocks, GoldilocksExt2, LastBoundEpoch, RssShare64,
    RssZeroSeeds64, Shake256Sponge, cshake256_32, ct_eq_bytes32, decode_fips205_adrs,
    dkg_beaver_frobenius_eval_gf256, dkg_beaver_frobenius_share_shamir_gf256,
    dkg_verify_shamir_2of3_key_bit_gf256, embed_gf256_to_tower128, encode_fips205_adrs,
    epoch_latch_advance, fips205_f, fips205_wots_chain, fips205_wots_checksum, gf16_add, gf16_mul,
    gf256_add, gf256_frobenius_residual, gf256_inv, gf256_inv_or_zero, gf256_is_boolean_frobenius,
    gf256_mul, goldilocks_add, goldilocks_canon, goldilocks_ext2_add, goldilocks_ext2_mul,
    goldilocks_ext2_sub, goldilocks_from_canonical, goldilocks_inv, goldilocks_inv_or_zero,
    goldilocks_mul, goldilocks_pow7, goldilocks_sub, keccak_f1600, rss_and_gate,
    rss_keccak_chi_lane, rss_not, rss_reconstruct, rss_xor, shake256_32,
    shamir_degree_reduce_2of3_gf256, shamir_eval_poly_gf256, shamir_eval_poly_goldilocks,
    shamir_lagrange_at_zero_gf256, shamir_lagrange_at_zero_goldilocks,
    shamir_validate_points_gf256, tower128_mul, tsw_canonical_target_sum, tsw_check_target_sum,
    wots_checksum_base16, wots_extract_base16_digits,
};

#[test]
fn test_cshake256_nist_sp800_185_kat() {
    // NIST cSHAKE sample #3: N = "", S = "Email Signature", X = 00010203.
    // First 32 bytes of the official 512-bit output (cSHAKE output is prefix-consistent).
    // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/cSHAKE_samples.pdf
    let expected = [
        0xd0, 0x08, 0x82, 0x8e, 0x2b, 0x80, 0xac, 0x9d, 0x22, 0x18, 0xff, 0xee, 0x1d, 0x07, 0x0c,
        0x48, 0xb8, 0xe4, 0xc8, 0x7b, 0xff, 0x32, 0xc9, 0x69, 0x9d, 0x5b, 0x68, 0x96, 0xee, 0xe0,
        0xed, 0xd1,
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

/// Production `Cshake256Xof::absorb` panics after squeezing began; the extracted sponge must too.
#[test]
#[should_panic(expected = "cannot absorb into Shake256Sponge after squeezing began")]
fn test_shake256_absorb_after_squeeze_panics() {
    let mut sp = qsag_verified::Shake256Sponge::new_shake256();
    sp.absorb(b"abc");
    let mut out = [0u8; 8];
    sp.squeeze(&mut out);
    sp.absorb(b"late");
}

/// `finalize` and `squeeze` stay legal after squeezing began, and the stream continues.
#[test]
fn test_shake256_squeeze_is_resumable_after_finalize() {
    let mut one = qsag_verified::Shake256Sponge::new_shake256();
    one.absorb(b"abc");
    let mut whole = [0u8; 64];
    one.squeeze(&mut whole);
    let mut two = qsag_verified::Shake256Sponge::new_shake256();
    two.absorb(b"abc");
    two.finalize();
    two.finalize();
    let (mut head, mut tail) = ([0u8; 24], [0u8; 40]);
    two.squeeze(&mut head);
    two.squeeze(&mut tail);
    assert_eq!(&whole[..24], &head[..]);
    assert_eq!(&whole[24..], &tail[..]);
}

#[test]
fn test_goldilocks_branchless_and_ext2_field_laws() {
    assert!(goldilocks_from_canonical(GOLDILOCKS_PRIME - 1).is_ok());
    assert!(goldilocks_from_canonical(GOLDILOCKS_PRIME).is_err());
    assert!(goldilocks_from_canonical(u64::MAX).is_err());
    assert_eq!(goldilocks_canon(0), Goldilocks(0));
    assert_eq!(
        goldilocks_canon(GOLDILOCKS_PRIME - 1),
        Goldilocks(GOLDILOCKS_PRIME - 1)
    );
    assert_eq!(goldilocks_canon(GOLDILOCKS_PRIME), Goldilocks(0));
    assert_eq!(goldilocks_canon(GOLDILOCKS_PRIME + 1), Goldilocks(1));
    assert_eq!(
        goldilocks_canon(u64::MAX),
        Goldilocks(u64::MAX - GOLDILOCKS_PRIME)
    );
    assert_eq!(goldilocks_inv_or_zero(Goldilocks(0)), Goldilocks(0));
    assert_eq!(
        goldilocks_inv_or_zero(Goldilocks(GOLDILOCKS_PRIME)),
        Goldilocks(0)
    );

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
fn test_wiedemann_tower_frobenius() {
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
    assert!(shamir_validate_points_gf256(&[
        Gf256(1),
        Gf256(2),
        Gf256(3),
        Gf256(4)
    ]));
    assert!(!shamir_validate_points_gf256(&[]));
    assert!(!shamir_validate_points_gf256(&[
        Gf256(1),
        Gf256(2),
        Gf256(0)
    ]));
    assert!(!shamir_validate_points_gf256(&[
        Gf256(1),
        Gf256(2),
        Gf256(2)
    ]));

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

    // Beaver Shamir share linearity
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

    // Shamir Goldilocks & 2-of-3 RSS gates
    let poly_gf = [Gf256(0x9C), Gf256(0x31), Gf256(0xF4)];
    let pts_gf = [Gf256(1), Gf256(2), Gf256(5)];
    let sh_gf = [
        shamir_eval_poly_gf256(&poly_gf, pts_gf[0]),
        shamir_eval_poly_gf256(&poly_gf, pts_gf[1]),
        shamir_eval_poly_gf256(&poly_gf, pts_gf[2]),
    ];
    assert_eq!(
        shamir_lagrange_at_zero_gf256(&pts_gf, &sh_gf),
        Some(poly_gf[0])
    );

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

    let det_r_rand = |epoch: u64, msg_digest: &[u8; 32]| -> [u8; 32] {
        let mut buf = [0u8; 104];
        buf[0..32].copy_from_slice(&sk_prf);
        buf[32..64].copy_from_slice(&key_id);
        buf[64..72].copy_from_slice(&epoch.to_be_bytes());
        buf[72..104].copy_from_slice(msg_digest);
        cshake256_32(b"QSAG.PQ.BAGGYSIG.DET/v1", &buf)
    };

    let r0 = det_r_rand(0, &msg_a);
    assert_eq!(r0, det_r_rand(0, &msg_a));
    assert_ne!(r0, det_r_rand(1, &msg_a));

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
        bound_epoch0()
            .acquire_or_retry(EpochSignRequest {
                requested_epoch: 0,
                key_epoch_id: key_id,
                msg_digest: msg_a,
                deterministic_r_rand: drifted_r,
            })
            .err(),
        Some(EpochLatchError::RetryRandomizerMismatch { epoch: 0 })
    );

    // 4. Equivocation attempt on epoch 0 with msg_b MUST fail!
    let r0_b = det_r_rand(0, &msg_b);
    assert_eq!(
        bound_epoch0()
            .acquire_or_retry(EpochSignRequest {
                requested_epoch: 0,
                key_epoch_id: key_id,
                msg_digest: msg_b,
                deterministic_r_rand: r0_b,
            })
            .err(),
        Some(EpochLatchError::EpochEquivocationAttempt { epoch: 0 })
    );

    // 5. Advance to epoch 1 on msg_b
    let r1 = det_r_rand(1, &msg_b);
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

    let bound_epoch1 = || {
        bound_epoch0()
            .acquire_or_retry(EpochSignRequest {
                requested_epoch: 1,
                key_epoch_id: key_id,
                msg_digest: msg_b,
                deterministic_r_rand: r1,
            })
            .unwrap()
            .0
    };

    // 6. Replay of sealed epoch 0 MUST fail once epoch 1 is active!
    assert_eq!(
        st2.acquire_or_retry(req0).err(),
        Some(EpochLatchError::NonSequentialEpoch {
            expected: 2,
            requested: 0,
        })
    );

    // 7. Tree exhaustion at epoch 2 (max_epoch = 2)
    let r2 = det_r_rand(2, &msg_a);
    assert_eq!(
        bound_epoch1()
            .acquire_or_retry(EpochSignRequest {
                requested_epoch: 2,
                key_epoch_id: key_id,
                msg_digest: msg_a,
                deterministic_r_rand: r2,
            })
            .err(),
        Some(EpochLatchError::TreeExhausted { max_epoch: 2 })
    );

    // Fresh epoch-only advance preserves an empty retry slot.
    let (st_fresh_adv, adv0) = epoch_latch_advance(
        EpochLatch::new(2, key_id),
        EpochRequest {
            requested_epoch: 0,
            key_epoch_id: key_id,
        },
    )
    .unwrap();
    assert_eq!(adv0, 0);
    assert_eq!(st_fresh_adv.next_epoch(), 1);
    assert!(matches!(st_fresh_adv.last_bound(), LastBoundEpoch::Unset));
    assert_eq!(st_fresh_adv.max_epoch(), 2);
    assert_eq!(st_fresh_adv.key_epoch_id(), key_id);

    // Advancing epoch 1 seals the bound epoch 0 against subsequent retries.
    let (st_after_adv, adv1) = epoch_latch_advance(
        bound_epoch0(),
        EpochRequest {
            requested_epoch: 1,
            key_epoch_id: key_id,
        },
    )
    .unwrap();
    assert_eq!(adv1, 1);
    assert_eq!(st_after_adv.next_epoch(), 2);
    assert!(matches!(st_after_adv.last_bound(), LastBoundEpoch::Unset));
    assert_eq!(st_after_adv.max_epoch(), 2);
    assert_eq!(st_after_adv.key_epoch_id(), key_id);
    assert_eq!(
        st_after_adv.acquire_or_retry(req0).err(),
        Some(EpochLatchError::NonSequentialEpoch {
            expected: 2,
            requested: 0,
        })
    );

    // Key binding and sequential checks apply with either retry-slot state.
    for bound in [false, true] {
        let fixture = || {
            if bound {
                bound_epoch0()
            } else {
                epoch_latch_advance(
                    EpochLatch::new(2, key_id),
                    EpochRequest {
                        requested_epoch: 0,
                        key_epoch_id: key_id,
                    },
                )
                .unwrap()
                .0
            }
        };
        assert_eq!(
            epoch_latch_advance(
                fixture(),
                EpochRequest {
                    requested_epoch: 1,
                    key_epoch_id: bad_key,
                }
            )
            .err(),
            Some(EpochLatchError::KeyBindingMismatch)
        );
        for requested_epoch in [0, 2] {
            assert_eq!(
                epoch_latch_advance(
                    fixture(),
                    EpochRequest {
                        requested_epoch,
                        key_epoch_id: key_id,
                    }
                )
                .err(),
                Some(EpochLatchError::NonSequentialEpoch {
                    expected: 1,
                    requested: requested_epoch
                })
            );
        }
    }
}

#[test]
fn test_rss_cut_session_anti_dfa_phase_barrier() {
    use qsag_verified::{
        RssCutError, RssCutGateSession, RssCutPhase, RssCutStepInput, RssCutStepOutput,
        compute_rss_mask_commitment,
    };

    let sid = [0x41u8; 32];
    let mask = [0x7Fu8; 32];
    let salt = [0x99u8; 32];
    let cand = [0xEEu8; 32];
    let commit = compute_rss_mask_commitment(&sid, 1, &mask, &salt);

    // 1. Honest Round1 -> Round2 -> Round3 -> CutOpened flow
    let s0 = RssCutGateSession::new_round1_committed(sid, commit);
    assert!(matches!(s0.phase(), RssCutPhase::Round1MaskCommitted));
    assert!(!s0.is_poisoned());
    let (s1, r2) = s0.advance_round2_chi(sid, commit, cand);
    assert_eq!(r2, Ok(()));
    assert!(matches!(s1.phase(), RssCutPhase::Round2ChiEvaluated));
    assert!(!s1.is_consistency_verified());

    let (s2, r3) = s1.advance_round3_verify_consistency(sid, 0, 0, 0);
    assert_eq!(r3, Ok(()));
    assert!(matches!(s2.phase(), RssCutPhase::Round3ConsistencyVerified));
    assert!(s2.is_consistency_verified());

    let (s3, opened) = s2.open_verified_cut(sid);
    assert_eq!(opened, Ok(cand));
    assert!(matches!(s3.phase(), RssCutPhase::CutOpened));

    // Second opening attempt MUST fail and poison!
    let (s4, replay) = s3.open_verified_cut(sid);
    assert_eq!(replay, Err(RssCutError::InvalidPhaseTransition));
    assert!(s4.is_poisoned());

    // 2. Skipping Round 3 consistency check MUST poison and never release cut!
    let s_skip0 = RssCutGateSession::new_round1_committed(sid, commit);
    let (s_skip1, _) = s_skip0.advance_round2_chi(sid, commit, cand);
    let (s_skip2, skip_res) = s_skip1.open_verified_cut(sid);
    assert_eq!(skip_res, Err(RssCutError::InvalidPhaseTransition));
    assert!(s_skip2.is_poisoned());

    // 3. Non-zero SPDZ MAC or BBCGGI19 dZK residual MUST poison and permanently block release!
    let s_bad0 = RssCutGateSession::new_round1_committed(sid, commit);
    let (s_bad1, _) = s_bad0.advance_round2_chi(sid, commit, cand);
    let (s_bad2, bad_r3) = s_bad1.advance_round3_verify_consistency(sid, 0, 0, 1);
    assert_eq!(bad_r3, Err(RssCutError::ConsistencyCheckFailed));
    assert!(s_bad2.is_poisoned());
    let (s_bad3, after_poison) = s_bad2.open_verified_cut(sid);
    assert_eq!(after_poison, Err(RssCutError::SessionPoisoned));
    assert!(s_bad3.is_poisoned());

    // 4. Unified step() entry point parity
    let u0 = RssCutGateSession::new_round1_committed(sid, commit);
    let (u1, o1) = u0.step(RssCutStepInput::AdvanceRound2Chi {
        req_session_id: sid,
        recomputed_mask_commitment: commit,
        chi_cut_candidate: cand,
    });
    assert!(matches!(o1, Ok(RssCutStepOutput::Round2Ready)));
    let (u2, o2) = u1.step(RssCutStepInput::AdvanceRound3VerifyConsistency {
        req_session_id: sid,
        spdz_mac_residual_lo: 0,
        spdz_mac_residual_hi: 0,
        bbcggi_dzk_residual: 0,
    });
    assert!(matches!(o2, Ok(RssCutStepOutput::Round3Verified)));
    let (_u3, o3) = u2.step(RssCutStepInput::OpenVerifiedCut {
        req_session_id: sid,
    });
    assert!(matches!(o3, Ok(RssCutStepOutput::CutReleased(c)) if c == cand));
}

#[test]
fn test_policy_velocity_guard_intent128_codec_and_hybrid_framing() {
    use qsag_verified::{
        CanonicalIntent128, HybridRoleTag, IntentAddressVersion, IntentIdentityKind,
        IntentSuiteTag, PolicyAddrError, SUITE_HYBRID_ED25519_MLDSA65,
        SUITE_HYBRID_SECP256K1_MLDSA44, StatefulVelocityGuard, VelocitySpendRequest,
        check_hybrid_domain_framing, decode_intent_128, derive_hybrid_transcript_digest,
        encode_intent_128,
    };

    let pol_pin = [0xAAu8; 32];
    let auth_pin = [0xBBu8; 32];
    let g0 = StatefulVelocityGuard::new_window(7, 1_000, pol_pin, auth_pin);

    let (g1, a1) = g0.authorize_spend(VelocitySpendRequest {
        window_id: 7,
        nonce: 1,
        amount_units: 600,
        policy_pin: pol_pin,
        authority_pin: auth_pin,
    });
    assert_eq!(a1, Ok(600));
    assert_eq!(g1.spent_units(), 600);

    // Nonce replay rejected without mutating spent_units
    let (g1b, replay_err) = g1.authorize_spend(VelocitySpendRequest {
        window_id: 7,
        nonce: 1,
        amount_units: 100,
        policy_pin: pol_pin,
        authority_pin: auth_pin,
    });
    assert_eq!(replay_err, Err(PolicyAddrError::NonMonotonicNonce));
    assert_eq!(g1b.spent_units(), 600);

    // Cap exceeded rejected
    let (g1c, cap_err) = g1b.authorize_spend(VelocitySpendRequest {
        window_id: 7,
        nonce: 2,
        amount_units: 401,
        policy_pin: pol_pin,
        authority_pin: auth_pin,
    });
    assert_eq!(cap_err, Err(PolicyAddrError::VelocityCapExceeded));
    assert_eq!(g1c.spent_units(), 600);

    // u128::MAX wraparound attempt rejected cleanly!
    let (g1d, ovf_err) = g1c.authorize_spend(VelocitySpendRequest {
        window_id: 7,
        nonce: 2,
        amount_units: u128::MAX - 500,
        policy_pin: pol_pin,
        authority_pin: auth_pin,
    });
    assert_eq!(ovf_err, Err(PolicyAddrError::VelocityArithmeticOverflow));
    assert_eq!(g1d.spent_units(), 600);

    // Exact remaining cap succeeds!
    let (g2, a2) = g1d.authorize_spend(VelocitySpendRequest {
        window_id: 7,
        nonce: 2,
        amount_units: 400,
        policy_pin: pol_pin,
        authority_pin: auth_pin,
    });
    assert_eq!(a2, Ok(400));
    assert_eq!(g2.spent_units(), 1_000);

    // Forward window rotation succeeds; backward/same window rejected
    let (g2b, bad_rot) = g2.rotate_window(7, pol_pin, auth_pin);
    assert_eq!(bad_rot, Err(PolicyAddrError::InvalidWindowRotation));
    let (g3, ok_rot) = g2b.rotate_window(8, pol_pin, auth_pin);
    assert_eq!(ok_rot, Ok(()));
    assert_eq!(g3.window_id(), 8);
    assert_eq!(g3.spent_units(), 0);

    // Canonical 128-byte TransactionIntent roundtrip & tag validation
    let intent = CanonicalIntent128 {
        suite_tag: IntentSuiteTag::HybridEd25519MlDsa65,
        address_version: IntentAddressVersion::V2,
        identity_kind: IntentIdentityKind::HybridConjunctive,
        chain_id: 0x0102_0304_0506_0708,
        nonce: 42,
        timestamp_secs: 1_794_614_400,
        amount_units: (0x1234_5678_9ABCu128 << 64) | 0xDEF0_1122_3344_5566u128,
        rolling_window_spent: 999_999,
        recipient_commitment: [0xCDu8; 32],
        payload_digest: [0xEFu8; 32],
    };
    let encoded = encode_intent_128(&intent);
    let decoded = decode_intent_128(&encoded).expect("canonical intent must decode");
    assert_eq!(decoded.suite_tag, intent.suite_tag);
    assert_eq!(decoded.address_version, intent.address_version);
    assert_eq!(decoded.identity_kind, intent.identity_kind);
    assert_eq!(decoded.chain_id, intent.chain_id);
    assert_eq!(decoded.nonce, intent.nonce);
    assert_eq!(decoded.timestamp_secs, intent.timestamp_secs);
    assert_eq!(decoded.amount_units, intent.amount_units);
    assert_eq!(decoded.rolling_window_spent, intent.rolling_window_spent);
    assert_eq!(decoded.recipient_commitment, intent.recipient_commitment);
    assert_eq!(decoded.payload_digest, intent.payload_digest);
    assert_eq!(encode_intent_128(&decoded), encoded);

    let mut bad_magic = encoded;
    bad_magic[0] ^= 0x01;
    assert!(decode_intent_128(&bad_magic).is_none());
    let mut bad_suite = encoded;
    bad_suite[4] = 0xFF;
    assert!(decode_intent_128(&bad_suite).is_none());
    let mut bad_ver = encoded;
    bad_ver[6] = 0;
    assert!(decode_intent_128(&bad_ver).is_none());
    let mut bad_id = encoded;
    bad_id[7] = 9;
    assert!(decode_intent_128(&bad_id).is_none());

    // The verified intent namespace uses the canonical `qsag-addr` wire words and bytes.
    for (tag, word) in [
        (IntentSuiteTag::MlDsa65, 0x0102u16),
        (IntentSuiteTag::SlhDsa128f, 0x0202),
        (IntentSuiteTag::JortsPoseidon2, 0x0214),
        (IntentSuiteTag::HybridSecp256k1MlDsa44, 0x0501),
        (IntentSuiteTag::HybridEd25519MlDsa65, 0x0502),
    ] {
        assert_eq!(tag.to_u16(), word);
        assert_eq!(IntentSuiteTag::from_u16(word), Some(tag));
    }
    // Words the old verified namespace used for other suites are no longer admitted.
    for word in [0x0101u16, 0x0201, 0x0302] {
        assert_eq!(IntentSuiteTag::from_u16(word), None);
    }
    for (kind, byte) in [
        (IntentIdentityKind::SingleOrThreshold, 1u8),
        (IntentIdentityKind::HybridConjunctive, 2),
        (IntentIdentityKind::ScriptPredicate, 3),
    ] {
        assert_eq!(kind.to_u8(), byte);
        assert_eq!(IntentIdentityKind::from_u8(byte), Some(kind));
    }
    assert_eq!(SUITE_HYBRID_SECP256K1_MLDSA44, 0x0501);
    assert_eq!(SUITE_HYBRID_ED25519_MLDSA65, 0x0502);

    // The decoder reads a frame back only when the identity kind is the one the suite
    // mandates; the encoder is total, so every other pair encodes to a refused frame.
    let mut admitted = 0;
    for (suite, expected_kind) in [
        (
            IntentSuiteTag::MlDsa65,
            IntentIdentityKind::SingleOrThreshold,
        ),
        (
            IntentSuiteTag::SlhDsa128f,
            IntentIdentityKind::SingleOrThreshold,
        ),
        (
            IntentSuiteTag::JortsPoseidon2,
            IntentIdentityKind::SingleOrThreshold,
        ),
        (
            IntentSuiteTag::HybridSecp256k1MlDsa44,
            IntentIdentityKind::HybridConjunctive,
        ),
        (
            IntentSuiteTag::HybridEd25519MlDsa65,
            IntentIdentityKind::HybridConjunctive,
        ),
    ] {
        assert_eq!(suite.expected_identity_kind(), expected_kind);
        for kind in [
            IntentIdentityKind::SingleOrThreshold,
            IntentIdentityKind::HybridConjunctive,
            IntentIdentityKind::ScriptPredicate,
        ] {
            let paired = CanonicalIntent128 {
                suite_tag: suite,
                identity_kind: kind,
                ..intent
            };
            let frame = encode_intent_128(&paired);
            assert_eq!(suite.admits_identity_kind(kind), kind == expected_kind);
            match decode_intent_128(&frame) {
                Some(back) => {
                    assert_eq!(kind, expected_kind);
                    assert_eq!(back.suite_tag, suite);
                    assert_eq!(back.identity_kind, kind);
                    assert_eq!(encode_intent_128(&back), frame);
                    admitted += 1;
                }
                None => assert_ne!(kind, expected_kind),
            }
        }
    }
    assert_eq!(admitted, 5);

    // Hybrid domain framing role separation
    let magic = b"QSAG.HYBRID.V2";
    let id_c = [0x77u8; 32];
    let msg_d = [0x88u8; 32];
    assert!(check_hybrid_domain_framing(
        magic,
        0x01,
        HybridRoleTag::Classical,
        SUITE_HYBRID_ED25519_MLDSA65,
        &id_c,
        &id_c,
    ));
    // Classical role byte MUST NOT validate as PostQuantum!
    assert!(!check_hybrid_domain_framing(
        magic,
        0x01,
        HybridRoleTag::PostQuantum,
        SUITE_HYBRID_ED25519_MLDSA65,
        &id_c,
        &id_c,
    ));
    // Single-primitive suite code MUST NOT validate in hybrid framing!
    assert!(!check_hybrid_domain_framing(
        magic,
        0x02,
        HybridRoleTag::PostQuantum,
        0x0102,
        &id_c,
        &id_c,
    ));
    let d_cls = derive_hybrid_transcript_digest(
        HybridRoleTag::Classical,
        SUITE_HYBRID_ED25519_MLDSA65,
        &id_c,
        &[3; 32],
        &[4; 32],
        &msg_d,
    )
    .unwrap();
    let d_pq = derive_hybrid_transcript_digest(
        HybridRoleTag::PostQuantum,
        SUITE_HYBRID_ED25519_MLDSA65,
        &id_c,
        &[3; 32],
        &[4; 32],
        &msg_d,
    )
    .unwrap();
    assert_ne!(d_cls, d_pq);
}

#[test]
fn test_mldsa_release_gate_toprf_majority_and_hd_zero_test() {
    use qsag_verified::{
        CredHdGuardError, HdCommittedZeroTest, HdZeroTestPhase, MLDSA_Q, MLDSA44_R0_NORM_BOUND,
        MLDSA44_Z_NORM_BOUND, MLDSA65_R0_NORM_BOUND, MLDSA65_Z_NORM_BOUND, MlDsaBarrierChecks,
        MlDsaReleaseGate, check_mldsa44_norm_bounds, check_mldsa65_norm_bounds,
        mldsa44_sample_eta2_nibble_mod_q, toprf_majority_of_3_goldilocks,
    };

    // 0. FIPS 204 ML-DSA-44 eta=2 uniform nibble rejection (b < 15 -> 2 - (b mod 5) mod q)
    let mut counts = [0usize; 5]; // [0, 1, 2, q-2, q-1]
    for b in 0u8..16 {
        if b == 15 {
            assert_eq!(mldsa44_sample_eta2_nibble_mod_q(b), None);
        } else {
            let v = mldsa44_sample_eta2_nibble_mod_q(b).unwrap();
            match v {
                0 => counts[0] += 1,
                1 => counts[1] += 1,
                2 => counts[2] += 1,
                x if x == MLDSA_Q - 2 => counts[3] += 1,
                x if x == MLDSA_Q - 1 => counts[4] += 1,
                other => panic!("unexpected eta=2 residue {other}"),
            }
        }
    }
    assert_eq!(counts, [3, 3, 3, 3, 3]);
    assert_eq!(
        check_mldsa44_norm_bounds(MLDSA44_Z_NORM_BOUND - 1, MLDSA44_R0_NORM_BOUND - 1),
        (true, true)
    );
    assert_eq!(
        check_mldsa44_norm_bounds(MLDSA44_Z_NORM_BOUND, MLDSA44_R0_NORM_BOUND - 1),
        (false, true)
    );

    // 1. Threshold ML-DSA Rejection-Barrier Release Gate (P0-06)
    assert_eq!(
        check_mldsa65_norm_bounds(MLDSA65_Z_NORM_BOUND - 1, MLDSA65_R0_NORM_BOUND - 1),
        (true, true)
    );
    assert_eq!(
        check_mldsa65_norm_bounds(MLDSA65_Z_NORM_BOUND, MLDSA65_R0_NORM_BOUND - 1),
        (false, true)
    );

    let sid = [0x9Au8; 32];
    let secret_z = [0x5Cu8; 32];

    // Any single false barrier flag MUST block z_share release and abort!
    let gate_rej = MlDsaReleaseGate::new_sealed(sid, 4, secret_z);
    let (gate_rej1, res_rej) = gate_rej.try_release_z_share(MlDsaBarrierChecks {
        req_session_id: sid,
        req_attempt: 4,
        z_norm_ok: true,
        r0_norm_ok: false,
        w1_match: true,
        u_com_bound: true,
    });
    assert_eq!(
        res_rej,
        Err(CredHdGuardError::RejectionSamplingBarrierFailed)
    );
    assert!(gate_rej1.aborted());
    let (_gate_rej2, res_after_abort) = gate_rej1.try_release_z_share(MlDsaBarrierChecks {
        req_session_id: sid,
        req_attempt: 4,
        z_norm_ok: true,
        r0_norm_ok: true,
        w1_match: true,
        u_com_bound: true,
    });
    assert_eq!(
        res_after_abort,
        Err(CredHdGuardError::GateAbortedOrReleased)
    );

    // All 4 barrier predicates true -> releases once, then blocks replay!
    let gate_ok = MlDsaReleaseGate::new_sealed(sid, 4, secret_z);
    let (gate_ok1, res_ok) = gate_ok.try_release_z_share(MlDsaBarrierChecks {
        req_session_id: sid,
        req_attempt: 4,
        z_norm_ok: true,
        r0_norm_ok: true,
        w1_match: true,
        u_com_bound: true,
    });
    assert_eq!(res_ok, Ok(secret_z));
    assert!(gate_ok1.released());

    // 2. 2-of-5 Poseidon2 TOPRF 2-of-3 Goldilocks Majority + Cheater Pinpointing
    let v = GOLDILOCKS_PRIME - 7;
    assert_eq!(toprf_majority_of_3_goldilocks(v, v, v), Some((v, None)));
    assert_eq!(toprf_majority_of_3_goldilocks(99, v, v), Some((v, Some(0))));
    assert_eq!(
        toprf_majority_of_3_goldilocks(v, u64::MAX, v),
        Some((v, Some(1)))
    );
    assert_eq!(
        toprf_majority_of_3_goldilocks(v, v, GOLDILOCKS_PRIME),
        Some((v, Some(2)))
    );
    assert_eq!(toprf_majority_of_3_goldilocks(1, 2, 3), None);
    // Unanimous non-canonical >= GOLDILOCKS_PRIME MUST reject!
    assert_eq!(
        toprf_majority_of_3_goldilocks(GOLDILOCKS_PRIME, GOLDILOCKS_PRIME, GOLDILOCKS_PRIME),
        None
    );

    // 3. qsag-hd Committed Zero-Test Gate (P0-10)
    let q: u32 = 8_380_417;
    let local_res: u32 = 1_234_567;
    let peer_res: u32 = q - local_res;
    let peer_com = [0xE1u8; 32];

    // Premature local opening BEFORE freezing peer commitment MUST quarantine!
    let hd_premature = HdCommittedZeroTest::new_awaiting_peer_commit(sid, local_res, q);
    let (hd_q, pre_err) = hd_premature.open_local_residual(sid);
    assert_eq!(pre_err, Err(CredHdGuardError::InvalidHdPhaseTransition));
    assert!(hd_q.family_quarantined());

    // Non-zero sum mismatch MUST quarantine!
    let hd_bad0 = HdCommittedZeroTest::new_awaiting_peer_commit(sid, local_res, q);
    let (hd_bad1, _) = hd_bad0.freeze_peer_commitment(sid, peer_com);
    let (hd_bad2, opened_local) = hd_bad1.open_local_residual(sid);
    assert_eq!(opened_local, Ok(local_res));
    let (hd_bad3, zerr) = hd_bad2.verify_peer_opening(sid, peer_com, peer_res - 1);
    assert_eq!(zerr, Err(CredHdGuardError::HdZeroTestMismatchQuarantined));
    assert!(hd_bad3.family_quarantined());
    assert!(matches!(
        hd_bad3.phase(),
        HdZeroTestPhase::FamilyQuarantined
    ));

    // Honest freeze -> open -> verify_peer_opening succeeds when (local + peer) % q == 0!
    let hd_ok0 = HdCommittedZeroTest::new_awaiting_peer_commit(sid, local_res, q);
    let (hd_ok1, f_ok) = hd_ok0.freeze_peer_commitment(sid, peer_com);
    assert_eq!(f_ok, Ok(()));
    let (hd_ok2, l_ok) = hd_ok1.open_local_residual(sid);
    assert_eq!(l_ok, Ok(local_res));
    let (hd_ok3, v_ok) = hd_ok2.verify_peer_opening(sid, peer_com, peer_res);
    assert_eq!(v_ok, Ok(()));
    assert!(matches!(hd_ok3.phase(), HdZeroTestPhase::VerifiedZero));
    assert!(!hd_ok3.family_quarantined());
}

#[test]
fn test_pants_and_quorum_guards_kat_and_adversarial() {
    use qsag_verified::{
        PantsGuardError, RssLatchStepInput, RssLatchStepOutput, VerifiedRssPoisonLatch,
        VerifiedWaistbandRootGuard, VerifiedWotsC256Guard, WOTSC256_BASE_W, WOTSC256_CHAINS,
        WOTSC256_TARGET_SUM, WaistbandDerivationRequest, verified_wotsc256_extract_digits,
        verified_wotsc256_verify_sum, wotsc256_extract_digit,
    };

    // =========================================================================
    // 1. VerifiedBeltQuorumGuard: 2*q > n + f + global-liveness + jump + poison
    // =========================================================================
    // 2. VerifiedWotsC256Guard: w = 4, chains = 128, target_sum = 192
    // =========================================================================
    assert_eq!(WOTSC256_BASE_W, 4);
    assert_eq!(WOTSC256_CHAINS, 128);
    assert_eq!(WOTSC256_TARGET_SUM, 192);

    // 0x99 = 0b10_01_10_01 -> base-4 digits [2, 1, 2, 1] per byte -> sum = 6 * 32 = 192!
    let balanced_digest = [0x99u8; 32];
    assert_eq!(wotsc256_extract_digit(&balanced_digest, 0), 2);
    assert_eq!(wotsc256_extract_digit(&balanced_digest, 1), 1);
    assert_eq!(wotsc256_extract_digit(&balanced_digest, 2), 2);
    assert_eq!(wotsc256_extract_digit(&balanced_digest, 3), 1);
    assert!(verified_wotsc256_verify_sum(&balanced_digest));

    let digits = verified_wotsc256_extract_digits(&balanced_digest);
    let manual_sum: u32 = digits.iter().map(|&d| u32::from(d)).sum();
    assert_eq!(manual_sum, 192);

    let wg = match VerifiedWotsC256Guard::from_digest_verified(balanced_digest) {
        Ok(g) => g,
        Err(e) => panic!("balanced 192-sum digest rejected: {e:?}"),
    };
    assert_eq!(wg.validated_digest(), balanced_digest);
    assert_eq!(wg.verified_sum(), 192);
    assert_eq!(wg.digits(), digits);
    assert_eq!(wg.digit_at(0), Some(2));
    assert_eq!(wg.digit_at(127), Some(1));
    assert_eq!(wg.digit_at(128), None);

    // Perturbing a single digit changes sum != 192 -> REJECT!
    let mut bad_digest = balanced_digest;
    bad_digest[0] = 0x98; // [2, 1, 2, 0] -> sum = 191
    assert!(!verified_wotsc256_verify_sum(&bad_digest));
    assert!(!verified_wotsc256_verify_sum(&[0x00u8; 32]));
    assert!(!verified_wotsc256_verify_sum(&[0xFFu8; 32]));
    match VerifiedWotsC256Guard::from_digest_verified(bad_digest) {
        Ok(_) => panic!("sum=191 digest must be rejected"),
        Err(e) => assert_eq!(e, PantsGuardError::InvalidWotsC256TargetSum),
    }

    // =========================================================================
    // 3. VerifiedRssPoisonLatch: sticky poison BEFORE clearing pending_relations
    // =========================================================================
    let rl0 = VerifiedRssPoisonLatch::new_clean();
    assert_eq!(rl0.pending_relations(), 0);
    assert!(!rl0.is_unverified());
    assert!(!rl0.is_poisoned());

    // Staging relations marks unverified = true and blocks premature authorize_open()
    let (rl1, stg_ok) = rl0.stage_relations(64);
    assert_eq!(stg_ok, Ok(64));
    assert!(rl1.is_unverified());
    let (rl1b, early_open) = rl1.authorize_open();
    assert_eq!(early_open, Err(PantsGuardError::RssOpenBeforeCheck));

    // Failed check (`check_ok = false`) sets `poisoned = true` BEFORE clearing `pending_relations = 0`!
    let (rl_failed, chk_err) = rl1b.record_check_result(false);
    assert_eq!(chk_err, Err(PantsGuardError::RssVerificationCheckFailed));
    assert!(rl_failed.is_poisoned());
    assert!(rl_failed.is_unverified());
    assert_eq!(rl_failed.pending_relations(), 0);

    // Adversarial second check `record_check_result(true)` on `pending_relations == 0` MUST stay poisoned!
    let (rl_retry_true, retry_chk) =
        rl_failed.step(RssLatchStepInput::RecordCheckResult { check_ok: true });
    assert_eq!(retry_chk, Err(PantsGuardError::RssEnginePoisoned));
    assert!(rl_retry_true.is_poisoned());
    let (_rl_final, open_after_fail) = rl_retry_true.step(RssLatchStepInput::AuthorizeOpen);
    assert_eq!(open_after_fail, Err(PantsGuardError::RssEnginePoisoned));

    // Honest flow: stage -> record_check_result(true) -> authorize_open() == Ok
    let (h1, _) = VerifiedRssPoisonLatch::new_clean().stage_relations(32);
    let (h2, hchk) = h1.record_check_result(true);
    assert_eq!(hchk, Ok(()));
    let (h3, hopen) = h2.authorize_open();
    assert!(hopen.is_ok());
    let (_h4, hstep_open) = h3.step(RssLatchStepInput::AuthorizeOpen);
    assert!(matches!(
        hstep_open,
        Ok(RssLatchStepOutput::OpenAuthorized(_))
    ));

    // =========================================================================
    // 4. VerifiedWaistbandRootGuard: pk/params/child_root + first-signed lock
    // =========================================================================
    let pk_tag = [0x11u8; 32];
    let params_tag = [0x22u8; 32];
    let child_root = [0x33u8; 32];
    let cw_tag_1 = [0x44u8; 32];
    let cw_tag_2 = [0x55u8; 32];

    let wb0 = VerifiedWaistbandRootGuard::new_enrolled(pk_tag, params_tag, 3, 77, 5, child_root);
    assert!(!wb0.has_locked_codeword());
    assert!(!wb0.is_poisoned());
    assert_eq!(wb0.expected_static_child_root(), child_root);

    let honest_req = WaistbandDerivationRequest {
        req_layer: 3,
        req_tree: 77,
        req_kp: 5,
        cache_pk_tag: pk_tag,
        cache_params_tag: params_tag,
        recomputed_child_root: child_root,
        candidate_ancestor_codeword_tag: cw_tag_1,
    };

    // Corrupted intermediate child root fails closed and poisons!
    let mut bad_root_req = honest_req;
    bad_root_req.recomputed_child_root[0] ^= 0xFF;
    let (wb_bad, bad_res) =
        VerifiedWaistbandRootGuard::new_enrolled(pk_tag, params_tag, 3, 77, 5, child_root)
            .authorize_ancestor_derivation(bad_root_req);
    assert_eq!(
        bad_res.err(),
        Some(PantsGuardError::WaistbandChildRootMismatch)
    );
    assert!(wb_bad.is_poisoned());

    // Mismatched cache params tag fails closed and poisons!
    let mut bad_params_req = honest_req;
    bad_params_req.cache_params_tag[31] ^= 1;
    let (wb_bad_p, bad_p_res) =
        VerifiedWaistbandRootGuard::new_enrolled(pk_tag, params_tag, 3, 77, 5, child_root)
            .authorize_ancestor_derivation(bad_params_req);
    assert_eq!(
        bad_p_res.err(),
        Some(PantsGuardError::WaistbandCacheParamsMismatch)
    );
    assert!(wb_bad_p.is_poisoned());

    // Honest derivation locks codeword 1; idempotent replay succeeds; distinct codeword 2 fails closed!
    let (wb1, ok1) = wb0.authorize_ancestor_derivation(honest_req);
    let p1 = match ok1 {
        Ok(p) => p,
        Err(e) => panic!("honest waistband derivation failed: {e:?}"),
    };
    assert_eq!(p1.verified_child_root, child_root);
    assert_eq!(p1.authorized_codeword_tag, cw_tag_1);
    assert!(wb1.has_locked_codeword());
    assert_eq!(wb1.locked_ancestor_codeword_tag(), cw_tag_1);

    let (wb2, ok2) = wb1.authorize_ancestor_derivation(honest_req);
    assert!(ok2.is_ok());

    let mut second_cw_req = honest_req;
    second_cw_req.candidate_ancestor_codeword_tag = cw_tag_2;
    let (wb3, eqv_cw) = wb2.authorize_ancestor_derivation(second_cw_req);
    assert_eq!(
        eqv_cw.err(),
        Some(PantsGuardError::WaistbandCodewordEquivocation)
    );
    assert!(wb3.is_poisoned());
}
