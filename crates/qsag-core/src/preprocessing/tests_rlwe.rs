use super::ot_ext::establish_ideal_ot_ext_channel_for_test;
use super::rlwe_proof::{
    RLWE_WITNESS_ENERGY_BOUND, RLWE_ZKPOK_Z_BOUND, bounded_ternary_witness, gaussian_accept,
    gaussian_exp_lower_bound, gaussian_exp_probability, gaussian_exp_upper_bound,
    gaussian_fraction_lt, gaussian_fraction_mul, hash_rlwe_zkpok_joint_challenges,
    mul_chal11_public, mul_chal11_signed_ct, poly_from_chal11, sample_gaussian_box,
    signed_box_to_rlwe_poly,
};
use super::*;

#[test]
fn test_rlwe_crs_orsigma_fo_and_kos_regressions() {
    // Worst-case ternary noise at `RLWE_N = 1024`: `|e| <= 1024 + 1024 + 1 = 2049 < 3072 = floor(q/4)`
    for &mag in &[0u16, 1, 512, 1025, 2049, 3071] {
        let f_pos = mag % RLWE_Q;
        let f_neg = (RLWE_Q - (mag % RLWE_Q)) % RLWE_Q;
        let t_pos = (RLWE_HALF_Q + mag) % RLWE_Q;
        let t_neg = (RLWE_HALF_Q + RLWE_Q - mag) % RLWE_Q;
        assert_eq!(rlwe_decode_bit_ct(f_pos), 0);
        assert_eq!(rlwe_decode_bit_ct(f_neg), 0);
        assert_eq!(rlwe_decode_bit_ct(t_pos), 1);
        assert_eq!(rlwe_decode_bit_ct(t_neg), 1);
    }

    let mut rng_s = PartyPrivateRng::from_seed([0x11; 32], b"ot-s");
    let mut rng_r = PartyPrivateRng::from_seed([0x22; 32], b"ot-r");
    let sid = [0xAA; 32];
    for idx in 0..2u32 {
        let choice = (idx & 1) == 1;
        let s0 = rng_s.next_bytes32();
        let s1 = rng_s.next_bytes32();
        let (sec, mut req) = rlwe_ot_choose(&sid, 0, 1, idx, choice, &mut rng_r);
        let mut resp = try_rlwe_ot_transfer(&sid, 0, 1, idx, &req, &s0, &s1, &mut rng_s).unwrap();
        let got = rlwe_ot_decrypt(&sec, &resp).unwrap();
        assert_eq!(got, if choice { s1 } else { s0 });

        // Forged Receiver OR-Sigma ZKPoK MUST abort at `try_rlwe_ot_transfer`!
        req.pok.chal0[0] ^= 0x01;
        assert_eq!(
            try_rlwe_ot_transfer(&sid, 0, 1, idx, &req, &s0, &s1, &mut rng_s).unwrap_err(),
            PreprocessError::BaseOtReceiverProofFailed {
                sender_id: 0,
                receiver_id: 1,
            }
        );

        // Active Chou-Orlandi / selective-failure ciphertext tamper on Receiver's chosen branch
        // (`b = 0` when `choice == false`, `b = 1` when `choice == true`) MUST abort via FO re-encryption!
        if choice {
            resp.u1.0[0] = (resp.u1.0[0] + 1) % RLWE_Q;
        } else {
            resp.u0.0[0] = (resp.u0.0[0] + 1) % RLWE_Q;
        }
        assert_eq!(
            rlwe_ot_decrypt(&sec, &resp),
            Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: 0,
                receiver_id: 1,
                ot_idx: idx,
            })
        );
    }

    // Verify isolated committed-CRS + OR-Sigma + 384-branch FO + 4-ciphertext combiner ceremony
    let (crs_r0, crs_com) = BaseOtCrsReceiverRound0::commit(sid, 0, 1, &mut rng_r);
    let (crs_s0, crs_sh) = BaseOtCrsSenderRound0::respond(sid, 0, 1, &crs_com, &mut rng_s);
    let (r_crs_coin, mut bad_crs_open) = crs_r0.open_and_derive_crs_coin(&crs_sh);
    let good_crs_open = bad_crs_open;
    bad_crs_open.receiver_crs_share[0] ^= 0x80;
    assert_eq!(
        crs_s0.verify_and_derive_crs_coin(&bad_crs_open),
        Err(PreprocessError::CoinCommitMismatch { party_id: 1 })
    );
    let (_, crs_s0_ok_sh) = BaseOtCrsSenderRound0::respond(sid, 0, 1, &crs_com, &mut rng_s);
    let _ = crs_s0_ok_sh;
    // Exercise KOS with ideal base OTs; the full bootstrap has a separate soak.
    let (mut s_chan, mut r_chan) =
        establish_ideal_ot_ext_channel_for_test(sid, 0, 1, &mut rng_s, &mut rng_r);
    let _ = (r_crs_coin, good_crs_open);

    let choices = [0xCAFE_BABE_1234_5678u64];
    let (pend_r, u_msg) = r_chan.round1_send_u_cols(&choices, &mut rng_r);
    let (pend_s, chal_msg) = s_chan.round2_sample_challenge(&u_msg, &mut rng_s).unwrap();
    let (proof_msg, r_pads) = r_chan.round3_prove_and_finish(pend_r, &chal_msg);
    let s_pads = s_chan.round4_verify_and_finish(pend_s, &proof_msg).unwrap();
    for b in 0..64 {
        let bit = ((choices[0] >> b) & 1) == 1;
        assert_eq!(r_pads[b], if bit { s_pads[b].1 } else { s_pads[b].0 });
    }
}

#[test]
fn test_negacyclic_ntt_matches_schoolbook_exact() {
    // Independent integer convolution, including wraparound signs, checks
    // every coefficient rather than an evaluation or a digest of the result.
    let mut rng = PartyPrivateRng::from_seed([0x97; 32], b"ntt-differential");
    for case in 0..12 {
        let mut a = RlwePoly::ZERO;
        let mut b = RlwePoly::ZERO;
        for (x, y) in a.0.iter_mut().zip(&mut b.0) {
            *x = (rng.next_u64() % u64::from(RLWE_Q)) as u16;
            *y = (rng.next_u64() % u64::from(RLWE_Q)) as u16;
        }
        match case {
            0 => a.0.fill(0),
            1 => {
                a.0.fill(0);
                a.0[0] = 1;
            }
            2 => {
                a.0.fill(0);
                a.0[RLWE_N - 1] = 1;
            }
            3 => {
                a.0.fill(RLWE_Q - 1);
                b.0.fill(RLWE_Q - 1);
            }
            _ => {}
        }
        let mut convolution = [0i64; RLWE_N];
        for (i, &x) in a.0.iter().enumerate() {
            for (j, &y) in b.0.iter().enumerate() {
                let product = i64::from(x) * i64::from(y);
                if i + j < RLWE_N {
                    convolution[i + j] += product;
                } else {
                    convolution[i + j - RLWE_N] -= product;
                }
            }
        }
        let expected = RlwePoly(convolution.map(|x| x.rem_euclid(i64::from(RLWE_Q)) as u16));
        assert_eq!(a.mul_negacyclic(&b), expected, "case {case}");
        let cached = a.to_ntt();
        assert_eq!(b.mul_ntt(&cached), expected, "cached case {case}");
        assert_eq!(cached.from_ntt(), a, "round trip case {case}");
    }
}

#[test]
fn gaussian_witness_energy_rejects_overweight_and_nonternary_inputs() {
    let s = RlwePoly([1; RLWE_N]);
    let mut e = RlwePoly([0; RLWE_N]);
    e.0[..RLWE_WITNESS_ENERGY_BOUND - RLWE_N].fill(RLWE_Q - 1);
    assert!(bounded_ternary_witness(&s, &e));
    e.0[RLWE_WITNESS_ENERGY_BOUND - RLWE_N] = 1;
    assert!(!bounded_ternary_witness(&s, &e));
    e.0.fill(0);
    e.0[0] = 2;
    assert!(!bounded_ternary_witness(&s, &e));
}

#[test]
fn gaussian_early_rejection_preserves_exact_samples() {
    // Exhaust the mask domain, including the wider box endpoints.
    for x in -3072i64..=3072 {
        let exponent = (x * x) as u64;
        let exact = gaussian_exp_probability::<24>(exponent);
        let upper = gaussian_exp_upper_bound(exponent);
        assert!(u128::from(exact[2]) < upper);
        let rounded = gaussian_exp_probability::<24>(exponent & !0x3fff);
        assert!(upper - u128::from(rounded[2]) <= 21);
        // A high limb below the lower bound accepts whatever the low limbs are.
        let lower = gaussian_exp_lower_bound(exponent);
        assert!(lower <= exact[2] && exact[2] - lower < 49);
        assert!(lower == 0 || gaussian_fraction_lt([u64::MAX, u64::MAX, lower - 1], exact));
    }
    for response in [false, true] {
        let mut fast = PartyPrivateRng::from_seed([0x61; 32], b"gaussian-parity");
        let mut reference = PartyPrivateRng::from_seed([0x61; 32], b"gaussian-parity");
        let half = if response {
            RLWE_ZKPOK_Z_BOUND
        } else {
            RLWE_ZKPOK_Z_BOUND + 2
        };
        for _ in 0..8 {
            let expected: [i16; RLWE_N] = core::array::from_fn(|_| {
                loop {
                    let mut coins = [0; 26];
                    reference.fill_bytes(&mut coins[..10]);
                    let proposal = u16::from_le_bytes([coins[0], coins[1]]) & 0x1fff;
                    let valid = proposal < 2 * half as u16;
                    let x = (proposal & 0u16.wrapping_sub(u16::from(valid))) as i16 - half;
                    let exponent = (i64::from(x) * i64::from(x)) as u64;
                    let probability = gaussian_exp_probability::<24>(exponent);
                    let high = u64::from_le_bytes(core::array::from_fn(|j| coins[2 + j]));
                    if u128::from(high) >= gaussian_exp_upper_bound(exponent) {
                        // Even all-zero lower limbs cannot accept this proposal.
                        assert!(!gaussian_fraction_lt([0, 0, high], probability));
                        continue;
                    }
                    reference.fill_bytes(&mut coins[10..]);
                    let random = [
                        u64::from_le_bytes(core::array::from_fn(|j| coins[10 + j])),
                        u64::from_le_bytes(core::array::from_fn(|j| coins[18 + j])),
                        high,
                    ];
                    if gaussian_fraction_lt(random, probability) & valid {
                        break x;
                    }
                }
            });
            assert_eq!(sample_gaussian_box(&mut fast, response), expected);
        }
        assert_eq!(fast.next_bytes32(), reference.next_bytes32());
    }
}

#[test]
fn gaussian_fixed_point_and_signed_encoding_regressions() {
    let vectors = [
        (
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
        ),
        (
            [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
            [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
            [0xfffffffffffffffe, 0xffffffffffffffff, 0xffffffffffffffff],
        ),
        (
            [0x0000000000000000, 0x0000000000000000, 0x8000000000000000],
            [0x0000000000000000, 0x0000000000000000, 0x8000000000000000],
            [0x0000000000000000, 0x0000000000000000, 0x4000000000000000],
        ),
        (
            [0x6014507ff930c949, 0x2cf7b739274dff8c, 0x61bcb43777160001],
            [0x4ddb63c11326c96a, 0x928291a04d74bd65, 0x8bba6dff24ffe4a1],
            [0x994355c4fa1a380c, 0xb14c99d84fa1d3b4, 0x3558a2f3cfc8d489],
        ),
        (
            [0x6004fe755afeb7fa, 0x99589bc0a8523e54, 0x0057101def3c8efc],
            [0xb447956ab300c18e, 0xc381f70308d60d1b, 0x052d3beeac8875ef],
            [0x7362140f8fb0a529, 0x3932d5ccc26f171d, 0x0001c2b2ccd1cba4],
        ),
        (
            [0xf7ac7bbe142ae0fa, 0x7a177925c88483e4, 0x965179c14ec364d6],
            [0x463bb39b81c52669, 0x212422d54eb4541b, 0xfa5dd0c6b3c0c132],
            [0xa9bbc172d8257923, 0x196b76b6cf0df9e1, 0x9302a716e1a1cfa5],
        ),
        (
            [0x60e666f9bd0f7d26, 0xa92e05e46db888d2, 0x6f1e3fe1377d50b3],
            [0x1c0ad2df2abe85f1, 0x8fe7168433e8cb02, 0x5104d2d66fd6eb12],
            [0x2200f7fffb8fb5c7, 0x2ad933d245dcd267, 0x232aaa33264f114c],
        ),
        (
            [0xc15a4ede0be61b32, 0x6735231d6c88fce9, 0x60b24dcef7168b11],
            [0x7e500f7fe9114bf6, 0x5d9b4e6816a7c70c, 0xfbe4672753993448],
            [0x139ab51a5e768557, 0xca318cbaff11e1da, 0x5f25180dd0a2f7e9],
        ),
        (
            [0x2819bcd0144b1fc2, 0x5f54ab4b0224d706, 0xd4203e771187f9b0],
            [0xe333474131549297, 0x64664ddd53c99715, 0xd45d20e208af1cf2],
            [0xbee22b75ef5620e5, 0x09b7e53a38eb5adb, 0xaff7deb09f3e1c75],
        ),
        (
            [0xf661780090c57d30, 0x098bf69e15023400, 0x68d3f90b8e7a7768],
            [0xea3acbb94239efff, 0x7689678e497106b8, 0xebd2970f3d43d0f7],
            [0x4a723e06d370dadc, 0x8818cbfbb405c161, 0x6090d15b2cacfc2d],
        ),
        (
            [0x3cfb5b7151707404, 0x880087b562bae564, 0x580fa697214fefca],
            [0x74f4c085da2221ee, 0xeec40f38322beba1, 0x630354181ec6d6b8],
            [0xb429ae69f91bc144, 0xbd93ee97eb7edc3c, 0x220f3288d45ebe41],
        ),
        (
            [0x3447b2216365d2a5, 0xeec753bf6f2aba9f, 0xb61dd1ba35c4f4af],
            [0x09da5a75f2152d42, 0x0835ba039102776f, 0xda91eb0cf2b40702],
            [0xb9dc372a3f51b286, 0x7b65d46d3a16bb06, 0x9b7d32b2f1d63338],
        ),
        (
            [0x6343e36b763c134b, 0x6c60f7581a504718, 0x50d06ff03873a409],
            [0x9d9b71229ad2551c, 0x3142cea4b94b437c, 0xbd6b015a2504e0fe],
            [0xdb3b7bea22836b35, 0xe9776e8698395d5a, 0x3bcbaa30687bed92],
        ),
        (
            [0x0e0e6f9f27252c47, 0xed938ededc8401bb, 0x36687a9a96e81572],
            [0xec99e2ae26b8f518, 0xdfef2c778e994ec2, 0xd62d34da314b3891],
            [0x1574924fa47891f7, 0xdb8e74f4b6335435, 0x2d84f2165fac531e],
        ),
        (
            [0x0f5e9b4953bc2d90, 0x3e104c2896c2c2da, 0x80d4681b0bab50c5],
            [0xb6db9067f9169b21, 0x99eff90ea26a4d0d, 0xdc56a7499f155f11],
            [0x174ad8491040ed11, 0xbdcf93db986f2d37, 0x6ee22501d3a72736],
        ),
        (
            [0x480c438810f20565, 0x796d0c6bbbdf1b32, 0x9adf1a43a6c20ea6],
            [0xfa0958ff3f6761b9, 0x8daa6cf1ec56fcfb, 0xaa8de815d392bf58],
            [0x7824d1977bc289ee, 0xed89e5f505d1d778, 0x672e00b9c818d6ed],
        ),
        (
            [0xbd56cdf245df737d, 0xe43ee088dff86a9f, 0xe3518d8dc7adff5e],
            [0xb972e8e63c6cc1b5, 0xe1c645d9d5ea329a, 0x59ca12c7e7a908bb],
            [0x684ef1ec9ee10999, 0xb5b0891a9d998f13, 0x4fbac93d3a58bda6],
        ),
        (
            [0xdb5c5ca15e439cff, 0xcb0c0db7f3eee465, 0x9f3c2e4e18210981],
            [0xe3553d6c77956d75, 0xf1e6567405bd7735, 0x252fa2738eb1efcb],
            [0x288ce05b1548ca25, 0x9fd3fcfefed6b0e8, 0x172153c9bfeb7c3d],
        ),
        (
            [0xd6eeb05ab8bbf310, 0x11d333606941a5ce, 0x6190b31b084e4cdc],
            [0xdbd03ebcb6c9c24b, 0x61a8d6ae2982baec, 0x9f9c7ee38bbbfdb7],
            [0x1aaf2e5fc5b68b33, 0xd35b02a003d4809d, 0x3cd483c6df590726],
        ),
    ];
    for (a, b, expected) in vectors {
        assert_eq!(gaussian_fraction_mul(a, b), expected);
        assert_eq!(
            gaussian_fraction_lt(a, b),
            a.iter().rev().cmp(b.iter().rev()).is_lt()
        );
    }
    let mut rng = PartyPrivateRng::from_seed([0x79; 32], b"gaussian-test");
    for _ in 0..8 {
        let response = sample_gaussian_box(&mut rng, true);
        assert!(
            response
                .iter()
                .all(|x| (-RLWE_ZKPOK_Z_BOUND..RLWE_ZKPOK_Z_BOUND).contains(x))
        );
    }
    for value in [-12000, -6145, -1, 0, 6145, 12000] {
        let encoded = signed_box_to_rlwe_poly(&[value; RLWE_N]);
        assert!(
            encoded
                .0
                .iter()
                .all(|&x| i32::from(x) == i32::from(value).rem_euclid(i32::from(RLWE_Q)))
        );
    }
    // Even a large positive log ratio must not wrap the fixed-point
    // exponent into an accepting probability.
    assert!(!gaussian_accept(690_000_000, &mut rng));
    assert!(!gaussian_accept(1 << 40, &mut rng));
    assert!(gaussian_accept(-690_000_000, &mut rng));
}

#[test]
fn test_real_rlwe_base_ot_bootstrap_end_to_end() {
    let mut sender = PartyPrivateRng::from_seed([0x31; 32], b"bootstrap-soak");
    let mut receiver = PartyPrivateRng::from_seed([0x32; 32], b"bootstrap-soak");
    let (mut send, mut recv) =
        try_establish_rlwe_ot_ext_channel([0x33; 32], 0, 1, &mut sender, &mut receiver).unwrap();
    let choices = [0x1234_5678_9abc_def0];
    let (rp, u) = recv.round1_send_u_cols(&choices, &mut receiver);
    let (sp, challenge) = send.round2_sample_challenge(&u, &mut sender).unwrap();
    let (proof, received) = recv.round3_prove_and_finish(rp, &challenge);
    let sent = send.round4_verify_and_finish(sp, &proof).unwrap();
    for (bit, (&got, &(zero, one))) in received.iter().zip(&sent).enumerate() {
        assert_eq!(
            got,
            if (choices[0] >> bit) & 1 == 0 {
                zero
            } else {
                one
            }
        );
    }
}

/// X^1024+1 splits into 1024 distinct roots modulo 12289. At every root,
/// all 2048 signed monomials have different evaluations, so no distinct
/// challenge difference vanishes in any CRT factor: every difference is a unit.
#[test]
fn signed_monomial_challenge_differences_are_units_in_every_crt_factor() {
    fn power(mut a: u32, mut e: usize) -> u32 {
        let mut out = 1;
        while e != 0 {
            if e & 1 != 0 {
                out = out * a % u32::from(RLWE_Q);
            }
            a = a * a % u32::from(RLWE_Q);
            e >>= 1;
        }
        out
    }
    let mut roots = 0;
    for root in 1..u32::from(RLWE_Q) {
        if power(root, RLWE_N) != u32::from(RLWE_Q) - 1 {
            continue;
        }
        roots += 1;
        let mut seen = vec![false; usize::from(RLWE_Q)];
        let mut value = 1u32;
        for _ in 0..2 * RLWE_N {
            assert!(!seen[value as usize], "colliding challenges at root {root}");
            seen[value as usize] = true;
            value = value * root % u32::from(RLWE_Q);
        }
        assert_eq!(value, 1);
    }
    assert_eq!(roots, RLWE_N);
    assert_eq!(RLWE_ZKPOK_REPS * RLWE_ZKPOK_CHAL_BITS as usize, 264);
}

#[test]
fn joint_proof_ot_roundtrip_both_choices() {
    let mut rng_diff = PartyPrivateRng::from_seed([0x44; 32], b"chal11-diff");
    let mut signed_a = [0i16; RLWE_N];
    for coeff in &mut signed_a {
        *coeff = ((rng_diff.next_u64() % 2001) as i16) - 1000;
    }
    let poly_a = signed_box_to_rlwe_poly(&signed_a);
    for u in [0u32, 1, 511, 1023, 1024, 1025, 1536, 2047] {
        let expected = poly_from_chal11(u).mul_negacyclic(&poly_a);
        assert_eq!(mul_chal11_public(&poly_a, u), expected);
        assert_eq!(
            signed_box_to_rlwe_poly(&mul_chal11_signed_ct(&signed_a, u)),
            expected
        );
    }

    let sid = [0xaa; 32];
    let mut receiver = PartyPrivateRng::from_seed([0x22; 32], b"joint-proof");
    let mut sender = PartyPrivateRng::from_seed([0x11; 32], b"joint-proof");
    for index in 0..2 {
        let (secret, request) = rlwe_ot_choose(&sid, 0, 1, index, index == 1, &mut receiver);
        let mut malformed = request.clone();
        malformed.pok.chal0[0] |= 1 << RLWE_ZKPOK_CHAL_BITS;
        assert!(
            try_rlwe_ot_transfer(
                &sid,
                0,
                1,
                index,
                &malformed,
                &[0x31; 32],
                &[0x72; 32],
                &mut sender
            )
            .is_err()
        );
        let mut malformed = request.clone();
        malformed.pok.chal0[0] |= 1 << 20;
        assert!(
            try_rlwe_ot_transfer(
                &sid,
                0,
                1,
                index,
                &malformed,
                &[0x31; 32],
                &[0x72; 32],
                &mut sender
            )
            .is_err()
        );
        let mut malformed = request.clone();
        malformed.pok.z_s0[0][0] = RLWE_ZKPOK_Z_BOUND;
        assert!(
            try_rlwe_ot_transfer(
                &sid,
                0,
                1,
                index,
                &malformed,
                &[0x31; 32],
                &[0x72; 32],
                &mut sender
            )
            .is_err()
        );
        // Fiat-Shamir-consistent transcript for a large-L2 / small-Linf pair
        // `s_bad = [1; 1024], e_bad = [-2000; 1024]`: every coordinate lies in `[-2000, 2000]`
        // (`||z||_inf = 2000 < 3070`) and every ring + Fiat-Shamir equation holds with `w0 = w1 = 0`,
        // yet `||z_s0||_2^2 + ||z_e0||_2^2 = 4_096_001_024 > RLWE_ZKPOK_PAIR_L2_SQ_BOUND` rejects it.
        let a_crs = RlwePoly::from_crs_xof_with_coin(&secret.crs_coin, &sid, 0, 1, index, 0);
        let a_ntt = a_crs.to_ntt();
        let t_crs = RlwePoly::from_crs_xof_with_coin(&secret.crs_coin, &sid, 0, 1, index, 1);
        let s_bad = [1i16; RLWE_N];
        let e_bad = [-2000i16; RLWE_N];
        let pk0_bad = signed_box_to_rlwe_poly(&s_bad)
            .mul_ntt(&a_ntt)
            .add(&signed_box_to_rlwe_poly(&e_bad));
        let zero_coms = vec![(RlwePoly::ZERO, RlwePoly::ZERO); RLWE_ZKPOK_REPS];
        let forged_chals = hash_rlwe_zkpok_joint_challenges(
            &secret.crs_coin,
            &sid,
            0,
            1,
            index,
            &a_crs,
            &pk0_bad,
            &t_crs,
            &zero_coms,
        );
        let mut l2_forged = RlweReceiverZkPok {
            chal0: forged_chals,
            chal1: [0u32; RLWE_ZKPOK_REPS],
            z_s0: Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]),
            z_e0: Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]),
            z_s1: Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]),
            z_e1: Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]),
        };
        for ((zs0, ze0), &chal) in l2_forged
            .z_s0
            .iter_mut()
            .zip(l2_forged.z_e0.iter_mut())
            .zip(forged_chals.iter())
        {
            *zs0 = mul_chal11_signed_ct(&s_bad, chal);
            *ze0 = mul_chal11_signed_ct(&e_bad, chal);
        }
        assert!(!l2_forged.verify(
            &secret.crs_coin,
            &sid,
            0,
            1,
            index,
            &a_ntt,
            &t_crs,
            &pk0_bad,
        ));
        let response = try_rlwe_ot_transfer(
            &sid,
            0,
            1,
            index,
            &request,
            &[0x31; 32],
            &[0x72; 32],
            &mut sender,
        )
        .unwrap();
        assert_eq!(
            rlwe_ot_decrypt(&secret, &response).unwrap(),
            if index == 1 { [0x72; 32] } else { [0x31; 32] }
        );
    }
}

#[test]
fn joint_challenge_binds_every_repetition() {
    let zero = RlwePoly([0; RLWE_N]);
    let mut commitments = vec![(zero, zero); RLWE_ZKPOK_REPS];
    let base = hash_rlwe_zkpok_joint_challenges(
        &[0; 32],
        &[1; 32],
        0,
        1,
        0,
        &zero,
        &zero,
        &zero,
        &commitments,
    );
    for rep in 0..RLWE_ZKPOK_REPS {
        commitments[rep].0.0[0] ^= 1;
        let changed = hash_rlwe_zkpok_joint_challenges(
            &[0; 32],
            &[1; 32],
            0,
            1,
            0,
            &zero,
            &zero,
            &zero,
            &commitments,
        );
        assert_ne!(base, changed);
        assert!(base.iter().zip(changed).filter(|(a, b)| *a != b).count() >= RLWE_ZKPOK_REPS - 3);
        commitments[rep].0.0[0] ^= 1;
    }
}

#[test]
fn joint_challenge_and_verify_bind_public_poly_a() {
    let sid = [0x5a; 32];
    let mut receiver = PartyPrivateRng::from_seed([0x33; 32], b"bind-poly-a");
    let (secret, request) = rlwe_ot_choose(&sid, 0, 1, 7, true, &mut receiver);
    let a_crs = RlwePoly::from_crs_xof_with_coin(&secret.crs_coin, &sid, 0, 1, 7, 0);
    let a_ntt = a_crs.to_ntt();
    let t_crs = RlwePoly::from_crs_xof_with_coin(&secret.crs_coin, &sid, 0, 1, 7, 1);
    assert!(request.pok.verify(
        &secret.crs_coin,
        &sid,
        0,
        1,
        7,
        &a_ntt,
        &t_crs,
        &request.pk0,
    ));

    // Perturbing any coefficient of `a_crs` changes the Fiat-Shamir challenge vector
    // and causes `RlweReceiverZkPok::verify` to reject immediately.
    let commitments = vec![(RlwePoly::ZERO, RlwePoly::ZERO); RLWE_ZKPOK_REPS];
    let base_chals = hash_rlwe_zkpok_joint_challenges(
        &secret.crs_coin,
        &sid,
        0,
        1,
        7,
        &a_crs,
        &request.pk0,
        &t_crs,
        &commitments,
    );
    for coeff_idx in [0usize, 1, 511, RLWE_N - 1] {
        let mut tampered_a = a_crs;
        tampered_a.0[coeff_idx] = (tampered_a.0[coeff_idx] + 1) % RLWE_Q;
        let tampered_chals = hash_rlwe_zkpok_joint_challenges(
            &secret.crs_coin,
            &sid,
            0,
            1,
            7,
            &tampered_a,
            &request.pk0,
            &t_crs,
            &commitments,
        );
        assert_ne!(base_chals, tampered_chals);
        assert!(!request.pok.verify(
            &secret.crs_coin,
            &sid,
            0,
            1,
            7,
            &tampered_a.to_ntt(),
            &t_crs,
            &request.pk0,
        ));
    }
}
