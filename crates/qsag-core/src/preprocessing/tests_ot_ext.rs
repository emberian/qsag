use super::ot_ext::{
    derive_ot_ext_check_seed, establish_ideal_ot_ext_channel_for_test, hash_kos_u_cols,
    transpose_cols128_to_rows,
};
use super::rlwe_base_ot::{combiner_step_hash32, combiner_step_hash32_x4};
use super::*;

#[test]
fn ot_ext_check_key_polynomial_hash_matches_reference_including_odd_tails() {
    let mut rng = PartyPrivateRng::from_seed([0x73; 32], b"softspoken-hash");
    let chi_seed = rng.next_bytes32();
    let s0 = u128::from_le_bytes(chi_seed[..16].try_into().unwrap());
    let s1 = u128::from_le_bytes(chi_seed[16..].try_into().unwrap());
    let gf_mul = |a: u128, b: u128| {
        qsag_asm::gf2_128_dot(core::slice::from_ref(&a), core::slice::from_ref(&b))
    };
    for payload_words in [0usize, 1, 2, 3, 4, 5, 63, 64, 127, 128] {
        let col: Vec<u64> = (0..payload_words + 4).map(|_| rng.next_u64()).collect();
        let key = OtExtCheckKey::new(&chi_seed, payload_words);
        let actual = key.hash(&col);
        let blocks = payload_words.div_ceil(2);
        let eval_lane = |s: u128, tail: u128| {
            let mut acc = tail;
            let mut pow = s;
            for k in 0..blocks {
                let lo = col[2 * k] as u128;
                let hi = if 2 * k + 1 < payload_words {
                    (col[2 * k + 1] as u128) << 64
                } else {
                    0
                };
                acc ^= gf_mul(lo | hi, pow);
                pow = gf_mul(pow, s);
            }
            acc
        };
        let tail0 = (col[payload_words] as u128) | ((col[payload_words + 1] as u128) << 64);
        let tail1 = (col[payload_words + 2] as u128) | ((col[payload_words + 3] as u128) << 64);
        assert_eq!(actual, [eval_lane(s0, tail0), eval_lane(s1, tail1)]);
    }
}

#[test]
fn test_interactive_kos_ot_extension_kills_roy22_and_poisons_channel() {
    let mut rng_s = PartyPrivateRng::from_seed([0x31; 32], b"kos-s");
    let mut rng_r = PartyPrivateRng::from_seed([0x32; 32], b"kos-r");
    let (mut s_chan, mut r_chan) =
        establish_ideal_ot_ext_channel_for_test([0x55; 32], 0, 1, &mut rng_s, &mut rng_r);
    let choices = [0xDEAD_BEEF_CAFE_BABEu64, 0x0123_4567_89AB_CDEFu64];

    let (pend_r, u_msg) = r_chan.round1_send_u_cols(&choices, &mut rng_r);
    let (pend_s, chal_msg) = s_chan.round2_sample_challenge(&u_msg, &mut rng_s).unwrap();
    let (proof_msg, recv_pads) = r_chan.round3_prove_and_finish(pend_r, &chal_msg);
    let send_pads = s_chan.round4_verify_and_finish(pend_s, &proof_msg).unwrap();
    for w in 0..choices.len() {
        for b in 0..64 {
            let bit = ((choices[w] >> b) & 1) == 1;
            let exp = if bit {
                send_pads[64 * w + b].1
            } else {
                send_pads[64 * w + b].0
            };
            assert_eq!(recv_pads[64 * w + b], exp);
        }
    }

    // Corrupt 1 bit in column 127 (full 128-column KOS!) BEFORE seeing `chi_seed` -> rejects & poisons!
    let (pend_r_bad, mut u_msg_bad) = r_chan.round1_send_u_cols(&choices, &mut rng_r);
    u_msg_bad.u_cols[127][0] ^= 1;
    let (pend_s_bad, chal_bad) = s_chan
        .round2_sample_challenge(&u_msg_bad, &mut rng_s)
        .unwrap();
    let (proof_bad, _) = r_chan.round3_prove_and_finish(pend_r_bad, &chal_bad);
    assert_eq!(
        s_chan.round4_verify_and_finish(pend_s_bad, &proof_bad),
        Err(PreprocessError::KosOtCheckFailed {
            sender_id: 0,
            receiver_id: 1
        })
    );

    let (_, u_msg_after) = r_chan.round1_send_u_cols(&choices, &mut rng_r);
    assert!(matches!(
        s_chan.round2_sample_challenge(&u_msg_after, &mut rng_s),
        Err(PreprocessError::ChannelPoisoned {
            sender_id: 0,
            receiver_id: 1
        })
    ));
}

#[test]
fn kos_transpose_orientation_and_tail() {
    let cols: Vec<Vec<u64>> = (0..128).map(|i| vec![1u64 << (i % 64), !0u64]).collect();
    let rows = transpose_cols128_to_rows(&cols, 2);
    for b in 0..64 {
        let expected = (1u128 << b) | (1u128 << (b + 64));
        assert_eq!(rows[b], expected);
        assert_eq!(rows[64 + b], u128::MAX);
    }
    for col in 0..128 {
        for bit in 0..64 {
            let mut cols = vec![vec![0]; 128];
            cols[col][0] = 1u64 << bit;
            let rows = transpose_cols128_to_rows(&cols, 1);
            assert_eq!(rows[bit], 1u128 << col);
            assert_eq!(rows.iter().filter(|&&x| x != 0).count(), 1);
        }
    }
}

#[test]
fn four_branches_match_scalar_combiner() {
    let labels = ([0x19; 32], [0xe1; 32]);
    let seeds = ([0x28; 32], [0x83; 32]);
    for row in [0, 127] {
        for step in [0, 1, 383] {
            let batch = combiner_step_hash32_x4(&[0x57; 32], row, step, &labels, &seeds);
            for (slot, value) in batch.iter().enumerate() {
                assert_eq!(
                    *value,
                    combiner_step_hash32(
                        &[0x57; 32],
                        row,
                        step,
                        (slot / 2) as u8,
                        (slot % 2) as u8,
                        if slot / 2 == 0 { &labels.0 } else { &labels.1 },
                        if slot % 2 == 0 { &seeds.0 } else { &seeds.1 }
                    )
                );
            }
        }
    }
}

#[test]
fn forked_substream_kos_abort_poisons_parent_and_siblings() {
    let mut s_rng = PartyPrivateRng::from_seed([0x71; 32], b"ot_fork_s");
    let mut r_rng = PartyPrivateRng::from_seed([0x72; 32], b"ot_fork_r");
    let (mut s_parent, r_parent) =
        establish_ideal_ot_ext_channel_for_test([0xA1; 32], 0, 1, &mut s_rng, &mut r_rng);

    // Dropping a healthy finished child substream must NOT poison the parent or siblings.
    {
        let mut s_ok = s_parent.fork_substream([0xB0; 32], 0).unwrap();
        let mut r_ok = r_parent.fork_substream([0xB0; 32], 0);
        let (r_pend, u_msg) = r_ok.round1_send_u_cols(&[0xDEAD_BEEF_CAFE_BABEu64], &mut r_rng);
        let (s_pend, chal) = s_ok.round2_sample_challenge(&u_msg, &mut s_rng).unwrap();
        let (proof, _r_pads) = r_ok.round3_prove_and_finish(r_pend, &chal);
        let _s_pads = s_ok.round4_verify_and_finish(s_pend, &proof).unwrap();
    }
    assert!(!s_parent.is_poisoned());

    // Fork two concurrent child substreams sharing `delta`.
    let mut s_child_a = s_parent.fork_substream([0xB1; 32], 1).unwrap();
    let mut r_child_a = r_parent.fork_substream([0xB1; 32], 1);
    let mut s_child_b = s_parent.fork_substream([0xB2; 32], 2).unwrap();
    let mut r_child_b = r_parent.fork_substream([0xB2; 32], 2);

    // Start `child_b` round 2 BEFORE `child_a` fails its KOS consistency check.
    let (r_pend_b, u_msg_b) = r_child_b.round1_send_u_cols(&[0x1234_5678u64], &mut r_rng);
    let (s_pend_b, chal_b) = s_child_b
        .round2_sample_challenge(&u_msg_b, &mut s_rng)
        .unwrap();
    let (proof_b, _) = r_child_b.round3_prove_and_finish(r_pend_b, &chal_b);

    // Corrupt `child_a`'s SoftSpokenOT proof -> selective-failure probe on `delta`!
    let (r_pend_a, u_msg_a) = r_child_a.round1_send_u_cols(&[0xAAAA_5555u64], &mut r_rng);
    let (s_pend_a, chal_a) = s_child_a
        .round2_sample_challenge(&u_msg_a, &mut s_rng)
        .unwrap();
    let (mut bad_proof_a, _) = r_child_a.round3_prove_and_finish(r_pend_a, &chal_a);
    bad_proof_a.t_hash[255][0] ^= 1;
    assert!(matches!(
        s_child_a.round4_verify_and_finish(s_pend_a, &bad_proof_a),
        Err(PreprocessError::KosOtCheckFailed {
            sender_id: 0,
            receiver_id: 1
        })
    ));

    // Parent and sibling `child_b` (including its in-flight round 4!) must now be poisoned.
    assert!(s_parent.is_poisoned());
    assert!(s_child_a.is_poisoned());
    assert!(s_child_b.is_poisoned());
    assert!(matches!(
        s_parent.fork_substream([0xB3; 32], 3),
        Err(PreprocessError::ChannelPoisoned {
            sender_id: 0,
            receiver_id: 1
        })
    ));
    assert!(matches!(
        s_parent.round2_sample_challenge(&u_msg_b, &mut s_rng),
        Err(PreprocessError::ChannelPoisoned {
            sender_id: 0,
            receiver_id: 1
        })
    ));
    assert!(matches!(
        s_child_b.round4_verify_and_finish(s_pend_b, &proof_b),
        Err(PreprocessError::ChannelPoisoned {
            sender_id: 0,
            receiver_id: 1
        })
    ));
}

#[test]
fn softspoken_f4_slice_selective_failure_exact_quarter_probability_and_wire_roundtrip() {
    let sid = [0xC7; 32];
    let mut s_rng = PartyPrivateRng::from_seed([0x41; 32], b"ssot-s");
    let mut r_rng = PartyPrivateRng::from_seed([0x42; 32], b"ssot-r");

    // 1. Verify full 512-OT BaseOtRound4Msg + 8,224-byte OtExtProofMsg wire codecs.
    let (crs_r0, crs_com) = BaseOtCrsReceiverRound0::commit(sid, 0, 1, &mut r_rng);
    let (crs_s0, crs_sh) = BaseOtCrsSenderRound0::respond(sid, 0, 1, &crs_com, &mut s_rng);
    let (r_crs, crs_open) = crs_r0.open_and_derive_crs_coin(&crs_sh);
    let s_crs = crs_s0.verify_and_derive_crs_coin(&crs_open).unwrap();
    let (s_r1, msg1) = BaseOtExtSenderRound1::start_with_crs(s_crs, sid, 0, 1, &mut s_rng);
    assert_eq!(msg1.pk0s.len(), 512);
    assert_eq!(msg1.block_poks.len(), 4);
    let msg1_rt = BaseOtRound1Msg::from_bytes(&msg1.to_bytes()).unwrap();
    let (r_r2, msg2) =
        BaseOtExtReceiverRound2::respond_with_crs(r_crs, sid, 0, 1, &msg1_rt, &mut r_rng).unwrap();
    let msg2_rt = BaseOtRound2Msg::from_bytes(&msg2.to_bytes()).unwrap();
    let (s_r3, msg3) = s_r1
        .verify_fo_and_respond_coin(&msg2_rt, &mut s_rng)
        .unwrap();
    let (mut r_chan, msg4) = r_r2.finalize(&msg3);
    let msg4_bytes = msg4.to_bytes();
    let msg4_rt = BaseOtRound4Msg::from_bytes(&msg4_bytes).unwrap();
    let mut s_chan = s_r3.finalize(&msg4_rt).unwrap();

    let choices = [
        0xFEDC_BA98_7654_3210u64,
        0x1357_9BDF_2468_ACE0u64,
        0x7777_8888_9999_AAAAu64,
    ];
    let (r_pend, u_msg) = r_chan.round1_send_u_cols(&choices, &mut r_rng);
    assert_eq!(u_msg.u_cols.len(), 128);
    let (s_pend, chal) = s_chan.round2_sample_challenge(&u_msg, &mut s_rng).unwrap();
    let (proof, r_pads) = r_chan.round3_prove_and_finish(r_pend, &chal);
    let proof_bytes = proof.to_bytes();
    assert_eq!(proof_bytes.len(), OT_EXT_PROOF_BYTES);
    let proof_rt = OtExtProofMsg::from_bytes(&proof_bytes).unwrap();
    let s_pads = s_chan.round4_verify_and_finish(s_pend, &proof_rt).unwrap();
    for bit_idx in 0..(64 * choices.len()) {
        let bit = ((choices[bit_idx / 64] >> (bit_idx % 64)) & 1) == 1;
        assert_eq!(
            r_pads[bit_idx],
            if bit {
                s_pads[bit_idx].1
            } else {
                s_pads[bit_idx].0
            }
        );
    }

    // 2. Verify F_4 (`k = 2`) selective-abort predicate on slice `j`: flipping 1 bit of
    //    `u_cols[j]` passes for AT MOST 1 of the 4 F_4 digits `(b0, b1) in {0, 1}^2`!
    for j in [0usize, 1, 63, 64, 127] {
        for target_digit in 0..4u8 {
            let tb0 = (target_digit >> 1) & 1;
            let tb1 = target_digit & 1;
            let mut accepted = 0usize;
            for actual_digit in 0..4u8 {
                let ab0 = (actual_digit >> 1) & 1;
                let ab1 = actual_digit & 1;
                let (mut sc, mut rc) =
                    establish_ideal_ot_ext_channel_for_test(sid, 0, 1, &mut s_rng, &mut r_rng);
                sc.delta[0] = (sc.delta[0] & !(1u128 << j)) | ((ab0 as u128) << j);
                sc.delta[1] = (sc.delta[1] & !(1u128 << j)) | ((ab1 as u128) << j);
                sc.punctured_seeds[j] = rc.slice_seeds[j];
                softspoken_f4_zero_punctured_slot_ct(&mut sc.punctured_seeds[j], ab0, ab1);

                let (mut rp, mut um) =
                    rc.round1_send_u_cols(&[0x1234_5678_9ABC_DEF0u64], &mut r_rng);
                um.u_cols[j][0] ^= 1;
                rp.u_cols_digest = hash_kos_u_cols(
                    &rc.session_id,
                    rc.sender_id,
                    rc.receiver_id,
                    rp.batch_ctr,
                    &um.u_cols,
                );
                let (sp, ch) = sc.round2_sample_challenge(&um, &mut s_rng).unwrap();
                let check_seed = derive_ot_ext_check_seed(
                    &rc.session_id,
                    rc.sender_id,
                    rc.receiver_id,
                    0,
                    &sp.u_cols_digest,
                    &ch.chi_seed,
                );
                let key = OtExtCheckKey::new(&check_seed, 1);
                let err_h = key.hash(&[1, 0, 0, 0, 0]);
                let (mut prf, _) = rc.round3_prove_and_finish(rp, &ch);
                if tb0 == 1 {
                    prf.t_hash[j][0] ^= err_h[0];
                    prf.t_hash[j][1] ^= err_h[1];
                }
                if tb1 == 1 {
                    prf.t_hash[128 + j][0] ^= err_h[0];
                    prf.t_hash[128 + j][1] ^= err_h[1];
                }
                let ok = sc.round4_verify_and_finish(sp, &prf).is_ok();
                assert_eq!(ok, actual_digit == target_digit);
                if ok {
                    accepted += 1;
                }
            }
            assert_eq!(
                accepted, 1,
                "exactly 1 of 4 F_4 digits may accept on slice {j}"
            );
        }
    }
}
