use qsag_whir_verified::{
    FP5_NONRESIDUE_W, Fp5, GOLDILOCKS_P, cwyz_bridge_claim_step_fp5, cwyz_duet_fold_fp5,
    decode_canonical_fp5, decode_canonical_gl24_digest, eval_fp5_univariate_at_base,
    eval_quadratic_sumcheck_wire_fp5, fp5_add, fp5_frobenius, fp5_mul, step_merkle_pair_order_400,
    step_merkle_pair_order_gl24, verify_affine_duet_fold_step_fp5,
    verify_cwyz_bridge_claim_step_fp5, verify_cwyz_duet_fold_step_fp5,
    verify_fp5_univariate_at_base_pin, verify_ood_pin_eq_fp5, verify_qsaghqm2_header,
    verify_quintic_schedule_envelope,
};

fn ext(x: [u64; 5]) -> Fp5 {
    Fp5 {
        c0: x[0],
        c1: x[1],
        c2: x[2],
        c3: x[3],
        c4: x[4],
    }
}

fn limbs(x: Fp5) -> [u64; 5] {
    [x.c0, x.c1, x.c2, x.c3, x.c4]
}

fn add(x: [u64; 5], y: [u64; 5]) -> [u64; 5] {
    core::array::from_fn(|i| ((x[i] as u128 + y[i] as u128) % GOLDILOCKS_P as u128) as u64)
}

fn sub(x: [u64; 5], y: [u64; 5]) -> [u64; 5] {
    core::array::from_fn(|i| {
        let rb = y[i] % GOLDILOCKS_P;
        ((x[i] as u128 + (GOLDILOCKS_P - rb) as u128) % GOLDILOCKS_P as u128) as u64
    })
}

fn scale(x: [u64; 5], y: u64) -> [u64; 5] {
    x.map(|v| ((v as u128 * y as u128) % GOLDILOCKS_P as u128) as u64)
}

// Independent schoolbook convolution, reducing X^5 = 3 term by term.
fn product(x: [u64; 5], y: [u64; 5]) -> [u64; 5] {
    let mut out = [0u64; 5];
    let p = GOLDILOCKS_P as u128;
    for i in 0..5 {
        for j in 0..5 {
            let term = (x[i] as u128 * y[j] as u128) % p;
            let term = term
                * if i + j >= 5 {
                    FP5_NONRESIDUE_W as u128
                } else {
                    1
                };
            out[(i + j) % 5] = ((out[(i + j) % 5] as u128 + term) % p) as u64;
        }
    }
    out
}

fn perturb_limb(x: [u64; 5], idx: usize) -> [u64; 5] {
    let mut out = x;
    out[idx] = ((out[idx] as u128 + 1) % GOLDILOCKS_P as u128) as u64;
    out
}

#[test]
fn quintic_frobenius_matches_lean_kats_and_is_ring_endomorphism() {
    // Matches `frob_katWide` in `lean/Qsag/Math/QuinticExt5.lean`.
    let wide = [
        81_985_529_216_486_895,
        18_364_758_544_493_064_720,
        16_045_690_984_503_098_046,
        1_089_357_896_855_742_840,
        1_234_605_616_436_508_552,
    ];
    assert_eq!(
        limbs(fp5_frobenius(ext(wide))),
        [
            81_985_529_216_486_895,
            9_961_272_706_250_400_476,
            4_912_495_906_482_251_711,
            9_291_945_967_817_452_589,
            15_493_897_884_983_376_685,
        ]
    );

    let b = [7, GOLDILOCKS_P - 5, 19, 42, 999_999];
    assert_eq!(
        limbs(fp5_frobenius(fp5_mul(ext(wide), ext(b)))),
        limbs(fp5_mul(fp5_frobenius(ext(wide)), fp5_frobenius(ext(b))))
    );
    assert_eq!(
        limbs(fp5_frobenius(fp5_add(ext(wide), ext(b)))),
        limbs(fp5_add(fp5_frobenius(ext(wide)), fp5_frobenius(ext(b))))
    );
}

#[test]
fn production_quintic_fold_and_verifiers_recover_coset_and_reject_perturbations() {
    let p = GOLDILOCKS_P;
    let inv_two = p / 2 + 1;
    for y in [1u64, 2, 7, p - 1] {
        let mut iy = 1u128;
        let mut base = (2 * y as u128) % p as u128;
        let mut exp = p - 2;
        while exp > 0 {
            if exp & 1 != 0 {
                iy = iy * base % p as u128;
            }
            base = base * base % p as u128;
            exp >>= 1;
        }
        let iy = iy as u64;
        for even in [[0; 5], [1, 2, 3, 4, 5], [p - 1; 5]] {
            let odd = [p - 2, 5, 9, 13, 17];
            let theta = [3, 7, p - 1, 11, 15];
            let alpha = [17, p - 2, 19, 23, 27];
            let beta = [29, 31, 37, 41, 43];
            let yo = scale(odd, y);
            let v0 = add(even, yo);
            let v1 = sub(even, yo);
            let yy = (y as u128 * y as u128 % p as u128) as u64;

            let expected_duet = add(odd, product(alpha, even));
            assert!(verify_affine_duet_fold_step_fp5(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                ext(alpha),
                ext(expected_duet),
            ));
            for limb in 0..5 {
                assert!(!verify_affine_duet_fold_step_fp5(
                    ext(v0),
                    ext(v1),
                    iy,
                    inv_two,
                    ext(alpha),
                    ext(perturb_limb(expected_duet, limb)),
                ));
            }

            let expected_cwyz = add(
                odd,
                product(add(alpha, scale(beta, yy)), add(even, product(theta, odd))),
            );
            let actual_cwyz = cwyz_duet_fold_fp5(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                yy,
                ext(theta),
                ext(alpha),
                ext(beta),
            );
            assert_eq!(limbs(actual_cwyz), expected_cwyz);
            assert!(verify_cwyz_duet_fold_step_fp5(
                ext(v0),
                ext(v1),
                iy,
                inv_two,
                yy,
                ext(theta),
                ext(alpha),
                ext(beta),
                ext(expected_cwyz),
            ));
            for limb in 0..5 {
                assert!(!verify_cwyz_duet_fold_step_fp5(
                    ext(v0),
                    ext(v1),
                    iy,
                    inv_two,
                    yy,
                    ext(theta),
                    ext(alpha),
                    ext(beta),
                    ext(perturb_limb(expected_cwyz, limb)),
                ));
            }
        }
    }
}

#[test]
fn cwyz_bridge_and_quadratic_sumcheck_verifiers_accept_and_reject_perturbations() {
    let p = GOLDILOCKS_P;
    let a0 = [3, 5, 7, 11, 13];
    let a1 = [13, p - 2, 19, 23, 29];
    let b0 = [29, 31, 37, 41, 43];
    let b1 = [43, 47, p - 3, 53, 59];
    let kn = [59, 61, 67, 71, 73];
    let phi = [2, 4, 6, 8, 10];
    let theta = [9, 10, 12, 14, 16];
    let alpha = [15, 16, 18, 20, 22];
    let beta = [21, 22, 24, 25, 27];

    let w0 = product(a0, b0);
    let w1 = product(a0, b1);
    let w2 = product(a1, b0);
    let w3 = product(a0, kn);
    let w4 = product(a1, kn);
    let claim = add(w0, product(a1, b1));

    let folded_a = add(a0, product(theta, a1));
    let c0_prime = add(a1, product(alpha, folded_a));
    let c1_prime = product(beta, folded_a);
    let k0_prime = add(b0, product(phi, b1));
    let expected = add(product(c0_prime, k0_prime), product(c1_prime, kn));

    let actual = cwyz_bridge_claim_step_fp5(
        ext(w0),
        ext(w1),
        ext(w2),
        ext(w3),
        ext(w4),
        ext(claim),
        ext(phi),
        ext(theta),
        ext(alpha),
        ext(beta),
    );
    assert_eq!(limbs(actual), expected);
    assert!(verify_cwyz_bridge_claim_step_fp5(
        ext(w0),
        ext(w1),
        ext(w2),
        ext(w3),
        ext(w4),
        ext(claim),
        ext(phi),
        ext(theta),
        ext(alpha),
        ext(beta),
        ext(expected),
    ));
    for limb in 0..5 {
        assert!(!verify_cwyz_bridge_claim_step_fp5(
            ext(w0),
            ext(w1),
            ext(w2),
            ext(w3),
            ext(w4),
            ext(claim),
            ext(phi),
            ext(theta),
            ext(alpha),
            ext(beta),
            ext(perturb_limb(expected, limb)),
        ));
    }

    // Quadratic sumcheck wire: g(0) + g(1) == sum_claim and g(r) == c0 + c1*r + c2*r^2.
    let g0 = eval_quadratic_sumcheck_wire_fp5(ext(a0), ext(a1), ext(claim), ext([0; 5]));
    let g1 = eval_quadratic_sumcheck_wire_fp5(ext(a0), ext(a1), ext(claim), ext([1, 0, 0, 0, 0]));
    let kernel_eval = limbs(fp5_add(g0, g1));
    assert!(verify_ood_pin_eq_fp5(ext(kernel_eval), ext(claim)));
    for limb in 0..5 {
        assert!(!verify_ood_pin_eq_fp5(
            ext(kernel_eval),
            ext(perturb_limb(claim, limb))
        ));
    }
}

#[test]
fn horner_canopy_and_wire_envelope_entrypoints() {
    let raw = [
        [GOLDILOCKS_P - 1, 1, 2, 3, 4],
        [5, 6, 7, 8, 9],
        [10, 11, 12, 13, 14],
    ];
    for n in 0..=raw.len() {
        let coeffs: Vec<_> = raw[..n].iter().copied().map(ext).collect();
        for z in [0, 1, 2, GOLDILOCKS_P - 1, u64::MAX] {
            let mut power = 1u64;
            let mut expected = [0u64; 5];
            for &c in &raw[..n] {
                expected = add(expected, scale(c, power));
                power = (power as u128 * z as u128 % GOLDILOCKS_P as u128) as u64;
            }
            assert_eq!(limbs(eval_fp5_univariate_at_base(&coeffs, z)), expected);
            assert!(verify_fp5_univariate_at_base_pin(&coeffs, z, ext(expected),));
            for limb in 0..5 {
                assert!(!verify_fp5_univariate_at_base_pin(
                    &coeffs,
                    z,
                    ext(perturb_limb(expected, limb)),
                ));
            }
        }
    }

    let mut raw40 = [0u8; 40];
    for i in 0..5 {
        raw40[8 * i..8 * (i + 1)].copy_from_slice(&(GOLDILOCKS_P - 1 - i as u64).to_le_bytes());
    }
    assert!(decode_canonical_fp5(&raw40).is_some());

    let mut raw56 = [0u8; 56];
    for i in 0..7 {
        raw56[8 * i..8 * (i + 1)].copy_from_slice(&(i as u64 + 10).to_le_bytes());
    }
    let gl24 = decode_canonical_gl24_digest(&raw56).expect("canonical gl24");
    assert_eq!(
        [
            gl24.l0, gl24.l1, gl24.l2, gl24.l3, gl24.l4, gl24.l5, gl24.l6
        ],
        [10, 11, 12, 13, 14, 15, 16]
    );
    assert!(step_merkle_pair_order_400(5, 0, [0xAA; 50], [0xBB; 50]).is_some());
    assert!(
        step_merkle_pair_order_gl24(
            5,
            0,
            gl24,
            qsag_whir_verified::Gl24Digest {
                l0: 1,
                l1: 1,
                l2: 1,
                l3: 1,
                l4: 1,
                l5: 1,
                l6: 1,
            }
        )
        .is_some()
    );
    assert!(verify_qsaghqm2_header(*b"QSAGHQM2", 1, 1, 1, 64, 64).is_some());
    assert!(verify_quintic_schedule_envelope(24, 8, 16, 4));
}

#[test]
fn slice_cursor_boundaries_and_canonical_limbs() {
    use qsag_whir_verified::*;
    let mut bytes = [0u8; 57];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = i as u8;
    }
    assert_eq!(load_le_u64_slice(&bytes, 1), Some(0x0807060504030201));
    for off in [50, 57, usize::MAX] {
        assert_eq!(load_le_u64_slice(&bytes, off), None);
    }
    for limb in 0..7 {
        let mut bad = bytes;
        bad[1 + 8 * limb..9 + 8 * limb].copy_from_slice(&GOLDILOCKS_P.to_le_bytes());
        assert!(decode_canonical_gl24_at(&bad, 1).is_none());
        assert_eq!(decode_canonical_fp5_at(&bad, 1).is_none(), limb < 5);
    }
    assert!(decode_canonical_gl24_at(&bytes, 1).is_some());
    assert!(decode_canonical_gl24_at(&bytes, 2).is_none());
    assert!(decode_canonical_fp5_at(&bytes, usize::MAX).is_none());
}

#[test]
fn steiner_count_matches_level_pruning_for_every_small_tree_opening() {
    use qsag_whir_verified::compute_steiner_multiproof_siblings as count;
    for depth in 0..=4 {
        let n = 1usize << depth;
        for mask in 1u32..1 << n {
            let leaves: Vec<_> = (0..n).filter(|&i| mask >> i & 1 != 0).collect();
            let mut active = mask;
            let mut expected = 0;
            for level in 0..depth {
                let mut parents = 0;
                for parent in 0..n >> (level + 1) {
                    let children = (active >> (2 * parent)) & 3;
                    if children == 1 || children == 2 {
                        expected += 1;
                    }
                    if children != 0 {
                        parents |= 1 << parent;
                    }
                }
                active = parents;
            }
            assert_eq!(count(depth, &leaves), Some(expected));
        }
    }
    for invalid in [&[][..], &[1, 1], &[3, 1], &[16], &[usize::MAX]] {
        assert_eq!(count(4, invalid), None);
    }
    assert_eq!(count(29, &[0]), None);
    assert_eq!(count(28, &[0, (1 << 28) - 1]), Some(54));
}

#[test]
fn row_round_interpolates_and_rejects_tampering() {
    use qsag_whir_verified::*;
    // Degree eight over the base field, challenged at an extension point.
    let polynomial = |x: Fp5| {
        let x = limbs(x);
        let mut y = fp5_one();
        for _ in 0..8 {
            y = fp5_mul(y, ext(x));
        }
        fp5_add(y, fp5_from_base(17))
    };
    let mut bytes = [0u8; 361];
    for i in 0..9 {
        let v = polynomial(fp5_from_base(i as u64));
        bytes[1 + 40 * i..9 + 40 * i].copy_from_slice(&v.c0.to_le_bytes());
    }
    for r in [[0; 5], [8, 0, 0, 0, 0], [0, 1, 2, 3, 4]] {
        let run = |b: &[u8], off, claim| {
            verify_deg8_row_sumcheck_round_at(b, off, fp5_from_base(claim), ext(r))
        };
        assert!(fp5_eq(run(&bytes, 1, 35).unwrap(), polynomial(ext(r))));
        assert!(run(&bytes, 1, 36).is_none());
        assert!(run(&bytes[..360], 1, 35).is_none());
        assert!(run(&bytes, usize::MAX, 35).is_none());
        for limb in 0..45 {
            let mut bad = bytes;
            bad[1 + 8 * limb..9 + 8 * limb].copy_from_slice(&GOLDILOCKS_P.to_le_bytes());
            assert!(run(&bad, 1, 35).is_none());
        }
    }
}

#[test]
fn row_chain_threads_the_claim_through_every_round() {
    use qsag_whir_verified::*;
    // The first polynomial is 2X - 1. At 3 it hands 5 to the second polynomial 5X.
    let mut bytes = [0u8; 721];
    for i in 0..9u64 {
        let first = qsag_whir_verified::sub(2 * i, 1);
        let pos = 1 + 40 * i as usize;
        bytes[pos..pos + 8].copy_from_slice(&first.to_le_bytes());
        bytes[pos + 360..pos + 368].copy_from_slice(&(5 * i).to_le_bytes());
    }
    let challenges = [fp5_from_base(3), fp5_from_base(7)];
    let run = |b: &[u8]| verify_qsaghqm2_row_rounds_at(b, 1, &challenges);
    assert!(fp5_eq(run(&bytes).unwrap(), fp5_from_base(35)));
    assert!(run(&bytes[..720]).is_none());
    bytes[361] = 1;
    assert!(run(&bytes).is_none());
    assert!(verify_qsaghqm2_row_rounds_at(&[], 0, &[]).is_some());
    assert!(verify_qsaghqm2_row_rounds_at(&[], usize::MAX, &[]).is_none());
    let too_many = [const { fp5_zero() }; 21];
    assert!(verify_qsaghqm2_row_rounds_at(&[0; 7560], 0, &too_many).is_none());
}

#[test]
fn opening_offsets_bind_the_fibers_and_profile_specific_path() {
    use qsag_whir_verified::*;
    let indices = [0, 1, 6];
    for (tag, width) in [(QSAGHQM2_PROFILE_TURBO400, 50), (QSAGHQM2_PROFILE_GL24, 56)] {
        for base in [false, true] {
            let split = 1 + 3 * 4 * if base { 8 } else { 40 };
            let end = split + 3 * width;
            let mut raw = vec![0; end + 1];
            let read = |bytes: &[u8]| qsaghqm2_opening_bounds(bytes, 1, &indices, 3, 2, base, tag);
            assert_eq!(read(&raw), Some((split, end)));
            assert_eq!(read(&raw[..end - 1]), None);
            raw[split - 8..split].copy_from_slice(&GOLDILOCKS_P.to_le_bytes());
            assert_eq!(read(&raw), None);
            raw[split - 8..split].fill(0);
            raw[end - 8..end].copy_from_slice(&GOLDILOCKS_P.to_le_bytes());
            assert_eq!(
                read(&raw),
                if tag == QSAGHQM2_PROFILE_GL24 {
                    None
                } else {
                    Some((split, end))
                }
            );
        }
    }
    assert_eq!(qsaghqm2_digest_block_end(&[], usize::MAX, 0, 1), None);
    assert_eq!(qsaghqm2_digest_block_end(&[], 0, usize::MAX, 2), None);
    assert_eq!(qsaghqm2_digest_block_end(&[], 0, 0, 3), None);
}

#[test]
fn deployed_fold_decodes_five_elements_and_threads_the_claim() {
    use qsag_whir_verified::*;
    let challenges = || CwyzFoldChals {
        phi: ext([3, 4, 1, 0, 2]),
        theta: fp5_from_base(7),
        alpha: fp5_from_base(11),
        beta: fp5_from_base(13),
    };
    let mut payload = vec![99];
    let mut claim = fp5_from_base(5);
    for i in 0..2 {
        let words: [[u64; 5]; 5] =
            core::array::from_fn(|j| core::array::from_fn(|k| 1 + (25 * i + 5 * j + k) as u64));
        for word in words.iter().flatten() {
            payload.extend(word.to_le_bytes());
        }
        let [a, b, c, f, g] = words.map(ext);
        let ch = challenges();
        claim =
            cwyz_bridge_claim_step_fp5(a, b, c, f, g, claim, ch.phi, ch.theta, ch.alpha, ch.beta);
    }
    let run = |b: &[u8], off| {
        verify_qsaghqm2_cwyz_folds_at(b, off, fp5_from_base(5), &[challenges(), challenges()])
    };
    assert!(fp5_eq(run(&payload, 1).unwrap(), claim));
    assert!(run(&payload[..400], 1).is_none());
    assert!(run(&payload, usize::MAX).is_none());
    for j in 0..50 {
        let mut bad = payload.clone();
        bad[1 + 8 * j..9 + 8 * j].copy_from_slice(&GOLDILOCKS_P.to_le_bytes());
        assert!(run(&bad, 1).is_none());
    }
}

#[test]
fn payload_consumes_deployed_sections_in_both_stage_counts_and_profiles() {
    use qsag_whir_verified::*;
    for steps in [&[4, 4, 4][..], &[6, 5, 4, 4][..]] {
        let rows = steps.iter().sum::<usize>() + 4 - 8;
        let challenges: Vec<_> = (0..rows).map(|_| fp5_zero()).collect();
        let stages = || {
            let stage = |step: usize| StageEnvelope {
                step_vars: step as u32,
                log_leaves: 3,
                indices: &[0, 1, 6],
            };
            PayloadStages {
                first: stage(steps[0]),
                second: stage(steps[1]),
                third: stage(steps[2]),
                fourth: steps.get(3).copied().map(stage),
            }
        };
        for (tag, width) in [(1, 50), (2, 56)] {
            let mut buf = vec![0; width + rows * 360 + 256 * 40 + 5 * 40];
            let mut fields = vec![width, width + rows * 360, buf.len() - 8];
            for (i, &step) in steps.iter().enumerate() {
                fields.push(buf.len());
                buf.resize(buf.len() + 200 * step, 0);
                if i + 1 < steps.len() {
                    buf.resize(buf.len() + width, 0);
                    fields.push(buf.len());
                    buf.resize(buf.len() + 80, 0);
                } else {
                    fields.push(buf.len());
                    buf.resize(buf.len() + 18 * 40, 0);
                }
                fields.push(buf.len());
                buf.resize(buf.len() + 3 * (1 << step) * if i == 0 { 8 } else { 40 }, 0);
                if tag == 2 {
                    fields.push(buf.len());
                }
                buf.resize(buf.len() + 3 * width, 0);
            }
            let run = |bytes: &[u8]| {
                verify_qsaghqm2_multiproof_and_rounds(bytes, tag, &challenges, 4, stages())
            };
            assert!(fp5_eq(run(&buf).unwrap(), fp5_zero()));
            assert!(run(&buf[..buf.len() - 1]).is_none());
            buf.push(0);
            assert!(run(&buf).is_none());
            buf.pop();
            for off in fields {
                buf[off..off + 8].copy_from_slice(&GOLDILOCKS_P.to_le_bytes());
                assert!(run(&buf).is_none());
                buf[off..off + 8].fill(0);
            }
            buf[width] = 1;
            assert!(run(&buf).is_none());
        }
    }
}
