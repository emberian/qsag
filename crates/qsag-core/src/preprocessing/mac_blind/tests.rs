use super::*;
use crate::preprocessing::gf256_auth::shamir_share_bits64_gf256_mats;
use crate::preprocessing::gf256_auth::shamir_share_tower128;
use crate::preprocessing::goldilocks_auth::{shamir_share_ext2, shamir_share_goldilocks};

fn rngs(tape: u8) -> Vec<PartyPrivateRng> {
    [tape, 200]
        .into_iter()
        .map(|seed| PartyPrivateRng::from_seed([seed; 32], b"mac-blind-regression"))
        .collect()
}

fn tower_rngs(n: usize, tape: u8) -> Vec<PartyPrivateRng> {
    (0..n)
        .map(|p| PartyPrivateRng::from_seed([tape ^ (p as u8); 32], b"mac-blind-pool"))
        .collect()
}

#[test]
fn pooled_blinding_consumes_each_triple_once_and_blinds_nonzero_residuals() {
    let n = 3;
    let sid = [0x4c; 32];
    let mut rngs = tower_rngs(n, 0x71);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    assert_eq!(mesh.staged_blinded_checks(), 0);
    mesh.prestage_blinded_checks(3, &mut rngs).unwrap();
    assert_eq!(mesh.staged_blinded_checks(), 3);
    let serials = mesh.staged_blinding_serials();
    assert_eq!(serials, (0..6).collect::<Vec<u64>>());

    // Every staged triple is a correct product of independent, nonzero values.
    let sum = |v: &[Tower128]| v.iter().fold(Tower128::ZERO, |a, &b| a.add(b));
    let mut seen = Vec::new();
    for triple in &mesh.blind_pool.triples {
        let (r, a, c) = (sum(&triple.r), sum(&triple.a), sum(&triple.c));
        assert!(c.ct_eq(r.mul(a)));
        assert!(!seen.contains(&r.0) && !seen.contains(&a.0));
        seen.push(r.0);
        seen.push(a.0);
    }

    // A zero residual, split additively, opens to zero and spends exactly two triples.
    let zero = [Tower128(0x55), Tower128(0x11), Tower128(0x44)];
    let w = blind_open_tower128(&sid, "pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
    assert!(w.ct_eq(Tower128::ZERO));
    assert_eq!(mesh.staged_blinding_serials(), (0..4).collect::<Vec<u64>>());

    // A nonzero residual stops at its first round, spending one more triple, and the
    // same residual opens to a different nonzero value under the next triple.
    let d = Tower128(0x1234_5678_9abc_def0_0fed_cba9_8765_4321);
    let bad = [d.add(Tower128(7)), Tower128(7), Tower128::ZERO];
    let w1 = blind_open_tower128(&sid, "pool_bad", &bad, Some(&mut mesh), &mut rngs).unwrap();
    assert_eq!(mesh.staged_blinding_serials(), (0..3).collect::<Vec<u64>>());
    let w2 = blind_open_tower128(&sid, "pool_bad", &bad, Some(&mut mesh), &mut rngs).unwrap();
    assert_eq!(mesh.staged_blinding_serials(), (0..2).collect::<Vec<u64>>());
    assert!(!w1.ct_eq(Tower128::ZERO) && !w2.ct_eq(Tower128::ZERO));
    assert!(!w1.ct_eq(w2) && !w1.ct_eq(d) && !w2.ct_eq(d));

    // An empty pool refills itself with serials that were never issued before.
    let w = blind_open_tower128(&sid, "pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
    assert!(w.ct_eq(Tower128::ZERO));
    assert!(mesh.staged_blinding_serials().is_empty());
    let w = blind_open_tower128(&sid, "pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
    assert!(w.ct_eq(Tower128::ZERO));
    let refilled = mesh.staged_blinding_serials();
    assert_eq!(
        refilled.len(),
        BLIND_ROUNDS * BLIND_AUTO_REFILL_CHECKS - BLIND_ROUNDS
    );
    assert!(refilled.iter().all(|&s| s >= 6));
}

#[test]
fn pooled_blinding_matches_direct_verdict_and_fails_closed_on_refill_failure() {
    let n = 3;
    let sid = [0x4d; 32];
    let mut rngs = tower_rngs(n, 0x72);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    let zero = [Tower128(9), Tower128(8), Tower128(1)];
    let bad = [Tower128(9), Tower128(8), Tower128(3)];
    for (residual, expect_zero) in [(&zero, true), (&bad, false)] {
        let pooled =
            blind_open_tower128(&sid, "pool_cmp", residual, Some(&mut mesh), &mut rngs).unwrap();
        let direct = blind_open_tower128(&sid, "pool_cmp", residual, None, &mut rngs).unwrap();
        assert_eq!(pooled.ct_eq(Tower128::ZERO), expect_zero);
        assert_eq!(direct.ct_eq(Tower128::ZERO), expect_zero);
    }

    // Wrong shapes are refused before any triple is spent.
    let before = mesh.staged_blinding_serials();
    assert!(
        blind_open_tower128(&sid, "pool_shape", &zero[..2], Some(&mut mesh), &mut rngs).is_err()
    );
    assert_eq!(mesh.staged_blinding_serials(), before);

    // Drain the pool, then make the automatic refill fail: the check is refused, the
    // pool is poisoned, and neither a later check nor a later refill is served.
    while mesh.staged_blinded_checks() > 0 {
        blind_open_tower128(&sid, "pool_drain", &zero, Some(&mut mesh), &mut rngs).unwrap();
    }
    mesh.fail_next_blinding_refill();
    assert_eq!(
        blind_open_tower128(&sid, "pool_fail", &zero, Some(&mut mesh), &mut rngs),
        Err(BLIND_POOL_POISONED)
    );
    assert!(mesh.blinding_poisoned());
    assert_eq!(
        blind_open_tower128(&sid, "pool_fail", &zero, Some(&mut mesh), &mut rngs),
        Err(BLIND_POOL_POISONED)
    );
    assert_eq!(
        mesh.prestage_blinded_checks(1, &mut rngs),
        Err(BLIND_POOL_POISONED)
    );
    assert_eq!(mesh.staged_blinded_checks(), 0);

    // A failed explicit refill discards what was already staged.
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    mesh.prestage_blinded_checks(2, &mut rngs).unwrap();
    mesh.fail_next_blinding_refill();
    assert!(mesh.prestage_blinded_checks(1, &mut rngs).is_err());
    assert!(mesh.blinding_poisoned() && mesh.staged_blinded_checks() == 0);
}

#[test]
fn unanimous_opening_share_shift_aborts_without_releasing_alpha() {
    let sid = [0x9d; 32];
    let points = [Goldilocks::ONE, Goldilocks::from_u64_reduced(2)];
    let alpha = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(19),
        Goldilocks::from_u64_reduced(23),
    );
    let x = Goldilocks::from_u64_reduced(41);
    let mut private = rngs(31);
    let alpha_shares = shamir_share_ext2(2, &points, alpha, &mut private[0]);
    let shares = shamir_share_goldilocks(2, &points, x, &mut private[0]);
    let macs = shamir_share_ext2(2, &points, alpha.mul_base(x), &mut private[0]);
    let mut shifted = shares.clone();
    shifted[0] += Goldilocks::ONE;
    assert!(matches!(
        commit_and_open_spdz_goldilocks_quorum(
            &sid,
            "unanimous_shift",
            2,
            &points,
            &shifted,
            &macs,
            &alpha_shares,
            &mut private,
        ),
        Err(PreprocessError::MacCheckFailed { .. })
    ));
    assert_eq!(
        commit_and_open_spdz_goldilocks_quorum(
            &sid,
            "unanimous_honest",
            2,
            &points,
            &shares,
            &macs,
            &alpha_shares,
            &mut private,
        )
        .unwrap(),
        x
    );
}

#[test]
fn degree_consistent_dealer_shift_with_full_redundancy_aborts() {
    let sid = [0x8d; 32];
    let points = (1..=3)
        .map(Goldilocks::from_u64_reduced)
        .collect::<Vec<_>>();
    let mut private = (0..3)
        .map(|p| PartyPrivateRng::from_seed([p + 60; 32], b"dealer-shift"))
        .collect::<Vec<_>>();
    let alpha = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(19),
        Goldilocks::from_u64_reduced(23),
    );
    let x = Goldilocks::from_u64_reduced(41);
    let keys = shamir_share_ext2(2, &points, alpha, &mut private[0]);
    let macs = shamir_share_ext2(2, &points, alpha.mul_base(x), &mut private[0]);
    let mut shares = shamir_share_goldilocks(2, &points, x, &mut private[0]);
    for share in &mut shares {
        *share += Goldilocks::ONE;
    }
    assert_eq!(
        open_and_check_degree_goldilocks(2, &points, &shares, "dealer_shift").unwrap(),
        x + Goldilocks::ONE
    );
    assert!(matches!(
        commit_and_open_spdz_goldilocks_quorum(
            &sid,
            "dealer_shift",
            2,
            &points,
            &shares,
            &macs,
            &keys,
            &mut private,
        ),
        Err(PreprocessError::MacCheckFailed { .. })
    ));
}

#[test]
fn degree_consistent_three_of_four_shift_aborts() {
    let sid = [0x8e; 32];
    let points = (1..=4)
        .map(Goldilocks::from_u64_reduced)
        .collect::<Vec<_>>();
    let mut private = (0..4)
        .map(|p| PartyPrivateRng::from_seed([p + 70; 32], b"three-of-four"))
        .collect::<Vec<_>>();
    let alpha = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(19),
        Goldilocks::from_u64_reduced(23),
    );
    let x = Goldilocks::from_u64_reduced(41);
    let keys = shamir_share_ext2(3, &points, alpha, &mut private[0]);
    let macs = shamir_share_ext2(3, &points, alpha.mul_base(x), &mut private[0]);
    let mut shares = shamir_share_goldilocks(3, &points, x, &mut private[0]);
    // The two corrupt points shift by a quadratic that vanishes at both
    // honest points. All four values STILL have degree <3, but x moves by 12.
    for p in 0..2 {
        shares[p] += (points[p] - points[2]) * (points[p] - points[3]);
    }
    assert_eq!(
        open_and_check_degree_goldilocks(3, &points, &shares, "coalition").unwrap(),
        x + Goldilocks::from_u64_reduced(12)
    );
    assert!(matches!(
        commit_and_open_spdz_goldilocks_quorum(
            &sid,
            "three_of_four_shift",
            3,
            &points,
            &shares,
            &macs,
            &keys,
            &mut private,
        ),
        Err(PreprocessError::MacCheckFailed { .. })
    ));
}

#[test]
fn private_degree_checks_reject_mac_tampering_at_an_extra_recipient() {
    let sid = [0x81; 32];
    let mut private = (0..4)
        .map(|p| PartyPrivateRng::from_seed([p + 80; 32], b"private-degree"))
        .collect::<Vec<_>>();
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
    let points = (1..=4)
        .map(Goldilocks::from_u64_reduced)
        .collect::<Vec<_>>();
    let mut shares = shamir_share_ext2(3, &points, GoldilocksExt2::ZERO, &mut private[0]);
    assert_eq!(
        blind_open_degree_ext2(
            &sid,
            "private_degree_honest",
            3,
            &points,
            &shares,
            &mut mesh,
            &mut private
        )
        .unwrap(),
        GoldilocksExt2::ZERO
    );
    shares[3] += GoldilocksExt2::ONE;
    assert!(matches!(
        blind_open_degree_ext2(
            &sid,
            "private_degree",
            3,
            &points,
            &shares,
            &mut mesh,
            &mut private
        ),
        Err(PreprocessError::DegreeCheckFailed { .. })
    ));
    let points = (1..=4).map(TowerGf256).collect::<Vec<_>>();
    let mut shares = shamir_share_tower128(3, &points, Tower128::ZERO, &mut private[0]);
    assert_eq!(
        blind_open_degree_tower128(
            &sid,
            "private_degree_honest",
            3,
            &points,
            &shares,
            &mut mesh,
            &mut private
        )
        .unwrap(),
        Tower128::ZERO
    );
    shares[3] = shares[3].add(Tower128::ONE);
    assert!(matches!(
        blind_open_degree_tower128(
            &sid,
            "private_degree",
            3,
            &points,
            &shares,
            &mut mesh,
            &mut private
        ),
        Err(PreprocessError::DegreeCheckFailed { .. })
    ));
}

#[test]
fn unanimous_boolean_share_shift_aborts() {
    let sid = [0x7e; 32];
    let points = [TowerGf256(1), TowerGf256(2)];
    let mats = points
        .iter()
        .map(|&p| PublicGf256Matrix::from_public_scalar(p))
        .collect::<Vec<_>>();
    let alpha = [Tower128(0x123456), Tower128(0x987654)];
    let mut private = rngs(51);
    let mut alpha_shares = vec![[Tower128::ZERO; 2]; 2];
    let mut macs = vec![[[Tower128::ZERO; 64]; 2]; 2];
    for lane in 0..2 {
        let key = shamir_share_tower128(2, &points, alpha[lane], &mut private[0]);
        for p in 0..2 {
            alpha_shares[p][lane] = key[p];
        }
        #[expect(
            clippy::needless_range_loop,
            reason = "Each bit indexes the same lane in both parties' MAC arrays"
        )]
        for bit in 0..64 {
            let mac = shamir_share_tower128(
                2,
                &points,
                alpha[lane].mul_gf256(TowerGf256(((42u64 >> bit) & 1) as u8)),
                &mut private[0],
            );
            for p in 0..2 {
                macs[p][lane][bit] = mac[p];
            }
        }
    }
    let mut shares = shamir_share_bits64_gf256_mats(2, &mats, 42, &mut private[0]);
    shares[0][0] ^= 1;
    assert!(matches!(
        commit_and_open_spdz_bs_gf256_quorum(
            &sid,
            "unanimous_boolean_shift",
            2,
            &points,
            &shares,
            &macs,
            &alpha_shares,
            &mut private,
        ),
        Err(PreprocessError::MacCheckFailed { .. })
    ));
}

#[test]
fn pooled_ext2_blinding_consumes_each_triple_once_and_fails_closed() {
    let n = 3;
    let sid = [0x4e; 32];
    let mut rngs = tower_rngs(n, 0x73);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    assert_eq!(mesh.staged_ext2_blinded_checks(), 0);
    mesh.prestage_ext2_blinded_checks(3, &mut rngs).unwrap();
    assert_eq!(mesh.staged_ext2_blinded_checks(), 3);
    assert_eq!(
        mesh.staged_ext2_blinding_serials(),
        (0..3).collect::<Vec<u64>>()
    );

    let sum = |v: &[GoldilocksExt2]| v.iter().copied().fold(GoldilocksExt2::ZERO, |a, b| a + b);
    let mut seen = Vec::new();
    for triple in &mesh.blind_pool.ext2_triples {
        let (r, a, c) = (sum(&triple.r), sum(&triple.a), sum(&triple.c));
        assert!(c.ct_eq(r * a));
        assert!(!seen.contains(&r) && !seen.contains(&a));
        seen.push(r);
        seen.push(a);
    }

    let g1 = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(55),
        Goldilocks::from_u64_reduced(11),
    );
    let g2 = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(23),
        Goldilocks::from_u64_reduced(99),
    );
    let zero = [g1, g2, -(g1 + g2)];
    let w = blind_open_ext2(&sid, "ext2_pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
    assert!(w.ct_eq(GoldilocksExt2::ZERO));
    assert_eq!(
        mesh.staged_ext2_blinding_serials(),
        (0..2).collect::<Vec<u64>>()
    );

    let d = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(0x1234_5678),
        Goldilocks::from_u64_reduced(0x9abc_def0),
    );
    let bad = [d + g1, -g1, GoldilocksExt2::ZERO];
    let w1 = blind_open_ext2(&sid, "ext2_pool_bad", &bad, Some(&mut mesh), &mut rngs).unwrap();
    assert_eq!(mesh.staged_ext2_blinding_serials(), vec![0]);
    let w2 = blind_open_ext2(&sid, "ext2_pool_bad", &bad, Some(&mut mesh), &mut rngs).unwrap();
    assert!(mesh.staged_ext2_blinding_serials().is_empty());
    assert!(!w1.ct_eq(GoldilocksExt2::ZERO) && !w2.ct_eq(GoldilocksExt2::ZERO));
    assert!(!w1.ct_eq(w2) && !w1.ct_eq(d) && !w2.ct_eq(d));

    // Automatic refill issues strictly fresh monotone serials >= 3.
    let w = blind_open_ext2(&sid, "ext2_pool_zero", &zero, Some(&mut mesh), &mut rngs).unwrap();
    assert!(w.ct_eq(GoldilocksExt2::ZERO));
    let refilled = mesh.staged_ext2_blinding_serials();
    assert_eq!(refilled.len(), BLIND_AUTO_REFILL_CHECKS - 1);
    assert!(refilled.iter().all(|&s| s >= 3));

    // Wrong shapes are refused before spending a triple.
    let before = mesh.staged_ext2_blinding_serials();
    assert!(
        blind_open_ext2(
            &sid,
            "ext2_pool_shape",
            &zero[..2],
            Some(&mut mesh),
            &mut rngs
        )
        .is_err()
    );
    assert_eq!(mesh.staged_ext2_blinding_serials(), before);

    // Failed refill poisons permanently and wipes all staged triples.
    while mesh.staged_ext2_blinded_checks() > 0 {
        blind_open_ext2(&sid, "ext2_drain", &zero, Some(&mut mesh), &mut rngs).unwrap();
    }
    mesh.fail_next_ext2_blinding_refill();
    assert_eq!(
        blind_open_ext2(&sid, "ext2_fail", &zero, Some(&mut mesh), &mut rngs),
        Err(EXT2_BLIND_POOL_POISONED)
    );
    assert!(mesh.ext2_blinding_poisoned());
    assert_eq!(
        blind_open_ext2(&sid, "ext2_fail", &zero, Some(&mut mesh), &mut rngs),
        Err(EXT2_BLIND_POOL_POISONED)
    );
    assert_eq!(
        mesh.prestage_ext2_blinded_checks(1, &mut rngs),
        Err(EXT2_BLIND_POOL_POISONED)
    );
}

#[test]
fn repeated_aborts_with_fixed_alpha_open_fresh_field_permutations() {
    let sid = [0x4b; 32];
    let alpha = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(19),
        Goldilocks::from_u64_reduced(23),
    );
    let d = -alpha.mul_base(Goldilocks::from_u64_reduced(17));
    let residual = [d - GoldilocksExt2::ONE, GoldilocksExt2::ONE];
    let mut seen = Vec::new();
    for tape in 1..=16 {
        let mut private = rngs(tape);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
        mesh.prestage_ext2_blinded_checks(1, &mut private).unwrap();
        let r = mesh.next_ext2_blinding_randomizer().unwrap();
        assert_eq!(mesh.staged_ext2_blinding_serials(), vec![0]);
        let w = blind_open_ext2(
            &sid,
            "fixed_alpha_abort",
            &residual,
            Some(&mut mesh),
            &mut private,
        )
        .unwrap();
        assert!(mesh.staged_ext2_blinding_serials().is_empty());
        assert_eq!(w, r * d, "pooled OLE must open exactly r * d");
        assert!(!w.ct_eq(GoldilocksExt2::ZERO));
        assert!(!w.ct_eq(d), "raw -delta*alpha residual escaped");
        assert!(!seen.contains(&w), "random tapes reused a check value");
        seen.push(w);
    }
    // Algebraic distribution check, beyond a sampling assertion: multiplication
    // by either nonzero residual is bijective. For a fixed corrupt contribution,
    // the honest randomizer that yields any target w exists and is unique.
    let other = d + GoldilocksExt2::ONE;
    let corrupt_r = GoldilocksExt2::new(Goldilocks::ONE, Goldilocks::from_u64_reduced(7));
    for target in seen {
        for residual in [d, other] {
            let honest_r = target * residual.inv().unwrap() - corrupt_r;
            assert_eq!((honest_r + corrupt_r) * residual, target);
        }
    }
}

#[test]
fn tooth_beaver_sacrifice_rejects_corrupted_pooled_blinding_triples_and_poisons_mesh() {
    let n = 3;
    let sid = [0x5a; 32];
    // Test single-bit corruption on BOTH live (`col = 1`) and companion (`col = 5`) Tower128 triples.
    for bad_col in [1usize, 5usize] {
        let mut rngs = tower_rngs(n, 0x91 ^ (bad_col as u8));
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        mesh.prestage_blinded_checks(1, &mut rngs).unwrap();
        assert_eq!(mesh.staged_blinded_checks(), 1);
        mesh.tamper_next_blinding_refill_c(2, bad_col, Tower128(1));
        assert_eq!(
            mesh.prestage_blinded_checks(2, &mut rngs),
            Err(PreprocessError::SacrificeResidualNonZero {
                phase: "blind_pool_refill",
            })
        );
        assert!(mesh.blinding_poisoned());
        assert_eq!(mesh.staged_blinded_checks(), 0);
    }

    // Test corruption on live (`col = 0`) and both companion (`col = 2`, `col = 5`) GoldilocksExt2 triples.
    for bad_col in [0usize, 2usize, 5usize] {
        let mut rngs = tower_rngs(n, 0xa1 ^ (bad_col as u8));
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        mesh.prestage_ext2_blinded_checks(1, &mut rngs).unwrap();
        assert_eq!(mesh.staged_ext2_blinded_checks(), 1);
        mesh.tamper_next_ext2_blinding_refill_c(1, bad_col, GoldilocksExt2::ONE);
        assert_eq!(
            mesh.prestage_ext2_blinded_checks(2, &mut rngs),
            Err(PreprocessError::SacrificeResidualNonZero {
                phase: "ext2_blind_pool_refill",
            })
        );
        assert!(mesh.ext2_blinding_poisoned());
        assert_eq!(mesh.staged_ext2_blinded_checks(), 0);
    }
}

#[test]
#[ignore = "retained OtMesh GoldilocksExt2 pooled vs direct blinding latency"]
fn bench_ext2_retained_mesh_mac_latency() {
    let n = 3;
    let sid = [0x4f; 32];
    let mut rngs = tower_rngs(n, 0x81);
    let t_setup = std::time::Instant::now();
    let mut mesh = OtMesh::establish(sid, &mut rngs).unwrap();
    let setup_ms = t_setup.elapsed().as_secs_f64() * 1e3;

    let checks = 64usize;
    let t_refill = std::time::Instant::now();
    mesh.prestage_ext2_blinded_checks(checks, &mut rngs)
        .unwrap();
    let refill_ms = t_refill.elapsed().as_secs_f64() * 1e3;

    let g1 = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(101),
        Goldilocks::from_u64_reduced(202),
    );
    let g2 = GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(303),
        Goldilocks::from_u64_reduced(404),
    );
    let zero = [g1, g2, -(g1 + g2)];
    let mut samples = Vec::with_capacity(checks);
    for i in 0..checks {
        let call_sid = [i as u8; 32];
        let t0 = std::time::Instant::now();
        let w = blind_open_ext2(
            &call_sid,
            "bench_ext2_pool",
            &zero,
            Some(&mut mesh),
            &mut rngs,
        )
        .unwrap();
        samples.push(t0.elapsed().as_secs_f64() * 1e3);
        assert!(w.ct_eq(GoldilocksExt2::ZERO));
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    std::eprintln!(
        "GoldilocksExt2 retained mesh (n={n}): setup={setup_ms:.2} ms, \
         refill({checks})={refill_ms:.2} ms ({:.3} ms/check), \
         online min={:.3} / median={:.3} / max={:.3} ms",
        refill_ms / checks as f64,
        samples[0],
        samples[checks / 2],
        samples[checks - 1],
    );
}

#[test]
fn tower_blinding_is_multiplication_with_receiver_randomness() {
    let sid = [0x3c; 32];
    let mut seen = Vec::new();
    for tape in 1..=8 {
        let mut private = rngs(tape);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
        let w = blind_open_tower128(
            &sid,
            "tower_abort",
            &[Tower128(0x1234), Tower128(0x9876)],
            Some(&mut mesh),
            &mut private,
        )
        .unwrap();
        assert_ne!(w, Tower128::ZERO);
        assert!(!seen.contains(&w));
        seen.push(w);
    }
    let mut private = rngs(42);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
    assert_eq!(
        blind_open_tower128(
            &sid,
            "tower_zero",
            &[Tower128(7), Tower128(7)],
            Some(&mut mesh),
            &mut private
        )
        .unwrap(),
        Tower128::ZERO
    );
}

#[test]
fn tooth_blind_open_degree_rejects_extra_unmapped_shares() {
    // Previously `blind_open_degree_ext2` and `blind_open_degree_tower128`
    // omitted `points.len() == shares.len()`, assigning `0` coefficients to trailing shares
    // in `shares[points.len()..]` during both syndrome checks and constant-term opening!
    let sid = [0x91; 32];
    let mut rngs3 = tower_rngs(3, 0x33);
    let mut mesh3 = OtMesh::establish_ideal_for_test(sid, &mut rngs3);

    let pts_gl_2 = [Goldilocks::ONE, Goldilocks::TWO];
    let corrupted_ext2_shares = [
        GoldilocksExt2::ZERO,
        GoldilocksExt2::ZERO,
        GoldilocksExt2::new(Goldilocks::from_u64_reduced(999), Goldilocks::ONE),
    ];
    assert_eq!(
        blind_open_degree_ext2(
            &sid,
            "tooth_ext2_mismatch",
            2,
            &pts_gl_2,
            &corrupted_ext2_shares,
            &mut mesh3,
            &mut rngs3,
        ),
        Err(PreprocessError::InvalidThreshold { t: 2, n: 3 })
    );

    let pts_t8_2 = [TowerGf256(1), TowerGf256(2)];
    let corrupted_t128_shares = [Tower128::ZERO, Tower128::ZERO, Tower128(0xDEAD_BEEF)];
    assert_eq!(
        blind_open_degree_tower128(
            &sid,
            "tooth_t128_mismatch",
            2,
            &pts_t8_2,
            &corrupted_t128_shares,
            &mut mesh3,
            &mut rngs3,
        ),
        Err(PreprocessError::InvalidThreshold { t: 2, n: 3 })
    );
}
