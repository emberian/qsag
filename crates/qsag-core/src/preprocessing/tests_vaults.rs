#![allow(clippy::needless_range_loop)]

use super::gf256_auth::shamir_share_bits64_gf256;
use super::goldilocks_auth::shamir_share_goldilocks;
use super::keccak_vault::{
    checked_boolean_product_with_hook, run_dealerless_pi_triple_f2_with_alpha_and_fault,
};
use super::*;

use crate::sponge::poseidon2::poseidon2_sbox7;

#[test]
fn dense_active_three_party_product() {
    let sid = [0x19; 32];
    let mut rngs: Vec<_> = (0..3)
        .map(|i| PartyPrivateRng::from_seed([i + 1; 32], b"dense-active-test"))
        .collect();
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    let a = vec![
        vec![0x123456789abcdef0],
        vec![0xdeadbeefcafebabe],
        vec![0x33335555ffff0000],
    ];
    let b = vec![
        vec![0x12340000ffff9876],
        vec![0x5555aaaa12344321],
        vec![0x777788889999aaaa],
    ];
    let c = checked_boolean_product(&sid, &a, &b, &mut mesh, &mut rngs).unwrap();
    assert_eq!(
        c.iter().fold(0, |x, p| x ^ p[0]),
        a.iter().fold(0, |x, p| x ^ p[0]) & b.iter().fold(0, |x, p| x ^ p[0])
    );
    assert!(
        checked_boolean_product_with_hook(&sid, &a, &b, &mut mesh, &mut rngs, |shares| {
            shares[0][0][0] ^= 1
        })
        .is_err()
    );
}

#[test]
fn test_dealerless_pi_triple_f2_dishonest_majority_booleanity_and_mac_abort() {
    let sid = [0x77; 32];
    // Dishonest majority 3-of-4 (`2t - 1 = 5 > 4`, up to `2` active corruptions)
    let t = 3usize;
    let n = 4usize;
    let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
    let mut rngs = make_party_rngs(n, 0x40);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

    // regression guard: zero or duplicate `eval_point` at index `>= t` MUST be rejected!
    let mut bad_pts_zero = pts.clone();
    bad_pts_zero[3] = TowerGf256::ZERO;
    assert_eq!(
        run_dealerless_pi_triple_f2(sid, t, &bad_pts_zero, 1, &mut mesh, &mut rngs).unwrap_err(),
        PreprocessError::DuplicateOrZeroEvalPoint
    );
    let mut bad_pts_dup = pts.clone();
    bad_pts_dup[3] = bad_pts_dup[1];
    assert_eq!(
        run_dealerless_pi_triple_f2(sid, t, &bad_pts_dup, 1, &mut mesh, &mut rngs).unwrap_err(),
        PreprocessError::DuplicateOrZeroEvalPoint
    );

    let mut vaults = run_dealerless_pi_triple_f2(sid, t, &pts, 2, &mut mesh, &mut rngs).unwrap();
    for k in 0..2 {
        let a_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].a).collect();
        let b_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].b).collect();
        let c_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].c).collect();
        let a_macs: Vec<[[Tower128; 64]; 2]> = (0..t).map(|q| vaults[q].triples[k].a_mac).collect();
        let alpha_sh: Vec<[Tower128; 2]> = (0..t).map(|q| vaults[q].mac_alpha_lanes).collect();

        // Honest quorum SPDZ opening passes (`t=3` out of `n=4`)
        let a = commit_and_open_spdz_bs_gf256_quorum(
            &sid,
            "test_spdz_open",
            t,
            &pts[..t],
            &a_sh[..t],
            &a_macs,
            &alpha_sh,
            &mut rngs[..t],
        )
        .unwrap();
        let b = open_and_check_degree_bs_gf256(t, &pts, &b_sh, "test").unwrap();
        let c = open_and_check_degree_bs_gf256(t, &pts, &c_sh, "test").unwrap();
        assert_eq!(&a[1..], &[0u64; 7]);
        assert_eq!(&b[1..], &[0u64; 7]);
        assert_eq!(&c[1..], &[0u64; 7]);
        assert_eq!(c[0], a[0] & b[0]);

        // Dishonest-majority (`c = 2` corrupt parties in `0..t`) share forgery (`f(0)` flipped by `1`)
        // MUST fail SPDZ `MacCheck`! (Note: on `[1, 2, 3]` in `GF(2^8)`, `lambda = [1, 1, 1]`, so
        // flipping plane 0 at `p = 0` and cancelling plane 1 across `p = 0, 1` shifts `f(0)` by `1`!)
        let mut forged_a = a_sh[..t].to_vec();
        forged_a[0][0] ^= 1;
        forged_a[0][1] ^= 1;
        forged_a[1][1] ^= 1;
        assert!(matches!(
            commit_and_open_spdz_bs_gf256_quorum(
                &sid,
                "test_spdz_forge",
                t,
                &pts[..t],
                &forged_a,
                &a_macs,
                &alpha_sh,
                &mut rngs[..t],
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
    }

    // Poisoning burns `mac_alpha_lanes` and blocks all future `pop_triple()` calls
    vaults[0].poison_and_wipe();
    assert_eq!(vaults[0].mac_alpha_lanes, [Tower128::ZERO; 2]);
    assert_eq!(
        vaults[0].pop_triple().unwrap_err(),
        PreprocessError::VaultPoisoned {
            kind: "Keccak triple"
        }
    );

    // single-lane non-Boolean injection (`TowerGf256(2) \in GF(256) \ GF(2)` at bit `37`)
    // MUST pass `0..n` degree check AND abort with `NonBooleanBitDetected` (`2^{-256}` soundness, 0 blind spots)!
    let mut non_bool_planes = [[0u64; 8]; 4];
    let nb_poly = [TowerGf256(2), TowerGf256(9), TowerGf256(17)];
    for p in 0..n {
        bs_gf256_insert_lane(
            &mut non_bool_planes[p],
            37,
            eval_poly_gf256(&nb_poly, pts[p]),
        );
    }
    let err_nb = run_dealerless_pi_triple_f2_with_fault(
        [0x78; 32],
        t,
        &pts,
        1,
        &mut mesh,
        &mut rngs,
        |p, a_vec, _| {
            bs_gf256_xor_assign(&mut a_vec[0], &non_bool_planes[p]);
        },
    )
    .unwrap_err();
    // The hook mutates already-authenticated Shamir shares, so PiMAC rejects
    // before the value can be released or combined.
    assert_eq!(
        err_nb,
        PreprocessError::MacCheckFailed {
            phase: "spdz_bs_gf256_pimac",
            accused_party: None,
        }
    );

    // Corrupt `c_sh` with a consistent degree-`<t` Boolean offset -> SPDZ companion sacrifice MUST abort!
    let bad_offset = shamir_share_bits64_gf256(t, &pts, 1u64, &mut rngs[0]);
    let err = run_dealerless_pi_triple_f2_with_fault(
        [0x79; 32],
        t,
        &pts,
        1,
        &mut mesh,
        &mut rngs,
        |p, _, c_vec| {
            bs_gf256_xor_assign(&mut c_vec[0], &bad_offset[p]);
        },
    )
    .unwrap_err();
    assert_eq!(
        err,
        PreprocessError::MacCheckFailed {
            phase: "spdz_bs_gf256_pimac",
            accused_party: None,
        }
    );
}

type PiTripleF2Run = Result<(Vec<PreprocessedKeccakPartyVault>, [u8; 32]), PreprocessError>;

/// One `Π_triple_f2` run from party seeds `rng_tag`, returning the vaults and the
/// ceremony's transcript digest.
fn run_pi_triple_f2_with_transcript<F>(
    sid: [u8; 32],
    t: usize,
    pts: &[TowerGf256],
    num_triples: usize,
    rng_tag: u8,
    fault_hook: F,
) -> PiTripleF2Run
where
    F: FnMut(usize, &mut [BitslicedGf256x64], &mut [BitslicedGf256x64]),
{
    let mut rngs = make_party_rngs(pts.len(), rng_tag);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    let (alpha_contribs, alpha_shamir) = spdz_setup_alpha_gf256(&sid, t, pts, &mut rngs)?;
    run_dealerless_pi_triple_f2_with_alpha_and_fault(
        sid,
        t,
        pts,
        num_triples,
        &alpha_contribs,
        &alpha_shamir,
        &mut mesh,
        &mut rngs,
        fault_hook,
    )
}

#[test]
fn test_coin_permutation_is_a_permutation_and_roughly_uniform() {
    for len in [0usize, 1, 2, 3, 12, 97, 1000] {
        let perm = derive_coin_permutation(&[0x42; 32], b"test", len);
        let mut sorted = perm.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..len as u32).collect::<Vec<u32>>());
    }
    // Domain and coin both select the permutation.
    let base = derive_coin_permutation(&[0x42; 32], b"test", 97);
    assert_ne!(base, derive_coin_permutation(&[0x43; 32], b"test", 97));
    assert_ne!(base, derive_coin_permutation(&[0x42; 32], b"other", 97));
    assert_eq!(base, derive_coin_permutation(&[0x42; 32], b"test", 97));

    // Every value lands on every position about equally often (expected 1200 of 6000
    // each, standard deviation about 31; the bounds are more than 6 sigma wide).
    let mut hits = [[0u32; 5]; 5];
    for trial in 0u32..6000 {
        let mut coin = [0u8; 32];
        coin[0..4].copy_from_slice(&trial.to_le_bytes());
        let perm = derive_coin_permutation(&coin, b"test", 5);
        for (pos, &val) in perm.iter().enumerate() {
            hits[pos][val as usize] += 1;
        }
    }
    for row in &hits {
        for &count in row {
            assert!(
                (1000..=1400).contains(&count),
                "position/value count {}",
                count
            );
        }
    }
}

#[test]
fn test_pi_triple_f2_honest_valid_and_transcript_follows_the_parties_coins() {
    let sid = [0x7A; 32];
    let t = 2usize;
    let n = 2usize;
    let num_triples = 4usize;
    let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();

    let mut transcripts = Vec::new();
    let mut opened = Vec::new();
    for rng_tag in [0x51u8, 0x52, 0x51] {
        let (vaults, transcript) =
            run_pi_triple_f2_with_transcript(sid, t, &pts, num_triples, rng_tag, |_, _, _| {})
                .expect("honest run");
        for k in 0..num_triples {
            let a_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].a).collect();
            let b_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].b).collect();
            let c_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].c).collect();
            let a = open_and_check_degree_bs_gf256(t, &pts, &a_sh, "test").unwrap();
            let b = open_and_check_degree_bs_gf256(t, &pts, &b_sh, "test").unwrap();
            let c = open_and_check_degree_bs_gf256(t, &pts, &c_sh, "test").unwrap();
            assert_eq!(&a[1..], &[0u64; 7]);
            assert_eq!(&b[1..], &[0u64; 7]);
            assert_eq!(&c[1..], &[0u64; 7]);
            assert_eq!(c[0], a[0] & b[0]);
            opened.push((a[0], b[0]));
        }
        transcripts.push(transcript);
    }
    // Same seeds, same ceremony; other seeds, another transcript and other triples.
    assert_eq!(transcripts[0], transcripts[2]);
    assert_ne!(transcripts[0], transcripts[1]);
    assert_eq!(opened[..num_triples], opened[2 * num_triples..]);
    assert_ne!(opened[..num_triples], opened[num_triples..2 * num_triples]);
}

#[test]
fn test_pi_triple_f2_offset_on_final_product_shares_is_detected() {
    let sid = [0x7B; 32];
    let t = 2usize;
    let n = 2usize;
    let num_triples = 2usize;
    let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();

    // A consistent degree-`< t` offset on a final `c` word has no MAC to go with it.
    let mut offset_rng = PartyPrivateRng::from_seed([0x7C; 32], b"test");
    let bad_offset = shamir_share_bits64_gf256(t, &pts, 1u64 << 17, &mut offset_rng);
    let err = run_pi_triple_f2_with_transcript(sid, t, &pts, num_triples, 0x53, |p, _, c_vec| {
        bs_gf256_xor_assign(&mut c_vec[1], &bad_offset[p]);
    })
    .unwrap_err();
    assert_eq!(
        err,
        PreprocessError::MacCheckFailed {
            phase: "spdz_bs_gf256_pimac",
            accused_party: None,
        }
    );
}

#[test]
fn goldilocks_authentication_crosses_block_boundaries_and_rejects_bad_degree() {
    let sid = [0xD1; 32];
    let t = 2;
    let n = 3;
    let points: Vec<_> = (1..=n as u64).map(Goldilocks::from_u64_reduced).collect();
    let mut rngs = make_party_rngs(n, 0x52);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    let (alpha, alpha_shares) = spdz_setup_alpha_goldilocks(&sid, t, &points, &mut rngs).unwrap();
    let mut values = vec![Vec::new(); n];
    for k in 0..65 {
        let shares = shamir_share_goldilocks(
            t,
            &points,
            Goldilocks::from_u64_reduced(k + 1),
            &mut rngs[0],
        );
        for p in 0..n {
            values[p].push(shares[p]);
        }
    }
    let macs = spdz_authenticate_goldilocks_batch_ext2(
        &sid,
        t,
        &points,
        &mut mesh,
        &alpha,
        &alpha_shares,
        &values,
        &mut rngs,
    )
    .unwrap();
    let key = open_and_check_degree_ext2(t, &points, &alpha_shares, "test_key").unwrap();
    for k in 0..65 {
        let shares: Vec<_> = macs.iter().map(|row| row[k]).collect();
        assert_eq!(
            open_and_check_degree_ext2(t, &points, &shares, "test_mac").unwrap(),
            key.mul_base(Goldilocks::from_u64_reduced(k as u64 + 1))
        );
    }
    values[2][64] += Goldilocks::ONE;
    assert!(
        spdz_authenticate_goldilocks_batch_ext2(
            &sid,
            t,
            &points,
            &mut mesh,
            &alpha,
            &alpha_shares,
            &values,
            &mut rngs
        )
        .is_err()
    );
}

#[test]
fn test_dealerless_pi_pow7_and_canonical_a2b_masks() {
    let sid = [0x88; 32];
    // Dishonest majority 3-of-4 (`2t - 1 = 5 > 4`)
    let t = 3usize;
    let n = 4usize;
    let pts: Vec<Goldilocks> = (1..=n as u64).map(Goldilocks::from_u64_reduced).collect();
    let mut rngs = make_party_rngs(n, 0x60);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

    let mut vaults = run_dealerless_pi_pow7(sid, t, &pts, 2, 2, 1, &mut mesh, &mut rngs).unwrap();
    let alpha_sh: Vec<GoldilocksExt2> = (0..n).map(|p| vaults[p].mac_alpha_share).collect();
    let alpha_global = open_and_check_degree_ext2(t, &pts, &alpha_sh, "alpha").unwrap();

    for k in 0..2 {
        let mut pows = [Goldilocks::ZERO; 7];
        for (d, pows_d_item) in pows[..7].iter_mut().enumerate() {
            let sh: Vec<Goldilocks> = (0..n).map(|p| vaults[p].pow7_tuples[k].r_pows[d]).collect();
            *pows_d_item = open_and_check_degree_goldilocks(t, &pts, &sh, "test").unwrap();
            let mac_sh: Vec<GoldilocksExt2> =
                (0..n).map(|p| vaults[p].pow7_tuples[k].r_macs[d]).collect();
            let mac = open_and_check_degree_ext2(t, &pts, &mac_sh, "mac").unwrap();
            assert_eq!(mac, alpha_global.mul_base(*pows_d_item));
        }
        let r = pows[0];
        assert_eq!(pows[1], r * r);
        assert_eq!(pows[2], r * r * r);
        assert_eq!(pows[6], poseidon2_sbox7(r));
    }

    // Verify A2B masks are Boolean, sum strictly `< p`, and carry valid SPDZ MACs
    for m in 0..1 {
        let mut acc_u128 = 0u128;
        for bit in 0..64 {
            let b_sh: Vec<Goldilocks> = (0..n)
                .map(|p| vaults[p].a2b_masks[m].bit_shares[bit])
                .collect();
            let b_mac: Vec<GoldilocksExt2> = (0..n)
                .map(|p| vaults[p].a2b_masks[m].bit_macs[bit])
                .collect();
            let b_f = commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "a2b_bit_spdz",
                t,
                &pts[..t],
                &b_sh[..t],
                &b_mac[..t],
                &alpha_sh[..t],
                &mut rngs[..t],
            )
            .unwrap();
            let b_val = b_f.to_canonical_u64();
            assert!(b_val == 0 || b_val == 1);
            acc_u128 |= (b_val as u128) << bit;
        }
        assert!(acc_u128 < (crate::field::goldilocks::GOLDILOCKS_PRIME as u128));
        let f_sh: Vec<Goldilocks> = (0..n)
            .map(|p| vaults[p].a2b_masks[m].field_sum_share)
            .collect();
        let f_mac: Vec<GoldilocksExt2> = (0..n)
            .map(|p| vaults[p].a2b_masks[m].field_sum_mac)
            .collect();
        let f_val = commit_and_open_spdz_goldilocks_quorum(
            &sid,
            "a2b_sum_spdz",
            t,
            &pts[..t],
            &f_sh[..t],
            &f_mac[..t],
            &alpha_sh[..t],
            &mut rngs[..t],
        )
        .unwrap()
        .to_canonical_u64();
        assert_eq!(f_val as u128, acc_u128);
    }

    let initial_power = vaults[0].pow7_tuples[0].r_pows;
    let initial_bits = vaults[0].a2b_masks[0].bit_shares;
    assert_eq!(vaults[0].pop_pow7().unwrap().r_pows, initial_power);
    assert_eq!(vaults[0].pop_a2b_mask().unwrap().bit_shares, initial_bits);
    assert_eq!(vaults[0].pow7_tuples[0].r_pows, [Goldilocks::ZERO; 7]);
    assert_eq!(vaults[0].pow7_tuples[0].r_macs, [GoldilocksExt2::ZERO; 7]);
    assert_eq!(vaults[0].a2b_masks[0].bit_shares, [Goldilocks::ZERO; 64]);
    assert_eq!(vaults[0].a2b_masks[0].bit_macs, [GoldilocksExt2::ZERO; 64]);
    // Poisoning wipes `mac_alpha_share` and blocks vault pops
    vaults[0].poison_and_wipe();
    assert_eq!(vaults[0].mac_alpha_share, GoldilocksExt2::ZERO);
    assert_eq!(
        vaults[0].pop_pow7().unwrap_err(),
        PreprocessError::VaultPoisoned {
            kind: "Poseidon2 pow7"
        }
    );

    let bad_off = shamir_share_goldilocks(t, &pts, Goldilocks::ONE, &mut rngs[0]);
    let err = run_dealerless_pi_pow7_with_fault(
        [0x89; 32],
        t,
        &pts,
        1,
        0,
        0,
        &mut mesh,
        &mut rngs,
        |p, c_vec| {
            c_vec[0] += bad_off[p];
        },
    )
    .unwrap_err();
    assert_eq!(
        err,
        PreprocessError::SacrificeResidualNonZero { phase: "pi_pow7" }
    );
}

#[test]
fn gilboa_bounded_blocks_preserve_cross_party_products_at_the_boundary() {
    let mut rngs: Vec<_> = (0..3)
        .map(|p| PartyPrivateRng::from_seed([0x80 + p; 32], b"gilboa-blocks"))
        .collect();
    let mut mesh = OtMesh::try_establish([0x86; 32], &mut rngs).unwrap();
    let u: Vec<Vec<_>> = (0..3)
        .map(|p| {
            (0..33)
                .map(|k| Goldilocks::from_u64_reduced(17 * p + k + 1))
                .collect()
        })
        .collect();
    let v: Vec<Vec<_>> = (0..3)
        .map(|p| {
            (0..33)
                .map(|k| Goldilocks::from_u64_reduced(5 * p + 3 * k + 2))
                .collect()
        })
        .collect();
    let w = pairwise_gilboa_ole_goldilocks(&mut mesh, &u, &v, &mut rngs).unwrap();
    assert!(w.iter().all(|row| row.len() == 33));
    for k in 0..33 {
        let sum =
            |rows: &[Vec<Goldilocks>]| rows.iter().fold(Goldilocks::ZERO, |acc, row| acc + row[k]);
        assert_eq!(sum(&w), sum(&u) * sum(&v));
    }
}

#[test]
fn opening_tables_reconstruct_and_reject_off_polynomial() {
    let points: Vec<_> = (1..=5).map(Goldilocks::from_u64_reduced).collect();
    let tables = GoldilocksOpeningTables::new(3, &points).unwrap();
    let mut shares: Vec<_> = points
        .iter()
        .map(|&x| Goldilocks::from_u64_reduced(17) + x + x * x)
        .collect();
    assert_eq!(
        tables.open(&shares, "table").unwrap(),
        Goldilocks::from_u64_reduced(17)
    );
    shares[4] += Goldilocks::ONE;
    assert!(tables.open(&shares, "table").is_err());
    let points: Vec<_> = (1..=5).map(TowerGf256).collect();
    let tables = Gf256OpeningTables::new(3, &points).unwrap();
    let mut shares: Vec<_> = points
        .iter()
        .map(|&x| TowerGf256(17).add(x).add(x.mul(x)))
        .collect();
    assert_eq!(tables.open(&shares, "table").unwrap(), TowerGf256(17));
    shares[4] = shares[4].add(TowerGf256::ONE);
    assert!(tables.open(&shares, "table").is_err());
}

#[test]
fn reservations_are_disjoint_and_fail_without_rewind() {
    let mut cursor = 0;
    assert_eq!(
        reserve_material(&mut cursor, 8, 3, false, "test").unwrap(),
        0..3
    );
    assert_eq!(
        reserve_material(&mut cursor, 8, 2, false, "test").unwrap(),
        3..5
    );
    assert!(reserve_material(&mut cursor, 8, usize::MAX, false, "test").is_err());
    assert_eq!(cursor, 5);
    assert!(reserve_material(&mut cursor, 8, 1, true, "test").is_err());
    assert_eq!(cursor, 5);
}

#[test]
fn subtraction_reducer_matches_remainder_oracle() {
    let p = crate::field::goldilocks::GOLDILOCKS_PRIME as u128;
    for x in [0, 1, p - 1, p, p + 1, u64::MAX as u128, u128::MAX] {
        assert_eq!(Goldilocks::reduce128(x).to_canonical_u64(), (x % p) as u64);
    }
    let mut rng = PartyPrivateRng::from_seed([2; 32], b"reduction test");
    for _ in 0..4096 {
        let x = rng.next_u128();
        assert_eq!(Goldilocks::reduce128(x).to_canonical_u64(), (x % p) as u64);
    }
}
