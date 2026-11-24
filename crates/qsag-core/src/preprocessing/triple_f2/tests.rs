use super::authentication::{
    ADDITIVE_CHECK_OPENINGS, ADDITIVE_CHECK_WEIGHTS, open_additive_authenticated,
};
use super::combine::{COMBINE_SECURITY_BITS, combine_arity, combine_input_words, combine_pass};
use super::sacrifice::{CRH_WIDTH, CrhOut, FoldPlan, crh_prefix, crh_x8};
use super::*;

#[test]
fn crh_x8_is_one_shake256_per_row() {
    let prefix = crh_prefix(&[0x5a; 32], 2, 1, 7);
    let index: [u64; CRH_WIDTH] = core::array::from_fn(|s| 1000 + 3 * s as u64);
    let rows: [Row; CRH_WIDTH] = core::array::from_fn(|s| {
        let v = 0x0123_4567_89ab_cdef_0f1e_2d3c_4b5a_6978u128.rotate_left(11 * s as u32);
        [v, !v ^ (s as u128)]
    });
    let mut out: CrhOut = [[0u64; RATE_WORDS * MAX_CRH_BLOCKS]; CRH_WIDTH];
    for backend in [qsag_asm::SimdBackend::Portable, qsag_asm::detect_backend()] {
        crh_x8(&prefix, index, &rows, MAX_CRH_BLOCKS, backend, &mut out);
        for s in 0..CRH_WIDTH {
            let mut msg = Vec::new();
            for word in prefix {
                msg.extend_from_slice(&word.to_le_bytes());
            }
            msg.extend_from_slice(&index[s].to_le_bytes());
            msg.extend_from_slice(&rows[s][0].to_le_bytes());
            msg.extend_from_slice(&rows[s][1].to_le_bytes());
            let want = crate::sponge::keccak::shake256_xof(8 * RATE_WORDS * MAX_CRH_BLOCKS, &msg);
            let got: Vec<u8> = out[s].iter().flat_map(|w| w.to_le_bytes()).collect();
            assert_eq!(got, want, "lane {s}, backend {backend:?}");
        }
    }
}

#[test]
fn additive_share_shift_opens_only_fresh_randomized_residuals() {
    // Keep the portable field circuit out of loop vectorization.
    #[inline(never)]
    fn expected_product(r: Tower128, d: Tower128) -> Tower128 {
        r.mul(d)
    }
    let sid = [0xe1; 32];
    let delta = [[0x1234u128, 0x5678u128], [0x9876u128, 0xabcdu128]];
    let macs = vec![vec![[0u128; 2]]; 2];
    let shifted = vec![vec![1u128], vec![0u128]];
    let total = delta[0][0] ^ delta[1][0];
    let mut seen = alloc::collections::BTreeSet::new();
    let mut seen_randomizers = alloc::collections::BTreeSet::new();
    for honest_tape in 1..=16 {
        // Fixed alpha, shift, corrupt tape and base-OT setup. Only the
        // honest party's fresh private randomness varies between aborts.
        let tapes = [0x91, honest_tape];
        let rngs = || {
            tapes
                .iter()
                .map(|&seed| PartyPrivateRng::from_seed([seed; 32], b"additive-abort"))
                .collect::<Vec<_>>()
        };
        let mut private = rngs();
        let mut setup_rngs: Vec<_> = (0..2)
            .map(|p| PartyPrivateRng::from_seed([0x42 + p; 32], b"fixed-additive-base-ot"))
            .collect();
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut setup_rngs);
        let before = mesh.transcript_digest();
        // The retained mesh blinds from its single-use pool. Stage it from the same
        // private tapes and read the joint randomizer the first round will consume.
        mesh.prestage_blinded_checks(1, &mut private).unwrap();
        let staged = mesh.staged_blinding_serials();
        let randomizer = mesh.next_blinding_randomizer().unwrap();
        ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().clear());
        ADDITIVE_CHECK_WEIGHTS.with(|weights| weights.borrow_mut().clear());
        assert!(matches!(
            open_additive_authenticated(
                &sid,
                "additive_shift",
                &shifted,
                &macs,
                &delta,
                &mut mesh,
                &mut private
            ),
            Err(PreprocessError::MacCheckFailed {
                phase: "additive_shift",
                ..
            })
        ));
        let checks = ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow().clone());
        let weights = ADDITIVE_CHECK_WEIGHTS.with(|weights| weights.borrow().clone());
        assert_eq!(weights.len(), 1);
        let projected = Tower128(gf_mul(weights[0], total));
        assert_eq!(checks, [expected_product(randomizer, projected)]);
        assert_ne!(checks[0], Tower128::ZERO);
        assert_ne!(checks[0], projected);
        assert_ne!(mesh.transcript_digest(), before);
        // The rejecting round spent exactly the triple whose randomizer was read.
        assert_eq!(mesh.staged_blinding_serials(), staged[..staged.len() - 1]);
        assert!(seen_randomizers.insert(randomizer.0));
        seen.insert(checks[0].0);
    }
    assert_eq!(seen.len(), 16);
    // A fault confined to the second lane is also rejected.
    let mut private: Vec<_> = (0..2)
        .map(|p| PartyPrivateRng::from_seed([0x51 + p; 32], b"additive-second-lane"))
        .collect();
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut private);
    let delta = [[0, 19], [0, 23]];
    ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().clear());
    assert!(matches!(
        open_additive_authenticated(
            &sid,
            "additive_second_lane",
            &shifted,
            &macs,
            &delta,
            &mut mesh,
            &mut private
        ),
        Err(PreprocessError::MacCheckFailed { .. })
    ));
    ADDITIVE_CHECK_OPENINGS.with(|checks| {
        assert_eq!(checks.borrow().len(), 2);
        assert_eq!(checks.borrow()[0], Tower128::ZERO);
        assert_ne!(checks.borrow()[1], Tower128::ZERO);
    });
    ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().clear());
    assert_eq!(
        open_additive_authenticated(
            &sid,
            "additive_honest",
            &vec![vec![0]; 2],
            &macs,
            &delta,
            &mut mesh,
            &mut private
        )
        .unwrap(),
        [0]
    );
    // All three projections and BOTH MAC lanes must be checked on success.
    ADDITIVE_CHECK_OPENINGS.with(|checks| assert_eq!(*checks.borrow(), [Tower128::ZERO; 6]));
    // A fault in a late element crosses gf_dot's 128-element chunks.
    let fields = 257;
    let mut shifted = vec![vec![0u128; fields]; 2];
    shifted[0][fields - 1] = 1;
    ADDITIVE_CHECK_OPENINGS.with(|checks| checks.borrow_mut().clear());
    assert!(matches!(
        open_additive_authenticated(
            &sid,
            "additive_late_element",
            &shifted,
            &vec![vec![[0u128; 2]; fields]; 2],
            &delta,
            &mut mesh,
            &mut private
        ),
        Err(PreprocessError::MacCheckFailed { .. })
    ));
    ADDITIVE_CHECK_OPENINGS.with(|checks| {
        assert_eq!(checks.borrow().len(), 2);
        assert_eq!(checks.borrow()[0], Tower128::ZERO);
        assert_ne!(checks.borrow()[1], Tower128::ZERO);
    });
}

type TestSetup = (
    [TowerGf256; 3],
    Vec<PartyPrivateRng>,
    OtMesh,
    Vec<[Tower128; 2]>,
    Vec<[Tower128; 2]>,
);
fn setup(sid: [u8; 32], tag: &[u8]) -> TestSetup {
    let points = [TowerGf256(1), TowerGf256(2), TowerGf256(3)];
    let mut rngs: Vec<_> = (0..3)
        .map(|p| PartyPrivateRng::from_seed([p + 0x30; 32], tag))
        .collect();
    let mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    let (alpha, shared) = spdz_setup_alpha_gf256(&sid, 2, &points, &mut rngs).unwrap();
    (points, rngs, mesh, alpha, shared)
}

/// Opened `(a, b, c)` bits of additive triples, after checking `c = a & b` and both MAC
/// lanes of every bit against the XOR of the key shares.
fn open_additive(triples: &BitTriples, alpha: &[[Tower128; 2]]) -> [Vec<u64>; 3] {
    let n = alpha.len();
    let words = triples.words();
    let key: Row = core::array::from_fn(|lane| alpha.iter().fold(0, |k, a| k ^ a[lane].0));
    let opened: [Vec<u64>; 3] = core::array::from_fn(|which| {
        (0..words)
            .map(|w| (0..n).fold(0, |x, p| x ^ triples.bits[which][p][w]))
            .collect()
    });
    for which in 0..3 {
        for lane in 0..2 {
            for k in 0..64 * words {
                let mac = (0..n).fold(0, |m, p| m ^ triples.macs[which][p][lane][k]);
                assert_eq!(mac, bit_mask(word_bit(&opened[which], k)) & key[lane]);
            }
        }
    }
    for w in 0..words {
        assert_eq!(opened[2][w], opened[0][w] & opened[1][w]);
    }
    opened
}

/// `log2 C(n, k)`. Kept out of line: inlined into the loops of its caller, this sum sends
/// LLVM's loop vectorizer into minutes of planning.
#[inline(never)]
fn log2_binom(n: usize, k: usize) -> f64 {
    let mut acc = 0.0;
    for i in 0..k {
        acc += ((n - i) as f64).log2() - ((i + 1) as f64).log2();
    }
    acc
}

/// `log2` of `C(n, g) / C(f (n + 1), f g)`: the chance that a fixed set of `f g` raw
/// positions is a union of `g` kept buckets.
#[inline(never)]
fn log2_union_chance(n: usize, f: usize, g: usize) -> f64 {
    log2_binom(n, g) - log2_binom(f * (n + 1), f * g)
}

#[test]
fn combine_arity_meets_its_bound() {
    // Hand-checked values: the production pool, one raw ceremony's worth, small requests.
    assert_eq!(combine_arity(64 * POOL_WORDS), 3);
    assert_eq!(combine_arity(64 * 7720), 4);
    assert_eq!(combine_arity(64 * 7000), 4);
    assert_eq!(combine_arity(64 * 1015), 4);
    assert_eq!(combine_arity(64 * 100), 4);
    assert_eq!(combine_arity(64 * 4), 6);
    assert_eq!(combine_arity(64), 7);

    for words in [
        1usize, 2, 3, 4, 5, 8, 25, 64, 126, 512, 1015, 7720, 8192, 16383,
    ] {
        let n = core::hint::black_box(64 * words);
        let f = combine_arity(n);
        // The chance is largest for a single bucket, and that is below 2^-40.
        let single = log2_union_chance(n, f, 1);
        assert!(single <= -f64::from(COMBINE_SECURITY_BITS), "{words} words");
        let mut probes: Vec<usize> = (2..=64).collect();
        probes.extend([n / 3, n / 2, n - 2, n - 1, n]);
        for g in probes {
            if (2..=n).contains(&g) {
                assert!(
                    log2_union_chance(n, f, g) < single,
                    "{words} words, {g} buckets"
                );
            }
        }
        // One member fewer per bucket would not do.
        if f > 2 {
            let short = log2_union_chance(n, f - 1, 1);
            assert!(short > -f64::from(COMBINE_SECURITY_BITS), "{words} words");
        }
    }
    // The two-pass shape of the silent path at its chunk size.
    assert_eq!(combine_shape(5, Leak::BothFactors), (156, 5, Some((31, 6))));
}

/// A pool with a single set raw `b` bit, shared and authenticated by hand.
fn one_hot_pool(words: usize, hot: usize, delta: &[Row]) -> BitTriples {
    let n = delta.len();
    let mut pool = BitTriples {
        bits: core::array::from_fn(|_| SecretBuffer(vec![vec![0u64; words]; n])),
        macs: core::array::from_fn(|_| {
            SecretBuffer(
                (0..n)
                    .map(|_| [vec![0u128; 64 * words], vec![0u128; 64 * words]])
                    .collect(),
            )
        }),
    };
    // `a` is all ones, so `c = b`; party 0 holds the values, every party its MAC share.
    for w in 0..words {
        pool.bits[0][0][w] = u64::MAX;
    }
    pool.bits[1][0][hot / 64] = 1 << (hot % 64);
    pool.bits[2][0][hot / 64] = 1 << (hot % 64);
    for p in 0..n {
        for lane in 0..2 {
            pool.macs[0][p][lane].fill(delta[p][lane]);
            pool.macs[1][p][lane][hot] = delta[p][lane];
            pool.macs[2][p][lane][hot] = delta[p][lane];
        }
    }
    pool
}

/// The bucket permutation acts on bits, not words: one marked raw bit lands on output bit
/// offsets unrelated to its own, in either output word, or in the discarded positions, and
/// the outputs stay valid authenticated triples.
#[test]
fn combine_permutes_single_bits_and_keeps_triples_valid() {
    let delta: Vec<Row> = vec![[3, 5], [0x11 << 64, 7 << 100], [9 << 30, 1 << 127]];
    let alpha: Vec<[Tower128; 2]> = delta
        .iter()
        .map(|d| [Tower128(d[0]), Tower128(d[1])])
        .collect();
    let out_words = 2;
    let arity = combine_arity(64 * out_words);
    let raw_words = combine_input_words(out_words, arity);
    let hot = 64 * 3 + 17;
    let (mut landed, mut same_offset, mut dropped) = (0usize, 0usize, 0usize);
    let mut seen = alloc::collections::BTreeSet::new();
    for trial in 0u8..96 {
        let pool = one_hot_pool(raw_words, hot, &delta);
        let mut rngs: Vec<_> = (0..3)
            .map(|p| PartyPrivateRng::from_seed([trial; 32], &[b'c', p]))
            .collect();
        let mut mesh = OtMesh::establish_ideal_for_test([trial; 32], &mut rngs);
        let mut transcript = [trial; 32];
        let out = combine_pass(
            &[0x77; 32],
            "pi_triple_f2_comb_b",
            1,
            arity,
            out_words,
            &[&pool],
            &delta,
            &mut transcript,
            &mut mesh,
            &mut rngs,
            &mut PiTripleF2Faults::default(),
        )
        .unwrap();
        let opened = open_additive(&out, &alpha);
        assert_eq!(opened[0], [u64::MAX; 2]);
        let ones: u32 = opened[1].iter().map(|w| w.count_ones()).sum();
        assert!(ones <= 1);
        if ones == 0 {
            dropped += 1;
            continue;
        }
        let pos = (0..128).find(|k| word_bit(&opened[1], *k) == 1).unwrap();
        landed += 1;
        same_offset += usize::from(pos % 64 == hot % 64);
        seen.insert(pos);
    }
    // 768 of the 832 raw positions are in kept buckets, so about 7 trials in 96 drop the
    // bit; a word-level permutation would keep its offset in all of the others.
    assert!((1..=30).contains(&dropped), "dropped {dropped}");
    assert!(
        same_offset <= 8,
        "offset kept {same_offset} of {landed} times"
    );
    assert!(seen.len() >= 40, "only {} distinct positions", seen.len());
}

/// Additive output mode: valid authenticated triples under the additive key shares, the
/// same for the same seeds, and no word repeated.
#[test]
fn additive_triples_are_valid_authenticated_and_deterministic() {
    let run = || {
        let sid = [0xa0; 32];
        let (_, mut rngs, mut mesh, alpha, _) = setup(sid, b"additive");
        let before = mesh.transcript_digest();
        let (triples, transcript) = run_pi_triple_f2_additive(
            sid,
            5,
            &alpha,
            &mut mesh,
            &mut rngs,
            &mut PiTripleF2Faults::default(),
        )
        .unwrap();
        assert_eq!(triples.words(), 5);
        assert_ne!(mesh.transcript_digest(), before);
        (open_additive(&triples, &alpha), transcript)
    };
    let (opened, transcript) = run();
    for w in 0..5 {
        assert!((0..w).all(|v| (opened[0][v], opened[1][v]) != (opened[0][w], opened[1][w])));
    }
    assert_eq!((opened, transcript), run());
}

/// Several raw ceremonies, two of them concurrent, feeding one combine pool: every triple
/// is valid and the result is a function of the seeds alone.
#[test]
fn pooled_ceremonies_are_valid_and_independent_of_scheduling() {
    let run = || {
        let sid = [0xc0; 32];
        let (_, mut rngs, mut mesh, alpha, _) = setup(sid, b"pooled-ceremonies");
        // Seven words need 42 raw words: three ceremonies of 14.
        let (triples, _, transcript) = additive_pool(
            sid,
            7,
            16,
            &alpha,
            &mut mesh,
            &mut rngs,
            &mut PiTripleF2Faults::default(),
        )
        .unwrap();
        (open_additive(&triples, &alpha), transcript)
    };
    let first = run();
    assert_eq!(first.0[0].len(), 7);
    assert_eq!(first, run());
}

#[test]
fn shamir_triples_are_boolean_products_of_degree_below_t() {
    let sid = [0xd0; 32];
    let (points, mut rngs, mut mesh, alpha, shared) = setup(sid, b"shamir");
    let (vaults, _) = run_pi_triple_f2(
        sid,
        2,
        &points,
        3,
        &alpha,
        &shared,
        &mut mesh,
        &mut rngs,
        &mut PiTripleF2Faults::default(),
    )
    .unwrap();
    for k in 0..3 {
        let open = |pick: fn(&KeccakBitTripleShare64) -> BitslicedGf256x64| {
            let shares: Vec<_> = vaults.iter().map(|v| pick(&v.triples[k])).collect();
            open_and_check_degree_bs_gf256(2, &points, &shares, "test").unwrap()
        };
        let (a, b, c) = (open(|tr| tr.a), open(|tr| tr.b), open(|tr| tr.c));
        assert_eq!(
            (&a[1..], &b[1..], &c[1..]),
            (&[0u64; 7][..], &[0u64; 7][..], &[0u64; 7][..])
        );
        assert_eq!(c[0], a[0] & b[0]);
    }
}

/// Every point where a party acts on its own shares: a wrong product share, a wrong fold
/// cross term, a chosen-choice product fed something other than the party's share of the
/// folded `b` (in a fold round and in the base case), a wrong share of a combine opening,
/// and wrong Shamir value or MAC shares.
#[test]
fn rejects_product_fold_choice_opening_mac_and_degree_corruption() {
    for attack in 0..7 {
        let sid = [0xb0 + attack; 32];
        let (points, mut rngs, mut mesh, alpha, shared) = setup(sid, b"corruption");
        let mut product = |p: usize, words: &mut [u64]| {
            if p == 0 {
                words[0] ^= 1;
            }
        };
        let mut fold = |round: usize, p: usize, terms: &mut [[u128; 2]; 2]| {
            if round == 0 && p == 0 {
                terms[0][0] ^= 1;
                terms[1][0] ^= 1;
            }
        };
        let mut seen_generic = None;
        let mut choice_fold = |round: usize, p: usize, choice: &mut u128| {
            let first = *seen_generic.get_or_insert(round);
            if round == first && p == 1 {
                *choice ^= 1 << 77;
            }
        };
        // The base case reports the round count as its round.
        let base_round = FoldPlan::new(64 * combine_shape(2, Leak::ChoiceSide).0)
            .unwrap()
            .rounds();
        let mut choice_base = |round: usize, p: usize, choice: &mut u128| {
            if round == base_round && p == 2 {
                *choice ^= 1;
            }
        };
        let mut opening = |p: usize, shares: &mut [u128]| {
            if p == 1 {
                shares[0] ^= 1 << 5;
            }
        };
        let mut mac = |p: usize, tags: &mut [[[Tower128; 64]; 2]]| {
            if p == 0 {
                tags[0][0][0].0 ^= 1;
            }
        };
        let mut degree = |p: usize, a: &mut [BitslicedGf256x64], _: &mut [BitslicedGf256x64]| {
            if p == 2 {
                a[0][0] ^= 1;
            }
        };
        let mut faults = PiTripleF2Faults::default();
        let phase = match attack {
            0 => {
                faults.product_shares = Some(&mut product);
                None
            }
            1 => {
                faults.fold_shares = Some(&mut fold);
                None
            }
            2 => {
                faults.choice_values = Some(&mut choice_fold);
                Some("pi_triple_f2_choice")
            }
            3 => {
                faults.choice_values = Some(&mut choice_base);
                Some("pi_triple_f2_choice")
            }
            4 => {
                faults.combine_shares = Some(&mut opening);
                Some("pi_triple_f2_comb_b")
            }
            5 => {
                faults.mac_shares = Some(&mut mac);
                None
            }
            _ => {
                faults.shamir_shares = Some(&mut degree);
                None
            }
        };
        let err = run_pi_triple_f2(
            sid,
            2,
            &points,
            2,
            &alpha,
            &shared,
            &mut mesh,
            &mut rngs,
            &mut faults,
        )
        .err()
        .unwrap_or_else(|| panic!("accepted attack {attack}"));
        if let Some(phase) = phase {
            assert!(
                matches!(err, PreprocessError::MacCheckFailed { phase: p, .. } if p == phase),
                "attack {attack}: {err:?}"
            );
        }
    }
}
