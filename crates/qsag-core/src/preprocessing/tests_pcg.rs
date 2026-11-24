use super::*;
use crate::pcg_dense::{
    MemorySeedBurnTracker, PcgTreeDepth as DenseTreeDepth, run_silent_chosen_ot_words,
    setup_dense_pcg_seeds,
};

use super::sparse_pcg::*;
#[test]
fn test_pcg_seed_expansion_sub24kb_65600_triples_and_2lane_bdoz_sacrifice() {
    let sid = [0x99; 32];
    let n = 2usize;
    let mut rngs = make_party_rngs(n, 0x71);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

    let seeds = PcgSeedExpansion::setup_seeds(sid, 14, &mut mesh, &mut rngs).unwrap();
    for s in &seeds {
        let wire = s.to_wire_bytes();
        assert!(
            wire.len() < PCG_MAX_SEED_WIRE_BYTES,
            "PCG wire seed {} bytes must be strictly < 24 KB ({})",
            wire.len(),
            PCG_MAX_SEED_WIRE_BYTES
        );
        let decoded = PcgPartySeed::from_wire_bytes(&wire).unwrap();
        assert_eq!(decoded.to_wire_bytes(), wire);
    }

    let vaults: Vec<PcgExpandedPartyVault> = seeds.into_iter().map(|s| s.expand_local()).collect();
    assert_eq!(vaults[0].num_boolean_triples(), 65_600);
    assert!(vaults[0].num_boolean_triples() > 65_536);
    assert_eq!(vaults[0].tower_triples.len(), PCG_NUM_TOWER_TRIPLES);

    for k in 0..PCG_NUM_WORDS {
        let a = vaults[0].bool_triple_words[k].a_word ^ vaults[1].bool_triple_words[k].a_word;
        let b = vaults[0].bool_triple_words[k].b_word ^ vaults[1].bool_triple_words[k].b_word;
        let c = vaults[0].bool_triple_words[k].c_word ^ vaults[1].bool_triple_words[k].c_word;
        assert_eq!(c, a & b, "Boolean triple word {} mismatch", k);
    }
    for k in 0..PCG_NUM_TOWER_TRIPLES {
        let a = vaults[0].tower_triples[k]
            .a
            .value
            .add(vaults[1].tower_triples[k].a.value);
        let b = vaults[0].tower_triples[k]
            .b
            .value
            .add(vaults[1].tower_triples[k].b.value);
        let c = vaults[0].tower_triples[k]
            .c
            .value
            .add(vaults[1].tower_triples[k].c.value);
        assert_eq!(c, a.mul(b));
    }

    PcgSeedExpansion::verify_2lane_bdoz_sacrifice(&vaults, &mut rngs).unwrap();

    let bad_seeds = PcgSeedExpansion::setup_seeds_with_fault(
        [0x9A; 32],
        14,
        &mut mesh,
        &mut rngs,
        |p, d_words| {
            if p == 0 {
                d_words[512] ^= 1u64 << 37;
            }
        },
    )
    .unwrap();
    let bad_vaults: Vec<PcgExpandedPartyVault> =
        bad_seeds.into_iter().map(|s| s.expand_local()).collect();
    assert_eq!(
        PcgSeedExpansion::verify_2lane_bdoz_sacrifice(&bad_vaults, &mut rngs),
        Err(PreprocessError::SacrificeResidualNonZero {
            phase: "pcg_boolean_triples"
        })
    );
}

fn make_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
    (0..n)
        .map(|i| {
            let mut seed = [0u8; 32];
            seed[0] = tag;
            seed[1] = (i + 1) as u8;
            PartyPrivateRng::from_seed(seed, b"QSAG.SILENT.PCG.TEST/v1")
        })
        .collect()
}

fn verify_keccak_vaults_algebra(
    t: usize,
    eval_points: &[TowerGf256],
    vaults: &[PreprocessedKeccakPartyVault],
    expected_words: usize,
) {
    let lambdas = lagrange_weights_zero_gf256(&eval_points[..t]).unwrap();
    let mut alpha_global = [Tower128::ZERO; 2];
    for (vault_q, &lambda_q) in vaults.iter().zip(lambdas.iter()).take(t) {
        for (ag, &mac_alpha) in alpha_global.iter_mut().zip(vault_q.mac_alpha_lanes.iter()) {
            *ag = ag.add(mac_alpha.mul_gf256(lambda_q));
        }
    }
    for v in vaults {
        assert_eq!(v.remaining(), expected_words);
    }
    for word_idx in 0..expected_words {
        let a_sh: Vec<BitslicedGf256x64> = (0..vaults.len())
            .map(|p| vaults[p].triples[word_idx].a)
            .collect();
        let b_sh: Vec<BitslicedGf256x64> = (0..vaults.len())
            .map(|p| vaults[p].triples[word_idx].b)
            .collect();
        let c_sh: Vec<BitslicedGf256x64> = (0..vaults.len())
            .map(|p| vaults[p].triples[word_idx].c)
            .collect();
        let a_open = open_and_check_degree_bs_gf256(t, eval_points, &a_sh, "silent_a").unwrap();
        let b_open = open_and_check_degree_bs_gf256(t, eval_points, &b_sh, "silent_b").unwrap();
        let c_open = open_and_check_degree_bs_gf256(t, eval_points, &c_sh, "silent_c").unwrap();
        // Every reconstructed lane is Boolean (`plane 1..8 == 0`) and satisfies `a & b == c`.
        for pl in 1..8 {
            assert_eq!(a_open[pl], 0);
            assert_eq!(b_open[pl], 0);
            assert_eq!(c_open[pl], 0);
        }
        assert_eq!(a_open[0] & b_open[0], c_open[0]);

        for bit in 0..64 {
            let a_gf = bs_gf256_extract_lane(&a_open, bit);
            let b_gf = bs_gf256_extract_lane(&b_open, bit);
            let c_gf = bs_gf256_extract_lane(&c_open, bit);
            for (lane, &alpha_l) in alpha_global.iter().enumerate() {
                let mut ma = Tower128::ZERO;
                let mut mb = Tower128::ZERO;
                let mut mc = Tower128::ZERO;
                for (vault_q, &lambda_q) in vaults.iter().zip(lambdas.iter()).take(t) {
                    ma = ma.add(vault_q.triples[word_idx].a_mac[lane][bit].mul_gf256(lambda_q));
                    mb = mb.add(vault_q.triples[word_idx].b_mac[lane][bit].mul_gf256(lambda_q));
                    mc = mc.add(vault_q.triples[word_idx].c_mac[lane][bit].mul_gf256(lambda_q));
                }
                assert_eq!(ma, alpha_l.mul_gf256(a_gf));
                assert_eq!(mb, alpha_l.mul_gf256(b_gf));
                assert_eq!(mc, alpha_l.mul_gf256(c_gf));
            }
        }
    }
}

#[test]
fn silent_pcg_ot_correlations_and_exhaustion_roundtrip() {
    let sid = [0x61; 32];
    let mut rngs = make_rngs(2, 0x11);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    let mut seeds =
        setup_dense_pcg_seeds(sid, DenseTreeDepth::TestDepth8, &mut mesh, &mut rngs).unwrap();
    let seed1 = seeds.pop().unwrap();
    let seed0 = seeds.pop().unwrap();
    let mut burns = MemorySeedBurnTracker::new();
    let mut v0 = seed0.expand_local(&mut burns).unwrap();
    let mut v1 = seed1.expand_local(&mut burns).unwrap();

    let ot_sid = [0x62; 32];
    let send_pads = v0.derive_silent_sender_ot_pads(&ot_sid, 1, 4).unwrap();
    let (choices, recv_pads) = v1.derive_silent_receiver_ot_pads(&ot_sid, 0, 4).unwrap();
    assert_eq!(send_pads.len(), 256);
    assert_eq!(recv_pads.len(), 256);
    for bit_idx in 0..256 {
        let c_bit = ((choices[bit_idx >> 6] >> (bit_idx & 63)) & 1) == 1;
        let expected = if c_bit {
            send_pads[bit_idx].1
        } else {
            send_pads[bit_idx].0
        };
        assert_eq!(recv_pads[bit_idx], expected);
    }

    let chosen = [0xdead_beef_cafe_babe_u64, 0x0123_4567_89ab_cdef_u64];
    let (chosen_send, chosen_recv) =
        run_silent_chosen_ot_words(&[0x63; 32], &mut v1, &mut v0, &chosen).unwrap();
    for bit_idx in 0..128 {
        let c_bit = ((chosen[bit_idx >> 6] >> (bit_idx & 63)) & 1) == 1;
        let expected = if c_bit {
            chosen_send[bit_idx].1
        } else {
            chosen_send[bit_idx].0
        };
        assert_eq!(chosen_recv[bit_idx], expected);
    }

    // Consuming past the 1024-word budget fails closed with VaultExhausted.
    assert!(matches!(
        v0.derive_silent_sender_ot_pads(&ot_sid, 1, 1021),
        Err(PreprocessError::VaultExhausted {
            kind: "pcg_dense_subfield_vole_send"
        })
    ));
}

#[test]
fn silent_pcg_keccak_vaults_honest_2p_3p_and_tamper_rejection() {
    let _memory = crate::test_budget::reserve_mb(1000);
    // 1. 2-of-2 silent seed burn + local expansion + blinded-check materialization.
    let sid0 = [0x71; 32];
    let sid1 = [0x72; 32];
    let mut rngs = make_rngs(2, 0x22);
    let mut mesh = OtMesh::establish_ideal_for_test(sid0, &mut rngs);
    let seeds0 =
        setup_dense_pcg_seeds(sid0, DenseTreeDepth::TestDepth8, &mut mesh, &mut rngs).unwrap();
    let seeds1 =
        setup_dense_pcg_seeds(sid1, DenseTreeDepth::TestDepth8, &mut mesh, &mut rngs).unwrap();
    let wire0_p0 = seeds0[0].to_wire_bytes();
    let pts2 = [TowerGf256(1), TowerGf256(2)];
    let mut burns = MemorySeedBurnTracker::new();
    let vaults_2p = expand_and_materialize_silent_pcg_keccak_vaults(
        [0x73; 32], 2, &pts2, 5, seeds0, seeds1, &mut burns, &mut rngs,
    )
    .unwrap();
    verify_keccak_vaults_algebra(2, &pts2, &vaults_2p, 5);

    // Replaying a burned seed wire image is deterministically rejected.
    let replay = crate::pcg_dense::DensePcgPartySeed::from_wire_bytes(&wire0_p0).unwrap();
    assert_eq!(
        replay.expand_local(&mut burns).err(),
        Some(PreprocessError::PcgSeedAlreadyBurned)
    );

    // 2. 2-of-3 threshold end-to-end `run_silent_pcg_keccak_vaults` across a chunk boundary
    //    (`7 > SILENT_PCG_KECCAK_CHUNK_WORDS`).
    let mut rngs3 = make_rngs(3, 0x33);
    let sid3 = [0x74; 32];
    let mut mesh3 = OtMesh::establish_ideal_for_test(sid3, &mut rngs3);
    let pts3 = [TowerGf256(1), TowerGf256(2), TowerGf256(3)];
    let mut burns3 = MemorySeedBurnTracker::new();
    let vaults_3p = run_silent_pcg_keccak_vaults(
        sid3,
        2,
        &pts3,
        DenseTreeDepth::TestDepth8,
        7,
        &mut burns3,
        &mut mesh3,
        &mut rngs3,
    )
    .unwrap();
    verify_keccak_vaults_algebra(2, &pts3, &vaults_3p, 7);

    // 3. Corrupting a silent Boolean Beaver product `c_word` before sacrifice is caught!
    let sid_bad0 = [0x75; 32];
    let sid_bad1 = [0x76; 32];
    let mut rngs_bad = make_rngs(2, 0x44);
    let mut mesh_bad = OtMesh::establish_ideal_for_test(sid_bad0, &mut rngs_bad);
    let s0 = setup_dense_pcg_seeds(
        sid_bad0,
        DenseTreeDepth::TestDepth8,
        &mut mesh_bad,
        &mut rngs_bad,
    )
    .unwrap();
    let s1 = setup_dense_pcg_seeds(
        sid_bad1,
        DenseTreeDepth::TestDepth8,
        &mut mesh_bad,
        &mut rngs_bad,
    )
    .unwrap();
    let mut burns_bad = MemorySeedBurnTracker::new();
    let mut v0_bad: Vec<_> = s0
        .into_iter()
        .map(|s| s.expand_local(&mut burns_bad).unwrap())
        .collect();
    let mut v1_bad: Vec<_> = s1
        .into_iter()
        .map(|s| s.expand_local(&mut burns_bad).unwrap())
        .collect();
    v0_bad[0].corrupt_bool_triple_c_word_for_audit(0, 1);
    assert!(matches!(
        materialize_silent_pcg_keccak_vaults(
            [0x77; 32],
            2,
            &pts2,
            4,
            &mut v0_bad,
            &mut v1_bad,
            &mut rngs_bad,
        ),
        Err(PreprocessError::SacrificeResidualNonZero {
            phase: "pi_triple_f2"
        })
    ));
}

#[test]
fn hostile_counts_are_rejected_before_allocation() {
    assert!(validate_frame_count(usize::MAX, 64, usize::MAX).is_err());
    assert!(validate_frame_count(1, MAX_FRAME_BUDGET + 1, usize::MAX).is_err());
    assert!(validate_frame_count(2, 64, 127).is_err());
    assert!(validate_frame_count(2, 64, 128).is_ok());
    let mut wire = vec![0u8; 111];
    wire[..8].copy_from_slice(PCG_WIRE_MAGIC);
    wire[42..44].copy_from_slice(&u16::MAX.to_le_bytes());
    wire[44] = PCG_MIN_TREE_DEPTH as u8;
    wire[109..111].copy_from_slice(&(u16::MAX - 1).to_le_bytes());
    assert!(PcgPartySeed::from_wire_bytes(&wire).is_err());
}
