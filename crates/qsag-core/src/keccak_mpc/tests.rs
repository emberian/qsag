#[test]
fn plane_beaver_mac_matches_scalar_for_distinct_field_lanes() {
    let mut rng = PartyPrivateRng::from_seed([0x9a; 32], b"plane-mac");
    for iteration in 0..8 {
        let a = core::array::from_fn(|_| core::array::from_fn(|_| rng.next_tower128()));
        let b = core::array::from_fn(|_| core::array::from_fn(|_| rng.next_tower128()));
        let c = core::array::from_fn(|_| core::array::from_fn(|_| rng.next_tower128()));
        let alpha = [rng.next_tower128(), rng.next_tower128()];
        let mut d = core::array::from_fn(|_| rng.next_u64());
        let mut e = core::array::from_fn(|_| rng.next_u64());
        if iteration % 2 == 0 {
            d[1..].fill(0);
            e[1..].fill(0);
        }
        let de = bs_gf256_mul_planes_ct(&d, &e);
        let got = beaver_mac_planes(&c, &b, &a, &alpha, &d, &e, &de);
        for ml in 0..2 {
            for bit in 0..64 {
                assert_eq!(
                    got[ml][bit],
                    c[ml][bit]
                        .add(b[ml][bit].mul_gf256(bs_gf256_extract_lane(&d, bit)))
                        .add(a[ml][bit].mul_gf256(bs_gf256_extract_lane(&e, bit)))
                        .add(alpha[ml].mul_gf256(bs_gf256_extract_lane(&de, bit)))
                );
            }
        }
    }
}
use super::*;
use crate::fips205::{
    fips205_prf_msg, slh_keygen_internal, slh_keygen_mpc, slh_sign_mpc, slh_verify,
};
use crate::preprocessing::KeccakBitTripleShare64;
use crate::sponge::keccak::keccak_f1600;
use crate::tsw_baggy::{PqSecretKey, derive_public_key, sign_hypertree_core};

#[test]
fn slh_oracle_binds_profile_and_seed_before_computation() {
    let sid = [0x81; 32];
    let mut rngs = make_rngs3(0x52);
    let (keys, seed) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    let mut cluster = RssSlhMpcCluster::new(sid, keys, rngs).unwrap();
    cluster
        .bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_128F, &seed[..16])
        .unwrap();
    assert!(
        cluster
            .bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_128S, &seed[..16])
            .is_err()
    );
    let mut wrong = seed;
    wrong[0] ^= 1;
    assert!(
        cluster
            .bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_128F, &wrong[..16])
            .is_err()
    );
    let wrong_pk = crate::fips205::SlhPublicKey::new(&wrong[..16], &[0; 16]).unwrap();
    assert!(
        slh_sign_mpc(
            &Fips205Params::SLH_DSA_SHAKE_128F,
            &mut cluster,
            b"message",
            b"",
            &wrong_pk,
            None
        )
        .is_err()
    );
    assert_eq!(cluster.lane_permutations(), 0);
}

#[test]
fn scheduled_chunks_preserve_serial_shares_counters_and_verifier_rng() {
    let _memory = crate::test_budget::reserve_mb(400);
    let make = || {
        let mut rngs = make_rngs3(0x23);
        let (keys, _) = run_dealerless_rss_dkg_2of3([0x44; 32], 16, &mut rngs).unwrap();
        RssSlhMpcCluster::new([0x44; 32], keys, rngs).unwrap()
    };
    let mut serial = make();
    let mut scheduled = make();
    let pk_seed = serial.keys[0].pk_seed[..16].to_vec();
    let plans: Vec<_> = (0..3)
        .map(|chunk| {
            let prf: Vec<_> = (0..3)
                .map(|lane| {
                    let mut address = Fips205Adrs::ZERO;
                    address.adrs_type = Fips205AdrsType::WotsPrf;
                    address.f5 = chunk * 3 + lane;
                    address
                })
                .collect();
            let steps = (0..15)
                .map(|step| {
                    (
                        prf.iter()
                            .map(|a| {
                                let mut a = *a;
                                a.adrs_type = Fips205AdrsType::WotsHash;
                                a.f6 = step;
                                a
                            })
                            .collect(),
                        if chunk == 1 && step == 3 { 0 } else { 5 },
                    )
                })
                .collect();
            RssChunkPlan { prf, steps }
        })
        .collect();
    // Exercise a barrier partway through a chunk, not just at its end.
    for cluster in [&mut serial, &mut scheduled] {
        let (mut p, mut s) = cluster
            .eval_prf_batch64_secret_deferred(&pk_seed, &plans[0].prf)
            .unwrap();
        wipe_rss_states(&mut p, &mut s);
    }
    // Repeat with the same pool: stale witnesses or lane counts must not leak into the next group.
    for _ in 0..2 {
        let mut expected = RssCutBuffer::new();
        for plan in &plans {
            let (p, s) = serial
                .eval_prf_batch64_secret_deferred(&pk_seed, &plan.prf)
                .unwrap();
            let mut p = SecretBuffer(p);
            let mut s = SecretBuffer(s);
            for (addresses, mask) in &plan.steps {
                serial
                    .eval_f_step_masked_batch64(&pk_seed, addresses, *mask, &mut p, &mut s)
                    .unwrap();
            }
            for party in 0..3 {
                expected.push_party_slices(party, &p[party][..128], &s[party][..128]);
            }
        }
        let mut actual = RssCutBuffer::new();
        scheduled
            .evaluate_chunks(&pk_seed, &plans, &mut actual)
            .unwrap();
        assert_eq!(expected.prim, actual.prim);
        assert_eq!(expected.sec, actual.sec);
        assert_eq!(serial.batch_ctr, scheduled.batch_ctr);
        assert_eq!(serial.pending_dzk.a, scheduled.pending_dzk.a);
        assert_eq!(serial.pending_dzk.b, scheduled.pending_dzk.b);
        assert_eq!(serial.pending_dzk.c, scheduled.pending_dzk.c);
        assert_eq!(serial.lane_permutations(), scheduled.lane_permutations());
        let a = serial
            .flush_verify_and_open_cut("test_chunk_parity", &expected)
            .unwrap()
            .0;
        let b = scheduled
            .flush_verify_and_open_cut("test_chunk_parity", &actual)
            .unwrap()
            .0;
        assert_eq!(a, b);
        for party in 0..3 {
            assert_eq!(
                serial.party_rngs[party].next_bytes32(),
                scheduled.party_rngs[party].next_bytes32()
            );
        }
        assert!(scheduled.chunk_scratch.iter().all(|scratch| {
            scratch
                .a
                .iter()
                .chain(&scratch.b)
                .chain(&scratch.c)
                .all(Vec::is_empty)
        }));
    }
}

#[test]
fn rss_partial_prf_and_masked_f_match_fips_and_reject_bad_replica() {
    let sid = [0x44; 32];
    let mut rngs = make_rngs3(0x23);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    let seed: [u8; 16] = core::array::from_fn(|i| {
        keys[0].sk_seed_primary[i] ^ keys[1].sk_seed_primary[i] ^ keys[2].sk_seed_primary[i]
    });
    let pk_seed = keys[0].pk_seed[..16].to_vec();
    let mut cluster = RssSlhMpcCluster::new(sid, keys, rngs).unwrap();
    let adrs: [Fips205Adrs; 3] = core::array::from_fn(|i| {
        let mut a = Fips205Adrs::ZERO;
        a.adrs_type = Fips205AdrsType::WotsPrf;
        a.f5 = i as u32;
        a
    });
    let (mut p, mut s) = cluster.eval_prf_batch64_secret(&pk_seed, &adrs).unwrap();
    let step = adrs.map(|mut a| {
        a.adrs_type = Fips205AdrsType::WotsHash;
        a
    });
    cluster
        .eval_f_step_masked_batch64(&pk_seed, &step, 0b101, &mut p, &mut s)
        .unwrap();
    let (opened, _) = cluster
        .verify_and_open_cut_blocks("rss_partial_regression", 3, &p, &s)
        .unwrap();
    for i in 0..3 {
        let prf = crate::fips205::fips205_prf(16, &pk_seed, &seed, &adrs[i]);
        let expected = if i == 1 {
            prf
        } else {
            crate::fips205::fips205_f(16, &pk_seed, &step[i], &prf)
        };
        assert_eq!(opened[i], expected);
    }
    cluster.keys[0].sk_seed_secondary[0] ^= 1;
    assert!(matches!(
        cluster.eval_prf_batch64_secret(&pk_seed, &adrs),
        Err(KeccakMpcError::RssShareEqualityFailed(_))
    ));
    assert!(cluster.is_poisoned());
}

fn cut_of(p: &[[u64; 256]; 3], s: &[[u64; 256]; 3], words: usize) -> RssCutBuffer {
    let mut cut = RssCutBuffer::new();
    for party in 0..3 {
        cut.prim[party].extend_from_slice(&p[party][..words]);
        cut.sec[party].extend_from_slice(&s[party][..words]);
    }
    cut
}

/// Every evaluation, verification and opening entry point refuses a poisoned cluster
/// and leaves its counters where they were.
fn assert_rss_cluster_dead(
    cluster: &mut RssSlhMpcCluster,
    pk_seed: &[u8],
    adrs: &[Fips205Adrs],
    p: &[[u64; 256]; 3],
    s: &[[u64; 256]; 3],
) {
    assert!(cluster.is_poisoned());
    let before = (cluster.batch_ctr, cluster.lane_permutations());
    let cut = cut_of(p, s, 128);
    // A second barrier finds no pending relations; it must not pass.
    assert!(matches!(
        cluster.flush_verify_and_open_cut("latch_again", &cut),
        Err(KeccakMpcError::Poisoned)
    ));
    assert!(matches!(
        cluster.verify_and_open_cut_blocks("latch_open", adrs.len(), p, s),
        Err(KeccakMpcError::Poisoned)
    ));
    assert!(matches!(
        cluster.eval_prf_batch64_secret(pk_seed, adrs),
        Err(KeccakMpcError::Poisoned)
    ));
    let (mut cp, mut cs) = (*p, *s);
    assert_eq!(
        cluster.eval_f_step_masked_batch64(pk_seed, adrs, 0b11, &mut cp, &mut cs),
        Err(KeccakMpcError::Poisoned)
    );
    assert_eq!((cp, cs), ([[0u64; 256]; 3], [[0u64; 256]; 3]));
    let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
    let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
    assert_eq!(
        cluster.permute_batch64(1, &mut st_p, &mut st_s),
        Err(KeccakMpcError::Poisoned)
    );
    assert!(matches!(
        cluster.prf_msg_shared(16, &[0u8; 16], b"m"),
        Err(KeccakMpcError::Poisoned)
    ));
    assert_eq!(
        cluster.eval_prf_msg_mpc(16, &[0u8; 16], b"m").unwrap_err(),
        Fips205Error::MpcActiveTamperDetected
    );
    let p128f = Fips205Params::SLH_DSA_SHAKE_128F;
    assert_eq!(
        cluster
            .eval_wots_pkgen_subtree_mpc(&p128f, pk_seed, 0, 0)
            .unwrap_err(),
        Fips205Error::MpcActiveTamperDetected
    );
    assert_eq!(
        cluster
            .eval_fors_trees_mpc(&p128f, pk_seed, Fips205Adrs::ZERO, &vec![0u32; p128f.k])
            .unwrap_err(),
        Fips205Error::MpcActiveTamperDetected
    );
    assert_eq!((cluster.batch_ctr, cluster.lane_permutations()), before);
    assert!(cluster.is_poisoned());
}

#[test]
fn rss_cluster_latches_a_failed_check_and_refuses_every_later_check_and_opening() {
    let prf_adrs: [Fips205Adrs; 2] = core::array::from_fn(|i| {
        let mut a = Fips205Adrs::ZERO;
        a.adrs_type = Fips205AdrsType::WotsPrf;
        a.f5 = i as u32;
        a
    });
    let fresh = |tag: u8| {
        let sid = [tag; 32];
        let mut rngs = make_rngs3(tag);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let pk_seed = keys[0].pk_seed[..16].to_vec();
        (RssSlhMpcCluster::new(sid, keys, rngs).unwrap(), pk_seed)
    };

    // 1. A false AND relation is pending when the barrier runs: the check fails, and a
    //    second check on the now empty relation set must not open the cut.
    let (mut cluster, pk_seed) = fresh(0x61);
    let (p, s) = cluster
        .eval_prf_batch64_secret(&pk_seed, &prf_adrs)
        .unwrap();
    assert!(!cluster.is_poisoned());
    let mut bad = random_relations(b"latch", 3, u64::MAX);
    bad.c[1][2] ^= 1 << 17;
    for slot in 0..3 {
        cluster.pending_dzk.a[slot].extend_from_slice(&bad.a[slot]);
        cluster.pending_dzk.b[slot].extend_from_slice(&bad.b[slot]);
        cluster.pending_dzk.c[slot].extend_from_slice(&bad.c[slot]);
    }
    let cut = cut_of(&p, &s, 128);
    assert!(matches!(
        cluster.flush_verify_and_open_cut("latch", &cut),
        Err(KeccakMpcError::RssSacrificeFailed)
    ));
    assert_eq!(cluster.pending_dzk.len_words(), 0);
    assert_rss_cluster_dead(&mut cluster, &pk_seed, &prf_adrs, &p, &s);

    // 2. A holder pair whose mask streams disagree: the fault is caught inside the
    //    evaluation, and the cluster is dead from then on.
    let (mut cluster, pk_seed) = fresh(0x64);
    let (p, s) = cluster
        .eval_prf_batch64_secret(&pk_seed, &prf_adrs)
        .unwrap();
    cluster.mask_session.sec[2][0] ^= 1;
    cluster.mask_session.shared = false;
    let err = cluster
        .eval_prf_batch64_secret(&pk_seed, &prf_adrs)
        .unwrap_err();
    assert!(matches!(
        err,
        KeccakMpcError::RssSacrificeFailed | KeccakMpcError::RssShareEqualityFailed(_)
    ));
    assert_rss_cluster_dead(&mut cluster, &pk_seed, &prf_adrs, &p, &s);

    // 3. An inconsistent replica in the opening itself.
    let (mut cluster, pk_seed) = fresh(0x67);
    let (p, mut s) = cluster
        .eval_prf_batch64_secret(&pk_seed, &prf_adrs)
        .unwrap();
    s[1][3] ^= 1;
    assert!(matches!(
        cluster.verify_and_open_cut_blocks("latch_replica", 2, &p, &s),
        Err(KeccakMpcError::RssShareEqualityFailed(_))
    ));
    s[1][3] ^= 1;
    assert_rss_cluster_dead(&mut cluster, &pk_seed, &prf_adrs, &p, &s);

    // 4. A cluster poisoned by an engine built on its parts.
    let (mut cluster, pk_seed) = fresh(0x6a);
    let (p, s) = cluster
        .eval_prf_batch64_secret(&pk_seed, &prf_adrs)
        .unwrap();
    cluster.poison();
    assert_rss_cluster_dead(&mut cluster, &pk_seed, &prf_adrs, &p, &s);
}

#[test]
fn rss_relation_accumulator_never_verifies_again_after_a_failure() {
    let sid = [0x9b; 32];
    let mut rngs = make_rngs3(0x6d);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    let mask = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
    let mut pending = random_relations(b"acc", 5, u64::MAX);
    pending.c[0][4] ^= 1;
    assert!(!pending.is_poisoned());
    assert_eq!(
        verify_rss_boolean_triples_seeded(&sid, 0, &mut pending, &mask, &mut rngs, None),
        Err(KeccakMpcError::RssSacrificeFailed)
    );
    assert!(pending.is_poisoned());
    assert_eq!(pending.len_words(), 0);
    // Empty accumulator, same or new counter, with or without a caller seed.
    for (ctr, seed) in [(0u64, None), (1, None), (2, Some(&[9u8; 32]))] {
        assert_eq!(
            verify_rss_boolean_triples_seeded(&sid, ctr, &mut pending, &mask, &mut rngs, seed),
            Err(KeccakMpcError::Poisoned)
        );
    }
    // Honest relations recorded afterwards do not revive it.
    let honest = random_relations(b"acc2", 4, u64::MAX);
    for slot in 0..3 {
        pending.a[slot].extend_from_slice(&honest.a[slot]);
        pending.b[slot].extend_from_slice(&honest.b[slot]);
        pending.c[slot].extend_from_slice(&honest.c[slot]);
    }
    assert_eq!(
        verify_rss_boolean_triples_seeded(&sid, 3, &mut pending, &mask, &mut rngs, None),
        Err(KeccakMpcError::Poisoned)
    );
    assert_eq!(pending.len_words(), 0);
    let mut prim = [[0u64; 1600]; 3];
    let mut sec = [[0u64; 1600]; 3];
    assert_eq!(
        eval_rss_keccak_f1600_batch64_record(&sid, 4, 1, &mut prim, &mut sec, &mask, &mut pending),
        Err(KeccakMpcError::Poisoned)
    );
    assert_eq!(pending.len_words(), 0);
}

#[test]
fn rss_tensor_partition_preserves_every_sum() {
    let groups = 131;
    let mut pending = RssPendingDzkTriples::new();
    let mut rng = PartyPrivateRng::from_seed([0x98; 32], b"rss-tensor-partition");
    for slot in 0..3 {
        pending.a[slot] = (0..groups * RSS_DZK_GROUP_WORDS)
            .map(|_| rng.next_u64())
            .collect();
        pending.b[slot] = (0..groups * RSS_DZK_GROUP_WORDS)
            .map(|_| rng.next_u64())
            .collect();
    }
    let weights: Vec<_> = (0..groups)
        .map(|_| [rng.next_u128(), rng.next_u128()])
        .collect();
    let reference = rss_dzk_tensor_tables_range(&pending, 0, &weights);
    assert_eq!(rss_dzk_tensor_tables(&pending, groups, &weights), reference);
    let mut partitioned = rss_dzk_tensor_tables_range(&pending, 0, &weights[..63]);
    let tail = rss_dzk_tensor_tables_range(&pending, 63, &weights[63..]);
    for (dst, src) in partitioned.iter_mut().zip(tail) {
        for (dst, src) in dst.iter_mut().zip(src) {
            dst[0] ^= src[0];
            dst[1] ^= src[1];
        }
    }
    assert_eq!(partitioned, reference);
}

/// The packed tables against one field multiplication per group and point.
#[test]
fn rss_tensor_tables_match_field_reference() {
    let groups = 5;
    let pending = random_relations(b"tensor-reference", groups * RSS_DZK_GROUP_WORDS, !0);
    let mut rng = PartyPrivateRng::from_seed([0x96; 32], b"rss-tensor-reference");
    let mut weights: Vec<_> = (0..groups)
        .map(|_| [rng.next_u128(), rng.next_u128()])
        .collect();
    weights[0] = [u128::MAX, 1 << 127];
    let tabs = rss_dzk_tensor_tables_range(&pending, 0, &weights);
    let mut ea = [[0u64; RSS_DZK_TERNARY]; 3];
    let mut eb = [[0u64; RSS_DZK_TERNARY]; 3];
    let mut want = [[[RssProofField::ZERO; 2]; RSS_DZK_TERNARY]; 3];
    for (g, nu) in weights.iter().enumerate() {
        for s in 0..3 {
            rss_ternary_expand(&pending.a[s][g * RSS_DZK_GROUP_WORDS..], &mut ea[s]);
            rss_ternary_expand(&pending.b[s][g * RSS_DZK_GROUP_WORDS..], &mut eb[s]);
        }
        for p in 0..3 {
            let q = (p + 1) % 3;
            for e in 0..RSS_DZK_TERNARY {
                let word = (ea[p][e] & (eb[p][e] ^ eb[q][e])) ^ (ea[q][e] & eb[p][e]);
                for lane in 0..2 {
                    want[p][e][lane] = want[p][e][lane]
                        .add(RssProofField(u128::from(word)).mul(RssProofField(nu[lane])));
                }
            }
        }
    }
    for p in 0..3 {
        for e in 0..RSS_DZK_TERNARY {
            assert_eq!(tabs[p][e], want[p][e].map(|v| v.0), "party {p}, point {e}");
        }
    }
}

/// The weighted claims against one field multiplication per relation word, on both the
/// serial and (with `std`) the threaded path.
#[test]
fn rss_initial_claims_match_field_reference() {
    let mut rng = PartyPrivateRng::from_seed([0x95; 32], b"rss-claims-reference");
    for groups in [3usize, 131] {
        let pending = random_relations(b"claims-reference", groups * RSS_DZK_GROUP_WORDS, !0);
        let weights: [RssDzkWeights; 2] = core::array::from_fn(|_| RssDzkWeights {
            mu: core::array::from_fn(|_| RssProofField(rng.next_u128())),
            nu: (0..groups)
                .map(|_| RssProofField(rng.next_u128()))
                .collect(),
        });
        let nu_pairs: Vec<[u128; 2]> = (0..groups)
            .map(|g| [weights[0].nu[g].0, weights[1].nu[g].0])
            .collect();
        let claims = rss_dzk_initial_claims(&pending, groups, &weights, &nu_pairs);
        for (pass, (claims, weights)) in claims.iter().zip(&weights).enumerate() {
            for (s, (claim, words)) in claims.iter().zip(&pending.c).enumerate() {
                let mut want = RssProofField::ZERO;
                for (k, word) in words.iter().enumerate() {
                    let mut weight = weights.nu[k / RSS_DZK_GROUP_WORDS];
                    for (l, mu) in weights.mu.iter().enumerate() {
                        if (k >> l) & 1 == 1 {
                            weight = weight.mul(*mu);
                        }
                    }
                    want = want.add(weight.mul(RssProofField(u128::from(*word))));
                }
                assert_eq!(claim.0, want.0, "groups {groups}, pass {pass}, slot {s}");
            }
        }
    }
}

#[test]
fn rss_proof_field_matches_polynomial_reference_on_every_basis_product() {
    let mut xof = Cshake256Xof::new(b"RSS.FIELD.REGRESSION");
    let mut bytes = [0u8; 32];
    for _ in 0..256 {
        xof.squeeze(&mut bytes);
        let a = u128::from_le_bytes(bytes[..16].try_into().unwrap());
        let b = u128::from_le_bytes(bytes[16..].try_into().unwrap());
        assert_eq!(
            RssProofField(a).mul(RssProofField(b)).0,
            qsag_asm::portable::poly128_mul_const(a, b)
        );
    }
    assert_eq!(
        RssProofField(u128::MAX).mul(RssProofField(u128::MAX)).0,
        qsag_asm::portable::poly128_mul_const(u128::MAX, u128::MAX)
    );
    for i in 0..128 {
        for j in 0..128 {
            let a = 1u128 << i;
            let b = 1u128 << j;
            assert_eq!(
                RssProofField(a).mul(RssProofField(b)).0,
                qsag_asm::portable::poly128_mul_const(a, b)
            );
        }
    }
    assert_ne!(RssProofField(1 << 127).mul(RssProofField(2)).0, 0);
}

/// Random consistent relation words: slot shares of `a`, `b` and of `c = a & b`.
fn random_relations(tag: &[u8], words: usize, active: u64) -> RssPendingDzkTriples {
    let mut xof = Cshake256Xof::new(b"RSS.RELATION.FIXTURE");
    xof.absorb(tag);
    let mut next = || {
        let mut bytes = [0u8; 8];
        xof.squeeze(&mut bytes);
        u64::from_le_bytes(bytes) & active
    };
    let mut pending = RssPendingDzkTriples::new();
    for _ in 0..words {
        let a: [u64; 3] = core::array::from_fn(|_| next());
        let b: [u64; 3] = core::array::from_fn(|_| next());
        let c0 = next();
        let c1 = next();
        let c2 = ((a[0] ^ a[1] ^ a[2]) & (b[0] ^ b[1] ^ b[2])) ^ c0 ^ c1;
        for (s, c) in [c0, c1, c2].into_iter().enumerate() {
            pending.a[s].push(a[s]);
            pending.b[s].push(b[s]);
            pending.c[s].push(c);
        }
    }
    pending
}

fn clone_relations(src: &RssPendingDzkTriples) -> RssPendingDzkTriples {
    RssPendingDzkTriples {
        a: src.a.clone(),
        b: src.b.clone(),
        c: src.c.clone(),
        lane_perms: src.lane_perms,
        fold_tables: RssDzkTables::default(),
        poison: RssPoisonLatch::new(),
    }
}

#[test]
fn rss_proof_helpers_match_bit_references() {
    let mut xof = Cshake256Xof::new(b"RSS.HELPER.REGRESSION");
    let mut word = || {
        let mut bytes = [0u8; 8];
        xof.squeeze(&mut bytes);
        u64::from_le_bytes(bytes)
    };
    // Transpose.
    let rows: [u64; 64] = core::array::from_fn(|_| word());
    let mut t = rows.map(|row| [row, !row, 0, 0]);
    qsag_asm::transpose64x256(&mut t);
    for (i, row) in rows.iter().enumerate() {
        for (j, col) in t.iter().enumerate() {
            assert_eq!((col[0] >> i) & 1, (row >> j) & 1);
            assert_eq!((col[1] >> i) & 1, (!row >> j) & 1);
            assert_eq!(col[2..], [0, 0]);
        }
    }
    // Ternary expansion: digit 0/1 selects a half, digit 2 is the XOR of both.
    let src: [u64; RSS_DZK_GROUP_WORDS] = core::array::from_fn(|_| word());
    let mut cur = [0u64; RSS_DZK_TERNARY];
    rss_ternary_expand(&src, &mut cur);
    for (e, got) in cur.iter().enumerate() {
        let mut expected = 0u64;
        for (u, value) in src.iter().enumerate() {
            let mut digits = e;
            let mut included = true;
            for l in 0..RSS_DZK_TENSOR_BITS {
                let digit = digits % 3;
                digits /= 3;
                included &= digit == 2 || digit == (u >> l) & 1;
            }
            if included {
                expected ^= value;
            }
        }
        assert_eq!(*got, expected, "point {e}");
    }
    // Group binding against per-bit accumulation.
    let beta: [u128; RSS_DZK_GROUP_WORDS] =
        core::array::from_fn(|_| u128::from(word()) | (u128::from(word()) << 64));
    let mut pattern = [[0u8; RSS_DZK_NIBBLES]; 128];
    for (bit, nibbles) in pattern.iter_mut().enumerate() {
        for g in 0..RSS_DZK_NIBBLES {
            for d in 0..4 {
                nibbles[g] |= (((beta[4 * g + d] >> bit) & 1) as u8) << d;
            }
        }
    }
    let rows: [[u64; 4]; RSS_DZK_GROUP_WORDS] =
        core::array::from_fn(|u| [src[u], word(), 0, word()]);
    let mut planes = [[[0u64; 4]; 64]; 2];
    let mut out = [[0u128; 4]; RSS_DZK_LANES];
    rss_bind_columns(&rows, &pattern, &mut planes, &mut out);
    for (lane, got) in out.iter().enumerate() {
        for (column, got) in got.iter().enumerate() {
            let mut expected = 0u128;
            for (row, weight) in rows.iter().zip(&beta) {
                if (row[column] >> lane) & 1 == 1 {
                    expected ^= weight;
                }
            }
            assert_eq!(*got, expected, "lane {lane}, column {column}");
        }
    }
    // Monomial multiplication and public inversion.
    let v = RssProofField(u128::from(word()) | (u128::from(word()) << 64));
    for shift in 0..64u32 {
        let mut mono = RssProofField::ONE;
        for _ in 0..shift {
            mono = mono.mul(RssProofField(2));
        }
        assert_eq!(v.mul_t_pow(shift).0, v.mul(mono).0);
    }
    assert_eq!(v.mul(v.inv_public()).0, 1);
}

/// A halving round split across workers and scratch blocks gives the scalar-field sums.
/// The length is above the threading threshold and not a multiple of any block size.
#[test]
fn rss_fold_round_split_matches_scalar_reference() {
    let n = (1usize << 14) + 37;
    let mut xof = Cshake256Xof::new(b"RSS.FOLD.FIXTURE");
    let mut next = || {
        let mut bytes = [0u8; 16];
        xof.squeeze(&mut bytes);
        u128::from_le_bytes(bytes)
    };
    let mut table =
        || -> [Vec<u128>; 3] { core::array::from_fn(|_| (0..2 * n + 5).map(|_| next()).collect()) };
    let (mut x, y) = (table(), table());
    let upper = n + 5;
    let f = RssProofField;
    let dots = rss_fold_cross_dots(
        &rss_fold_halves(&x, upper, n),
        &rss_fold_halves(&y, upper, n),
    );
    for p in 0..3 {
        let q = (p + 1) % 3;
        let (mut l, mut r) = (RssProofField::ZERO, RssProofField::ZERO);
        for i in 0..n {
            let hi = upper + i;
            l = l
                .add(f(x[p][i]).mul(f(y[p][hi] ^ y[q][hi])))
                .add(f(x[q][i]).mul(f(y[p][hi])));
            r = r
                .add(f(x[p][hi]).mul(f(y[p][i] ^ y[q][i])))
                .add(f(x[q][hi]).mul(f(y[p][i])));
        }
        assert_eq!(dots[p], [l.0, r.0]);
    }

    let before = x.clone();
    let scales = [f(next()), f(next()), f(next())];
    let mut jobs: Vec<(&mut [u128], &mut [u128], RssProofField)> = Vec::new();
    for (slot, scale) in x.iter_mut().zip(scales) {
        let (lo, hi) = slot.split_at_mut(upper);
        jobs.push((&mut lo[..n], &mut hi[..n], scale));
    }
    rss_fold_scale_xor(&mut jobs);
    for s in 0..3 {
        for i in 0..n {
            assert_eq!(
                x[s][i],
                before[s][i] ^ scales[s].mul(f(before[s][upper + i])).0
            );
        }
        assert_eq!(x[s][n..upper], before[s][n..upper]);
        assert!(x[s][upper..upper + n].iter().all(|v| *v == 0));
        assert_eq!(x[s][upper + n..], before[s][upper + n..]);
    }
}

/// One full Keccak batch (600 groups): its halving rounds cross the threading threshold.
#[test]
fn rss_proof_at_keccak_batch_size_accepts_honest_and_rejects_one_flipped_product() {
    let sid = [0x98; 32];
    let mut rngs = make_rngs3(0x3a);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    let mask = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
    let words = 24 * 1600;
    let honest = random_relations(b"keccak-batch", words, u64::MAX);
    let mut pending = clone_relations(&honest);
    verify_rss_boolean_triples_bbcggi19(&sid, 0, &mut pending, &mask, &mut rngs).unwrap();
    // Corrupt one product bit in the lower and in the upper half of the group index.
    for (ctr, word) in [(1u64, 17usize), (2, words - 3)] {
        let mut bad = clone_relations(&honest);
        bad.c[word % 3][word] ^= 1u64 << (word % 64);
        assert!(matches!(
            verify_rss_boolean_triples_bbcggi19(&sid, ctr, &mut bad, &mask, &mut rngs),
            Err(KeccakMpcError::RssSacrificeFailed)
        ));
    }
}

#[test]
fn rss_proof_accepts_honest_and_rejects_every_bit_position_and_operand() {
    let sid = [0x97; 32];
    let mut rngs = make_rngs3(0x39);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    let mask = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
    let mut ctr = 0u64;
    // Word counts cover one partial group, exact groups, and a non-power-of-two group count.
    for (words, active) in [
        (1usize, 1u64),
        (3, 0x7f),
        (64, u64::MAX),
        (130, u64::MAX),
        (321, u64::MAX >> 1),
    ] {
        let honest = random_relations(&[words as u8], words, active);
        let mut pending = clone_relations(&honest);
        verify_rss_boolean_triples_bbcggi19(&sid, ctr, &mut pending, &mask, &mut rngs).unwrap();
        assert_eq!(pending.len_words(), 0);
        ctr += 1;
        for bit in 0..64usize {
            // Rotate the corrupted word, slot and operand with the bit position.
            let word = (bit * 37 + words / 2) % words;
            let slot = bit % 3;
            let mut bad = clone_relations(&honest);
            match (bit / 3) % 3 {
                0 => bad.c[slot][word] ^= 1u64 << bit,
                1 => {
                    // Flipping `a` breaks the relation exactly where `b` is set.
                    bad.a[slot][word] ^= 1u64 << bit;
                    for (s, row) in bad.b.iter_mut().enumerate() {
                        row[word] |= u64::from(s == 0) << bit;
                        row[word] &= !(u64::from(s != 0) << bit);
                    }
                    let a_bit = ((bad.a[0][word] ^ bad.a[1][word] ^ bad.a[2][word]) >> bit) & 1;
                    let c_bit = ((bad.c[0][word] ^ bad.c[1][word] ^ bad.c[2][word]) >> bit) & 1;
                    if a_bit == c_bit {
                        bad.c[slot][word] ^= 1u64 << bit;
                    }
                }
                _ => {
                    bad.b[slot][word] ^= 1u64 << bit;
                    for (s, row) in bad.a.iter_mut().enumerate() {
                        row[word] |= u64::from(s == 0) << bit;
                        row[word] &= !(u64::from(s != 0) << bit);
                    }
                    let b_bit = ((bad.b[0][word] ^ bad.b[1][word] ^ bad.b[2][word]) >> bit) & 1;
                    let c_bit = ((bad.c[0][word] ^ bad.c[1][word] ^ bad.c[2][word]) >> bit) & 1;
                    if b_bit == c_bit {
                        bad.c[slot][word] ^= 1u64 << bit;
                    }
                }
            }
            let x = |v: &[Vec<u64>; 3]| ((v[0][word] ^ v[1][word] ^ v[2][word]) >> bit) & 1;
            assert_ne!(
                x(&bad.a) & x(&bad.b),
                x(&bad.c),
                "fixture must be a false relation"
            );
            assert!(matches!(
                verify_rss_boolean_triples_bbcggi19(&sid, ctr, &mut bad, &mask, &mut rngs),
                Err(KeccakMpcError::RssSacrificeFailed)
            ));
            assert_eq!(bad.len_words(), 0);
            ctr += 1;
        }
    }
}

#[test]
fn rss_keccak_proof_rejects_a_flipped_product_in_every_round_and_bit_position() {
    let sid = [0x95; 32];
    let mut rngs = make_rngs3(0x3b);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    let mask = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
    let mut prim = [[0u64; 1600]; 3];
    for (s, share) in prim.iter_mut().enumerate() {
        for (idx, word) in share.iter_mut().enumerate() {
            *word = (idx as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15 ^ (s as u64) << 7);
        }
    }
    let mut sec = [prim[1], prim[2], prim[0]];
    let mut honest = RssPendingDzkTriples::new();
    eval_rss_keccak_f1600_batch64_record(&sid, 0, 64, &mut prim, &mut sec, &mask, &mut honest)
        .unwrap();
    assert_eq!(honest.len_words(), 24 * 1600);
    let mut pending = clone_relations(&honest);
    verify_rss_boolean_triples_bbcggi19(&sid, 0, &mut pending, &mask, &mut rngs).unwrap();
    // Cover every round and every bit with 64 probes. The primitive proof
    // test above separately exhausts operand/bit combinations; repeating a
    // complete Keccak proof for their Cartesian product adds no new branch.
    for (ctr, bit) in (1u64..).zip(0..64usize) {
        let round = bit % 24;
        // A different state position for every (round, bit) pair.
        let word = round * 1600 + (bit * 25 + round * 67) % 1600;
        let mut bad = clone_relations(&honest);
        bad.c[(round + bit) % 3][word] ^= 1u64 << bit;
        assert!(matches!(
            verify_rss_boolean_triples_bbcggi19(&sid, ctr, &mut bad, &mask, &mut rngs),
            Err(KeccakMpcError::RssSacrificeFailed)
        ));
    }
}

#[test]
fn rss_mask_session_is_hedged_by_party_entropy_and_bound_to_shares() {
    let sid = [0x93; 32];
    let mut rngs = make_rngs3(0x3d);
    let (mut keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    let first = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
    assert!(first.shared);
    let mut fork_a = RssMaskSession {
        prim: first.prim,
        sec: first.sec,
        shared: first.shared,
    };
    let mut fork_b = RssMaskSession {
        prim: first.prim,
        sec: first.sec,
        shared: first.shared,
    };
    fork_a.hedge_transcript(b"same session/message one");
    fork_b.hedge_transcript(b"same session/message two");
    assert_ne!(fork_a.prim, fork_b.prim);
    for p in 0..3 {
        assert_eq!(fork_a.prim[p], fork_a.sec[(p + 2) % 3]);
    }
    // Same session identifier and keys, fresh party entropy: every stream key changes.
    let second = RssMaskSession::derive(&sid, &keys, &mut rngs).unwrap();
    for p in 0..3 {
        assert_ne!(first.prim[p], second.prim[p]);
        assert_eq!(second.sec[p], second.prim[(p + 1) % 3]);
        for q in 0..3 {
            assert!(p == q || second.prim[p] != second.prim[q]);
        }
    }
    // One party repeating its entropy is not enough to repeat the joint coin.
    let mut replay_a = make_rngs3(0x50);
    let mut replay_b = make_rngs3(0x50);
    replay_b[1] = PartyPrivateRng::from_seed([0x99; 32], b"rss-test");
    let a = RssMaskSession::derive(&sid, &keys, &mut replay_a).unwrap();
    let b = RssMaskSession::derive(&sid, &keys, &mut replay_b).unwrap();
    assert_ne!(a.prim, b.prim);
    // Identical entropy but a different replicated secret share: the slot key changes.
    let mut replay_c = make_rngs3(0x50);
    keys[0].sk_seed_primary[0] ^= 1;
    keys[2].sk_seed_secondary[0] ^= 1;
    let c = RssMaskSession::derive(&sid, &keys, &mut replay_c).unwrap();
    assert!(c.shared);
    assert_ne!(a.prim[0], c.prim[0]);
    assert_eq!(a.prim[1], c.prim[1]);
    // A holder pair that disagrees is detected and loses the shared-stream path.
    keys[1].sk_prf_secondary[3] ^= 0x10;
    let mut replay_d = make_rngs3(0x50);
    assert!(
        !RssMaskSession::derive(&sid, &keys, &mut replay_d)
            .unwrap()
            .shared
    );
}

#[test]
fn rss_batch_rejects_invalid_lengths_and_inconsistent_replicas_without_mutation() {
    let sid = [0x98; 32];
    let mut rngs = make_rngs3(0x41);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    let mut primary = [[7u64; 1600]; 3];
    let mut secondary = primary;
    for len in [0, 65, usize::MAX] {
        assert!(matches!(
            eval_rss_keccak_f1600_batch64(
                &sid,
                0,
                len,
                &mut primary,
                &mut secondary,
                &keys,
                &mut rngs
            ),
            Err(KeccakMpcError::InvalidBatchSize(_))
        ));
        assert_eq!(primary, [[7; 1600]; 3]);
    }
    secondary[0][0] ^= 1;
    assert!(matches!(
        eval_rss_keccak_f1600_batch64(&sid, 0, 1, &mut primary, &mut secondary, &keys, &mut rngs),
        Err(KeccakMpcError::RssShareEqualityFailed(_))
    ));
    assert_eq!(primary, [[7; 1600]; 3]);
}

#[test]
fn rss_chi_rejects_mismatched_pairwise_mask_seed() {
    let sid = [0x91; 32];
    let mut rngs = make_rngs3(0x42);
    let (mut keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
    keys[0].prg_seed_secondary[0] ^= 1;
    let mut primary = [[1u64; 1600]; 3];
    let mut secondary = primary;
    assert!(
        eval_rss_keccak_f1600_batch64(&sid, 0, 1, &mut primary, &mut secondary, &keys, &mut rngs)
            .is_err()
    );
    // The permutation ran, its proof failed: no unverified output share is handed back.
    assert_eq!(primary, [[0u64; 1600]; 3]);
    assert_eq!(secondary, [[0u64; 1600]; 3]);
}

fn make_rngs3(tag: u8) -> [PartyPrivateRng; 3] {
    core::array::from_fn(|p| {
        PartyPrivateRng::from_seed([tag.wrapping_add(p as u8); 32], b"rss-test")
