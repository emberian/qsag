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
    })
}

#[test]
fn test_batch_active_mask_zero_shift_overflow_and_rss_64way_keccak_parity() {
    assert_eq!(batch_active_mask(0), 0);
    assert_eq!(batch_active_mask(1), 1);
    assert_eq!(batch_active_mask(63), (1u64 << 63) - 1);
    assert_eq!(batch_active_mask(64), u64::MAX);

    let sid = [0x33; 32];
    let mut rngs = make_rngs3(0x10);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();

    // Check all 64 parallel Keccak-f[1600] instances against native `keccak_f1600`!
    let mut ref_states = [[0u64; 25]; 64];
    let mut st_p = SecretBuffer([[0u64; 1600]; 3]);
    let mut st_s = SecretBuffer([[0u64; 1600]; 3]);
    let mut inst = 0;
    while inst < 64 {
        for lane in 0..25 {
            let w =
                ((inst as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)).wrapping_add(lane as u64 * 17);
            ref_states[inst][lane] = w;
            let s0 = rngs[0].next_u64() & (1u64 << inst);
            let s1 = rngs[1].next_u64() & (1u64 << inst);
            for z in 0..64 {
                let bit = ((w >> z) & 1) << inst;
                let s2 = bit ^ s0 ^ s1;
                st_p[0][lane * 64 + z] |= s0;
                st_s[0][lane * 64 + z] |= s1;
                st_p[1][lane * 64 + z] |= s1;
                st_s[1][lane * 64 + z] |= s2;
                st_p[2][lane * 64 + z] |= s2;
                st_s[2][lane * 64 + z] |= s0;
            }
        }
        keccak_f1600(&mut ref_states[inst]);
        inst += 1;
    }

    eval_rss_keccak_f1600_batch64(&sid, 0, 64, &mut st_p, &mut st_s, &keys, &mut rngs).unwrap();

    let mut inst = 0;
    while inst < 64 {
        for lane in 0..25 {
            let mut got = 0u64;
            for z in 0..64 {
                let b =
                    ((st_p[0][lane * 64 + z] ^ st_p[1][lane * 64 + z] ^ st_p[2][lane * 64 + z])
                        >> inst)
                        & 1;
                got |= b << z;
            }
            assert_eq!(got, ref_states[inst][lane]);
        }
        inst += 1;
    }

    // Active RSS share lie MUST emit `RssSlashingReceipt` with probability 1!
    let mut bad_sec = [vec![st_s[0][0]], vec![st_s[1][0]], vec![st_s[2][0] ^ 1]];
    let prim = [vec![st_p[0][0]], vec![st_p[1][0]], vec![st_p[2][0]]];
    let latch = RssPoisonLatch::new();
    assert_eq!(
        rss_commit_and_open_u64_batch(&sid, "tamper", &prim, &bad_sec, &mut rngs, &latch)
            .unwrap_err(),
        KeccakMpcError::RssShareEqualityFailed(RssSlashingReceipt {
            share_slot: 0,
            primary_party: 0,
            secondary_party: 2,
        })
    );
    assert!(latch.is_set());
    bad_sec[2][0] ^= 1;
    let latch = RssPoisonLatch::new();
    rss_commit_and_open_u64_batch(&sid, "honest", &prim, &bad_sec, &mut rngs, &latch).unwrap();
    assert!(!latch.is_set());
}

#[test]
#[ignore = "Full FIPS 205 production-height MPC soak; compact multilayer signatures and FIPS KATs run by default"]
fn test_rss_slh_dsa_mpc_128f_exact_kat_parity_and_distributed_tsw() {
    let sid = [0x51; 32];
    let mut rngs = make_rngs3(0x20);
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();

    // Verify distributed `SLH-DSA-SHAKE-128f` (`17,088 B` official NIST parameter set!)
    let sk_seed: [u8; 16] = core::array::from_fn(|b| {
        keys[0].sk_seed_primary[b] ^ keys[1].sk_seed_primary[b] ^ keys[2].sk_seed_primary[b]
    });
    let sk_prf: [u8; 16] = core::array::from_fn(|b| {
        keys[0].sk_prf_primary[b] ^ keys[1].sk_prf_primary[b] ^ keys[2].sk_prf_primary[b]
    });
    let pk_seed_16 = &keys[0].pk_seed[..16].to_vec();
    let p128f = Fips205Params::SLH_DSA_SHAKE_128F;
    let (ref_sk, ref_pk) = slh_keygen_internal(&p128f, &sk_seed, &sk_prf, pk_seed_16).unwrap();

    let mut cluster = RssSlhMpcCluster::new(sid, keys, rngs).unwrap();
    let mpc_pk = slh_keygen_mpc(&p128f, &mut cluster, pk_seed_16).unwrap();
    assert_eq!(mpc_pk, ref_pk);

    let msg = b"distributed-threshold-slh-dsa-128f";
    let ctx = b"qsag-mpc-ctx";
    #[cfg(feature = "std")]
    let sign_start = std::time::Instant::now();
    let mpc_sig = slh_sign_mpc(&p128f, &mut cluster, msg, ctx, &mpc_pk, None).unwrap();
    #[cfg(feature = "std")]
    std::eprintln!("SLH-DSA-SHAKE-128f MPC sign: {:?}", sign_start.elapsed());
    let ref_sig = crate::fips205::slh_sign(&p128f, msg, ctx, &ref_sk, None).unwrap();
    assert_eq!(mpc_sig.len(), 17_088);
    // Deterministic (`addrnd = None`) MPC signature MUST be 100% BIT-FOR-BIT IDENTICAL to FIPS 205!
    assert_eq!(mpc_sig, ref_sig);
    assert!(slh_verify(&p128f, msg, &mpc_sig, ctx, &mpc_pk));

    // Also test distributed `DkgCachedSubtrees::build_distributed_rss` + `sign_stateless_tsw_rss_mpc`
    let mut rngs32 = make_rngs3(0x40);
    let (keys32, _) = run_dealerless_rss_dkg_2of3([0x52; 32], 32, &mut rngs32).unwrap();
    // Reference-only reconstruction of the test fixture; the cluster keeps its shares.
    let xor3 = |pick: fn(&RssKeyShare256) -> [u8; 32]| -> [u8; 32] {
        let parts = [pick(&keys32[0]), pick(&keys32[1]), pick(&keys32[2])];
        core::array::from_fn(|b| parts[0][b] ^ parts[1][b] ^ parts[2][b])
    };
    let tsw_sk = PqSecretKey {
        sk_seed: xor3(|k| k.sk_seed_primary),
        sk_prf: xor3(|k| k.sk_prf_primary),
        pk_seed: keys32[0].pk_seed,
    };
    let mut cluster32 = RssSlhMpcCluster::new([0x52; 32], keys32, rngs32).unwrap();
    let tsw_params = PqHashParams::COMPACT_GOLDEN;
    let cached = DkgCachedSubtrees::build_distributed_rss(&tsw_params, &mut cluster32, 64).unwrap();
    // The distributed public key is the reference key of the same seeds.
    assert_eq!(
        cached.pk,
        derive_public_key(Cshake256Suite, &tsw_params, &tsw_sk)
    );
    let tsw_msg = b"distributed-corduroy-msg";
    let tsw_sig =
        sign_stateless_tsw_rss_mpc(&tsw_params, &mut cluster32, &cached.pk, tsw_msg, 100_000)
            .unwrap();
    assert!(verify_pq_hash_sig(
        Cshake256Suite,
        &tsw_params,
        &cached.pk,
        tsw_msg,
        &tsw_sig
    ));
    // Given the same randomizer, the distributed signature equals the reference signature
    // in every FORS opening, WOTS chain value, grind counter and authentication path.
    let mu = th_pre_hash(
        Cshake256Suite,
        &cached.pk.pk_seed,
        &cached.pk.pk_root,
        tsw_msg,
    );
    let (leaf, fors_idxs) = derive_stateless_leaf_and_fors_indices(
        Cshake256Suite,
        &tsw_params,
        &tsw_sig.r_rand,
        &cached.pk.pk_seed,
        &cached.pk.pk_root,
        &mu,
    )
    .unwrap();
    let reference_sig = sign_hypertree_core(
        Cshake256Suite,
        &tsw_params,
        &tsw_sk,
        &cached.pk,
        &mu,
        tsw_sig.r_rand,
        leaf,
        Some(&fors_idxs),
        100_000,
    )
    .unwrap();
    assert_eq!(tsw_sig, reference_sig);
    let mut forged = tsw_sig;
    forged.layer_sigs[0].wots_chains[0][0] ^= 1;
    assert!(!verify_pq_hash_sig(
        Cshake256Suite,
        &tsw_params,
        &cached.pk,
        tsw_msg,
        &forged
    ));
}

#[test]
fn tsw_rss_signer_randomizer_is_deterministic_and_bound_to_the_generated_key() {
    // Smallest well-formed stateless profile: 2 layers of 2 leaves, 2 FORS trees of 2 leaves.
    let params = PqHashParams {
        w: 4,
        ell1: 128,
        subtree_height: 1,
        num_layers: 2,
        fors_trees: 2,
        fors_height: 1,
        max_sigs_log2: 2,
        stateful: false,
    };
    assert!(params.is_well_formed());
    let mut dkg_rngs = make_rngs3(0x71);
    let (keys, _) = run_dealerless_rss_dkg_2of3([0x71; 32], 32, &mut dkg_rngs).unwrap();
    let sk_prf: [u8; 32] = core::array::from_fn(|b| {
        keys[0].sk_prf_primary[b] ^ keys[1].sk_prf_primary[b] ^ keys[2].sk_prf_primary[b]
    });
    let msg = b"one message, two sessions";
    let untouched = |c: &RssSlhMpcCluster| (c.batch_ctr, c.lane_permutations());

    // Shares that were never bound to a public key sign nothing.
    let mut first = RssSlhMpcCluster::new([0xa1; 32], keys, make_rngs3(0x81)).unwrap();
    let before = untouched(&first);
    let unbound_pk = PqPublicKey {
        pk_seed: first.keys[0].pk_seed,
        pk_root: [7u8; 32],
    };
    assert_eq!(
        sign_stateless_tsw_rss_mpc(&params, &mut first, &unbound_pk, msg, 100_000).unwrap_err(),
        KeccakMpcError::KeyBindingMismatch
    );
    assert_eq!(untouched(&first), before);

    let pk = DkgCachedSubtrees::build_distributed_rss(&params, &mut first, 64)
        .unwrap()
        .pk;

    // A root or parameter set other than the generated one is refused before any
    // evaluation or opening.
    let before = untouched(&first);
    let mut wrong_root = PqPublicKey {
        pk_seed: pk.pk_seed,
        pk_root: pk.pk_root,
    };
    wrong_root.pk_root[31] ^= 0x80;
    assert_eq!(
        sign_stateless_tsw_rss_mpc(&params, &mut first, &wrong_root, msg, 100_000).unwrap_err(),
        KeccakMpcError::KeyBindingMismatch
    );
    let mut other_params = params;
    other_params.fors_height = 2;
    assert_eq!(
        sign_stateless_tsw_rss_mpc(&other_params, &mut first, &pk, msg, 100_000).unwrap_err(),
        KeccakMpcError::KeyBindingMismatch
    );
    // Shorter chains under the bound key would open interior chain values.
    let short_chains = PqHashParams {
        w: 2,
        ell1: 256,
        ..params
    };
    assert!(short_chains.is_well_formed());
    assert_eq!(
        DkgCachedSubtrees::build_distributed_rss(&short_chains, &mut first, 64).unwrap_err(),
        KeccakMpcError::KeyBindingMismatch
    );
    assert_eq!(untouched(&first), before);
    assert!(!first.is_poisoned());

    let sig_first = sign_stateless_tsw_rss_mpc(&params, &mut first, &pk, msg, 100_000).unwrap();

    // Second session on the same key shares: another session id, other party randomness.
    let RssSlhMpcCluster { keys, .. } = first;
    let mut second = RssSlhMpcCluster::new([0xa2; 32], keys, make_rngs3(0x91)).unwrap();
    assert_ne!(second.mask_session.prim, [[0u8; 32]; 3]);
    let sig_second = sign_stateless_tsw_rss_mpc(&params, &mut second, &pk, msg, 100_000).unwrap();
    assert_eq!(sig_first.r_rand, sig_second.r_rand);
    assert_eq!(sig_first, sig_second);
    assert!(verify_pq_hash_sig(
        Cshake256Suite,
        &params,
        &pk,
        msg,
        &sig_first
    ));

    // `R` is the PRF of the shared key on public inputs fixed by the key and message.
    let mu = th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, msg);
    let expected_r = fips205_prf_msg(32, &sk_prf, &tsw_rss_opt_rand(&pk), &mu);
    assert_eq!(sig_first.r_rand.as_slice(), expected_r.as_slice());
}

/// Test-only trusted dealer for authenticated SPDZ Shamir material: degree-`< t` shares over
/// `TowerGf256` and matching 2-lane `Tower128` MAC shares under one global key. It replaces
/// dealerless preprocessing in these tests, which exercise the online protocol only.
pub(crate) struct SpdzTestDealer {
    t: usize,
    pts: Vec<TowerGf256>,
    alpha: [Tower128; 2],
    stream: Cshake256WordStream4,
}

impl SpdzTestDealer {
    pub(crate) fn new(tag: &[u8], t: usize, pts: &[TowerGf256]) -> Self {
        let mid = crate::sponge::keccak::cshake256_static_midstate(b"QSAG.TEST.SPDZ.DEALER/v1");
        let mut dealer = Self {
            t,
            pts: pts.to_vec(),
            alpha: [Tower128::ZERO; 2],
            stream: Cshake256WordStream4::new(&mid, tag),
        };
        dealer.alpha = [dealer.tower(), dealer.tower()];
        dealer
    }

    fn word(&mut self) -> u64 {
        let mut w = [0u64; 1];
        self.stream.fill_words(&mut w);
        w[0]
    }

    fn tower(&mut self) -> Tower128 {
        Tower128(u128::from(self.word()) | (u128::from(self.word()) << 64))
    }

    fn share_tower(&mut self, secret: Tower128) -> Vec<Tower128> {
        let coeffs: Vec<Tower128> = (1..self.t).map(|_| self.tower()).collect();
        self.pts
            .iter()
            .map(|&pt| {
                let mut acc = secret;
                let mut power = pt;
                for c in &coeffs {
                    acc = acc.add(c.mul_gf256(power));
                    power = power.mul(pt);
                }
                acc
            })
            .collect()
    }

    fn alpha_shares(&mut self) -> Vec<[Tower128; 2]> {
        let lanes = [
            self.share_tower(self.alpha[0]),
            self.share_tower(self.alpha[1]),
        ];
        (0..self.pts.len())
            .map(|p| [lanes[0][p], lanes[1][p]])
            .collect()
    }

    /// Authenticated sharing of 64 bits: per-party share word and MAC word.
    fn auth_word(&mut self, bits: u64) -> (Vec<BitslicedGf256x64>, Vec<SpdzMacWord>) {
        let n = self.pts.len();
        let mut sh = vec![[0u64; 8]; n];
        let mut mac = vec![[[Tower128::ZERO; 64]; 2]; n];
        // Sample independent degree-(t-1) polynomials in plane layout. This
        // test dealer must not dominate online circuit benchmarks with
        // millions of scalar field operations and one-word PRG calls.
        let mut coeffs = SecretBuffer(vec![[0u64; 8]; self.t]);
        coeffs[0][0] = bits;
        for coeff in &mut coeffs[1..] {
            self.stream.fill_words(coeff);
        }
        let mut tags = SecretBuffer(vec![[[0u64; 4]; 64]; self.t]);
        for bit in 0..64 {
            for col in 0..4 {
                let alpha_bit = (self.alpha[col / 2].0 >> (64 * (col % 2) + bit)) & 1;
                tags[0][bit][col] = bits & 0u64.wrapping_sub(alpha_bit as u64);
            }
        }
        for coeff in &mut tags[1..] {
            self.stream.fill_words(coeff.as_flattened_mut());
        }
        for (p, &pt) in self.pts.iter().enumerate() {
            let scale = crate::field::tower::PublicGf256Matrix::from_public_scalar(pt);
            let mut value = coeffs[self.t - 1];
            for coeff in coeffs[..self.t - 1].iter().rev() {
                value = scale.scale_planes(&value);
                bs_gf256_xor_assign(&mut value, coeff);
            }
            sh[p] = value;
            let mut planes = SecretBuffer(tags[self.t - 1]);
            for coeff in tags[..self.t - 1].iter().rev() {
                for col in 0..4 {
                    for byte in 0..8 {
                        let block = core::array::from_fn(|bit| planes[8 * byte + bit][col]);
                        let scaled = scale.scale_planes(&block);
                        for bit in 0..8 {
                            planes[8 * byte + bit][col] = scaled[bit] ^ coeff[8 * byte + bit][col];
                        }
                    }
                }
            }
            qsag_asm::transpose64x256(&mut planes);
            for i in 0..64 {
                for ml in 0..2 {
                    mac[p][ml][i] = Tower128(
                        u128::from(planes[i][2 * ml]) | (u128::from(planes[i][2 * ml + 1]) << 64),
                    );
                }
            }
        }
        (sh, mac)
    }

    pub(crate) fn vaults(&mut self, triples: usize) -> Vec<PreprocessedKeccakPartyVault> {
        let n = self.pts.len();
        let alpha_shares = self.alpha_shares();
        let mut per_party: Vec<Vec<KeccakBitTripleShare64>> =
            (0..n).map(|_| Vec::with_capacity(triples)).collect();
        for _ in 0..triples {
            let a = self.word();
            let b = self.word();
            let (a_sh, a_mac) = self.auth_word(a);
            let (b_sh, b_mac) = self.auth_word(b);
            let (c_sh, c_mac) = self.auth_word(a & b);
            for p in 0..n {
                per_party[p].push(KeccakBitTripleShare64 {
                    a: a_sh[p],
                    b: b_sh[p],
                    c: c_sh[p],
                    a_mac: a_mac[p],
                    b_mac: b_mac[p],
                    c_mac: c_mac[p],
                });
            }
        }
        per_party
            .into_iter()
            .enumerate()
            .map(|(p, triples)| PreprocessedKeccakPartyVault {
                party_id: p,
                eval_point: self.pts[p],
                mac_alpha_lanes: alpha_shares[p],
                triples,
                cursor: 0,
                poisoned: false,
            })
            .collect()
    }

    pub(crate) fn key_shares(
        &mut self,
        key_len: usize,
        pk_seed: [u8; 32],
        sk_seed: &[u8; 32],
        sk_prf: &[u8; 32],
    ) -> Vec<SpdzAuthenticatedKeyShare> {
        let n = self.pts.len();
        let auth = |dealer: &mut Self, key: &[u8; 32]| {
            let mut words = vec![[[0u64; 8]; 4]; n];
            let mut macs = vec![[[[Tower128::ZERO; 64]; 2]; 4]; n];
            for w in 0..4 {
                let mut bits = u64::from_le_bytes(key[8 * w..8 * w + 8].try_into().unwrap());
                if 8 * w >= key_len {
                    bits = 0;
                }
                let (sh, mac) = dealer.auth_word(bits);
                for p in 0..n {
                    words[p][w] = sh[p];
                    macs[p][w] = mac[p];
                }
            }
            (words, macs)
        };
        let (seed_words, seed_macs) = auth(self, sk_seed);
        let (prf_words, prf_macs) = auth(self, sk_prf);
        (0..n)
            .map(|p| SpdzAuthenticatedKeyShare {
                party_id: p,
                eval_point: self.pts[p],
                key_len,
                pk_seed,
                sk_seed_words: seed_words[p],
                sk_seed_macs: seed_macs[p],
                sk_prf_words: prf_words[p],
                sk_prf_macs: prf_macs[p],
                slh_profile: SlhProfileLatch::new(),
            })
            .collect()
    }
}

fn spdz_test_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
    (0..n)
        .map(|p| PartyPrivateRng::from_seed([tag + p as u8; 32], b"spdz-k"))
        .collect()
}

#[test]
fn rss_secret_codec_preserves_slh_and_tsw_profile_locks() {
    let mut rngs: [PartyPrivateRng; 3] = core::array::from_fn(|i| {
        PartyPrivateRng::from_seed([0x18 + i as u8; 32], b"codec-profile")
    });
    let (mut shares, _) = run_dealerless_rss_dkg_2of3([0x38; 32], 32, &mut rngs).unwrap();
    shares[0].slh_profile_digest =
        Some(slh_profile_digest_u64x4(&Fips205Params::SLH_DSA_SHAKE_256F));
    let encoded = shares[0].to_secret_bytes();
    assert_eq!(encoded.len(), 300);
    let mut restored = RssKeyShare256::from_secret_bytes(&encoded).unwrap();
    assert_eq!(restored.slh_profile_digest, shares[0].slh_profile_digest);
    assert!(restored.bind_scheme_identity(&[7; 32]).is_err());
    assert!(RssKeyShare256::from_secret_bytes(&encoded[..268]).is_err());
    shares[1].tsw_binding = Some(TswKeyBinding {
        params_digest: [7; 32],
        pk_root: [8; 32],
    });
    let encoded = shares[1].to_secret_bytes();
    assert_eq!(encoded.len(), 332);
    let restored = RssKeyShare256::from_secret_bytes(&encoded).unwrap();
    assert!(restored.tsw_binding == shares[1].tsw_binding);
}

#[test]
fn pending_mac_uses_retained_mesh_and_rejects_each_corrupt_lane() {
    let sid = [0x57; 32];
    let mut rngs = spdz_test_rngs(3, 0x3a);
    let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
    let points = [TowerGf256(1), TowerGf256(2), TowerGf256(3)];
    let opened = vec![[0u64; 8]];
    let mut macs = vec![vec![[[Tower128::ZERO; 64]; 2]]; 3];
    let alpha = [[Tower128(9), Tower128(11)]; 3];
    verify_pending_spdz_mac_batch_with_mesh(
        &sid,
        "test_pending_blind",
        2,
        &points,
        &opened,
        &macs,
        &alpha,
        &mut rngs,
        Some(&mut mesh),
    )
    .unwrap();
    for lane in 0..2 {
        macs[0][0][lane][0] = Tower128(1);
        assert!(matches!(
            verify_pending_spdz_mac_batch_with_mesh(
                &sid,
                "test_pending_blind",
                2,
                &points,
                &opened,
                &macs,
                &alpha,
                &mut rngs,
                Some(&mut mesh)
            ),
            Err(PreprocessError::MacCheckFailed { .. })
        ));
        macs[0][0][lane][0] = Tower128::ZERO;
    }
    assert!(
        verify_pending_spdz_mac_batch_with_mesh(
            &sid,
            "test_pending_blind",
            4,
            &points,
            &opened,
            &macs,
            &alpha,
            &mut rngs,
            Some(&mut mesh)
        )
        .is_err()
    );
}

#[test]
fn test_spdz_shamir_keccak_dishonest_majority_prf_msg_and_poison_abort() {
    // Dishonest-majority 3-of-4 Shamir (`2t - 1 = 5 > 4`, up to `2` active Byzantine signers!)
    let t = 3usize;
    let n = 4usize;
    let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
    let mut rngs = spdz_test_rngs(n, 0x70);
    let mut dealer = SpdzTestDealer::new(b"prf-msg", t, &pts);
    let sk_seed = [0x5a; 32];
    let sk_prf: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(29) ^ 0xc3);
    let mut pk_seed = [0u8; 32];
    pk_seed[..16].copy_from_slice(&[0x11; 16]);
    let mut auth_keys = dealer.key_shares(16, pk_seed, &sk_seed, &sk_prf);
    // 1200 triples = 2 Keccak-f[1600] blocks (`600` per permutation: 1 honest + 1 tamper test!)
    let mut vaults = dealer.vaults(1200);

    let opt_rand = [0xABu8; 16];
    let m_prime = b"\x00\x04ctx!spdz-shamir-keccak-test";
    let expected_r = fips205_prf_msg(16, &sk_prf[..16], &opt_rand, m_prime);

    // 1. Honest `t = 3` quorum (`parties 0, 1, 2`) matches `fips205_prf_msg` bit-for-bit!
    {
        let mut cluster = SpdzSlhMpcCluster::new(
            [0x67; 32],
            t,
            &auth_keys[..t],
            &mut vaults[..t],
            &mut rngs[..t],
        )
        .unwrap();
        let (got_r, _tok) = cluster.eval_prf_msg_mpc(16, &opt_rand, m_prime).unwrap();
        assert_eq!(got_r, expected_r);
    }
    assert!(
        vaults[..t]
            .iter()
            .all(|v| !v.poisoned && v.remaining() == 600)
    );

    // 2. Dishonest-majority active share tamper (`parties 0 and 1` collude and forge `sk_prf_words`)
    //    MUST be caught by SPDZ `MacCheck` BEFORE opening `R` AND permanently poison all vaults!
    auth_keys[0].sk_prf_words[0][0] ^= 1;
    auth_keys[0].sk_prf_words[0][1] ^= 1;
    auth_keys[1].sk_prf_words[0][1] ^= 1;
    {
        let mut bad_cluster = SpdzSlhMpcCluster::new(
            [0x68; 32],
            t,
            &auth_keys[..t],
            &mut vaults[..t],
            &mut rngs[..t],
        )
        .unwrap();
        assert_eq!(
            bad_cluster
                .eval_prf_msg_mpc(16, &opt_rand, m_prime)
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
    }
    assert!(vaults[0].poisoned && vaults[1].poisoned && vaults[2].poisoned);
    assert_eq!(vaults[2].mac_alpha_lanes, [Tower128::ZERO; 2]);
}

#[test]
fn spdz_batch64_prf_and_masked_f_match_fips_and_cut_tamper_poisons() {
    let _memory = crate::test_budget::reserve_mb(1700);
    let t = 2usize;
    let pts: Vec<TowerGf256> = (1..=2u8).map(TowerGf256).collect();
    let mut rngs = spdz_test_rngs(2, 0x80);
    let mut dealer = SpdzTestDealer::new(b"batch64", t, &pts);
    let sk_seed: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(37) ^ 0x6d);
    let sk_prf = [0x21; 32];
    let mut pk_seed = [0u8; 32];
    pk_seed[..16].copy_from_slice(&[0x33; 16]);
    let keys = dealer.key_shares(16, pk_seed, &sk_seed, &sk_prf);
    // Two 64-instance permutations: 24 rounds of 1600 triple words each.
    let per_batch = 24 * SPDZ_BATCH_POSITIONS;
    let mut vaults = dealer.vaults(2 * per_batch);
    let mut cluster = SpdzSlhMpcCluster::new([0x69; 32], t, &keys, &mut vaults, &mut rngs).unwrap();

    let prf_adrs: Vec<Fips205Adrs> = (0..64u32)
        .map(|i| {
            let mut a = Fips205Adrs::ZERO;
            a.layer = i % 3;
            a.adrs_type = Fips205AdrsType::WotsPrf;
            a.key_pair = i / 7;
            a.f5 = i;
            a
        })
        .collect();
    let step_adrs: Vec<Fips205Adrs> = prf_adrs
        .iter()
        .map(|a| {
            let mut s = *a;
            s.adrs_type = Fips205AdrsType::WotsHash;
            s.f6 = 5;
            s
        })
        .collect();
    // Every third instance keeps its PRF value; the others take one F step.
    let exec_mask = (0..64).fold(0u64, |m, i| if i % 3 == 0 { m } else { m | (1 << i) });

    let (mut cur_sh, mut cur_mac) = cluster
        .eval_prf_batch64_spdz(&pk_seed[..16], &prf_adrs)
        .unwrap();
    cluster
        .eval_f_step_masked_batch64_spdz(
            &pk_seed[..16],
            &step_adrs,
            exec_mask,
            &mut cur_sh,
            &mut cur_mac,
        )
        .unwrap();
    assert!(cluster.vaults.iter().all(|v| v.remaining() == 0));

    let (blocks, _tok) = cluster
        .finalize_cut_batches_spdz("spdz_cut_batch64_test", &cur_sh, &cur_mac, &[64])
        .unwrap();
    assert_eq!(blocks.len(), 64);
    for i in 0..64 {
        let prf = crate::fips205::fips205_prf(16, &pk_seed[..16], &sk_seed[..16], &prf_adrs[i]);
        let expected = if (exec_mask >> i) & 1 == 1 {
            crate::fips205::fips205_f(16, &pk_seed[..16], &step_adrs[i], &prf)
        } else {
            prf
        };
        assert_eq!(blocks[i], expected, "instance {i}");
    }

    // A forged cut share (consistent polynomial, wrong value) fails the cut `MacCheck`.
    cur_sh[0][5][0] ^= 1 << 9;
    assert_eq!(
        cluster
            .finalize_cut_batches_spdz("spdz_cut_batch64_test", &cur_sh, &cur_mac, &[64])
            .unwrap_err(),
        Fips205Error::MpcActiveTamperDetected
    );
    assert!(cluster.vaults.iter().all(|v| v.poisoned));
}

#[test]
fn spdz_batch64_aborts_and_poisons_on_corrupted_triple_and_exhaustion() {
    let _memory = crate::test_budget::reserve_mb(1700);
    let t = 2usize;
    let pts: Vec<TowerGf256> = (1..=2u8).map(TowerGf256).collect();
    let mut dealer = SpdzTestDealer::new(b"batch64-tamper", t, &pts);
    let mut pk_seed = [0u8; 32];
    pk_seed[..16].copy_from_slice(&[0x44; 16]);
    let keys = dealer.key_shares(16, pk_seed, &[0x17; 32], &[0x18; 32]);
    let adrs = [Fips205Adrs::ZERO; 3];
    let per_batch = 24 * SPDZ_BATCH_POSITIONS;

    // A wrong product bit in a first-round triple share reaches the Beaver openings of the
    // next round, so the batched `MacCheck` inside the evaluation rejects it.
    let mut vaults = dealer.vaults(per_batch);
    vaults[1].triples[77].c[0] ^= 1 << 2;
    let mut rngs = spdz_test_rngs(2, 0x90);
    {
        let mut cluster =
            SpdzSlhMpcCluster::new([0x6a; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
        assert_eq!(
            cluster
                .eval_prf_batch64_spdz(&pk_seed[..16], &adrs)
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
    }
    assert!(vaults.iter().all(|v| v.poisoned));

    // A wrong product bit in a last-round triple share of an output position is never
    // opened inside the batch: the shares come back, and the cut `MacCheck` rejects them
    // before anything is revealed.
    let mut vaults = dealer.vaults(per_batch);
    vaults[1].triples[23 * SPDZ_BATCH_POSITIONS + 5].c[0] ^= 1 << 1;
    {
        let mut cluster =
            SpdzSlhMpcCluster::new([0x6c; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
        let (out_sh, out_mac) = cluster
            .eval_prf_batch64_spdz(&pk_seed[..16], &adrs)
            .unwrap();
        assert_eq!(
            cluster
                .finalize_cut_batches_spdz("spdz_cut_batch64_test", &out_sh, &out_mac, &[3])
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
    }
    assert!(vaults.iter().all(|v| v.poisoned));

    // Too few triples for a whole batch: abort and poison rather than a partial evaluation.
    let mut short = dealer.vaults(SPDZ_BATCH_POSITIONS);
    let mut cluster = SpdzSlhMpcCluster::new([0x6b; 32], t, &keys, &mut short, &mut rngs).unwrap();
    assert_eq!(
        cluster
            .eval_prf_batch64_spdz(&pk_seed[..16], &adrs)
            .unwrap_err(),
        Fips205Error::MpcActiveTamperDetected
    );
    assert!(cluster.vaults.iter().all(|v| v.poisoned));
}

#[test]
fn spdz_poisoned_quorum_refuses_every_later_evaluation_and_opening() {
    let _memory = crate::test_budget::reserve_mb(1100);
    let t = 2usize;
    let pts: Vec<TowerGf256> = (1..=2u8).map(TowerGf256).collect();
    let mut dealer = SpdzTestDealer::new(b"batch64-latch", t, &pts);
    let mut pk_seed = [0u8; 32];
    pk_seed[..16].copy_from_slice(&[0x55; 16]);
    let keys = dealer.key_shares(16, pk_seed, &[0x27; 32], &[0x28; 32]);
    let adrs = [Fips205Adrs::ZERO; 3];
    let mut vaults = dealer.vaults(24 * SPDZ_BATCH_POSITIONS);
    let mut rngs = spdz_test_rngs(2, 0xa0);
    {
        let mut cluster =
            SpdzSlhMpcCluster::new([0x6d; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
        let (out_sh, out_mac) = cluster
            .eval_prf_batch64_spdz(&pk_seed[..16], &adrs)
            .unwrap();
        let mut forged = out_sh.clone();
        forged[0][5][0] ^= 1 << 1;
        assert_eq!(
            cluster
                .finalize_cut_batches_spdz("spdz_latch_test", &forged, &out_mac, &[3])
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        assert!(cluster.vaults.iter().all(|v| v.poisoned));

        // Poisoning zeroed the MAC key shares, so all-zero MAC shares now satisfy the MAC
        // relation of the true cut shares. The opening must be refused all the same.
        let zero_mac: Vec<Vec<SpdzMacWord>> = out_mac
            .iter()
            .map(|words| vec![[[Tower128::ZERO; 64]; 2]; words.len()])
            .collect();
        assert_eq!(
            cluster
                .finalize_cut_batches_spdz("spdz_latch_test", &out_sh, &zero_mac, &[3])
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        assert_eq!(
            cluster
                .finalize_cut_blocks_spdz("spdz_latch_test", &[], &zero_mac, &out_sh, &zero_mac)
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        let (mut cur_sh, mut cur_mac) = (out_sh.clone(), out_mac.clone());
        for exec_mask in [0u64, 0b111] {
            assert_eq!(
                cluster
                    .eval_f_step_masked_batch64_spdz(
                        &pk_seed[..16],
                        &adrs,
                        exec_mask,
                        &mut cur_sh,
                        &mut cur_mac
                    )
                    .unwrap_err(),
                Fips205Error::MpcActiveTamperDetected
            );
        }
        assert_eq!(
            cluster
                .eval_prf_batch64_spdz(&pk_seed[..16], &adrs)
                .unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
        assert_eq!(
            cluster.eval_prf_msg_mpc(16, &[0u8; 16], b"m").unwrap_err(),
            Fips205Error::MpcActiveTamperDetected
        );
    }
    // The poisoned vaults cannot be put behind a new cluster either.
    assert!(matches!(
        SpdzSlhMpcCluster::new([0x6e; 32], t, &keys, &mut vaults, &mut rngs),
        Err(KeccakMpcError::Poisoned)
    ));
}

#[test]
fn test_spdz_key_share_profile_binding_persists_across_clusters() {
    let t = 2usize;
    let n = 3usize;
    let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
    let mut rngs = spdz_test_rngs(n, 0x91);
    let mut dealer = SpdzTestDealer::new(b"spdz-bind", t, &pts);
    let sk_seed = [0x42; 32];
    let sk_prf = [0x24; 32];
    let pk_seed = [0x11; 32];
    let keys = dealer.key_shares(16, pk_seed, &sk_seed, &sk_prf);
    let mut vaults = dealer.vaults(4);

    let p_128s = Fips205Params::SLH_DSA_SHAKE_128S;
    let p_128f = Fips205Params::SLH_DSA_SHAKE_128F;
    {
        let mut cluster =
            SpdzSlhMpcCluster::new([0x01; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
        cluster.bind_key_params(&p_128s, &pk_seed[..16]).unwrap();
        cluster.bind_key_params(&p_128s, &pk_seed[..16]).unwrap();
        assert_eq!(
            cluster.bind_key_params(&p_128f, &pk_seed[..16]),
            Err(Fips205Error::InvalidParameterSet)
        );
    }
    // Constructing a fresh cluster over the same key shares must still enforce `p_128s`.
    let mut cluster2 =
        SpdzSlhMpcCluster::new([0x02; 32], t, &keys, &mut vaults, &mut rngs).unwrap();
    assert_eq!(
        cluster2.bind_key_params(&p_128f, &pk_seed[..16]),
        Err(Fips205Error::InvalidParameterSet)
    );
    cluster2.bind_key_params(&p_128s, &pk_seed[..16]).unwrap();
}

#[test]
fn rss_key_share_256_secret_bytes_roundtrip_and_canonicality() {
    let mut rngs = [
        PartyPrivateRng::from_seed([0x11; 32], b"rss-ser-0"),
        PartyPrivateRng::from_seed([0x22; 32], b"rss-ser-1"),
        PartyPrivateRng::from_seed([0x33; 32], b"rss-ser-2"),
    ];
    let (mut shares, pk_seed) = run_dealerless_rss_dkg_2of3([0x44; 32], 32, &mut rngs).unwrap();
    let scheme_id = [0xab; 32];
    shares[0].bind_scheme_identity(&scheme_id).unwrap();

    let encoded0 = shares[0].to_secret_bytes();
    assert_eq!(encoded0.0.len(), 268);
    assert_eq!(&encoded0.0[..8], b"QSRSSK01");
    let decoded0 = RssKeyShare256::from_secret_bytes(&encoded0.0).unwrap();
    assert_eq!(decoded0.party_id, 0);
    assert_eq!(decoded0.key_len, 32);
    assert_eq!(decoded0.pk_seed, pk_seed);
    assert_eq!(decoded0.scheme_identity(), Some(&scheme_id));

    let encoded1 = shares[1].to_secret_bytes();
    let decoded1 = RssKeyShare256::from_secret_bytes(&encoded1.0).unwrap();
    assert_eq!(decoded1.scheme_identity(), None);

    // Non-zero trailing scheme_identity bytes when has_scheme_id == 0 must be rejected.
    let mut bad = encoded1.0.clone();
    bad[236] = 1;
    assert_eq!(
        RssKeyShare256::from_secret_bytes(&bad).unwrap_err(),
        KeccakMpcError::InvalidParameters
    );

    // Bad reserved byte or out-of-range party_id must be rejected.
    let mut bad_res = encoded1.0.clone();
    bad_res[11] = 1;
    assert!(RssKeyShare256::from_secret_bytes(&bad_res).is_err());
    let mut bad_party = encoded1.0.clone();
    bad_party[8] = 3;
    assert!(RssKeyShare256::from_secret_bytes(&bad_party).is_err());

    // Direct construction from replicated shares validates party_id and key_len.
    let constructed = RssKeyShare256::from_replicated_shares(
        2,
        16,
        [0x55; 32],
        ([0x01; 32], [0x02; 32]),
        ([0x03; 32], [0x04; 32]),
        ([0x05; 32], [0x06; 32]),
    )
    .unwrap();
    assert_eq!(constructed.party_id, 2);
    assert_eq!(constructed.key_len, 16);
    assert_eq!(constructed.pk_seed[16..], [0u8; 16]);
    let rt = RssKeyShare256::from_secret_bytes(&constructed.to_secret_bytes().0).unwrap();
    assert_eq!(rt.party_id, 2);
    assert_eq!(rt.key_len, 16);
    assert!(
        RssKeyShare256::from_replicated_shares(
            3,
            32,
            [0; 32],
            ([0; 32], [0; 32]),
            ([0; 32], [0; 32]),
            ([0; 32], [0; 32]),
        )
        .is_err()
    );
}
