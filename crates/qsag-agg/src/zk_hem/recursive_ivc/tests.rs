use super::*;
use crate::zk_hem::relation::ConstraintSystem;
#[test]
fn quintic_and_permutation_match_native() {
    let mut cs = ConstraintSystem::new();
    let a = E(core::array::from_fn(|i| f((i + 3) as u64)));
    let d = E(core::array::from_fn(|i| f((i + 67) as u64)));
    let x = Quint::alloc(&mut cs, a);
    let y = Quint::alloc(&mut cs, d);
    let product = x.mul(&mut cs, &y);
    assert_eq!(E(product.0.map(|v| cs.eval(&v))), a * d);
    let mut st = core::array::from_fn(|i| f(i as u64 * 71));
    let mut state = st.map(|x| Backend::alloc(&mut cs, x));
    cs.perm_w24(&mut state);
    let mut quadratic = ConstraintSystem::new();
    let mut qc = st.map(|v| Backend::alloc(&mut quadratic, v));
    crate::zk_hem::relation::poseidon2_gl24_perm_quadratic(&mut quadratic, &mut qc);
    Native::default().perm_w24(&mut st);
    assert_eq!(quadratic.num_rows(), 944);
    assert_eq!(qc.map(|x| quadratic.eval(&x)), st);
    let (shape, z) = quadratic.finish();
    assert!(shape.is_satisfied(&z));
    assert_eq!(st, state.map(|v| cs.eval(&v)));
    let (shape, z) = cs.finish();
    assert!(shape.is_satisfied(&z));
}
#[test]
fn quintic_opening_and_wire() {
    let cfg = IvcStepConfig::diagnostic(5).unwrap();
    let ctx = [f(11), f(12)];
    let p: Vec<_> = (0..5).map(|i| E::X + E::from_u64(7 + i)).collect();
    let table: Vec<_> = (0..32).map(|i| f(7 + i * i)).collect();
    let st = IvcTableCommitment::commit(&cfg, &table, &[33; 32]).unwrap();
    let (value, proof) = st.open(&ctx, &p).unwrap();
    assert!(proof.verify(&cfg, &ctx, st.nonce(), st.root(), &p, value));
    assert!(!proof.verify(&cfg, &ctx, st.nonce(), st.root(), &p, value + E::ONE));
    let wire = proof.to_bytes();
    assert_eq!(wire.len(), cfg.opening_bytes());
    assert_eq!(
        Some(proof.clone()),
        FixedPathWhirW24::from_bytes_canonical(&cfg, &wire)
    );
    for pos in [0, 8, 128, wire.len() / 2, wire.len() - 1] {
        let mut bad = wire.clone();
        bad[pos] ^= 1;
        assert!(
            !FixedPathWhirW24::from_bytes_canonical(&cfg, &bad).is_some_and(|op| op.verify(
                &cfg,
                &ctx,
                st.nonce(),
                st.root(),
                &p,
                value
            ))
        );
    }
    let mut cs = ConstraintSystem::new();
    let public = ctx.map(|x| cs.public_input(x).into());
    let nonce = st.nonce().map(|x| cs.public_input(x).into());
    let root = st.root().map(|x| cs.public_input(x).into());
    let p = p
        .iter()
        .map(|x| Quint(x.0.map(|v| cs.public_input(v).into())))
        .collect::<Vec<_>>();
    let val = Quint(value.0.map(|x| cs.public_input(x).into()));
    verifier::check(&mut cs, &cfg, &public, &nonce, &root, &p, &val, &proof);
    assert_eq!(
        cs.num_rows(),
        cfg.opening_row_census(ctx.len()).total_rows()
    );
    let (shape, z) = cs.finish();
    assert!(shape.is_satisfied(&z));
}
#[test]
fn dkt26_opening_census() {
    let cfg = IvcStepConfig::dkt26(20).unwrap();
    let c = cfg.opening_row_census(22);
    std::println!(
        "log_cells=20 context_words=22 census={c:?} rows={} bytes={}",
        c.total_rows(),
        cfg.opening_bytes()
    );
}
#[test]
fn two_child_step_census() {
    for cfg in [tree::profile::<true>(), tree::profile::<false>()] {
        let c = cfg.row_census();
        std::println!(
            "step log_cells={} {c:?} rows={} padded={} opening_bytes={}",
            cfg.log_cells,
            c.total_rows(),
            (c.total_rows() + 12).next_power_of_two(),
            cfg.opening_bytes()
        );
        let expected = match cfg.log_cells {
            19 => (1145, 270_220, 44_918, 321_325),
            23 => (19_677, 4_643_772, 3_008_582, 7_776_699),
            _ => unreachable!(),
        };
        assert_eq!(
            (
                c.permutations,
                c.sbox_rows,
                c.multiplication_rows,
                c.witness_variables
            ),
            expected
        );
        assert!(c.total_rows() + 12 <= 1 << cfg.log_cells);
        assert!(1 + 29 + c.witness_variables + 12 <= 1 << cfg.log_cells);
    }
}
#[test]
#[ignore = "constructs eight Jorts shards and seven production-code recursive steps"]
fn recursive_tree_depths() {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    use crate::zk_hem::multisig::{MultisigSigner, Policy};
    let mut keys: Vec<_> = (0..8)
        .map(|i| {
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[41; 32], i)
        })
        .collect();
    let policies: Vec<_> = keys
        .iter()
        .enumerate()
        .map(|(i, key)| {
            (
                i as u64,
                Policy::new(vec![key.pk], 1, leaf::COMMITTEE.depth).unwrap(),
            )
        })
        .collect();
    let registry = IvcPolicyRegistry::new(&policies).unwrap();
    let digest = [145; 32];
    let signers: Vec<_> = keys
        .iter_mut()
        .enumerate()
        .map(|(i, key)| {
            let msg = ivc_signing_message(registry.root(), i as u64, digest);
            vec![MultisigSigner {
                member_index: 0,
                signature: key.sign_stateful_for_unit_test(&msg, 0).unwrap(),
            }]
        })
        .collect();
    let shards: Vec<_> = policies
        .iter()
        .zip(&signers)
        .map(|((i, p), s)| IvcShard {
            shard_id: *i,
            policy: p,
            signers: s,
        })
        .collect();
    let mut signature = signers[0].clone();
    signature[0].signature.layers[0].wots_chains[0][0] += F::ONE;
    let bad = IvcShard {
        shard_id: 0,
        policy: &policies[0].1,
        signers: &signature,
    };
    let first = IvcSubtreeStatement {
        shard_lo: 0,
        shard_hi: 1,
        total_quorums: 1,
        policy_registry_root: registry.root(),
        message_digest: digest,
    };
    assert!(leaf::Witness::new(&registry, &first, &bad).is_none());
    // Bypass the prover precheck and submit the altered chain directly to the leaf shape.
    let mut witness = leaf::Witness::new(&registry, &first, &shards[0]).unwrap();
    witness.corrupt_chain();
    let mut corrupt_cs = ConstraintSystem::new();
    leaf::populate(&mut corrupt_cs, &tree::profile::<true>(), &first, &witness);
    let (leaf_shape, z) = corrupt_cs.finish();
    assert!(!leaf_shape.is_satisfied(&z));
    drop((leaf_shape, z));
    let rel = IvcTreeStepRelation::<true>::new().expect("diagnostic fixed point");
    std::println!(
        "compiled step: rows={} vars={} digest={:02x?}",
        rel.shape().num_rows(),
        rel.shape().num_vars,
        rel.shape().digest()
    );
    let mut lengths = Vec::new();
    for depth in 1..=3 {
        let now = std::time::Instant::now();
        let (s, p) =
            prove_ivc_tree::<true>(&registry, digest, &shards[..1 << depth], &[depth as u8; 32])
                .expect("recursive tree proof");
        let bytes = p.to_bytes();
        let decoded = SuccinctIvcProof::<true>::from_bytes_canonical(&bytes).unwrap();
        assert!(verify_ivc_tree(&s, &decoded));
        assert_eq!(bytes.len(), SuccinctIvcProof::<true>::encoded_len());
        assert_eq!(bytes.len(), 26_185);
        assert_eq!(SuccinctIvcProof::<false>::encoded_len(), 639_673);
        assert!(SuccinctIvcProof::<false>::from_bytes_canonical(&bytes).is_none());
        assert!(
            SuccinctIvcProof::<true>::from_bytes_canonical(&bytes[..bytes.len() - 1]).is_none()
        );
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(SuccinctIvcProof::<true>::from_bytes_canonical(&trailing).is_none());
        let mut alias = bytes.clone();
        alias[9..17].copy_from_slice(&crate::field::GOLDILOCKS_PRIME.to_le_bytes());
        assert!(SuccinctIvcProof::<true>::from_bytes_canonical(&alias).is_none());
        std::println!(
            "depth={depth} shards={} bytes={} verified in {:?}",
            1 << depth,
            bytes.len(),
            now.elapsed()
        );
        lengths.push(bytes.len());
        if depth == 3 {
            assert_eq!(s.total_quorums, 8);
            for mut_s in 0..5 {
                let mut t = s.clone();
                match mut_s {
                    0 => t.total_quorums += 1,
                    1 => t.message_digest[0] ^= 1,
                    2 => t.policy_registry_root[0] ^= 1,
                    3 => t.shard_lo += 1,
                    _ => t.shard_hi -= 1,
                }
                assert!(!rel.verify(&t, &decoded));
            }
            // Exercise every bit of the serialized proof through canonical decoding
            // and the root verifier. A malformed wire can fail at either boundary.
            std::thread::scope(|scope| {
                let rel = &rel;
                let s = &s;
                for (i, part) in bytes.chunks(bytes.len().div_ceil(8)).enumerate() {
                    let first = i * bytes.len().div_ceil(8);
                    let mut wrong = bytes.clone();
                    scope.spawn(move || {
                        for k in first..first + part.len() {
                            for bit in 0..8 {
                                wrong[k] ^= 1 << bit;
                                assert!(
                                    !SuccinctIvcProof::<true>::from_bytes_canonical(&wrong)
                                        .is_some_and(|q| rel.verify(s, &q)),
                                    "byte {k}, bit {bit}"
                                );
                                wrong[k] ^= 1 << bit;
                            }
                        }
                    });
                }
            });
            for start in (9..bytes.len()).step_by(8) {
                let mut changed = bytes.clone();
                let word = u64::from_le_bytes(changed[start..start + 8].try_into().unwrap());
                changed[start..start + 8]
                    .copy_from_slice(&f(word).plus(&f(0x1000100010001)).to_le_bytes());
                assert!(
                    !SuccinctIvcProof::<true>::from_bytes_canonical(&changed)
                        .is_some_and(|q| rel.verify(&s, &q))
                );
            }
            std::println!("rejected all {} single-bit mutations", 8 * bytes.len());
        }
    }
    assert!(lengths.windows(2).all(|w| w[0] == w[1]));
}

#[test]
fn partition_constraints_reject_gaps_overlap_and_overflow() {
    let stmt = |lo, hi, total| IvcSubtreeStatement {
        policy_registry_root: [33; 32],
        message_digest: [77; 32],
        shard_lo: lo,
        shard_hi: hi,
        total_quorums: total,
    };
    let parent = stmt(u64::MAX - 4, u64::MAX, 1 << 32);
    let children = [
        stmt(u64::MAX - 4, u64::MAX - 2, u32::MAX as u64),
        stmt(u64::MAX - 2, u64::MAX, 1),
    ];
    let synthesize = |p: &IvcSubtreeStatement, c: &[IvcSubtreeStatement; 2]| {
        let mut cs = ConstraintSystem::new();
        let public = p.public_inputs().map(|v| cs.public_input(v).into());
        for x in &public {
            bits(&mut cs, x, 32);
        }
        tree::split(&mut cs, &public, c);
        cs.finish()
    };
    let (shape, z) = synthesize(&parent, &children);
    assert!(shape.is_satisfied(&z));
    for case in 0..6 {
        let mut c = children.clone();
        let mut p = parent.clone();
        match case {
            0 => c[1].shard_lo += 1,
            1 => c[1].shard_lo -= 1,
            2 => c[0].shard_hi = c[0].shard_lo,
            3 => {
                c[0].total_quorums = u64::MAX;
                p.total_quorums = 0;
            }
            4 => c[1].policy_registry_root[5] ^= 1,
            _ => c[0].message_digest[7] ^= 1,
        }
        let (other, z) = synthesize(&p, &c);
        assert_eq!(other.digest(), shape.digest());
        assert!(!shape.is_satisfied(&z));
    }
}

#[test]
#[ignore = "records both compiled production matrices"]
fn production_shape_matches_counter() {
    let cfg = tree::profile::<false>();
    let c = cfg.row_census();
    let rel = IvcTreeStepRelation::<false>::new().unwrap();
    let s = rel.shape();
    assert_eq!(s.num_rows(), (c.total_rows() + 12).next_power_of_two());
    assert_eq!(s.num_sbox, c.sbox_rows);
    assert_eq!(s.num_vars, c.witness_variables + 42);
    std::println!(
        "production shape rows={} vars={} digest={:02x?}",
        s.num_rows(),
        s.num_vars,
        s.digest()
    );
}

#[test]
fn shuffled_queries_and_octopus_match_recorded_shape() {
    let cfg = IvcStepConfig {
        log_cells: 9,
        schedule: Schedule {
            early_stop_vars: 2,
            stages: vec![
                StageSpec {
                    blowup: 4,
                    step_vars: 3,
                    num_queries: 31,
                },
                StageSpec {
                    blowup: 8,
                    step_vars: 4,
                    num_queries: 17,
                },
            ],
        },
    };
    let table: Vec<_> = (0..512).map(|i| f(i * i + 3)).collect();
    let committed = IvcTableCommitment::commit(&cfg, &table, &[7; 32]).unwrap();
    let mut reference = None;
    for k in [3, 13] {
        let point: Vec<_> = (0..9).map(|i| E::X + E::from_u64(k + i)).collect();
        let (value, p) = committed.open(&[], &point).unwrap();
        assert!(p.verify(
            &cfg,
            &[],
            committed.nonce(),
            committed.root(),
            &point,
            value
        ));
        let mut cs = ConstraintSystem::new();
        let root = committed.root().map(|v| cs.public_input(v).into());
        let nonce = committed.nonce().map(|v| cs.public_input(v).into());
        let point: Vec<_> = point
            .iter()
            .map(|q| Quint(q.0.map(|v| cs.public_input(v).into())))
            .collect();
        let val = Quint(value.0.map(|v| cs.public_input(v).into()));
        verifier::check(&mut cs, &cfg, &[], &nonce, &root, &point, &val, &p);
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        if let Some(digest) = reference {
            assert_eq!(shape.digest(), digest);
        }
        reference = Some(shape.digest());
    }
}

#[test]
#[ignore = "executes all WHIR rounds and fibers at the smallest DKT26 geometry"]
fn dkt26_real_opening() {
    let cfg = IvcStepConfig::dkt26(16).unwrap();
    let table: Vec<_> = (0..1 << 16).map(|i| f(i * i + 17)).collect();
    let commitment = IvcTableCommitment::commit(&cfg, &table, &[31; 32]).unwrap();
    let point: Vec<_> = (0..16).map(|i| E::X + E::from_u64(17 + i)).collect();
    let (value, p) = commitment.open(&[f(123)], &point).unwrap();
    assert!(p.verify(
        &cfg,
        &[f(123)],
        commitment.nonce(),
        commitment.root(),
        &point,
        value
    ));
    assert!(!p.verify(
        &cfg,
        &[f(122)],
        commitment.nonce(),
        commitment.root(),
        &point,
        value
    ));
}
