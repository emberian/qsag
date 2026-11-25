use super::*;
use crate::zk_hem::multisig::MultisigParams;

fn bitmap(indices: &[usize]) -> [u8; IVC_BITMAP_BYTES] {
    let mut bitmap = [0; IVC_BITMAP_BYTES];
    for &i in indices {
        bitmap[i / 8] |= 1 << (i % 8);
    }
    bitmap
}
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
    assert_eq!(SuccinctIvcProof::encoded_len(), 639_673);
    let committee = MultisigParams {
        capacity: 8,
        depth: 7,
    };
    for log in [19, 20] {
        let cfg = IvcStepConfig::dkt26(log).unwrap();
        let census = cfg.row_census();
        let fits = census.total_rows() + 12 <= 1 << log
            && census.witness_variables + 1 + STEP_WORDS + 12 <= 1 << log;
        assert_eq!(
            IvcTreeStepRelation::with_config_and_committee(cfg, committee).is_some(),
            fits
        );
    }
    for cfg in [IvcStepConfig::diagnostic(19).unwrap(), tree::profile()] {
        let c = cfg.row_census();
        std::println!(
            "step log_cells={} {c:?} rows={} padded={} opening_bytes={}",
            cfg.log_cells,
            c.total_rows(),
            (c.total_rows() + 12).next_power_of_two(),
            cfg.opening_bytes()
        );
        let expected = match cfg.log_cells {
            19 => (1147, 270_692, 47_228, 323_825),
            23 => (19_679, 4_644_244, 3_010_892, 7_779_199),
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
        assert!(1 + STEP_WORDS + c.witness_variables + 12 <= 1 << cfg.log_cells);
    }
}
#[test]
#[ignore = "constructs eight Jorts shards and seven recursive steps"]
fn recursive_tree_depths() {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    use crate::zk_hem::multisig::{MultisigSigner, Policy};
    let test_cfg = IvcStepConfig::diagnostic(19).unwrap();
    let committee = MultisigParams {
        capacity: 2,
        depth: 8,
    };
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
    let registry = IvcPolicyRegistry::with_committee(committee, &policies).unwrap();
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
        total_signers: 1,
        shard_threshold: 1,
        signer_bitmap: bitmap(&[0]),
        policy_registry_root: registry.root(),
        message_digest: digest,
    };
    assert!(leaf::Witness::new(&registry, &first, &bad).is_none());
    // Bypass the prover precheck and submit the altered chain directly to the leaf shape.
    let mut witness = leaf::Witness::new(&registry, &first, &shards[0]).unwrap();
    witness.corrupt_chain();
    let mut corrupt_cs = ConstraintSystem::new();
    leaf::populate(&mut corrupt_cs, &test_cfg, &first, &witness);
    let (leaf_shape, z) = corrupt_cs.finish();
    assert!(!leaf_shape.is_satisfied(&z));
    drop((leaf_shape, z));
    let rel = IvcTreeStepRelation::with_parameters(test_cfg.clone(), committee)
        .expect("test fixed point");
    std::println!(
        "compiled step: rows={} vars={} digest={:02x?}",
        rel.shape().num_rows(),
        rel.shape().num_vars,
        rel.shape().digest()
    );
    let mut lengths = Vec::new();
    for depth in 1..=3 {
        let now = std::time::Instant::now();
        let (s, p) = rel
            .prove(&registry, digest, &shards[..1 << depth], &[depth as u8; 32])
            .expect("recursive tree proof");
        let bytes = p.to_bytes_test_only();
        let decoded = SuccinctIvcProof::from_bytes_test_only(&test_cfg, &bytes).unwrap();
        assert!(rel.verify(&s, &decoded));
        assert_eq!(bytes.len(), 26_185);
        assert_eq!(SuccinctIvcProof::encoded_len(), 639_673);
        assert!(SuccinctIvcProof::from_bytes_canonical(&bytes).is_none());
        assert!(
            SuccinctIvcProof::from_bytes_test_only(&test_cfg, &bytes[..bytes.len() - 1]).is_none()
        );
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(SuccinctIvcProof::from_bytes_test_only(&test_cfg, &trailing).is_none());
        let mut alias = bytes.clone();
        alias[9..17].copy_from_slice(&crate::field::GOLDILOCKS_PRIME.to_le_bytes());
        assert!(SuccinctIvcProof::from_bytes_test_only(&test_cfg, &alias).is_none());
        std::println!(
            "depth={depth} shards={} bytes={} verified in {:?}",
            1 << depth,
            bytes.len(),
            now.elapsed()
        );
        lengths.push(bytes.len());
        if depth == 3 {
            assert_eq!(s.total_signers, 8);
            for mut_s in 0..5 {
                let mut t = s.clone();
                match mut_s {
                    0 => t.total_signers += 1,
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
                let test_cfg = &test_cfg;
                for (i, part) in bytes.chunks(bytes.len().div_ceil(8)).enumerate() {
                    let first = i * bytes.len().div_ceil(8);
                    let mut wrong = bytes.clone();
                    scope.spawn(move || {
                        for k in first..first + part.len() {
                            for bit in 0..8 {
                                wrong[k] ^= 1 << bit;
                                assert!(
                                    !SuccinctIvcProof::from_bytes_test_only(test_cfg, &wrong)
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
                    !SuccinctIvcProof::from_bytes_test_only(&test_cfg, &changed)
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
        total_signers: total,
        shard_threshold: 0,
        signer_bitmap: [0; IVC_BITMAP_BYTES],
    };
    let parent = stmt(u64::MAX - 4, u64::MAX, 1 << 32);
    let children = [
        stmt(u64::MAX - 4, u64::MAX - 2, u32::MAX as u64),
        stmt(u64::MAX - 2, u64::MAX, 1),
    ];
    let (shape, z) = split_assignment(&parent, &children);
    assert!(shape.is_satisfied(&z));
    for case in 0..6 {
        let mut c = children.clone();
        let mut p = parent.clone();
        match case {
            0 => c[1].shard_lo += 1,
            1 => c[1].shard_lo -= 1,
            2 => c[0].shard_hi = c[0].shard_lo,
            3 => {
                c[0].total_signers = u64::MAX;
                p.total_signers = 0;
            }
            4 => c[1].policy_registry_root[5] ^= 1,
            _ => c[0].message_digest[7] ^= 1,
        }
        let (other, z) = split_assignment(&p, &c);
        assert_eq!(other.digest(), shape.digest());
        assert!(!shape.is_satisfied(&z));
    }
}

#[test]
#[ignore = "records both compiled production matrices"]
fn production_shape_matches_counter() {
    let cfg = tree::profile();
    let c = cfg.row_census();
    let rel = IvcTreeStepRelation::new().unwrap();
    let s = rel.shape();
    assert_eq!(s.num_rows(), (c.total_rows() + 12).next_power_of_two());
    assert_eq!(s.num_sbox, c.sbox_rows);
    assert_eq!(s.num_vars, c.witness_variables + 1 + STEP_WORDS + 12);
    std::println!(
        "production shape rows={} vars={} digest={:02x?}",
        s.num_rows(),
        s.num_vars,
        s.digest()
    );
}

#[test]
fn tooth_succinct_ivc_proof_rejects_nonzero_profile_tag_and_wrong_length() {
    let cfg = tree::profile();
    let blank = SuccinctIvcProof(r1cs::Argument::blank(&cfg));
    let wire = blank.to_bytes();
    assert_eq!(wire.len(), SuccinctIvcProof::encoded_len());
    assert_eq!(wire.len(), 639_673);
    assert_eq!(&wire[..9], b"QSAGIVC1\x00");
    assert_eq!(
        SuccinctIvcProof::from_bytes_canonical(&wire),
        Some(blank.clone())
    );
    assert!(SuccinctIvcProof::from_bytes_canonical(&wire[..wire.len() - 1]).is_none());
    let mut trailing = wire.clone();
    trailing.push(0);
    assert!(SuccinctIvcProof::from_bytes_canonical(&trailing).is_none());
    let cfg = IvcStepConfig::dkt26(20).unwrap();
    let compact = SuccinctIvcProof(r1cs::Argument::blank(&cfg));
    let bytes = compact.to_bytes_for_config(&cfg).unwrap();
    assert_eq!(
        SuccinctIvcProof::from_bytes_for_config(&cfg, &bytes),
        Some(compact.clone())
    );
    assert!(blank.to_bytes_for_config(&cfg).is_none());
    assert!(SuccinctIvcProof::from_bytes_canonical(&bytes).is_none());
    let diagnostic = IvcStepConfig::diagnostic(20).unwrap();
    assert!(compact.to_bytes_for_config(&diagnostic).is_none());
    assert!(SuccinctIvcProof::from_bytes_for_config(&diagnostic, &bytes).is_none());
    for tag in [1u8, 2, 0xFF] {
        let mut bad = wire.clone();
        bad[8] = tag;
        assert!(
            SuccinctIvcProof::from_bytes_canonical(&bad).is_none(),
            "SuccinctIvcProof must reject non-production tag {tag:#04x}"
        );
    }
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

#[test]
fn tooth_ivc_small_diagnostic_census_and_verify_reject_without_panic() {
    // `IvcStepConfig::diagnostic(4)` is a valid 16-cell diagnostic config,
    // yet a 38-word IVC step has 39 public-column weights (`l = 6 > ry.len() = 4`).
    // Previously `r1cs::verify` sliced beyond the challenge vector and panicked out of bounds in `row_census()`.
    let cfg = IvcStepConfig::diagnostic(4).unwrap();
    let census = cfg.row_census();
    assert!(census.total_rows() > 0);

    let blank = r1cs::Argument::blank(&cfg);
    let mut native = Native::default();
    let _ = r1cs::verify(
        &mut native,
        &cfg,
        [0; 2],
        &F::ZERO,
        &[F::ZERO; STATEMENT_WORDS],
        &blank,
    );
    assert!(
        native.failed,
        "native verifier must reject undersized log_cells=4 step"
    );

    let mut cs = ConstraintSystem::new();
    let mode = cs.public_input(F::ZERO).into();
    let stmt: Vec<_> = (0..STATEMENT_WORDS)
        .map(|_| cs.public_input(F::ZERO).into())
        .collect();
    let _ = r1cs::verify(&mut cs, &cfg, [0; 2], &mode, &stmt, &blank);
    let (shape, z) = cs.finish();
    assert!(
        !shape.is_satisfied(&z),
        "R1CS circuit must emit unsatisfiable constraint when log_cells < ceil(log2(1 + public.len()))"
    );
}

#[test]
fn tooth_leaf_canonical_u64_bits_rejects_mod_p_registry_and_message_alias() {
    // Goldilocks prime p = 2^64 - 2^32 + 1 = 0xFFFF_FFFF_0000_0001 allows
    // `alias = v + p < 2^64` for every `v in [0, 2^32 - 2]`. Without the canonical `< p`
    // (`!(hi32 == 0xFFFF_FFFF && lo32 != 0)`) constraint inside `bits_canonical_u64`, a
    // single field wire `x = f(42)` could decompose to the 64 Boolean bits of `42 + p`,
    // forging distinct 32-byte registry roots (`leaf.rs:175`) or signed message bytes (`leaf.rs:183`).
    let val_u64 = 42u64;
    let alias_u64 = val_u64 + crate::field::GOLDILOCKS_PRIME;
    assert_eq!(alias_u64, 0xFFFF_FFFF_0000_002B);
    assert_eq!(f(alias_u64), f(val_u64));

    // 1. Confirm a naive 64-bit Boolean + mod-p sum gadget WOULD accept the `42 + p` alias.
    let mut naive = ConstraintSystem::new();
    let pub_naive: crate::zk_hem::relation::Lc = naive.public_input(f(val_u64)).into();
    let zero = crate::zk_hem::relation::Lc::zero();
    let one = <ConstraintSystem as Backend>::W::constant(F::ONE);
    let mut acc = zero.clone();
    for i in 0..64 {
        let bit = <ConstraintSystem as Backend>::alloc(&mut naive, f((alias_u64 >> i) & 1));
        <ConstraintSystem as Backend>::product(&mut naive, &bit, &one.minus(&bit), &zero);
        acc = acc.plus(&bit.scaled(f(1u64 << i)));
    }
    naive.enforce_equal(&pub_naive, &acc);
    let (naive_shape, naive_z) = naive.finish();
    assert!(
        naive_shape.is_satisfied(&naive_z),
        "sanity check: unconstrained 64-bit mod-p sum accepts the v + p alias"
    );

    // 2. Confirm `bits_canonical_u64` accepts canonical `val_u64 = 42`...
    let mut cs = ConstraintSystem::new();
    let pub_x: crate::zk_hem::relation::Lc = cs.public_input(f(val_u64)).into();
    let _ = bits_canonical_u64(&mut cs, &pub_x);
    let (shape, mut z) = cs.finish();
    assert!(shape.is_satisfied(&z));
    // Layout: z[0] = 1, z[1] = pub_x, z[2..66] = 64 bit wires, z[66..97] = 31 high-AND wires,
    // z[97..109] = 12 trailing zero-knowledge blinding padding slots added by `finish()`.
    assert_eq!(z.len(), 2 + 64 + 31 + 12);

    // 3. ...and REJECTS a malicious witness substituting the 64 bits of `alias_u64 = 42 + p`
    // (even when all 31 intermediate `high` AND-chain wires are consistently set to 1).
    let mut mod_p_sum = F::ZERO;
    for i in 0..64 {
        let b_val = f((alias_u64 >> i) & 1);
        z[2 + i] = b_val;
        mod_p_sum += b_val * f(1u64 << i);
    }
    assert_eq!(mod_p_sum, z[1]);
    for slot in &mut z[66..97] {
        *slot = F::ONE;
    }
    assert!(
        !shape.is_satisfied(&z),
        "bits_canonical_u64 must reject u64 >= GOLDILOCKS_PRIME witness alias"
    );
}

#[test]
fn tooth_ivc_zero_denominator_hints_and_query_label_contract() {
    // (a) `Fp5::inv_or_zero` must be total on zero while preserving `x * inv_or_zero(x) == 1`
    //     for nonzero elements, so malformed/fuzzed openings hitting `beta == 0` or `t == x`
    //     in `verifier.rs` reject cleanly via R1CS / `Native` without panicking.
    assert_eq!(E::ZERO.inv_or_zero(), E::ZERO);
    let elem = E::X + E::from_u64(9);
    assert_eq!(elem * elem.inv_or_zero(), E::ONE);

    let mut native = Native::default();
    let zero_q_native = Quint::constant(E::ZERO);
    let hint_native = Quint::alloc(&mut native, E::ZERO.inv_or_zero());
    zero_q_native
        .mul(&mut native, &hint_native)
        .equal(&mut native, &Quint::constant(E::ONE));
    assert!(
        native.failed,
        "Native backend must flag unsatisfied zero-denominator inverse without panicking"
    );

    let mut cs = ConstraintSystem::new();
    let zero_q_cs = Quint::constant(E::ZERO);
    let hint_cs = Quint::alloc(&mut cs, E::ZERO.inv_or_zero());
    zero_q_cs
        .mul(&mut cs, &hint_cs)
        .equal(&mut cs, &Quint::constant(E::ONE));
    let (shape, z) = cs.finish();
    assert!(
        !shape.is_satisfied(&z),
        "R1CS backend must reject zero-denominator inverse without panicking"
    );

    // (b) `<Duplex<F> as Channel>::squeeze_distinct_indices` must enforce `label == b"QUERY"`.
    let mut tr = Duplex::new();
    let indices = <Duplex<F> as Channel>::squeeze_distinct_indices(&mut tr, b"QUERY", 16, 4);
    assert_eq!(indices.len(), 4);
    for (idx_pos, &v) in indices.iter().enumerate() {
        assert!(v < 16);
        assert!(!indices[..idx_pos].contains(&v));
    }
    let bad_label = std::panic::catch_unwind(|| {
        let mut tr_bad = Duplex::new();
        let _ = <Duplex<F> as Channel>::squeeze_distinct_indices(&mut tr_bad, b"NOT_QUERY", 16, 2);
    });
    assert!(
        bad_label.is_err(),
        "Duplex::squeeze_distinct_indices must reject non-QUERY labels rather than silently ignoring them"
    );
}

fn split_assignment(
    parent: &IvcSubtreeStatement,
    children: &[IvcSubtreeStatement; 2],
) -> (crate::zk_hem::relation::Shape, Vec<F>) {
    let mut cs = ConstraintSystem::new();
    let public = parent.public_inputs().map(|v| cs.public_input(v).into());
    for x in public[..15].iter().chain(&public[23..]) {
        bits(&mut cs, x, 32);
    }
    tree::split(&mut cs, &public, children);
    cs.finish()
}

fn gossip_proof(
    rel: &IvcTreeStepRelation,
    threshold: u32,
    groups: [&[usize]; 2],
) -> (IvcSubtreeStatement, SuccinctIvcProof) {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    use crate::zk_hem::multisig::{MultisigSigner, Policy};
    let count = 1 << rel.committee().depth;
    let mut keys: Vec<_> = (0..count)
        .map(|i| {
            ValidatorKeypair::keygen_deterministic(
                AggSigProfile::JortsPoseidon2,
                &[67; 32],
                i as u32,
            )
        })
        .collect();
    let committee = rel.committee();
    let policy = Policy::new(
        keys.iter().map(|k| k.pk).collect(),
        threshold,
        committee.depth,
    )
    .unwrap();
    let registry = IvcPolicyRegistry::with_committee(committee, &[(0, policy.clone())]).unwrap();
    let digest = [83; 32];
    let message = ivc_signing_message(registry.root(), 0, digest);
    let mut signatures = alloc::collections::BTreeMap::new();
    for &i in groups.iter().flat_map(|v| v.iter()) {
        signatures.entry(i).or_insert_with(|| MultisigSigner {
            member_index: i,
            signature: keys[i].sign_stateful_for_unit_test(&message, 0).unwrap(),
        });
    }
    let sets = groups.map(|ids| {
        ids.iter()
            .map(|i| signatures[i].clone())
            .collect::<Vec<_>>()
    });
    let shards = sets.each_ref().map(|signers| IvcShard {
        shard_id: 0,
        policy: &policy,
        signers,
    });
    rel.prove(&registry, digest, &shards, &[57; 32]).unwrap()
}

#[test]
fn dkt26_overlapping_gossip_tree() {
    // Both full WHIR verifiers must also fit the table. Their row census
    // exceeds the smaller leaf-only geometries.
    let cfg = IvcStepConfig::dkt26(23).unwrap();
    let rel = IvcTreeStepRelation::with_config_and_committee(
        cfg.clone(),
        MultisigParams {
            capacity: 8,
            depth: 7,
        },
    )
    .unwrap();
    let (stmt, proof) = gossip_proof(&rel, 6, [&[0, 2, 5, 7], &[2, 5, 9, 12]]);
    assert_eq!(stmt.signer_bitmap, bitmap(&[0, 2, 5, 7, 9, 12]));
    assert_eq!((stmt.total_signers, stmt.shard_threshold), (6, 6));
    let bytes = proof.to_bytes_for_config(rel.config()).unwrap();
    assert_eq!(bytes.len(), 639_673);
    let decoded = SuccinctIvcProof::from_bytes_for_config(&cfg, &bytes).unwrap();
    assert!(rel.verify(&stmt, &decoded));
}

#[test]
fn tooth_overlapping_bitmap_merge_cannot_inflate_quorum_weight() {
    let cfg = IvcStepConfig::diagnostic(19).unwrap();
    let rel = IvcTreeStepRelation::with_parameters(
        cfg,
        MultisigParams {
            capacity: 1,
            depth: 1,
        },
    )
    .unwrap();
    let (stmt, proof) = gossip_proof(&rel, 2, [&[0], &[0]]);
    assert_eq!(stmt.signer_bitmap, bitmap(&[0]));
    assert_eq!((stmt.total_signers, stmt.shard_threshold), (1, 2));
    assert!(rel.verify_partial(&stmt, &proof));
    assert!(!rel.verify(&stmt, &proof));
    assert!(!verify_ivc_tree(&stmt, &proof));
    let children = [stmt.clone(), stmt.clone()];
    let mut inflated = stmt;
    inflated.total_signers = 2;
    assert!(!rel.verify_partial(&inflated, &proof));
    assert!(!rel.verify(&inflated, &proof));
    let (shape, z) = split_assignment(&inflated, &children);
    assert!(!shape.is_satisfied(&z));
}

#[test]
fn tooth_cross_shard_merge_rejects_under_threshold_single_shard() {
    let first = IvcSubtreeStatement {
        policy_registry_root: [3; 32],
        shard_lo: u32::MAX as u64,
        shard_hi: 1 << 32,
        total_signers: 2,
        shard_threshold: 2,
        signer_bitmap: bitmap(&[0, 255]),
        message_digest: [8; 32],
    };
    let second = IvcSubtreeStatement {
        shard_lo: first.shard_hi,
        shard_hi: first.shard_hi + 1,
        ..first.clone()
    };
    let mut parent = IvcSubtreeStatement::merge(&first, &second).unwrap();
    let mut children = [first, second];
    let (shape, assignment) = split_assignment(&parent, &children);
    assert!(shape.is_satisfied(&assignment));
    children[0].signer_bitmap = bitmap(&[0]);
    children[0].total_signers = 1;
    parent.total_signers = 3;
    assert!(IvcSubtreeStatement::merge(&children[0], &children[1]).is_none());
    let (_, assignment) = split_assignment(&parent, &children);
    assert!(!shape.is_satisfied(&assignment));
}

#[test]
fn production_leaf_committee_fits() {
    const {
        assert!(IvcPolicyRegistry::MAX_SIGNERS_PER_SHARD >= 64);
    }
    let cfg = tree::profile();
    for capacity in [leaf::COMMITTEE.capacity, 128] {
        let committee = MultisigParams { capacity, depth: 8 };
        let mut cs = ConstraintSystem::new();
        leaf::populate(
            &mut cs,
            &cfg,
            &IvcSubtreeStatement::blank(),
            &leaf::Witness::blank(committee),
        );
        let rows = cs.num_rows();
        let (shape, _) = cs.finish();
        std::println!(
            "capacity={capacity} rows={rows} padded={} vars={}",
            shape.num_rows(),
            shape.num_vars
        );
        assert!(shape.num_rows() <= 1 << cfg.log_cells() && shape.num_vars <= 1 << cfg.log_cells());
    }
}

#[test]
fn leaf_binds_bitmap_positions_and_policy_threshold() {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    use crate::zk_hem::multisig::{MultisigSigner, Policy};
    let committee = MultisigParams {
        capacity: 1,
        depth: 1,
    };
    let mut signer =
        ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[42; 32], 1);
    let other = ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[42; 32], 0);
    let policy = Policy::new(vec![other.pk, signer.pk], 2, 1).unwrap();
    let registry = IvcPolicyRegistry::with_committee(committee, &[(7, policy.clone())]).unwrap();
    let mut stmt = IvcSubtreeStatement {
        policy_registry_root: registry.root(),
        message_digest: [7; 32],
        shard_lo: 7,
        shard_hi: 8,
        total_signers: 1,
        shard_threshold: 2,
        signer_bitmap: bitmap(&[1]),
    };
    let message = ivc_signing_message(registry.root(), 7, stmt.message_digest);
    let signers = [MultisigSigner {
        member_index: 1,
        signature: signer.sign_stateful_for_unit_test(&message, 0).unwrap(),
    }];
    let witness = leaf::Witness::new(
        &registry,
        &stmt,
        &IvcShard {
            shard_id: 7,
            policy: &policy,
            signers: &signers,
        },
    )
    .unwrap();
    let cfg = IvcStepConfig::dkt26(19).unwrap();
    let mut cs = ConstraintSystem::new();
    leaf::populate(&mut cs, &cfg, &stmt, &witness);
    let (shape, assignment) = cs.finish();
    assert!(shape.is_satisfied(&assignment));
    for (bitmap, count, threshold) in [
        (bitmap(&[0]), 1, 2),
        (bitmap(&[1, 2]), 2, 2),
        (bitmap(&[1]), 1, 1),
    ] {
        stmt.signer_bitmap = bitmap;
        stmt.total_signers = count;
        stmt.shard_threshold = threshold;
        let mut cs = ConstraintSystem::witness_only();
        leaf::populate(&mut cs, &cfg, &stmt, &witness);
        let assignment = cs.finish_assignment(&shape).unwrap();
        assert!(!shape.is_satisfied(&assignment));
    }
}

#[test]
fn contiguous_shards_with_uneven_gossip_runs() {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    use crate::zk_hem::multisig::{MultisigSigner, Policy};
    let committee = MultisigParams {
        capacity: 1,
        depth: 1,
    };
    let cfg = IvcStepConfig::diagnostic(19).unwrap();
    let relation = IvcTreeStepRelation::with_parameters(cfg, committee).unwrap();
    let mut key =
        ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[92; 32], 0);
    let policy = Policy::new(vec![key.pk], 1, committee.depth).unwrap();
    let registry =
        IvcPolicyRegistry::with_committee(committee, &[(0, policy.clone()), (1, policy.clone())])
            .unwrap();
    let digest = [18; 32];
    let signatures = [0, 1].map(|id| {
        let message = ivc_signing_message(registry.root(), id, digest);
        [MultisigSigner {
            member_index: 0,
            signature: key
                .sign_stateful_for_unit_test(&message, id as u32)
                .unwrap(),
        }]
    });
    let leaves = [0, 0, 1].map(|shard_id| IvcShard {
        shard_id,
        policy: &policy,
        signers: &signatures[shard_id as usize],
    });
    let (stmt, proof) = relation
        .prove(&registry, digest, &leaves, &[52; 32])
        .unwrap();
    assert_eq!(
        (stmt.shard_lo, stmt.shard_hi, stmt.total_signers),
        (0, 2, 2)
    );
    assert_eq!(stmt.shard_threshold, 0);
    assert_eq!(stmt.signer_bitmap, bitmap(&[]));
    assert!(relation.verify(&stmt, &proof));
}

#[test]
#[cfg(feature = "vulkan")]
#[ignore = "requires an audited Vulkan device and the production step relation"]
fn vulkan_wire_parity_ivc1() {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    use crate::zk_hem::multisig::{MultisigSigner, Policy};
    let backend = qsag_accel::VulkanSpirvBackend::try_new_audited().unwrap();
    let session = backend.fp5_session().unwrap();
    let mut keys: [_; 2] = core::array::from_fn(|i| {
        ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[41; 32], i as u32)
    });
    let policies: Vec<_> = keys
        .iter()
        .enumerate()
        .map(|(i, k)| {
            (
                i as u64,
                Policy::new(vec![k.pk], 1, leaf::COMMITTEE.depth).unwrap(),
            )
        })
        .collect();
    let registry = IvcPolicyRegistry::new(&policies).unwrap();
    let digest = [145; 32];
    let signers: Vec<_> = keys
        .iter_mut()
        .enumerate()
        .map(|(i, k)| {
            [MultisigSigner {
                member_index: 0,
                signature: k
                    .sign_stateful_for_unit_test(
                        &ivc_signing_message(registry.root(), i as u64, digest),
                        0,
                    )
                    .unwrap(),
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
    let rel = IvcTreeStepRelation::new().unwrap();
    std::println!("Canonical IVC relation ready");
    let start = std::time::Instant::now();
    let (s, gpu) = rel
        .prove_with_vulkan(&session, &registry, digest, &shards, &[1; 32])
        .unwrap();
    let gpu_time = start.elapsed();
    std::println!("GPU root proof complete in {gpu_time:?}");
    assert!(rel.verify(&s, &gpu));
    let start = std::time::Instant::now();
    let (cs, cpu) = rel.prove(&registry, digest, &shards, &[1; 32]).unwrap();
    let cpu_time = start.elapsed();
    assert_eq!(cs, s);
    assert!(cpu.to_bytes() == gpu.to_bytes());
    assert_eq!(gpu.to_bytes().len(), 639673);
    assert!(backend.gpu_submission_count() > 0);
    assert_eq!(backend.cpu_fallback_count(), 0);
    std::println!("QSAGIVC1 639673 bytes, CPU {cpu_time:?}, GPU {gpu_time:?}");
}
