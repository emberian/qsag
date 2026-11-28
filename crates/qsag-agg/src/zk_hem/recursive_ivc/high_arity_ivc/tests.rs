use super::*;

#[test]
fn high_arity_geometry() {
    let mut cs = ConstraintSystem::with_row_templates();
    populate(
        &mut cs,
        &IvcSubtreeStatement::blank(),
        &leaf::Witness::blank(COMMITTEE),
    );
    let used = cs.num_rows();
    let (s, _) = cs.finish();
    let profile = Profile::TurboShakeJohnson400;
    let g = Geometry::new(profile, &s, 256).unwrap();
    assert_eq!(
        (used, s.num_rows(), s.num_vars, s.num_sbox),
        (79432, 131072, 80406, 73632)
    );
    assert_eq!((g.columns, g.log, g.stripes), (17, 24, 2));
    let max = Geometry::new(profile, &s, 131072).unwrap();
    assert_eq!((max.instances, max.stripes), (17, 1024));
    for count in [0, 131073] {
        assert_eq!(Geometry::new(profile, &s, count).err(), Some(InvalidBatch));
    }
}

#[test]
fn high_arity_signed_batch_and_rejections() {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    use crate::zk_hem::multisig::{MultisigSigner, Policy};
    let mut keys: Vec<_> = (0..3)
        .map(|i| {
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[62; 32], i)
        })
        .collect();
    let id = u32::MAX as u64;
    let policies = [
        (id, Policy::new(vec![keys[0].pk, keys[1].pk], 2, 8).unwrap()),
        (id + 1, Policy::new(vec![keys[2].pk], 1, 8).unwrap()),
    ];
    let registry = IvcPolicyRegistry::new(&policies).unwrap();
    let msg = [53; 32];
    let mut signed = Vec::new();
    for (i, k) in keys.iter_mut().enumerate() {
        let shard = id + u64::from(i == 2);
        signed.push(MultisigSigner {
            member_index: usize::from(i == 1),
            signature: k
                .sign_stateful_for_unit_test(&ivc_signing_message(registry.root(), shard, msg), 0)
                .unwrap(),
        });
    }
    let groups = [
        IvcShard {
            shard_id: id,
            policy: &policies[0].1,
            signers: &signed[..1],
        },
        IvcShard {
            shard_id: id,
            policy: &policies[0].1,
            signers: &signed[..2],
        },
        IvcShard {
            shard_id: id + 1,
            policy: &policies[1].1,
            signers: &signed[2..],
        },
    ];
    let profile = Profile::TurboShakeJohnson400;
    let rejected = |groups: &[IvcShard<'_>]| {
        prove_high_arity_tree(&registry, msg, groups, profile, &[4; 32]).err()
    };
    assert_eq!(rejected(&groups[..1]), Some(InvalidBatch));
    let partial = IvcShard {
        shard_id: id,
        policy: &policies[0].1,
        signers: &signed[..2],
    };
    let gap = IvcShard {
        shard_id: id + 2,
        policy: &policies[1].1,
        signers: &signed[2..],
    };
    assert_eq!(rejected(&[partial, gap]), Some(InvalidBatch));
    let (same, same_proof) =
        prove_high_arity_tree(&registry, msg, &groups[..2], profile, &[18; 32]).unwrap();
    assert_eq!(
        (
            same.total_signers,
            same.shard_threshold,
            same.signer_bitmap[0]
        ),
        (2, 2, 3)
    );
    assert!(verify_high_arity_tree(&same, &same_proof));
    let mut corrupt = signed[..2].to_vec();
    corrupt[1].signature.r_rand[0] += F::ONE;
    let invalid = IvcShard {
        shard_id: id,
        policy: &policies[0].1,
        signers: &corrupt,
    };
    assert_eq!(rejected(&[invalid]), Some(InvalidBatch));
    for profile in Profile::ALL {
        if profile.rate_half() {
            // Wire tags 18 and 19 have no `QSAGIVC2` schedule or oracle-call account.
            assert_eq!(
                prove_high_arity_tree(&registry, msg, &groups, profile, &[4; 32]).err(),
                Some(UnsupportedProfile)
            );
            continue;
        }
        let (s, p) = prove_high_arity_tree(&registry, msg, &groups, profile, &[4; 32]).unwrap();
        assert_eq!((s.shard_lo, s.shard_hi, s.total_signers), (id, id + 2, 3));
        let bytes = p.to_bytes();
        std::println!("three signer proof {profile:?} bytes={}", bytes.len());
        let decoded = HighArityProof::from_bytes(&bytes).unwrap();
        assert_eq!(bytes, decoded.to_bytes());
        assert!(verify_high_arity_tree(&s, &decoded));
        let mut changed = s.clone();
        changed.total_signers += 1;
        assert!(!verify_high_arity_tree(&changed, &p));
        let mut changed = s.clone();
        changed.message_digest[0] ^= 1;
        assert!(!verify_high_arity_tree(&changed, &p));
        let mut bad = p.clone();
        // Same public interval and total. The threshold and the actual signer
        // position must still agree with the committed private assignments.
        bad.roster[0].threshold = 1;
        assert_eq!(
            aggregate(&bad.roster, registry.root(), msg),
            Some(s.clone())
        );
        assert!(!verify_high_arity_tree(&s, &bad));
        let mut bad = p.clone();
        bad.roster[1].bitmap[0] = 2;
        assert!(!verify_high_arity_tree(&s, &bad));
        let mut bad = p.clone();
        bad.roster[1].id += 1;
        assert!(!verify_high_arity_tree(&s, &bad));
        assert!(HighArityProof::from_bytes(&bad.to_bytes()).is_none());
        let mut bad = p.clone();
        bad.fold.abc[1] += E::ONE;
        assert!(!verify_high_arity_tree(&s, &bad));
        for phase in 0..6 {
            let mut bad = p.clone();
            let round = &mut (match phase {
                0 => &mut bad.row,
                1 => &mut bad.fold.product,
                2 => &mut bad.fold.powers,
                3 => &mut bad.fold.square,
                4 => &mut bad.fold.reduce,
                _ => &mut bad.col,
            })[0];
            // Adding X(1-X) preserves both endpoints of this round.
            round[1] += E::ONE;
            round[2] -= E::ONE;
            assert!(!verify_high_arity_tree(&s, &bad));
        }
        let mut bad = p.clone();
        bad.z += E::ONE;
        assert!(!verify_high_arity_tree(&s, &bad));
        let mut bad = p.clone();
        bad.root[0] ^= 128;
        assert!(!verify_high_arity_tree(&s, &bad));
        let mut bad = p.clone();
        bad.opening.stage0_query.leaves[0].salt[0] ^= 1;
        assert!(!verify_high_arity_tree(&s, &bad));
        assert!(HighArityProof::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(HighArityProof::from_bytes(&extra).is_none());
        for tag in [0, 18, 19] {
            let mut bad = bytes.clone();
            bad[8] = tag;
            assert!(HighArityProof::from_bytes(&bad).is_none());
        }
        // A relabelled proof cannot reach the Johnson schedule through the verifier.
        let mut bad = p.clone();
        bad.profile = Profile::from_wire_tag(profile.wire_tag() + 2).unwrap();
        assert!(bad.profile.rate_half() && !verify_high_arity_tree(&s, &bad));
        let mut bad = bytes.clone();
        bad[9..13].fill(255);
        assert!(HighArityProof::from_bytes(&bad).is_none());
        let mut bad = bytes.clone();
        let first_field = 9 + wire::roster_bytes(&p.roster).len() + 32 + params::DIGEST_BYTES;
        bad[first_field..first_field + 8]
            .copy_from_slice(&crate::field::GOLDILOCKS_PRIME.to_le_bytes());
        assert!(HighArityProof::from_bytes(&bad).is_none());
        assert!(SuccinctIvcProof::from_bytes_canonical(&bytes).is_none());
    }
}

#[test]
fn high_arity_interleaved_opening() {
    let profile = Profile::TurboShakeJohnson400;
    let log = 16;
    let schedule = params::schedule(log).unwrap();
    let mut rng = SeedStream::new(b"IVC2-test-table", &[22; 32]);
    let mut table = vec![F::ZERO; 4 << log];
    rng.fill_base(&mut table);
    let mask = (0..pcs::mask_len(log, schedule.stages[0].step_vars))
        .map(|_| rng.next_fp5())
        .collect();
    let nonce = rng.next_bytes32();
    let c = pcs::interleave::Interleaved::commit(
        profile,
        log,
        &schedule,
        &table,
        mask,
        nonce,
        rng.next_bytes32(),
    )
    .unwrap();
    let mut tr = Transcript::new(profile, &[MAGIC, &nonce, &c.root()]);
    let point: Vec<_> = (0..log).map(|_| tr.squeeze_fp5(b"POINT")).collect();
    let weights = protocol::eq_table(&[tr.squeeze_fp5(b"I"), tr.squeeze_fp5(b"I")]);
    let basis = protocol::eq_table(&point);
    let z = table
        .chunks_exact(1 << log)
        .zip(&weights)
        .fold(E::ZERO, |s, (block, &w)| {
            s + w * block
                .iter()
                .zip(&basis)
                .fold(E::ZERO, |v, (&x, &y)| v + y.mul_base(x))
        });
    let mut proof = c
        .open(&weights, kernel(&point), z, &mut tr.clone())
        .unwrap();
    let term = pcs::TensorTerm {
        weight: E::ONE,
        point,
    };
    let verify = |p: &pcs::Opening, weights: &[E]| {
        pcs::interleave::verify(
            profile,
            &nonce,
            &c.root(),
            log,
            &schedule,
            weights,
            &term,
            z,
            p,
            &mut tr.clone(),
        )
    };
    assert!(verify(&proof, &weights));
    let mut wire = Vec::new();
    proof.push_bytes(&mut wire);
    let mut pos = 0;
    assert_eq!(
        pcs::Opening::read_interleaved(&wire, &mut pos, log, &schedule, 4),
        Some(proof.clone())
    );
    assert_eq!(pos, wire.len());
    let mut other = weights.clone();
    other.swap(0, 3);
    assert!(!verify(&proof, &other));
    let d = pcs::stage_dims(log, &schedule).unwrap()[0];
    proof.stage0_query.leaves[0].z.swap(0, 3 * d.arity());
    assert!(!verify(&proof, &weights));
}

/// Check the envelope for every accepted signer dimension. All logarithms
/// round against the security claim. The PCS calculator supplies its own
/// list bounds, OOD, mask, affine fold and distinct query errors.
#[test]
fn high_arity_qrom_accounting() {
    use crate::zk_hem::{
        bounds::log2_hi,
        v2::bounds::{FIELD_MILLIBITS, report_with},
    };
    let s = shape();
    for h in 1..=17 {
        let g = Geometry::new(Profile::TurboShakeJohnson400, &s, 1 << h).unwrap();
        let size = params::ShapeSize {
            log_rows: s.log_rows,
            num_vars: s.num_vars,
            num_public: s.num_public,
        };
        let mut report = report_with(
            Profile::TurboShakeJohnson400,
            size,
            g.log,
            g.columns,
            0,
            &g.schedule,
        )
        .unwrap();
        let st = &report.stages[0];
        let list = st.word_list;
        let first = g.schedule.stages[0];
        let n = (first.blowup as u128) << g.log;
        let d = (1u128 << g.log) - 1;
        let a = st.agreement << first.step_vars;
        let m = report.mask_m;
        // DKT26 Thm 5.12 on the raw symbol domain during a projection.
        assert!((2 * m * a).pow(2) >= (2 * m + 1).pow(2) * d * n);
        let exceptional = if g.stripes > 1 {
            ((2 * m + 1).pow(3) * n * n).div_ceil(3 * d)
        } else {
            0
        };
        let degree = (s.log_rows + h).max(STATEMENT_WORDS + 3);
        // The common point can erase a nonzero residual. Each reduction
        // coordinate can also erase a mismatch in the public prefix.
        let front = (degree as u128 * list).max(exceptional + 3 * list);
        let front_bits = FIELD_MILLIBITS - log2_hi(front);
        report.rbr_bits = report.rbr_bits.min(front_bits);
        let sumchecks = s.log_rows + 4 * h + g.columns;
        let stages = report.stages.len();
        let folded_vars = g.log - g.schedule.early_stop_vars;
        // Count query draws and their following batch weights separately.
        let rounds = 1 + sumchecks + 3 + 2 + 2 * folded_vars + 1 + 3 * (stages - 1) + 1;
        let dims = pcs::stage_dims(g.log, &g.schedule).unwrap();
        let tree_calls: usize = dims
            .iter()
            .map(|d| 1 + d.queries * (1 + d.log_leaves()))
            .sum();
        let short_commits = sumchecks + 5;
        let calls = usize::from(FS_CALLS) + short_commits + tree_calls;
        let openings: usize = dims.iter().map(|d| d.queries).sum::<usize>() + short_commits;
        assert!(rounds < 512 && calls + rounds <= 32768 && openings <= 32768);
        report.rounds = rounds;
        let bits = report.qrom_error_bits(64);
        assert!(bits > 128000);
        if [4, 6, 8, 17].contains(&h) {
            std::println!(
                "K={} log={} stripes={} m={m} list={list} projected_bad={exceptional} front_mbits={front_bits} rbr_mbits={} qrom_mbits={bits} rounds={rounds} calls={calls} openings={openings}",
                1usize << h,
                g.log,
                g.stripes,
                report.rbr_bits
            );
        }
    }
}
