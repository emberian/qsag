//! Measurements of zk-Hem v2, and the pin that keeps prover optimisations from changing a
//! proof byte.
//!
//! One case per process, so that the peak resident set belongs to it:
//!
//! ```sh
//! QSAG_V2_CASE=s20 cargo test --release -p qsag-agg --lib -- \
//!   zk_hem::v2::measure::measure_case --ignored --nocapture --exact
//! ```
//!
//! Cases: `s17`, `s20`, `s22` (synthetic, `2^n` rows, one fresh variable per row), `f82k`
//! (`2^17` rows, 82,000 variables), `bip32` (`2^21` rows, 1,088,721 variables), `blindvc`,
//! `multisig`. Optional `QSAG_V2_PROTO=turboshake|cshake` selects the hash profile (default
//! `CshakeJohnson400`). `QSAG_PROFILE=1` adds the phase lines of `crate::profile`.

use alloc::string::String;
use alloc::vec::Vec;

use super::bounds;
use super::params::{Profile, ShapeSize};
use super::protocol::{self as v2, ZkHemV2Proof, layout_of};
use crate::field::Goldilocks;
use crate::sponge::cshake256_32;
use crate::zk_hem::blind_vc::{BlindVcStatement, BlindVcWitness, MAX_VC_ATTRS};
use crate::zk_hem::multisig::{MultisigParams, MultisigRelation, MultisigSigner, Policy};
use crate::zk_hem::relation::{ConstraintSystem, Lc, Shape};

type F = Goldilocks;

const SEED: [u8; 32] = [0x5A; 32];
const RESERVED_ROWS: usize = 24;
const FIXED_VARS: usize = 18;

fn f(x: u64) -> F {
    F::from_u64_reduced(x)
}

fn synthetic(fresh: usize, checks: usize) -> ConstraintSystem {
    let mut cs = ConstraintSystem::new();
    let mut older: Lc = cs.public_input(f(3)).into();
    let mut newer: Lc = cs.public_input(f(5)).into();
    let mut products: Vec<(Lc, Lc, Lc)> = Vec::new();
    for i in 0..fresh {
        let a = Lc::combine(&[(F::ONE, &newer), (f(3), &older)]).plus_const(f(i as u64 + 1));
        let next: Lc = if i % 4 == 3 {
            let y: Lc = cs.mul(&a, &older).into();
            if products.len() < 64 {
                products.push((a, older.clone(), y.clone()));
            }
            y
        } else {
            cs.sbox7(&a).into()
        };
        older = core::mem::replace(&mut newer, next);
    }
    for i in 0..checks {
        let (a, b, c) = products[i % products.len()].clone();
        cs.enforce_mul(a, b, c);
    }
    cs
}

fn synthetic_sized(log_rows: usize, num_vars: usize) -> ConstraintSystem {
    let rows = (1usize << log_rows) - RESERVED_ROWS;
    let fresh = (num_vars - FIXED_VARS).min(rows);
    synthetic(fresh, rows - fresh)
}

struct Case {
    shape: Shape,
    assignment: Vec<F>,
    statement: Vec<u8>,
}

fn blind_vc_fixture() -> (BlindVcStatement, BlindVcWitness) {
    let w = BlindVcWitness {
        attrs: (0..MAX_VC_ATTRS).map(|i| f(1_000 + 17 * i as u64)).collect(),
        holder_blind: core::array::from_fn(|i| f(0xA000 + i as u64)),
        presentation_blind: core::array::from_fn(|i| f(0xB000 + i as u64)),
        path_bits: core::array::from_fn(|i| i % 3 == 1),
        siblings: core::array::from_fn(|l| core::array::from_fn(|j| f((l * 6 + j) as u64 + 5))),
    };
    let st = BlindVcStatement::derive(
        &w,
        7,
        0x1234_5678_9ABC,
        [f(11), f(22), f(33), f(44)],
        &[0, 5, 9],
    );
    (st, w)
}

fn multisig_case() -> Case {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    const MESSAGE: [u8; 32] = *b"qsag private policy multisig msg";
    let params = MultisigParams {
        capacity: 4,
        depth: 10,
    };
    let rel = MultisigRelation::new(params).unwrap();
    let mut keys: Vec<ValidatorKeypair> = (0..params.capacity as u32 + 3)
        .map(|i| ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[9; 32], i))
        .collect();
    let policy = Policy::new(keys.iter().map(|k| k.pk).collect(), 2, params.depth).unwrap();
    let signers: Vec<MultisigSigner> = [0usize, 2]
        .into_iter()
        .map(|i| MultisigSigner {
            member_index: i,
            signature: keys[i]
                .sign_stateful_for_unit_test(&MESSAGE, (i % 3) as u32)
                .unwrap(),
        })
        .collect();
    Case {
        assignment: rel.assignment(&policy, &MESSAGE, &signers).unwrap(),
        statement: rel.statement_bytes(),
        shape: rel.shape().clone(),
    }
}

fn case(name: &str) -> Case {
    let close = |cs: ConstraintSystem| {
        let (shape, assignment) = cs.finish_v2();
        Case {
            shape,
            assignment,
            statement: b"zk-Hem measurement".to_vec(),
        }
    };
    match name {
        "pin" => close(synthetic_sized(15, 1 << 15)),
        "s17" => close(synthetic_sized(17, 1 << 17)),
        "s20" => close(synthetic_sized(20, 1 << 20)),
        "s22" => close(synthetic_sized(22, 1 << 22)),
        "f82k" => close(synthetic_sized(17, 82_000)),
        "bip32" => close(synthetic_sized(21, 1_088_721)),
        "blindvc" => {
            let (st, w) = blind_vc_fixture();
            let (shape, assignment) = st.synthesize_v2(&w);
            Case {
                shape,
                assignment,
                statement: st.statement_bytes(b"ctx"),
            }
        }
        "multisig" => multisig_case(),
        other => panic!("unknown QSAG_V2_CASE {other}"),
    }
}

fn hex(bytes: &[u8]) -> String {
    use core::fmt::Write as _;
    bytes.iter().fold(String::new(), |mut s, b| {
        write!(s, "{b:02x}").unwrap();
        s
    })
}

fn proof_digest(bytes: &[u8]) -> String {
    hex(&cshake256_32(b"QSAG.ZKHEM.MEASURE/v1", bytes))
}

fn peak_mib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .unwrap_or_default()
        .lines()
        .find_map(|line| line.strip_prefix("VmHWM:"))
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|kib| kib.parse::<u64>().ok())
        .map_or(0, |kib| kib / 1024)
}

fn reset_peak() {
    let _ = std::fs::write("/proc/self/clear_refs", "5");
}

struct Measured {
    log_cells: usize,
    prove_s: f64,
    verify_s: f64,
    bytes: Vec<u8>,
    prove_peak: u64,
    verify_peak: u64,
}

fn median3(mut run: impl FnMut() -> f64) -> f64 {
    let mut times = [run(), run(), run()];
    times.sort_by(f64::total_cmp);
    times[1]
}

fn measure_v2(case: Case, profile: Profile) -> Measured {
    let Case {
        shape,
        assignment,
        statement,
    } = case;
    let public = assignment[1..=shape.num_public].to_vec();
    reset_peak();
    let t = std::time::Instant::now();
    let proof = v2::prove(&shape, assignment, &statement, profile, &SEED).unwrap();
    let prove_s = t.elapsed().as_secs_f64();
    let prove_peak = peak_mib();
    let bytes = proof.to_bytes();
    drop(proof);
    reset_peak();
    let verify_s = median3(|| {
        let t = std::time::Instant::now();
        let decoded = ZkHemV2Proof::from_bytes(&bytes, &shape).unwrap();
        assert!(v2::verify(&shape, &public, &statement, profile, &decoded));
        t.elapsed().as_secs_f64()
    });
    Measured {
        log_cells: layout_of(&shape).unwrap().log_cells,
        prove_s,
        verify_s,
        bytes,
        prove_peak,
        verify_peak: peak_mib(),
    }
}

#[test]
#[ignore = "measurement: QSAG_V2_CASE, optional QSAG_V2_PROTO; run with --ignored --nocapture"]
fn measure_case() {
    let name = std::env::var("QSAG_V2_CASE").expect("QSAG_V2_CASE");
    let proto = std::env::var("QSAG_V2_PROTO").unwrap_or_else(|_| String::from("v2"));
    let profile = match proto.as_str() {
        "v2" | "cshake" => Profile::CshakeJohnson400,
        "turboshake" => Profile::TurboShakeJohnson400,
        other => panic!("unknown QSAG_V2_PROTO {other}"),
    };
    let t = std::time::Instant::now();
    let case = case(&name);
    let setup_s = t.elapsed().as_secs_f64();
    let shape = &case.shape;
    let (log_rows, num_vars, num_sbox) = (shape.log_rows, shape.num_vars, shape.num_sbox);
    let nnz = shape.a.nnz() + shape.b.nnz() + shape.c.nnz();
    let size = ShapeSize {
        log_rows,
        num_vars,
        num_public: shape.num_public,
    };
    let model = bounds::report(profile, size).unwrap().proof_bytes;
    let setup_peak = peak_mib();
    let m = measure_v2(case, profile);
    assert!(m.bytes.len() <= model, "proof longer than the bound");
    std::println!(
        "ZKHEM_MEASURE case={name} proto={proto} rows=2^{log_rows} sbox_rows={num_sbox} \
         vars={num_vars} nnz={nnz} cells=2^{} prove_s={:.3} verify_s={:.4} proof_bytes={} \
         proof_kib={:.1} model_bytes={model} prove_peak_mib={} verify_peak_mib={} \
         setup_s={setup_s:.2} setup_peak_mib={setup_peak} workers={} proof_digest={}",
        m.log_cells,
        m.prove_s,
        m.verify_s,
        m.bytes.len(),
        m.bytes.len() as f64 / 1024.0,
        m.prove_peak,
        m.verify_peak,
        crate::parallel_workers(),
        proof_digest(&m.bytes),
    );
}

#[test]
fn proof_bytes_are_pinned() {
    let digest = |profile: Profile, workers: usize| {
        let Case {
            shape,
            assignment,
            statement,
        } = case("pin");
        let proof = crate::with_worker_limit(workers, || {
            v2::prove(&shape, assignment, &statement, profile, &SEED).unwrap()
        });
        let bytes = proof.to_bytes();
        let max_bytes = bounds::max_proof_bytes(profile, &shape).unwrap();
        assert!(bytes.len() <= max_bytes);
        (bytes.len(), proof_digest(&bytes))
    };
    let cshake = digest(Profile::CshakeJohnson400, usize::MAX);
    let turbo = digest(Profile::TurboShakeJohnson400, usize::MAX);
    // Worker-count invariance: 1, 3, and max workers produce byte-for-byte identical proofs.
    assert_eq!(digest(Profile::CshakeJohnson400, 1), cshake);
    assert_eq!(digest(Profile::CshakeJohnson400, 3), cshake);
    assert_eq!(digest(Profile::TurboShakeJohnson400, 1), turbo);
}
