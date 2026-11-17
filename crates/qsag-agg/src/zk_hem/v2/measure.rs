//! Measurements of zk-Hem v2 beside v1, and the pin that keeps prover optimisations from
//! changing a proof byte.
//!
//! One case and one protocol per process, so that the peak resident set belongs to it:
//!
//! ```sh
//! QSAG_V2_CASE=s20 QSAG_V2_PROTO=v2 cargo test --release -p qsag-agg --lib -- \
//!   zk_hem::v2::measure::measure_case --ignored --nocapture --exact
//! ```
//!
//! Cases: `s17`, `s20`, `s22` (synthetic, `2^n` rows, one fresh variable per row), `f82k`
//! (`2^17` rows, 82,000 variables), `bip32` (`2^21` rows, 1,088,721 variables), `blindvc`,
//! `multisig`. Protocols: `v1` (regime tag 4, `BciksJohnsonQrom128`) and `v2`
//! (`CshakeJohnson400`). `QSAG_PROFILE=1` adds the phase lines of `crate::profile`.

use alloc::string::String;
use alloc::vec::Vec;

use super::bounds;
use super::params::{Profile, ShapeSize};
use super::protocol::{self as v2, ZkHemV2Proof, layout_of};
use crate::field::Goldilocks;
use crate::pcs::WhirSecurityRegime;
use crate::sponge::cshake256_32;
use crate::zk_hem::blind_vc::{BlindVcStatement, BlindVcWitness, MAX_VC_ATTRS};
use crate::zk_hem::multisig::{MultisigParams, MultisigRelation, MultisigSigner, Policy};
use crate::zk_hem::protocol as v1;
use crate::zk_hem::relation::{ConstraintSystem, Lc, Shape};

type F = Goldilocks;

const V1_REGIME: WhirSecurityRegime = WhirSecurityRegime::BciksJohnsonQrom128;
const V2_PROFILE: Profile = Profile::CshakeJohnson400;
const SEED: [u8; 32] = [0x5A; 32];
/// Rows a v2 closing reserves; the synthetic relations leave them free under both closings.
const RESERVED_ROWS: usize = 24;
/// Variables a synthetic relation has besides its fresh ones under the v2 closing: the
/// constant, two public inputs and fifteen masking variables.
const FIXED_VARS: usize = 18;

fn f(x: u64) -> F {
    F::from_u64_reduced(x)
}

/// A satisfiable relation with two public inputs, `fresh` rows that each define a new
/// variable from the two before it (three S-box rows, then one multiplication row) and
/// `checks` multiplication rows that restate earlier products without a new variable.
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

/// A synthetic relation of `2^log_rows` rows with `num_vars` variables under the v2 closing
/// (three fewer under v1), every unreserved row used.
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

/// The fixture of `multisig::tests::bench_private_policy_multisig`: capacity 4, depth 10,
/// seven members, threshold 2.
fn multisig_case(is_v2: bool) -> Case {
    use crate::sig::{AggSigProfile, ValidatorKeypair};
    const MESSAGE: [u8; 32] = *b"qsag private policy multisig msg";
    let params = MultisigParams {
        capacity: 4,
        depth: 10,
    };
    let rel = if is_v2 {
        MultisigRelation::new_v2(params)
    } else {
        MultisigRelation::new(params)
    }
    .unwrap();
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

fn case(name: &str, is_v2: bool) -> Case {
    let close = |cs: ConstraintSystem| {
        let (shape, assignment) = if is_v2 {
            cs.finish_v2()
        } else {
            cs.finish()
        };
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
            let (shape, assignment) = if is_v2 {
                st.synthesize_v2(&w)
            } else {
                st.synthesize(&w)
            };
            Case {
                shape,
                assignment,
                statement: st.statement_bytes(b"ctx"),
            }
        }
        "multisig" => multisig_case(is_v2),
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

/// Peak resident set in MiB since the last [`reset_peak`] (`0` without `/proc`).
fn peak_mib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .unwrap_or_default()
        .lines()
        .find_map(|line| line.strip_prefix("VmHWM:"))
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|kib| kib.parse::<u64>().ok())
        .map_or(0, |kib| kib / 1024)
}

/// Restart the peak counter at the current resident set (Linux; a no-op elsewhere).
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

fn measure_v2(case: Case) -> Measured {
    let Case {
        shape,
        assignment,
        statement,
    } = case;
    let public = assignment[1..=shape.num_public].to_vec();
    reset_peak();
    let t = std::time::Instant::now();
    let proof = v2::prove(&shape, assignment, &statement, V2_PROFILE, &SEED).unwrap();
    let prove_s = t.elapsed().as_secs_f64();
    let prove_peak = peak_mib();
    let bytes = proof.to_bytes();
    drop(proof);
    reset_peak();
    let verify_s = median3(|| {
        let t = std::time::Instant::now();
        let decoded = ZkHemV2Proof::from_bytes(&bytes, &shape).unwrap();
        assert!(v2::verify(
            &shape,
            &public,
            &statement,
            V2_PROFILE,
            &decoded
        ));
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

fn measure_v1(case: Case) -> Measured {
    let Case {
        shape,
        assignment,
        statement,
    } = case;
    let public = assignment[1..=shape.num_public].to_vec();
    reset_peak();
    let t = std::time::Instant::now();
    let proof = v1::prove(&shape, assignment, &statement, V1_REGIME, &SEED).unwrap();
    let prove_s = t.elapsed().as_secs_f64();
    let prove_peak = peak_mib();
    let bytes = proof.to_bytes();
    drop(proof);
    reset_peak();
    let verify_s = median3(|| {
        let t = std::time::Instant::now();
        let decoded = v1::ZkHemProof::from_bytes(&bytes, &shape, V1_REGIME).unwrap();
        assert!(v1::verify(
            &shape, &public, &statement, V1_REGIME, &decoded
        ));
        t.elapsed().as_secs_f64()
    });
    Measured {
        log_cells: v1::Layout::new(&shape, V1_REGIME).unwrap().log_cells,
        prove_s,
        verify_s,
        bytes,
        prove_peak,
        verify_peak: peak_mib(),
    }
}

#[test]
#[ignore = "measurement: QSAG_V2_CASE, QSAG_V2_PROTO; run with --ignored --nocapture"]
fn measure_case() {
    let name = std::env::var("QSAG_V2_CASE").expect("QSAG_V2_CASE");
    let proto = std::env::var("QSAG_V2_PROTO").expect("QSAG_V2_PROTO");
    let is_v2 = match proto.as_str() {
        "v1" => false,
        "v2" => true,
        other => panic!("unknown QSAG_V2_PROTO {other}"),
    };
    let t = std::time::Instant::now();
    let case = case(&name, is_v2);
    let setup_s = t.elapsed().as_secs_f64();
    let shape = &case.shape;
    let (log_rows, num_vars, num_sbox) = (shape.log_rows, shape.num_vars, shape.num_sbox);
    let nnz = shape.a.nnz() + shape.b.nnz() + shape.c.nnz();
    let model = is_v2.then(|| {
        let size = ShapeSize {
            log_rows,
            num_vars,
            num_public: shape.num_public,
        };
        bounds::report(V2_PROFILE, size).unwrap().proof_bytes
    });
    let setup_peak = peak_mib();
    let m = if is_v2 {
        measure_v2(case)
    } else {
        measure_v1(case)
    };
    if let Some(model) = model {
        assert!(m.bytes.len() <= model, "proof longer than the bound");
    }
    std::println!(
        "ZKHEM_MEASURE case={name} proto={proto} rows=2^{log_rows} sbox_rows={num_sbox} \
         vars={num_vars} nnz={nnz} cells=2^{} prove_s={:.3} verify_s={:.4} proof_bytes={} \
         proof_kib={:.1} model_bytes={} prove_peak_mib={} verify_peak_mib={} \
         setup_s={setup_s:.2} setup_peak_mib={setup_peak} workers={} proof_digest={}",
        m.log_cells,
        m.prove_s,
        m.verify_s,
        m.bytes.len(),
        m.bytes.len() as f64 / 1024.0,
        model.map_or_else(|| String::from("-"), |b| std::format!("{b}")),
        m.prove_peak,
        m.verify_peak,
        crate::parallel_workers(),
        proof_digest(&m.bytes),
    );
}

/// The prover is deterministic in its seed. These digests were taken before any work on the
/// prover's speed; a change to them is a change of the protocol or of the wire format.
#[test]
fn proof_bytes_are_pinned() {
    let digest = |profile: Profile, workers: usize| {
        let Case {
            shape,
            assignment,
            statement,
        } = case("pin", true);
        let proof = crate::with_worker_limit(workers, || {
            v2::prove(&shape, assignment, &statement, profile, &SEED).unwrap()
        });
        let bytes = proof.to_bytes();
        (bytes.len(), proof_digest(&bytes))
    };
    let cshake = digest(Profile::CshakeJohnson400, usize::MAX);
    let turbo = digest(Profile::TurboShakeJohnson400, usize::MAX);
    assert_eq!(
        [(cshake.0, cshake.1.as_str()), (turbo.0, turbo.1.as_str())],
        [
            (
                271_272,
                "432d604e89b732df945655809530df14451eb1616dae605694ac0f133229f19f"
            ),
            (
                268_772,
                "303c32e08d7ec9506eeb5ccab320b4119c759f620fa3c69f75e49724c42d7939"
            ),
        ]
    );
    // The bytes do not depend on how the work is split across threads.
    assert_eq!(digest(Profile::CshakeJohnson400, 1), cshake);
    assert_eq!(digest(Profile::CshakeJohnson400, 3), cshake);
}
