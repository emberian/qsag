#!/usr/bin/env python3
"""Instrument an isolated remote copy of qsag-agg on bb2 ONLY (never run on /Users/ember/dev/qsag).

Exports three real cryptographic verification bundles for Verilator hardware replay + tamper tests:
  1. Real `QSAGSTA1` wire proof & full verifier trace under `Poseidon2Cdhz25JohnsonQrom128`
  2. Real `QSAGSTA1` wire proof & full verifier trace under `TurboShakeCdhz25JohnsonQrom128`
  3. Real `[CWYZ26]` `DuetFoldProof` over real `DuetFoldStatement` gates captured from `QSAGSTA1`
"""
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
assert "proof-source" in str(root.resolve()), f"Refusing to instrument non-isolated tree: {root}"
src = root / "crates/qsag-agg/src"

# 1. Add thread-local structured event recorder in lib.rs
lib_rs = src / "lib.rs"
lib_txt = lib_rs.read_text()
assert "pub(crate) mod asic_trace" not in lib_txt, "already instrumented; rsync clean crates first"
lib_txt += r'''
#[cfg(test)]
pub(crate) mod asic_trace {
    use std::cell::RefCell;
    use std::vec::Vec;
    use std::string::String;

    #[derive(Default)]
    pub struct Session {
        pub active: bool,
        pub p2_count: usize,
        pub k24_count: usize,
        pub k12_count: usize,
        pub p2_samples: Vec<([u64; 12], [u64; 12])>,
        pub k_samples: Vec<(usize, [u64; 25], [u64; 25])>,
        pub r0_leaves: Vec<String>,
        pub ext4_leaves: Vec<String>,
        pub canopy_openings: Vec<String>,
        pub ood_checks: Vec<String>,
        pub sumcheck_rounds: Vec<String>,
    }

    std::thread_local! {
        static SESS: RefCell<Session> = RefCell::new(Session::default());
    }

    pub fn start() {
        SESS.with(|s| {
            let mut b = s.borrow_mut();
            *b = Session::default();
            b.active = true;
        });
    }

    pub fn stop() -> Session {
        SESS.with(|s| {
            let mut b = s.borrow_mut();
            b.active = false;
            std::mem::take(&mut *b)
        })
    }

    pub fn rec_p2(inp: &[u64; 12], out: &[u64; 12]) {
        SESS.with(|s| {
            let mut b = s.borrow_mut();
            if b.active {
                b.p2_count += 1;
                if b.p2_samples.len() < 64 {
                    b.p2_samples.push((*inp, *out));
                }
            }
        });
    }

    pub fn rec_keccak(rounds: usize, inp: &[u64; 25], out: &[u64; 25]) {
        SESS.with(|s| {
            let mut b = s.borrow_mut();
            if b.active {
                if rounds == 12 { b.k12_count += 1; } else { b.k24_count += 1; }
                if b.k_samples.len() < 32 {
                    b.k_samples.push((rounds, *inp, *out));
                }
            }
        });
    }

    pub fn push_r0_leaf(j: String) {
        SESS.with(|s| { let mut b = s.borrow_mut(); if b.active { b.r0_leaves.push(j); } });
    }
    pub fn push_ext4_leaf(j: String) {
        SESS.with(|s| { let mut b = s.borrow_mut(); if b.active { b.ext4_leaves.push(j); } });
    }
    pub fn push_canopy(j: String) {
        SESS.with(|s| { let mut b = s.borrow_mut(); if b.active { b.canopy_openings.push(j); } });
    }
    pub fn push_ood(j: String) {
        SESS.with(|s| { let mut b = s.borrow_mut(); if b.active { b.ood_checks.push(j); } });
    }
    pub fn push_sumcheck(j: String) {
        SESS.with(|s| { let mut b = s.borrow_mut(); if b.active { b.sumcheck_rounds.push(j); } });
    }

    pub fn hex32(b: &[u8; 32]) -> String {
        b.iter().map(|x| std::format!("{:02x}", x)).collect()
    }
    pub fn hex_slice(b: &[u8]) -> String {
        b.iter().map(|x| std::format!("{:02x}", x)).collect()
    }
    pub fn u64s_json(ws: &[u64]) -> String {
        let parts: Vec<String> = ws.iter().map(|w| std::format!("\"{:016x}\"", w)).collect();
        std::format!("[{}]", parts.join(","))
    }
    pub fn ext4_json(e: crate::field::GoldilocksExt4) -> String {
        let l = e.to_limbs().map(|x| x.to_canonical_u64());
        u64s_json(&l)
    }
    pub fn ext4_slice_json(es: &[crate::field::GoldilocksExt4]) -> String {
        let parts: Vec<String> = es.iter().map(|e| ext4_json(*e)).collect();
        std::format!("[{}]", parts.join(","))
    }
}
'''
lib_rs.write_text(lib_txt)

# 2. Hook sponge.rs: Poseidon2 permute, keccak_f1600, keccak_p1600_12
sponge_rs = src / "sponge.rs"
s = sponge_rs.read_text()

needle_p2 = "pub(super) const fn permute(input: &[u64; 12]) -> [u64; 12] {"
assert s.count(needle_p2) == 1
s = s.replace(
    needle_p2,
    "pub(super) const fn permute_inner(input: &[u64; 12]) -> [u64; 12] {",
)
# Add non-const wrapper permute right before permute_inner, and keep const callers working if any:
# Wait: check if any const fn calls permute! Let's only trace in runtime or check const callers.
# Instead, keep `permute` non-const only if no const caller, OR check `astra`'s fix_kernel_capture.py:
# `astra` replaced `pub(super) const fn permute` with `pub(super) fn permute` and `cargo test` compiled cleanly!
s = s.replace(
    "pub(super) const fn permute_inner(input: &[u64; 12]) -> [u64; 12] {",
    """pub(super) fn permute(input: &[u64; 12]) -> [u64; 12] {
        let out = permute_const(input);
        #[cfg(test)] crate::asic_trace::rec_p2(input, &out);
        out
    }
    pub(super) const fn permute_const(input: &[u64; 12]) -> [u64; 12] {""",
)

needle_k24 = "pub const fn keccak_f1600(state: &mut [u64; 25]) {"
assert s.count(needle_k24) == 1
# keccak_f1600 IS called in const cshake256_static_midstate? No, that's in qsag_core! Let's check!
# Even safer: use core::intrinsics or only hook runtime sponge functions, OR check if keccak_p1600_12 is called in const!
# TURBOSHAKE_CANOPY_MIDSTATE might be const! So let's NOT remove `const` from `keccak_f1600` or `keccak_p1600_12`!
# Instead, let's hook `pcs.rs` and `zk_hem/protocol.rs` directly where runtime verification happens!
sponge_rs.write_text(s)

# 3. Hook pcs.rs: Canopy multiproof openings, Round-0 leaves, Ext4 leaves, Dual-OOD checks
pcs_rs = src / "pcs.rs"
s = pcs_rs.read_text()

needle_mp = """pub fn verify_canopy_multiproof_with(
    hash: CanopyHash,
    commitment: &CanopyCommitment,
    sorted_leaves: &[(usize, [u8; 32])],
    proof: &CanopyMultiProof,
) -> bool {"""
assert s.count(needle_mp) == 1
s = s.replace(
    needle_mp,
    needle_mp + r'''
    #[cfg(test)] {
        let (mode_str, stg) = match hash {
            CanopyHash::Cshake256 => ("cshake256", 0u8),
            CanopyHash::TurboShake256 => ("turboshake256", 0u8),
            CanopyHash::Poseidon2 { stage_idx } => ("poseidon2", stage_idx),
        };
        let leaves_j: std::vec::Vec<std::string::String> = sorted_leaves.iter()
            .map(|(idx, h)| std::format!("[{},\"{}\"]", idx, crate::asic_trace::hex32(h)))
            .collect();
        let sibs_j: std::vec::Vec<std::string::String> = proof.auth_siblings.iter()
            .map(|h| std::format!("\"{}\"", crate::asic_trace::hex32(h)))
            .collect();
        crate::asic_trace::push_canopy(std::format!(
            "{{\"mode\":\"{}\",\"stage_idx\":{},\"log_leaves\":{},\"root\":\"{}\",\"leaves\":[{}],\"siblings\":[{}]}}",
            mode_str, stg, commitment.log_leaves, crate::asic_trace::hex32(&commitment.root),
            leaves_j.join(","), sibs_j.join(",")
        ));
    }''',
)

needle_r0 = """fn round0_leaf_digest(
    hash: CanopyHash,
    leaf_idx: u32,
    salt: &[u8; 16],
    num_polys: usize,
    vals: &[Goldilocks],
) -> [u8; 32] {"""
assert s.count(needle_r0) == 1
s = s.replace(
    needle_r0,
    needle_r0 + r'''
    #[cfg(test)] {
        let mode_str = match hash {
            CanopyHash::Cshake256 => "cshake256",
            CanopyHash::TurboShake256 => "turboshake256",
            CanopyHash::Poseidon2 { .. } => "poseidon2",
        };
        let d = match hash {
            CanopyHash::Cshake256 => hash_round0_leaf_mode(false, leaf_idx, salt, num_polys, vals),
            CanopyHash::TurboShake256 => hash_round0_leaf_mode(true, leaf_idx, salt, num_polys, vals),
            CanopyHash::Poseidon2 { .. } => poseidon2_round0_leaf(leaf_idx, salt, num_polys, vals),
        };
        let vs: std::vec::Vec<u64> = vals.iter().map(|v| v.to_canonical_u64()).collect();
        crate::asic_trace::push_r0_leaf(std::format!(
            "{{\"mode\":\"{}\",\"leaf_idx\":{},\"salt\":\"{}\",\"num_polys\":{},\"vals\":{},\"digest\":\"{}\"}}",
            mode_str, leaf_idx, crate::asic_trace::hex_slice(salt), num_polys,
            crate::asic_trace::u64s_json(&vs), crate::asic_trace::hex32(&d)
        ));
    }''',
)

needle_e4 = """fn ext4_leaf_digest(
    hash: CanopyHash,
    stage_idx: u8,
    leaf_idx: u32,
    vals: &[GoldilocksExt4],
) -> [u8; 32] {"""
assert s.count(needle_e4) == 1
s = s.replace(
    needle_e4,
    needle_e4 + r'''
    #[cfg(test)] {
        let mode_str = match hash {
            CanopyHash::Cshake256 => "cshake256",
            CanopyHash::TurboShake256 => "turboshake256",
            CanopyHash::Poseidon2 { .. } => "poseidon2",
        };
        let d = match hash {
            CanopyHash::Cshake256 => hash_ext4_group_mode(false, stage_idx, leaf_idx, vals),
            CanopyHash::TurboShake256 => hash_ext4_group_mode(true, stage_idx, leaf_idx, vals),
            CanopyHash::Poseidon2 { .. } => poseidon2_ext4_leaf(stage_idx, leaf_idx, vals),
        };
        crate::asic_trace::push_ext4_leaf(std::format!(
            "{{\"mode\":\"{}\",\"stage_idx\":{},\"leaf_idx\":{},\"vals\":{},\"digest\":\"{}\"}}",
            mode_str, stage_idx, leaf_idx, crate::asic_trace::ext4_slice_json(vals),
            crate::asic_trace::hex32(&d)
        ));
    }''',
)

needle_ood = """    for (z, e) in z_ood_0.into_iter().zip(proof.stage0_ood_evals) {
        let xi = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
        kernel_claims.push(KernelClaim::evaluation(0, xi, z, num_vars));
        cur_sum_claim += xi * e;
    }"""
assert s.count(needle_ood) == 1
s = s.replace(
    needle_ood,
    r'''    #[cfg(test)] let claim_pre_ood0 = cur_sum_claim;
    #[cfg(test)] let mut xis_0 = std::vec::Vec::new();
    for (z, e) in z_ood_0.into_iter().zip(proof.stage0_ood_evals) {
        let xi = transcript.squeeze_ext4(b"WHIR_OOD_WEIGHT");
        #[cfg(test)] xis_0.push(xi);
        kernel_claims.push(KernelClaim::evaluation(0, xi, z, num_vars));
        cur_sum_claim += xi * e;
    }
    #[cfg(test)] crate::asic_trace::push_ood(std::format!(
        "{{\"stage\":0,\"claim_in\":{},\"z_ood\":{},\"evals\":{},\"xis\":{},\"claim_out\":{}}}",
        crate::asic_trace::ext4_json(claim_pre_ood0),
        crate::asic_trace::ext4_slice_json(&z_ood_0),
        crate::asic_trace::ext4_slice_json(&proof.stage0_ood_evals),
        crate::asic_trace::ext4_slice_json(&xis_0),
        crate::asic_trace::ext4_json(cur_sum_claim)
    ));''',
)
pcs_rs.write_text(s)

# 4. Hook zk_hem/protocol.rs: verify_sumcheck rounds
proto_rs = src / "zk_hem/protocol.rs"
s = proto_rs.read_text()
needle_sc = """        tr.absorb_ext4_slice(label, round);
        let c = tr.squeeze_ext4(label);
        claim = eval_poly(round, c);"""
assert s.count(needle_sc) == 1
s = s.replace(
    needle_sc,
    r'''        #[cfg(test)] let claim_in = claim;
        tr.absorb_ext4_slice(label, round);
        let c = tr.squeeze_ext4(label);
        claim = eval_poly(round, c);
        #[cfg(test)] crate::asic_trace::push_sumcheck(std::format!(
            "{{\"label\":\"{}\",\"claim_in\":{},\"coeffs\":{},\"chal\":{},\"claim_out\":{}}}",
            core::str::from_utf8(label).unwrap_or("?"),
            crate::asic_trace::ext4_json(claim_in),
            crate::asic_trace::ext4_slice_json(round),
            crate::asic_trace::ext4_json(c),
            crate::asic_trace::ext4_json(claim)
        ));''',
)
proto_rs.write_text(s)

# 5. Expose CAPTURE in recursive_fold.rs to crate tests so recursive.rs can drain real DuetFoldStatements
rf_rs = src / "recursive_fold.rs"
s = rf_rs.read_text()
s = s.replace("static CAPTURE_SESSION_LOCK:", "pub(crate) static CAPTURE_SESSION_LOCK:")
s = s.replace("static CAPTURE:", "pub(crate) static CAPTURE:")
rf_rs.write_text(s)

# 6. Append dedicated export test in recursive.rs
rec_rs = src / "recursive.rs"
s = rec_rs.read_text()
export_test = r'''
    #[test]
    fn export_asic_real_qsagsta1_and_duetfold_bundle() {
        use crate::zk_hem::{
            protocol,
            relation::{ConstraintSystem, Lc},
        };
        let out_dir = std::path::PathBuf::from(std::env::var("QSAG_ASIC_OUTDIR").unwrap());
        std::fs::create_dir_all(&out_dir).unwrap();

        let child_public = |index, weight| SubtreePublic {
            subtree_registry_root: [Goldilocks::from_u64_reduced(index + 20); 4],
            epoch_floor: Goldilocks::from_u64_reduced(7),
            message_digest: subtree_message_digest(b"roster fixture"),
            total_active_signers: Goldilocks::ONE,
            min_key_idx: index,
            max_key_idx: index,
            total_active_weight: weight,
        };
        let publics = [child_public(1, 2), child_public(4, 3)];
        let mut native = crate::zk_hem::recursive_whir::Native::default();
        let root =
            subtree_fold_merkle_gadget(&mut native, 0, &publics.map(|p| p.subtree_registry_root));
        let parent = SubtreePublic {
            subtree_registry_root: root,
            total_active_signers: Goldilocks::from_u64_reduced(2),
            min_key_idx: 1,
            max_key_idx: 4,
            total_active_weight: 5,
            ..publics[0]
        };

        let mut cs = ConstraintSystem::new_hologram_aligned();
        for word in parent.words() {
            let input: Lc = cs.public_input(word).into();
            cs.enforce_equal(&input, &Lc::constant(word));
        }
        let (root_shape, root_z) = cs.finish();

        let statement = RosterRootStatement {
            roster_root: crate::sponge::limbs4_to_le_bytes32(root),
            epoch_floor: 7,
            message: b"roster fixture",
            minimum_global_quorums: 2,
            minimum_active_weight: 5,
            min_key_idx: 1,
            max_key_idx: 4,
        };

        let run_regime = |regime: WhirSecurityRegime, tag: &str| -> (std::string::String, std::vec::Vec<crate::recursive_fold::DuetFoldStatement>) {
            let root_hologram = protocol::ShapeHologram::compile_native(&root_shape, regime).unwrap();
            let root_vk = root_hologram.verifier_key();
            let proof = SuccinctSubtreeAggregate {
                total_active_signers: 2,
                min_key_idx: 1,
                max_key_idx: 4,
                total_active_weight: 5,
                proof: protocol::prove_public_hologram(
                    &root_shape,
                    &root_hologram,
                    root_z.clone(),
                    SUBTREE_ROOT_LABEL,
                    &[64; 32],
                ).unwrap(),
            };
            let wire = proof.to_bytes();
            assert_eq!(&wire[..8], b"QSAGSTA1");
            assert_eq!(SuccinctSubtreeAggregate::from_bytes_canonical(root_vk, &wire), Some(proof.clone()));
            let bin_path = out_dir.join(std::format!("qsagsta1_{}.bin", tag));
            std::fs::write(&bin_path, &wire).unwrap();

            let _lock = crate::recursive_fold::CAPTURE_SESSION_LOCK.lock().unwrap_or_else(|e| e.into_inner());
            *crate::recursive_fold::CAPTURE.lock().unwrap_or_else(|e| e.into_inner()) = Some(std::vec::Vec::new());
            crate::asic_trace::start();
            assert!(verify_succinct_subtree_aggregate_against_roster_root(root_vk, &statement, &proof));
            let sess = crate::asic_trace::stop();
            let duet_gates = crate::recursive_fold::CAPTURE.lock().unwrap_or_else(|e| e.into_inner()).take().unwrap();
            drop(_lock);

            // Verify native tamper rejection too
            let mut bad_stmt = statement;
            bad_stmt.roster_root[0] ^= 1;
            assert!(!verify_succinct_subtree_aggregate_against_roster_root(root_vk, &bad_stmt, &proof));

            let p2_j: std::vec::Vec<std::string::String> = sess.p2_samples.iter()
                .map(|(i, o)| std::format!("{{\"in\":{},\"out\":{}}}", crate::asic_trace::u64s_json(i), crate::asic_trace::u64s_json(o)))
                .collect();
            let duet_j: std::vec::Vec<std::string::String> = duet_gates.iter()
                .map(|g| {
                    std::format!(
                        "{{\"v0\":{},\"v1\":{},\"theta\":{},\"alpha\":{},\"beta\":{},\"inv_two\":\"{:016x}\",\"inv_two_x\":\"{:016x}\",\"x_sq\":\"{:016x}\",\"claimed\":{}}}",
                        crate::asic_trace::ext4_json(g.v0),
                        crate::asic_trace::ext4_json(g.v1),
                        crate::asic_trace::ext4_json(g.theta),
                        crate::asic_trace::ext4_json(g.alpha),
                        crate::asic_trace::ext4_json(g.beta),
                        g.inv_two.to_canonical_u64(),
                        g.inv_two_x.to_canonical_u64(),
                        g.x_sq.to_canonical_u64(),
                        crate::asic_trace::ext4_json(g.claimed)
                    )
                })
                .collect();
            let pub_words: std::vec::Vec<u64> = parent.words().iter().map(|w| w.to_canonical_u64()).collect();
            let j = std::format!(
                "{{\"regime\":\"{}\",\"wire_bytes\":{},\"public_words\":{},\"p2_total_calls\":{},\"p2_samples\":[{}],\"sumcheck_rounds\":[{}],\"ood_checks\":[{}],\"r0_leaves\":[{}],\"ext4_leaves\":[{}],\"canopy_openings\":[{}],\"duet_gates\":[{}]}}",
                tag, wire.len(), crate::asic_trace::u64s_json(&pub_words),
                sess.p2_count, p2_j.join(","),
                sess.sumcheck_rounds.join(","),
                sess.ood_checks.join(","),
                sess.r0_leaves.join(","),
                sess.ext4_leaves.join(","),
                sess.canopy_openings.join(","),
                duet_j.join(",")
            );
            (j, duet_gates)
        };

        let (p2_json, p2_gates) = run_regime(WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128, "poseidon2");
        let (ts_json, ts_gates) = run_regime(WhirSecurityRegime::TurboShakeCdhz25JohnsonQrom128, "turboshake");
        assert!(!p2_gates.is_empty() && !ts_gates.is_empty());

        // Also generate a real [CWYZ26] DuetFoldProof over the real captured gates!
        let duet_context = [0x5Au8; 32];
        let duet_salt = [0xA5u8; 32];
        let duet_rows = &p2_gates[..p2_gates.len().min(4)];
        let duet_proof = crate::recursive_fold::prove_duet_folds(&duet_context, duet_rows, &duet_salt).unwrap();
        assert!(crate::recursive_fold::verify_duet_folds(&duet_context, duet_rows, &duet_proof));

        let rounds_j: std::vec::Vec<std::string::String> = duet_proof.round_polynomials.iter()
            .map(|rp| crate::asic_trace::ext4_slice_json(rp))
            .collect();
        let rows_j: std::vec::Vec<std::string::String> = duet_rows.iter()
            .map(|g| {
                let row: std::vec::Vec<u64> = g.witness_row().iter().map(|x| x.to_canonical_u64()).collect();
                crate::asic_trace::u64s_json(&row)
            })
            .collect();
        let duet_comp_json = std::format!(
            "{{\"context\":\"{}\",\"num_statements\":{},\"witness_rows\":[{}],\"commitment_root\":\"{}\",\"commitment_log_leaves\":{},\"round_polynomials\":[{}],\"column_evaluations\":{}}}",
            crate::asic_trace::hex32(&duet_context),
            duet_rows.len(),
            rows_j.join(","),
            crate::asic_trace::hex32(&duet_proof.commitment.root),
            duet_proof.commitment.log_leaves,
            rounds_j.join(","),
            crate::asic_trace::ext4_slice_json(&duet_proof.column_evaluations)
        );

        let bundle = std::format!(
            "{{\n  \"qsagsta1_poseidon2\": {},\n  \"qsagsta1_turboshake\": {},\n  \"cwyz26_duet_fold\": {}\n}}\n",
            p2_json, ts_json, duet_comp_json
        );
        std::fs::write(out_dir.join("real_proof_bundle.json"), bundle).unwrap();
        std::println!("EXPORTED REAL QSAGSTA1 (P2 + TS) + CWYZ26 DUETFOLD BUNDLE OK: p2_gates={}, ts_gates={}", p2_gates.len(), ts_gates.len());
    }
'''
# Insert right before the closing `}` of `mod tests` in recursive.rs
last_brace = s.rfind("}")
assert last_brace != -1
s = s[:last_brace] + export_test + "\n}\n"
rec_rs.write_text(s)
print("Instrumented isolated proof-source successfully.")
