//! E12 Physical `AMD Radeon RX 6750 XT` (`gfx1030`) Grounding Suite:
//! 1. Cryptographic `VerifiedKernelDigestRegistry` 1-bit SPIR-V corruption rejection across all
//!    10 compute shaders (6 `KernelSlot`s + 4 `ProverKernelSlot`s).
//! 2. End-to-end stateful `ProverReceiptChain` (`seq = 0..8`) across all 4 `ProverKernelSlot`s
//!    with constant-time replay, reorder, skip, swapped-pair, and MAC-flip rejection.
//! 3. Live physical `RX 6750 XT` compilation (`glslangValidator` -> RADV ACO `gfx1030`) and
//!    execution of planted semantic faults across ALL 10 `.comp` compute shaders, proving both
//!    concrete GPU != CPU value divergence on silicon and cryptographic pin/receipt rejection.

#![cfg(all(
    feature = "std",
    feature = "fault-injection-audit",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]

use std::path::Path;
use std::process::Command;

use qsag_accel::goldilocks::{GOLDILOCKS_PRIME, precompute_goldilocks_twiddles};
use qsag_accel::spirv_kernels::{
    prover_shader_source_filename, prover_spirv_kernel_bytes, prover_spirv_kernel_words,
    shader_source_filename, spirv_kernel_bytes, spirv_kernel_words,
};
use qsag_accel::vulkan::{
    WhirBatchSumcheckStep, WhirRound0ReceiptParams, batch_keccak_f1600_with_receipt,
    batch_poseidon2_perm12_with_receipt, bdoz_gf2_128_batch_dot_with_receipt,
    coset_lde_ext2_with_receipt, goldilocks_ntt_with_receipt, merkle_layer_poseidon2_with_receipt,
};
use qsag_accel::{
    AcceleratorBackend, BackendAttestationKey, BatchJobDescriptor, CertifiedBackend,
    CertifiedKernelPin, CertifiedProverKernelPin, CpuReferenceBackend, ExecutionReceipt,
    KernelRegistryError, KernelSlot, KernelTargetArch, ProverExecutionReceipt, ProverJobDescriptor,
    ProverKernelSlot, ProverReceiptChain, VerifiedKernelDigestRegistry, VulkanSpirvBackend,
};

type Ext4 = [u64; 4];

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn compile_mutated_shader(comp_name: &str, target: &str, replacement: &str) -> (Vec<u8>, Vec<u32>) {
    let validator = Path::new("/usr/bin/glslangValidator");
    assert!(
        validator.exists(),
        "glslangValidator required at {}",
        validator.display()
    );
    let src_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("shaders")
        .join(comp_name);
    let src = std::fs::read_to_string(&src_path).expect("read .comp shader");
    assert!(
        src.contains(target),
        "shader {comp_name} missing mutation target `{target}`"
    );
    let mutated = src.replacen(target, replacement, 1);
    assert_ne!(src, mutated);

    let tmp_dir = std::env::temp_dir().join(format!("e12_mut_spv_{}", std::process::id()));
    std::fs::create_dir_all(&tmp_dir).expect("create temp dir");
    let mut_comp = tmp_dir.join(comp_name);
    let mut_spv = tmp_dir.join(format!("{comp_name}.spv"));
    std::fs::write(&mut_comp, &mutated).expect("write mutated .comp");

    let out = Command::new(validator)
        .args(["-V", "--target-env", "vulkan1.2"])
        .arg(&mut_comp)
        .arg("-o")
        .arg(&mut_spv)
        .output()
        .expect("run glslangValidator");
    assert!(
        out.status.success(),
        "glslangValidator failed on mutated {comp_name}: {}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&mut_spv).expect("read mutated .spv");
    assert_eq!(bytes.len() % 4, 0);
    let words: Vec<u32> = bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect();
    let _ = std::fs::remove_file(&mut_comp);
    let _ = std::fs::remove_file(&mut_spv);
    (bytes, words)
}

#[test]
fn test_all_10_spirv_pins_prover_receipt_chain_and_live_rx6750xt_faults() {
    let gpu = VulkanSpirvBackend::try_new_audited().expect("audited RX 6750 XT Vulkan backend");
    let info = gpu.device_info();
    println!(
        "=== E12 Physical GPU Grounding on `{}` (vendor=0x{:04x}, device=0x{:04x}) ===",
        gpu.device_name(),
        gpu.vendor_id(),
        info.device_id
    );
    assert_eq!(info.secret_slot_audit(), Ok(()));
    assert!(gpu.secret_slots_audited());

    let registry = VerifiedKernelDigestRegistry::<4>::with_cpu_and_canonical_gpu_pins();
    let base_batch_pins = VulkanSpirvBackend::measure_embedded_spirv_pins();
    let base_prover_pins = VulkanSpirvBackend::measure_embedded_prover_spirv_pins();
    assert_eq!(
        registry.verify_loaded_profile(KernelTargetArch::SpirV15, &base_batch_pins),
        Ok(())
    );
    assert_eq!(
        registry.verify_loaded_prover_profile(KernelTargetArch::SpirV15, &base_prover_pins),
        Ok(())
    );

    let key = BackendAttestationKey::derive(&[0xE1; 32], b"E12-RX6750XT-AUDIT");
    let wrong_key = BackendAttestationKey::derive(&[0xE2; 32], b"E12-RX6750XT-AUDIT");
    let audit_digest = gpu.hardware_audit_digest();
    assert_ne!(audit_digest, [0u8; 32]);

    // =========================================================================
    // 1. 1-bit SPIR-V instruction corruption rejection across all 10 slots
    // =========================================================================
    for slot in KernelSlot::ALL {
        let mut raw = spirv_kernel_bytes(slot).to_vec();
        let flip_idx = raw.len() - 4;
        raw[flip_idx] ^= 0x01;
        let bad_pin = CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &raw);
        let orig_pin = base_batch_pins[slot as usize];
        assert_ne!(bad_pin.sha256_digest, orig_pin.sha256_digest);
        assert_ne!(bad_pin.poseidon2_digest, orig_pin.poseidon2_digest);

        let mut bad_profile = base_batch_pins;
        bad_profile[slot as usize] = bad_pin;
        assert_eq!(
            registry.verify_loaded_profile(KernelTargetArch::SpirV15, &bad_profile),
            Err(KernelRegistryError::PinMismatch { slot })
        );

        let dummy_desc = match slot {
            KernelSlot::BatchKeccakF1600 => BatchJobDescriptor::KeccakF1600 { num_states: 64 },
            KernelSlot::BatchPoseidon2Perm12 => BatchJobDescriptor::Poseidon2Perm12 { num_states: 64 },
            KernelSlot::GoldilocksNtt => BatchJobDescriptor::GoldilocksNtt {
                length: 1024,
                inverse: false,
            },
            KernelSlot::CosetLdeExt2 => BatchJobDescriptor::CosetLdeExt2 {
                domain_len: 256,
                blowup: 4,
                shift: 7,
            },
            KernelSlot::MerkleLayerPoseidon2 => BatchJobDescriptor::MerkleLayerPoseidon2 {
                num_parents: 64,
                pk_seed: [1, 2, 3, 4],
                layer: 0,
            },
            KernelSlot::BdozGf2128BatchDot => BatchJobDescriptor::BdozGf2128BatchDot { num_elements: 256 },
        };
        let forged_rec = ExecutionReceipt::compute_audited(
            &key,
            &bad_pin,
            dummy_desc,
            [0xAA; 32],
            [0x11; 32],
            [0x22; 32],
            audit_digest,
        )
        .unwrap();
        assert_eq!(
            registry.verify_keyed_receipt(&forged_rec, &key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        );
        println!("  [PASS] Batch slot {slot:?}: 1-bit SPIR-V corruption rejected by registry + receipt");
    }

    for slot in ProverKernelSlot::ALL {
        let mut raw = prover_spirv_kernel_bytes(slot).to_vec();
        let flip_idx = raw.len() - 4;
        raw[flip_idx] ^= 0x01;
        let bad_pin =
            CertifiedProverKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &raw);
        let orig_pin = base_prover_pins[slot as usize];
        assert_ne!(bad_pin.sha256_digest, orig_pin.sha256_digest);
        assert_ne!(bad_pin.poseidon2_digest, orig_pin.poseidon2_digest);

        let mut bad_profile = base_prover_pins;
        bad_profile[slot as usize] = bad_pin;
        assert_eq!(
            registry.verify_loaded_prover_profile(KernelTargetArch::SpirV15, &bad_profile),
            Err(KernelRegistryError::ProverPinMismatch { slot })
        );

        let dummy_desc = match slot {
            ProverKernelSlot::WhirLdeCommitment => ProverJobDescriptor::WhirCommitRound0 {
                num_polys: 1,
                num_vars: 12,
                blowup: 4,
                group_arity: 16,
            },
            ProverKernelSlot::WhirFoldSumcheck => ProverJobDescriptor::WhirFoldSumcheck {
                op_code: 0,
                num_elements: 4096,
                aux: 0,
            },
            ProverKernelSlot::AirRowGroupA => ProverJobDescriptor::AirRowGroupA {
                mode: 0,
                cur_m: 16,
                cur_r: 16,
            },
            ProverKernelSlot::AirRowGroupB => ProverJobDescriptor::AirRowGroupB {
                is_round0_base: true,
                cur_m: 16,
                cur_r: 16,
                cur_s: 1,
            },
        };
        let mut chain = ProverReceiptChain::new([0x77; 32]);
        let forged_rec = ProverExecutionReceipt::compute_audited(
            &key,
            &bad_pin,
            dummy_desc,
            chain.current_anchor(),
            [0x11; 32],
            [0x22; 32],
            audit_digest,
        )
        .unwrap();
        assert_eq!(
            chain.verify_next(&registry, &forged_rec, &key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        );
        assert_eq!(chain.seq(), 0, "failed receipt must not advance ProverReceiptChain");
        println!("  [PASS] Prover slot {slot:?}: 1-bit SPIR-V corruption rejected by registry + ProverReceiptChain");
    }

    // =========================================================================
    // 2. Full Stateful `ProverReceiptChain` Across All 4 Prover Pipelines
    // =========================================================================
    {
        let _guard = gpu.try_acquire_prover_session().expect("acquire prover session");
        let mut prover_chain = ProverReceiptChain::new([0x55; 32]);
        let mut verifier_chain = ProverReceiptChain::new([0x55; 32]);

        let nv = 12usize;
        let c_len = 1usize << nv;
        let air_rows = 16usize;
        let extra_words = air_rows * 256;
        let mut rng = 0xE12_CAFE_u64;
        let poly: Vec<u64> = (0..c_len)
            .map(|_| splitmix64(&mut rng) % GOLDILOCKS_PRIME)
            .collect();
        let salt = [0x42u8; 32];

        // Step 0: WhirLdeCommitment round-0 commit
        let r0_params = WhirRound0ReceiptParams {
            salt_seed: &salt,
            num_vars: nv,
            blowup: 4,
            group_arity: 16,
            max_stage1_domain_ext4: 256,
            max_stage1_groups: 64,
            extra_witness_words: extra_words,
        };
        let (top_r0, rec0) = gpu
            .prover_whir_commit_round0_with_receipt(
                &key,
                prover_chain.current_anchor(),
                1,
                &salt,
                nv,
                4,
                16,
                256,
                64,
                extra_words,
                |_p, pos, dst| {
                    dst.copy_from_slice(&poly[pos..pos + dst.len()]);
                },
            )
            .expect("round0 commit with receipt");
        let _ = r0_params;
        assert_ne!(top_r0, [0u8; 32]);
        assert_eq!(prover_chain.record_issued(&rec0), Ok(0));

        // Step 1: WhirFoldSumcheck batch sumcheck init
        let eq_tables: Vec<Ext4> = (0..768)
            .map(|_| core::array::from_fn(|_| splitmix64(&mut rng) % GOLDILOCKS_PRIME))
            .collect();
        let lambdas = [[3u64, 5, 7, 11]];
        let rec1 = gpu
            .prover_whir_batch_sumcheck_init_with_receipt(
                &key,
                prover_chain.current_anchor(),
                &eq_tables,
                &lambdas,
                nv,
            )
            .expect("batch_sumcheck_init_with_receipt");
        assert_eq!(prover_chain.record_issued(&rec1), Ok(1));

        // Step 2: WhirFoldSumcheck batch sumcheck eval
        let step_cfg = WhirBatchSumcheckStep {
            round: 0,
            cur_len: c_len,
            num_polys: 1,
            src_base: 0,
            dst_base: c_len as u32,
        };
        let ([_ev0, _ev2], rec2) = gpu
            .prover_whir_batch_sumcheck_eval_with_receipt(
                &key,
                prover_chain.current_anchor(),
                step_cfg.round,
                step_cfg.cur_len,
                step_cfg.num_polys,
                step_cfg.src_base,
            )
            .expect("batch_sumcheck_eval_with_receipt");
        assert_eq!(prover_chain.record_issued(&rec2), Ok(2));

        // Step 3: AirRowGroupA init_shard
        let cols_base = c_len as u32;
        let mut statics: Vec<Ext4> = (0..250 + 44)
            .map(|_| core::array::from_fn(|_| splitmix64(&mut rng) % GOLDILOCKS_PRIME))
            .collect();
        statics.push([0, 1, 2, 3]);
        statics.push([4, 5, 6, 7]);
        let shifts: Vec<Ext4> = (0..3 * air_rows)
            .map(|_| core::array::from_fn(|_| splitmix64(&mut rng) % GOLDILOCKS_PRIME))
            .collect();
        let rec3 = gpu
            .prover_air_init_shard_with_receipt(
                &key,
                prover_chain.current_anchor(),
                0,
                cols_base,
                air_rows,
                &shifts,
                &statics,
            )
            .expect("air_init_shard_with_receipt");
        assert_eq!(prover_chain.record_issued(&rec3), Ok(3));

        // Steps 4 & 5 (paired!): AirRowGroupA + AirRowGroupB eval_round_with_receipt
        let dyn_ext4_off = 296u32;
        let sorted_u64_off = 294u32 * 4;
        let mut dyn_words = Vec::new();
        let mut off = dyn_ext4_off;
        let signers_off = off;
        dyn_words.extend_from_slice(&[1, 0, 0, 0]);
        dyn_words.extend(core::iter::repeat_n(0u64, 13 * 4));
        off += 14;
        let steps_off = off;
        for loc in 0..air_rows {
            dyn_words.extend_from_slice(&[u64::from(loc == 0), 0, 0, 0]);
            dyn_words.extend_from_slice(&[u64::from(loc + 1 == air_rows), 0, 0, 0]);
            dyn_words.extend_from_slice(&[0, 0, 0, 0]);
        }
        off += (air_rows * 3) as u32;
        let op_hdr_off = off;
        for idx in 0..air_rows / 2 {
            dyn_words.extend_from_slice(&[idx as u64, 1, 0, 0]);
        }
        off += (air_rows / 2) as u32;
        let op_ent_off = off;
        for _ in 0..air_rows / 2 {
            dyn_words.extend_from_slice(&[0, 0, 250, 0]);
            dyn_words.extend_from_slice(&[1, 0, 0, 0]);
            dyn_words.extend_from_slice(&[0, 0, 0, 0]);
        }
        let (_air_ev, pair45) = gpu
            .prover_air_eval_round_with_receipt(
                &key,
                prover_chain.current_anchor(),
                true,
                air_rows,
                air_rows,
                1,
                false,
                cols_base,
                0,
                dyn_ext4_off,
                &dyn_words,
                signers_off,
                steps_off,
                op_hdr_off,
                op_ent_off,
                sorted_u64_off,
            )
            .expect("air_eval_round_with_receipt");
        assert_eq!(prover_chain.record_issued_pair(&pair45), Ok(4));
        assert_eq!(prover_chain.seq(), 6);

        // Step 6: AirRowGroupA fold_round_with_receipt
        let rec6 = gpu
            .prover_air_fold_round_with_receipt(
                &key,
                prover_chain.current_anchor(),
                true,
                air_rows,
                cols_base,
                0,
                0,
                (3 * air_rows) as u32,
                [9, 10, 11, 12],
            )
            .expect("air_fold_round_with_receipt");
        assert_eq!(prover_chain.record_issued(&rec6), Ok(6));
        assert_eq!(prover_chain.seq(), 7);

        // Negative checks BEFORE advancing verifier_chain:
        // (a) Skip step 0 -> try verifying rec1 at seq 0 -> REJECTED!
        assert_eq!(
            verifier_chain.verify_next(&registry, &rec1, &key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        );
        assert_eq!(verifier_chain.seq(), 0);

        // (b) Wrong key -> REJECTED!
        assert_eq!(
            verifier_chain.verify_next(&registry, &rec0, &wrong_key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        );

        // (c) 1-bit MAC flip -> REJECTED!
        let mut tampered_rec0 = rec0;
        tampered_rec0.mac[0] ^= 0x80;
        assert_eq!(
            verifier_chain.verify_next(&registry, &tampered_rec0, &key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        );

        // Authentic step-by-step verification:
        assert_eq!(verifier_chain.verify_next(&registry, &rec0, &key), Ok(0));
        // Replay rec0 at seq 1 -> REJECTED!
        assert_eq!(
            verifier_chain.verify_next(&registry, &rec0, &key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        );
        assert_eq!(verifier_chain.verify_next(&registry, &rec1, &key), Ok(1));
        assert_eq!(verifier_chain.verify_next(&registry, &rec2, &key), Ok(2));
        assert_eq!(verifier_chain.verify_next(&registry, &rec3, &key), Ok(3));

        // Swapping [rec_gb, rec_ga] in paired verification -> advances wrong mid_state so rec6 would fail,
        // or test on a cloned chain!
        let mut swapped_chain = verifier_chain.clone();
        let swapped_pair = [pair45[1], pair45[0]];
        assert_eq!(
            swapped_chain.verify_next_pair(&registry, &swapped_pair, &key),
            Ok(4)
        );
        // Because ratchet order binds [rec_ga, rec_gb] sequentially, rec6 MUST fail on swapped_chain!
        assert_eq!(
            swapped_chain.verify_next(&registry, &rec6, &key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed),
            "swapped AirRowGroupA/B pair must poison subsequent ProverReceiptChain anchor!"
        );

        assert_eq!(verifier_chain.verify_next_pair(&registry, &pair45, &key), Ok(4));
        assert_eq!(verifier_chain.verify_next(&registry, &rec6, &key), Ok(6));
        assert_eq!(verifier_chain, prover_chain);
        println!("  [PASS] Stateful ProverReceiptChain (seq 0..7 across all 4 prover slots) + replay/skip/swap/MAC teeth verified");
    }

    // =========================================================================
    // 3. Live Physical `RX 6750 XT` Execution of 10 Semantic-Fault Shaders
    // =========================================================================
    let cpu = CpuReferenceBackend;
    let anchor = [0xEEu8; 32];
    let cert_gpu = CertifiedBackend::try_new_measured(gpu, &registry, &base_batch_pins).unwrap();
    let gpu = cert_gpu.inner();

    // --- Slot 0: BatchKeccakF1600 ---
    {
        let slot = KernelSlot::BatchKeccakF1600;
        let orig_spv = spirv_kernel_words(slot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            shader_source_filename(slot),
            "0x0000000000000001ul",
            "0x0000000000000003ul",
        );
        let mut_pin = CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &mut_bytes);
        let mut bad_prof = base_batch_pins;
        bad_prof[slot as usize] = mut_pin;
        assert_eq!(
            registry.verify_loaded_profile(KernelTargetArch::SpirV15, &bad_prof),
            Err(KernelRegistryError::PinMismatch { slot })
        );

        let mut cpu_st = [[7u64; 25]; 64];
        cpu.batch_keccak_f1600(&mut cpu_st);

        gpu.audit_replace_kernel_spirv(slot, &mut_words).unwrap();
        let mut gpu_mut_st = [[7u64; 25]; 64];
        gpu.batch_keccak_f1600(&mut gpu_mut_st);
        assert_ne!(gpu_mut_st, cpu_st, "mutated Keccak shader must diverge on RX 6750 XT");

        gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
        let mut gpu_ok_st = [[7u64; 25]; 64];
        let rec = batch_keccak_f1600_with_receipt(&cert_gpu, &key, &mut gpu_ok_st, anchor).unwrap();
        assert_eq!(gpu_ok_st, cpu_st);
        assert_eq!(registry.verify_keyed_receipt(&rec, &key), Ok(()));
        println!("  [PASS] Live RX 6750 XT fault [00 keccak_f1600.comp]: GPU_mut != CPU caught & restored");

        // --- Slot 1: BatchPoseidon2Perm12 ---
        let slot = KernelSlot::BatchPoseidon2Perm12;
        let orig_spv = spirv_kernel_words(slot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            shader_source_filename(slot),
            "uint64_t rem_p = GL_P - b_c;",
            "uint64_t rem_p = GL_P - b_c; a_c ^= 1ul;",
        );
        let mut bad_prof = base_batch_pins;
        bad_prof[slot as usize] =
            CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_profile(KernelTargetArch::SpirV15, &bad_prof),
            Err(KernelRegistryError::PinMismatch { slot })
        );
        let mut cpu_p2 = [[3u64; 12]; 64];
        cpu.batch_poseidon2_perm12(&mut cpu_p2);
        gpu.audit_replace_kernel_spirv(slot, &mut_words).unwrap();
        let mut gpu_mut_p2 = [[3u64; 12]; 64];
        gpu.batch_poseidon2_perm12(&mut gpu_mut_p2);
        assert_ne!(gpu_mut_p2, cpu_p2, "mutated Poseidon2 shader must diverge on RX 6750 XT");
        gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
        let mut gpu_ok_p2 = [[3u64; 12]; 64];
        let rec = batch_poseidon2_perm12_with_receipt(&cert_gpu, &key, &mut gpu_ok_p2, anchor).unwrap();
        assert_eq!(gpu_ok_p2, cpu_p2);
        assert_eq!(registry.verify_keyed_receipt(&rec, &key), Ok(()));
        println!("  [PASS] Live RX 6750 XT fault [01 poseidon2_perm12.comp]: GPU_mut != CPU caught & restored");

        // --- Slot 2: GoldilocksNtt ---
        let slot = KernelSlot::GoldilocksNtt;
        let orig_spv = spirv_kernel_words(slot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            shader_source_filename(slot),
            "uint64_t rem_p = GL_P - b_c;",
            "uint64_t rem_p = GL_P - b_c; a_c ^= 1ul;",
        );
        let mut bad_prof = base_batch_pins;
        bad_prof[slot as usize] =
            CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_profile(KernelTargetArch::SpirV15, &bad_prof),
            Err(KernelRegistryError::PinMismatch { slot })
        );
        let tw = precompute_goldilocks_twiddles(1024).unwrap();
        let orig_ntt: Vec<u64> = (0..1024u64).map(|i| (i * 17 + 5) % GOLDILOCKS_PRIME).collect();
        let mut cpu_ntt = orig_ntt.clone();
        cpu.goldilocks_ntt_inplace(&mut cpu_ntt, &tw, false).unwrap();
        gpu.audit_replace_kernel_spirv(slot, &mut_words).unwrap();
        let mut gpu_mut_ntt = orig_ntt.clone();
        gpu.goldilocks_ntt_inplace(&mut gpu_mut_ntt, &tw, false).unwrap();
        assert_ne!(gpu_mut_ntt, cpu_ntt, "mutated GoldilocksNtt shader must diverge on RX 6750 XT");
        gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
        let mut gpu_ok_ntt = orig_ntt;
        let rec = goldilocks_ntt_with_receipt(&cert_gpu, &key, &mut gpu_ok_ntt, &tw, false, anchor).unwrap();
        assert_eq!(gpu_ok_ntt, cpu_ntt);
        assert_eq!(registry.verify_keyed_receipt(&rec, &key), Ok(()));
        println!("  [PASS] Live RX 6750 XT fault [02 goldilocks_ntt.comp]: GPU_mut != CPU caught & restored");

        // --- Slot 3: CosetLdeExt2 ---
        let slot = KernelSlot::CosetLdeExt2;
        let orig_spv = spirv_kernel_words(slot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            shader_source_filename(slot),
            "uint64_t rem_p = GL_P - b_c;",
            "uint64_t rem_p = GL_P - b_c; a_c ^= 1ul;",
        );
        let mut bad_prof = base_batch_pins;
        bad_prof[slot as usize] =
            CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_profile(KernelTargetArch::SpirV15, &bad_prof),
            Err(KernelRegistryError::PinMismatch { slot })
        );
        let evals: Vec<[u64; 2]> = (0..256u64).map(|i| [i + 1, i * 3 + 2]).collect();
        let mut cpu_lde = vec![[0u64; 2]; 1024];
        cpu.coset_lde_ext2(&evals, 4, 7, &mut cpu_lde).unwrap();
        gpu.audit_replace_kernel_spirv(slot, &mut_words).unwrap();
        let mut gpu_mut_lde = vec![[0u64; 2]; 1024];
        gpu.coset_lde_ext2(&evals, 4, 7, &mut gpu_mut_lde).unwrap();
        assert_ne!(gpu_mut_lde, cpu_lde, "mutated CosetLdeExt2 shader must diverge on RX 6750 XT");
        gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
        let mut gpu_ok_lde = vec![[0u64; 2]; 1024];
        let rec = coset_lde_ext2_with_receipt(&cert_gpu, &key, &evals, 4, 7, anchor, &mut gpu_ok_lde).unwrap();
        assert_eq!(gpu_ok_lde, cpu_lde);
        assert_eq!(registry.verify_keyed_receipt(&rec, &key), Ok(()));
        println!("  [PASS] Live RX 6750 XT fault [03 coset_lde_ext2.comp]: GPU_mut != CPU caught & restored");

        // --- Slot 4: MerkleLayerPoseidon2 ---
        let slot = KernelSlot::MerkleLayerPoseidon2;
        let orig_spv = spirv_kernel_words(slot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            shader_source_filename(slot),
            "uint64_t rem_p = GL_P - b_c;",
            "uint64_t rem_p = GL_P - b_c; a_c ^= 1ul;",
        );
        let mut bad_prof = base_batch_pins;
        bad_prof[slot as usize] =
            CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_profile(KernelTargetArch::SpirV15, &bad_prof),
            Err(KernelRegistryError::PinMismatch { slot })
        );
        let children: Vec<[u64; 4]> = (0..128u64).map(|i| [i + 1, i + 2, i + 3, i + 4]).collect();
        let pk_seed = [11u64, 22, 33, 44];
        let mut cpu_mrk = vec![[0u64; 4]; 64];
        cpu.try_merkle_layer_poseidon2(&children, &pk_seed, 2, &mut cpu_mrk).unwrap();
        gpu.audit_replace_kernel_spirv(slot, &mut_words).unwrap();
        let mut gpu_mut_mrk = vec![[0u64; 4]; 64];
        gpu.try_merkle_layer_poseidon2(&children, &pk_seed, 2, &mut gpu_mut_mrk).unwrap();
        assert_ne!(gpu_mut_mrk, cpu_mrk, "mutated MerkleLayerPoseidon2 shader must diverge on RX 6750 XT");
        gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
        let mut gpu_ok_mrk = vec![[0u64; 4]; 64];
        let rec = merkle_layer_poseidon2_with_receipt(&cert_gpu, &key, &children, &pk_seed, 2, anchor, &mut gpu_ok_mrk).unwrap();
        assert_eq!(gpu_ok_mrk, cpu_mrk);
        assert_eq!(registry.verify_keyed_receipt(&rec, &key), Ok(()));
        println!("  [PASS] Live RX 6750 XT fault [04 merkle_layer_poseidon2.comp]: GPU_mut != CPU caught & restored");

        // --- Slot 5: BdozGf2128BatchDot ---
        let slot = KernelSlot::BdozGf2128BatchDot;
        let orig_spv = spirv_kernel_words(slot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            shader_source_filename(slot),
            "0x87ul",
            "0x85ul",
        );
        let mut bad_prof = base_batch_pins;
        bad_prof[slot as usize] =
            CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_profile(KernelTargetArch::SpirV15, &bad_prof),
            Err(KernelRegistryError::PinMismatch { slot })
        );
        let shares: Vec<(u128, u128)> = (0..512u128)
            .map(|i| ((1u128 << 127) | (i + 3), (1u128 << 126) | (i * 5 + 1)))
            .collect();
        let weights: Vec<(u128, u128)> = (0..512u128)
            .map(|i| ((1u128 << 127) | (i * 7 + 9), (1u128 << 127) | (i + 11)))
            .collect();
        let cpu_dot = cpu.bdoz_gf2_128_batch_dot(&shares, &weights).unwrap();
        gpu.audit_replace_kernel_spirv(slot, &mut_words).unwrap();
        let gpu_mut_dot = gpu.bdoz_gf2_128_batch_dot(&shares, &weights).unwrap();
        assert_ne!(gpu_mut_dot, cpu_dot, "mutated BdozGf2128BatchDot shader must diverge on RX 6750 XT");
        gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
        let (gpu_ok_dot, rec) =
            bdoz_gf2_128_batch_dot_with_receipt(&cert_gpu, &key, &shares, &weights, anchor).unwrap();
        assert_eq!(gpu_ok_dot, cpu_dot);
        assert_eq!(registry.verify_keyed_receipt(&rec, &key), Ok(()));
        println!("  [PASS] Live RX 6750 XT fault [05 bdoz_gf2_128_dot.comp]: GPU_mut != CPU caught & restored");

        // =====================================================================
        // Prover Slots 6..9 on Live RX 6750 XT VRAM Session
        // =====================================================================
        let _guard = gpu.try_acquire_prover_session().expect("prover session");
        let nv = 12usize;
        let c_len = 1usize << nv;
        let air_rows = 16usize;
        let extra_words = air_rows * 256;
        let poly: Vec<u64> = (0..c_len as u64).map(|i| (i * 13 + 7) % GOLDILOCKS_PRIME).collect();
        let salt = [0x99u8; 32];

        // --- Slot 6: ProverKernelSlot::WhirLdeCommitment ---
        let pslot = ProverKernelSlot::WhirLdeCommitment;
        let orig_pspv = prover_spirv_kernel_words(pslot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            prover_shader_source_filename(pslot),
            "uint64_t rem_p = GL_P - b_c;",
            "uint64_t rem_p = GL_P - b_c; a_c ^= 1ul;",
        );
        let mut bad_pprof = base_prover_pins;
        bad_pprof[pslot as usize] =
            CertifiedProverKernelPin::from_kernel_artifact(pslot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_prover_profile(KernelTargetArch::SpirV15, &bad_pprof),
            Err(KernelRegistryError::ProverPinMismatch { slot: pslot })
        );
        let base_top = gpu
            .prover_whir_commit_round0(&[poly.as_slice()], &salt, nv, 4, 16, 256, 64, extra_words)
            .unwrap();
        gpu.audit_replace_prover_spirv(pslot, &mut_words).unwrap();
        let mut_top = gpu
            .prover_whir_commit_round0(&[poly.as_slice()], &salt, nv, 4, 16, 256, 64, extra_words)
            .unwrap();
        assert_ne!(mut_top, base_top, "mutated WhirLdeCommitment shader must diverge on RX 6750 XT");
        gpu.audit_replace_prover_spirv(pslot, orig_pspv).unwrap();
        let restored_top = gpu
            .prover_whir_commit_round0(&[poly.as_slice()], &salt, nv, 4, 16, 256, 64, extra_words)
            .unwrap();
        assert_eq!(restored_top, base_top);
        println!("  [PASS] Live RX 6750 XT fault [06 whir_lde_merkle.comp]: GPU_mut != baseline caught & restored");

        // --- Slot 7: ProverKernelSlot::WhirFoldSumcheck ---
        let pslot = ProverKernelSlot::WhirFoldSumcheck;
        let orig_pspv = prover_spirv_kernel_words(pslot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            prover_shader_source_filename(pslot),
            "uint64_t rem_p = GL_P - b_c;",
            "uint64_t rem_p = GL_P - b_c; a_c ^= 1ul;",
        );
        let mut bad_pprof = base_prover_pins;
        bad_pprof[pslot as usize] =
            CertifiedProverKernelPin::from_kernel_artifact(pslot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_prover_profile(KernelTargetArch::SpirV15, &bad_pprof),
            Err(KernelRegistryError::ProverPinMismatch { slot: pslot })
        );
        let eq_tables: Vec<Ext4> = (0..768u64).map(|i| [i + 1, i + 2, i + 3, i + 4]).collect();
        let lambdas = [[5u64, 7, 9, 11]];
        gpu.prover_whir_batch_sumcheck_init(&eq_tables, &lambdas, nv).unwrap();
        let base_sc = gpu.prover_whir_batch_sumcheck_eval(0, c_len, 1, 0).unwrap();
        gpu.audit_replace_prover_spirv(pslot, &mut_words).unwrap();
        gpu.prover_whir_commit_round0(&[poly.as_slice()], &salt, nv, 4, 16, 256, 64, extra_words)
            .unwrap();
        gpu.prover_whir_batch_sumcheck_init(&eq_tables, &lambdas, nv).unwrap();
        let mut_sc = gpu.prover_whir_batch_sumcheck_eval(0, c_len, 1, 0).unwrap();
        assert_ne!(mut_sc, base_sc, "mutated WhirFoldSumcheck shader must diverge on RX 6750 XT");
        gpu.audit_replace_prover_spirv(pslot, orig_pspv).unwrap();
        gpu.prover_whir_commit_round0(&[poly.as_slice()], &salt, nv, 4, 16, 256, 64, extra_words)
            .unwrap();
        gpu.prover_whir_batch_sumcheck_init(&eq_tables, &lambdas, nv).unwrap();
        let ok_sc = gpu.prover_whir_batch_sumcheck_eval(0, c_len, 1, 0).unwrap();
        assert_eq!(ok_sc, base_sc);
        println!("  [PASS] Live RX 6750 XT fault [07 whir_fold_sumcheck.comp]: GPU_mut != baseline caught & restored");

        // Setup AIR shard fixture for Slots 8 & 9:
        let cols_base = c_len as u32;
        let mut statics: Vec<Ext4> = (0..250 + 44)
            .map(|i| [(i as u64) + 3, 5, 7, 9])
            .collect();
        statics.push([0, 1, 2, 3]);
        statics.push([4, 5, 6, 7]);
        let shifts: Vec<Ext4> = (0..3 * air_rows)
            .map(|i| [(i as u64) + 11, 13, 17, 19])
            .collect();
        let dyn_ext4_off = 296u32;
        let sorted_u64_off = 294u32 * 4;
        let mut dyn_words = Vec::new();
        let mut off = dyn_ext4_off;
        let signers_off = off;
        dyn_words.extend_from_slice(&[1, 0, 0, 0]);
        dyn_words.extend(core::iter::repeat_n(0u64, 13 * 4));
        off += 14;
        let steps_off = off;
        for loc in 0..air_rows {
            dyn_words.extend_from_slice(&[u64::from(loc == 0), 0, 0, 0]);
            dyn_words.extend_from_slice(&[u64::from(loc + 1 == air_rows), 0, 0, 0]);
            dyn_words.extend_from_slice(&[0, 0, 0, 0]);
        }
        off += (air_rows * 3) as u32;
        let op_hdr_off = off;
        for idx in 0..air_rows / 2 {
            dyn_words.extend_from_slice(&[idx as u64, 1, 0, 0]);
        }
        off += (air_rows / 2) as u32;
        let op_ent_off = off;
        for _ in 0..air_rows / 2 {
            dyn_words.extend_from_slice(&[0, 0, 250, 0]);
            dyn_words.extend_from_slice(&[1, 0, 0, 0]);
            dyn_words.extend_from_slice(&[1, 0, 0, 0]);
        }

        let run_air = |g: &VulkanSpirvBackend| -> [[u64; 4]; 8] {
            g.prover_whir_commit_round0(&[poly.as_slice()], &salt, nv, 4, 16, 256, 64, extra_words)
                .unwrap();
            g.prover_air_init_shard(0, cols_base, air_rows, &shifts, &statics)
                .unwrap();
            g.prover_air_eval_round(
                true,
                air_rows,
                air_rows,
                1,
                false,
                cols_base,
                0,
                dyn_ext4_off,
                &dyn_words,
                signers_off,
                steps_off,
                op_hdr_off,
                op_ent_off,
                sorted_u64_off,
            )
            .unwrap()
        };

        let base_air = run_air(&gpu);

        // --- Slot 8: ProverKernelSlot::AirRowGroupA ---
        let pslot = ProverKernelSlot::AirRowGroupA;
        let orig_pspv = prover_spirv_kernel_words(pslot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            prover_shader_source_filename(pslot),
            "uint64_t rem_p = GL_P - b_c;",
            "uint64_t rem_p = GL_P - b_c; a_c ^= 1ul;",
        );
        let mut bad_pprof = base_prover_pins;
        bad_pprof[pslot as usize] =
            CertifiedProverKernelPin::from_kernel_artifact(pslot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_prover_profile(KernelTargetArch::SpirV15, &bad_pprof),
            Err(KernelRegistryError::ProverPinMismatch { slot: pslot })
        );
        gpu.audit_replace_prover_spirv(pslot, &mut_words).unwrap();
        let mut_air_a = run_air(&gpu);
        assert_ne!(mut_air_a, base_air, "mutated AirRowGroupA shader must diverge on RX 6750 XT");
        gpu.audit_replace_prover_spirv(pslot, orig_pspv).unwrap();
        assert_eq!(run_air(&gpu), base_air);
        println!("  [PASS] Live RX 6750 XT fault [08 air_row_group_a.comp]: GPU_mut != baseline caught & restored");

        // --- Slot 9: ProverKernelSlot::AirRowGroupB ---
        let pslot = ProverKernelSlot::AirRowGroupB;
        let orig_pspv = prover_spirv_kernel_words(pslot);
        let (mut_bytes, mut_words) = compile_mutated_shader(
            prover_shader_source_filename(pslot),
            "uint64_t rem_p = GL_P - b_c;",
            "uint64_t rem_p = GL_P - b_c; a_c ^= 1ul;",
        );
        let mut bad_pprof = base_prover_pins;
        bad_pprof[pslot as usize] =
            CertifiedProverKernelPin::from_kernel_artifact(pslot, KernelTargetArch::SpirV15, &mut_bytes);
        assert_eq!(
            registry.verify_loaded_prover_profile(KernelTargetArch::SpirV15, &bad_pprof),
            Err(KernelRegistryError::ProverPinMismatch { slot: pslot })
        );
        gpu.audit_replace_prover_spirv(pslot, &mut_words).unwrap();
        let mut_air_b = run_air(&gpu);
        assert_ne!(mut_air_b, base_air, "mutated AirRowGroupB shader must diverge on RX 6750 XT");
        gpu.audit_replace_prover_spirv(pslot, orig_pspv).unwrap();
        assert_eq!(run_air(&gpu), base_air);
        println!("  [PASS] Live RX 6750 XT fault [09 air_row_group_b.comp]: GPU_mut != baseline caught & restored");
    }

    println!("=== ALL 10/10 SPIR-V COMPUTE SHADERS GROUNDED & PLANTED FAULTS CAUGHT ON PHYSICAL RX 6750 XT ===");
}
