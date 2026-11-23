//! Physical `AMD Radeon RX 6750 XT` (`gfx1030`) Grounding Suite:
//! 1. Cryptographic `VerifiedKernelDigestRegistry` 1-bit SPIR-V corruption rejection across all
//!    6 certified compute shaders (`KernelSlot`).
//! 2. Live physical `RX 6750 XT` compilation (`glslangValidator` -> RADV ACO `gfx1030`) and
//!    execution of planted semantic faults across ALL 6 `.comp` compute shaders, proving both
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
use qsag_accel::spirv_kernels::{shader_source_filename, spirv_kernel_bytes, spirv_kernel_words};
use qsag_accel::vulkan::{
    batch_keccak_f1600_with_receipt, batch_poseidon2_perm12_with_receipt,
    bdoz_gf2_128_batch_dot_with_receipt, coset_lde_ext2_with_receipt, goldilocks_ntt_with_receipt,
    merkle_layer_poseidon2_with_receipt,
};
use qsag_accel::{
    AcceleratorBackend, BackendAttestationKey, BatchJobDescriptor, CertifiedBackend,
    CertifiedKernelPin, CpuReferenceBackend, ExecutionReceipt, KernelRegistryError, KernelSlot,
    KernelTargetArch, VerifiedKernelDigestRegistry, VulkanSpirvBackend,
};

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

    let tmp_dir = std::env::temp_dir().join(format!("qsag_mut_spv_{}", std::process::id()));
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
fn test_all_6_spirv_pins_and_live_rx6750xt_faults() {
    let gpu = VulkanSpirvBackend::try_new_audited().expect("audited RX 6750 XT Vulkan backend");
    let info = gpu.device_info();
    println!(
        "=== Physical GPU Grounding on `{}` (vendor=0x{:04x}, device=0x{:04x}) ===",
        gpu.device_name(),
        gpu.vendor_id(),
        info.device_id
    );
    assert_eq!(info.secret_slot_audit(), Ok(()));
    assert!(gpu.secret_slots_audited());

    let registry = VerifiedKernelDigestRegistry::<4>::with_cpu_and_canonical_gpu_pins();
    let base_batch_pins = VulkanSpirvBackend::measure_embedded_spirv_pins();
    assert_eq!(
        registry.verify_loaded_profile(KernelTargetArch::SpirV15, &base_batch_pins),
        Ok(())
    );

    let key = BackendAttestationKey::derive(&[0xE1; 32], b"QSAG-RX6750XT-AUDIT");
    let wrong_key = BackendAttestationKey::derive(&[0xE2; 32], b"QSAG-RX6750XT-AUDIT");
    let audit_digest = gpu.hardware_audit_digest();
    assert_ne!(audit_digest, [0u8; 32]);

    // =========================================================================
    // 1. 1-bit SPIR-V instruction corruption rejection across all 6 slots
    // =========================================================================
    for slot in KernelSlot::ALL {
        let mut raw = spirv_kernel_bytes(slot).to_vec();
        let flip_idx = raw.len() - 4;
        raw[flip_idx] ^= 0x01;
        let bad_pin =
            CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &raw);
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
            KernelSlot::BatchPoseidon2Perm12 => {
                BatchJobDescriptor::Poseidon2Perm12 { num_states: 64 }
            }
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
            KernelSlot::BdozGf2128BatchDot => {
                BatchJobDescriptor::BdozGf2128BatchDot { num_elements: 256 }
            }
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
        let ok_rec = ExecutionReceipt::compute_audited(
            &key,
            &orig_pin,
            dummy_desc,
            [0xAA; 32],
            [0x11; 32],
            [0x22; 32],
            audit_digest,
        )
        .unwrap();
        assert_eq!(registry.verify_keyed_receipt(&ok_rec, &key), Ok(()));
        assert_eq!(
            registry.verify_keyed_receipt(&ok_rec, &wrong_key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        );
        println!(
            "  [PASS] Batch slot {slot:?}: 1-bit SPIR-V corruption rejected by registry + receipt"
        );
    }

    // =========================================================================
    // 2. Live Physical `RX 6750 XT` Execution of 6 Semantic-Fault Shaders
    // =========================================================================
    let cpu = CpuReferenceBackend;
    let anchor = [0xEEu8; 32];
    let cert_gpu = CertifiedBackend::try_new_measured(gpu, &registry, &base_batch_pins).unwrap();
    let gpu = cert_gpu.inner();

    // --- Slot 0: BatchKeccakF1600 ---
    let slot = KernelSlot::BatchKeccakF1600;
    let orig_spv = spirv_kernel_words(slot);
    let (mut_bytes, mut_words) = compile_mutated_shader(
        shader_source_filename(slot),
        "0x0000000000000001ul",
        "0x0000000000000003ul",
    );
    let mut_pin =
        CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV15, &mut_bytes);
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
    assert_ne!(
        gpu_mut_st, cpu_st,
        "mutated Keccak shader must diverge on RX 6750 XT"
    );

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
    assert_ne!(
        gpu_mut_p2, cpu_p2,
        "mutated Poseidon2 shader must diverge on RX 6750 XT"
    );
    gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
    let mut gpu_ok_p2 = [[3u64; 12]; 64];
    let rec =
        batch_poseidon2_perm12_with_receipt(&cert_gpu, &key, &mut gpu_ok_p2, anchor).unwrap();
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
    cpu.goldilocks_ntt_inplace(&mut cpu_ntt, &tw, false)
        .unwrap();
    gpu.audit_replace_kernel_spirv(slot, &mut_words).unwrap();
    let mut gpu_mut_ntt = orig_ntt.clone();
    gpu.goldilocks_ntt_inplace(&mut gpu_mut_ntt, &tw, false)
        .unwrap();
    assert_ne!(
        gpu_mut_ntt, cpu_ntt,
        "mutated GoldilocksNtt shader must diverge on RX 6750 XT"
    );
    gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
    let mut gpu_ok_ntt = orig_ntt;
    let rec =
        goldilocks_ntt_with_receipt(&cert_gpu, &key, &mut gpu_ok_ntt, &tw, false, anchor).unwrap();
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
    assert_ne!(
        gpu_mut_lde, cpu_lde,
        "mutated CosetLdeExt2 shader must diverge on RX 6750 XT"
    );
    gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
    let mut gpu_ok_lde = vec![[0u64; 2]; 1024];
    let rec =
        coset_lde_ext2_with_receipt(&cert_gpu, &key, &evals, 4, 7, anchor, &mut gpu_ok_lde)
            .unwrap();
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
    cpu.try_merkle_layer_poseidon2(&children, &pk_seed, 2, &mut cpu_mrk)
        .unwrap();
    gpu.audit_replace_kernel_spirv(slot, &mut_words).unwrap();
    let mut gpu_mut_mrk = vec![[0u64; 4]; 64];
    gpu.try_merkle_layer_poseidon2(&children, &pk_seed, 2, &mut gpu_mut_mrk)
        .unwrap();
    assert_ne!(
        gpu_mut_mrk, cpu_mrk,
        "mutated MerkleLayerPoseidon2 shader must diverge on RX 6750 XT"
    );
    gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
    let mut gpu_ok_mrk = vec![[0u64; 4]; 64];
    let rec = merkle_layer_poseidon2_with_receipt(
        &cert_gpu,
        &key,
        &children,
        &pk_seed,
        2,
        anchor,
        &mut gpu_ok_mrk,
    )
    .unwrap();
    assert_eq!(gpu_ok_mrk, cpu_mrk);
    assert_eq!(registry.verify_keyed_receipt(&rec, &key), Ok(()));
    println!("  [PASS] Live RX 6750 XT fault [04 merkle_layer_poseidon2.comp]: GPU_mut != CPU caught & restored");

    // --- Slot 5: BdozGf2128BatchDot ---
    let slot = KernelSlot::BdozGf2128BatchDot;
    let orig_spv = spirv_kernel_words(slot);
    let (mut_bytes, mut_words) =
        compile_mutated_shader(shader_source_filename(slot), "0x87ul", "0x85ul");
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
    assert_ne!(
        gpu_mut_dot, cpu_dot,
        "mutated BdozGf2128BatchDot shader must diverge on RX 6750 XT"
    );
    gpu.audit_replace_kernel_spirv(slot, orig_spv).unwrap();
    let (gpu_ok_dot, rec) =
        bdoz_gf2_128_batch_dot_with_receipt(&cert_gpu, &key, &shares, &weights, anchor).unwrap();
    assert_eq!(gpu_ok_dot, cpu_dot);
    assert_eq!(registry.verify_keyed_receipt(&rec, &key), Ok(()));
    println!("  [PASS] Live RX 6750 XT fault [05 bdoz_gf2_128_dot.comp]: GPU_mut != CPU caught & restored");
}
