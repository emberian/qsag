//! Hardware differential, kernel-pin provenance, `ExecutionReceipt` authentication, and SPIR-V
//! reproducibility tests for `VulkanSpirvBackend` (`VulkanRdna2Backend`).

#![cfg(feature = "std")]

use std::path::Path;
use std::process::Command;

use qsag_accel::goldilocks::{
    GOLDILOCKS_PRIME, gl_reduce_u64, precompute_goldilocks_twiddles,
};
use qsag_accel::spirv_kernels::{shader_source_filename, spirv_kernel_bytes};
use qsag_accel::vulkan::{
    batch_keccak_f1600_with_receipt, batch_poseidon2_perm12_with_receipt,
    bdoz_gf2_128_batch_dot_with_receipt, coset_lde_ext2_with_receipt, goldilocks_ntt_input_digest,
    goldilocks_ntt_output_digest, goldilocks_ntt_with_receipt, merkle_layer_poseidon2_with_receipt,
};
use qsag_accel::{
    AccelError, AcceleratorBackend, BackendAttestationKey, CertifiedBackend, CertifiedKernelPin,
    CpuReferenceBackend, KernelRegistryError, KernelSlot, KernelTargetArch,
    VerifiedKernelDigestRegistry, VulkanError, VulkanRdna2Backend, VulkanSpirvBackend,
    spot_check_merkle_layer,
};

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

#[test]
fn test_spirv_shaders_reproducible_from_comp_sources() {
    let validator = Path::new("/usr/bin/glslangValidator");
    if !validator.exists() {
        return;
    }

    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let shaders_dir = manifest_dir.join("shaders");
    let out_dir = std::env::temp_dir().join(format!("qsag_spv_repro_{}", std::process::id()));
    std::fs::create_dir_all(&out_dir).expect("create temp shader dir");

    for slot in KernelSlot::ALL {
        let comp_name = shader_source_filename(slot);
        let comp_path = shaders_dir.join(comp_name);
        let spv_path = out_dir.join(format!("{comp_name}.spv"));

        let output = Command::new(validator)
            .args(["-V", "--target-env", "vulkan1.2"])
            .arg(&comp_path)
            .arg("-o")
            .arg(&spv_path)
            .output()
            .expect("invoke glslangValidator");
        assert!(
            output.status.success(),
            "glslangValidator failed on {comp_name}: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        let compiled = std::fs::read(&spv_path).expect("read compiled .spv");
        assert_eq!(
            compiled.as_slice(),
            spirv_kernel_bytes(slot),
            "embedded SPIR-V bytes drifted from shaders/{comp_name}"
        );
        assert_eq!(
            CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::SpirV16, &compiled),
            VulkanSpirvBackend::canonical_pin(slot),
            "canonical CertifiedKernelPin mismatch for {slot:?}"
        );
    }

    let _ = std::fs::remove_dir_all(&out_dir);
}

#[test]
fn test_vulkan_rdna2_bit_exact_differential_and_receipts() {
    let gpu = match VulkanRdna2Backend::try_new() {
        Ok(b) => b,
        Err(
            VulkanError::UnsupportedPlatform
            | VulkanError::LibraryLoadFailed
            | VulkanError::NoDiscreteGpuFound,
        ) => {
            return;
        }
        Err(other) => panic!("unexpected Vulkan initialization error: {other}"),
    };

    // 1. Hardware metadata & discrete GPU checks.
    let info = gpu.device_info();
    assert!(!gpu.device_name().is_empty());
    assert_eq!(info.device_type, 2, "expected VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU");
    assert!(gpu.vendor_id() != 0);
    assert!(gpu.driver_version() != 0);
    assert_eq!(gpu.target_arch(), KernelTargetArch::SpirV16);
    println!(
        "Bound discrete Vulkan GPU: {} (vendor=0x{:04x}, device=0x{:04x}, driver=0x{:08x})",
        gpu.device_name(),
        gpu.vendor_id(),
        info.device_id,
        gpu.driver_version()
    );

    // 2. Registry pinning & negative loader-measurement checks.
    let mut registry = VerifiedKernelDigestRegistry::<4>::with_cpu_reference_pins();
    let measured_pins = VulkanSpirvBackend::measure_embedded_spirv_pins();
    registry
        .register_measured_profile(KernelTargetArch::SpirV16, measured_pins)
        .expect("register SpirV16 profile");
    assert_eq!(
        VerifiedKernelDigestRegistry::<4>::with_cpu_and_spirv_pins().verify_backend(&gpu),
        Ok(())
    );

    let mut bad_pins = measured_pins;
    bad_pins[KernelSlot::GoldilocksNtt as usize] = CertifiedKernelPin::from_kernel_artifact(
        KernelSlot::GoldilocksNtt,
        KernelTargetArch::SpirV16,
        b"CORRUPTED_SPIRV_BINARY",
    );
    assert_eq!(
        registry.verify_loaded_profile(KernelTargetArch::SpirV16, &bad_pins),
        Err(KernelRegistryError::PinMismatch {
            slot: KernelSlot::GoldilocksNtt
        })
    );

    // Malformed shapes must fail BEFORE touching the GPU (`gpu_submission_count` unchanged).
    let subs_before_errors = gpu.gpu_submission_count();
    assert_eq!(subs_before_errors, 0);
    let mut bad_ntt = [1u64, 2, 3];
    assert_eq!(
        gpu.goldilocks_ntt_inplace(&mut bad_ntt, &[1], false),
        Err(AccelError::NotPowerOfTwo {
            what: "NTT buffer",
            len: 3,
        })
    );
    let mut bad_parents = [[0u64; 4]; 2];
    assert_eq!(
        gpu.try_merkle_layer_poseidon2(&[[0u64; 4]; 3], &[1, 2, 3, 4], 0, &mut bad_parents),
        Err(AccelError::LengthMismatch {
            what: "Merkle layer children",
            expected: 4,
            actual: 3,
        })
    );
    assert_eq!(
        gpu.bdoz_gf2_128_batch_dot(&[(1, 2)], &[]),
        Err(AccelError::LengthMismatch {
            what: "BDOZ batch dot weights",
            expected: 1,
            actual: 0,
        })
    );
    assert_eq!(gpu.gpu_submission_count(), 0);

    // Wrap inside `CertifiedBackend` with independent loader measurements.
    let unmeasured_err = CertifiedBackend::try_new(gpu, &registry).err();
    assert_eq!(
        unmeasured_err,
        Some(KernelRegistryError::LoaderMeasurementRequired)
    );
    let gpu = VulkanRdna2Backend::try_new().expect("re-open discrete GPU");
    let certified_gpu = CertifiedBackend::try_new_measured(gpu, &registry, &measured_pins)
        .expect("certified GPU backend with verified SPIR-V loader pins");

    let cpu = CpuReferenceBackend::new();
    let gpu_key = BackendAttestationKey::derive(&[0x5A; 32], b"rdna2-spirv-gpu-0");
    let cpu_key = BackendAttestationKey::derive(&[0x5A; 32], b"cpu-reference-0");
    let anchor = [0xA5u8; 32];
    let mut rng = 0xDEAD_BEEF_CAFE_BABEu64;

    // -------------------------------------------------------------------------
    // Kernel 1: BatchKeccakF1600 (`4,096` states + edge cases)
    // -------------------------------------------------------------------------
    let mut keccak_gpu: Vec<[u64; 25]> = (0..4096)
        .map(|i| {
            core::array::from_fn(|lane| match (i, lane) {
                (0, _) => 0,
                (1, _) => u64::MAX,
                _ => splitmix64(&mut rng),
            })
        })
        .collect();
    let mut keccak_cpu = keccak_gpu.clone();
    let subs0 = certified_gpu.inner().gpu_submission_count();
    let r_keccak_gpu =
        batch_keccak_f1600_with_receipt(&certified_gpu, &gpu_key, &mut keccak_gpu, anchor).unwrap();
    let r_keccak_cpu =
        batch_keccak_f1600_with_receipt(&cpu, &cpu_key, &mut keccak_cpu, anchor).unwrap();
    assert_eq!(certified_gpu.inner().gpu_submission_count(), subs0 + 1);
    assert_eq!(keccak_gpu, keccak_cpu, "BatchKeccakF1600 GPU != CPU");
    assert_eq!(r_keccak_gpu.input_digest, r_keccak_cpu.input_digest);
    assert_eq!(r_keccak_gpu.output_digest, r_keccak_cpu.output_digest);
    assert_eq!(registry.verify_keyed_receipt(&r_keccak_gpu, &gpu_key), Ok(()));
    assert_eq!(registry.verify_keyed_receipt(&r_keccak_cpu, &cpu_key), Ok(()));

    // -------------------------------------------------------------------------
    // Kernel 2: BatchPoseidon2Perm12 (`65,536` states incl. non-canonical >= p)
    // -------------------------------------------------------------------------
    let mut p2_gpu: Vec<[u64; 12]> = (0..65_536)
        .map(|i| {
            core::array::from_fn(|lane| match i {
                0 => 0,
                1 => GOLDILOCKS_PRIME - 1,
                2 => GOLDILOCKS_PRIME,
                3 => GOLDILOCKS_PRIME + (lane as u64),
                4 => u64::MAX - (lane as u64),
                _ => splitmix64(&mut rng),
            })
        })
        .collect();
    let mut p2_cpu = p2_gpu.clone();
    let subs1 = certified_gpu.inner().gpu_submission_count();
    let r_p2_gpu =
        batch_poseidon2_perm12_with_receipt(&certified_gpu, &gpu_key, &mut p2_gpu, anchor).unwrap();
    let r_p2_cpu = batch_poseidon2_perm12_with_receipt(&cpu, &cpu_key, &mut p2_cpu, anchor).unwrap();
    assert_eq!(certified_gpu.inner().gpu_submission_count(), subs1 + 1);
    assert_eq!(p2_gpu, p2_cpu, "BatchPoseidon2Perm12 (65,536 states) GPU != CPU");
    assert_eq!(r_p2_gpu.output_digest, r_p2_cpu.output_digest);
    assert_eq!(registry.verify_keyed_receipt(&r_p2_gpu, &gpu_key), Ok(()));

    // -------------------------------------------------------------------------
    // Kernel 3: GoldilocksNtt (`N = 1, 2, 16, 2^10, 2^16, 2^20` forward & inverse)
    // -------------------------------------------------------------------------
    for &log2_n in &[0u32, 1, 4, 10, 16, 20] {
        let n = 1usize << log2_n;
        let tw = precompute_goldilocks_twiddles(n).unwrap();
        let orig: Vec<u64> = (0..n)
            .map(|i| match i {
                0 => u64::MAX,
                1 => GOLDILOCKS_PRIME,
                2 => GOLDILOCKS_PRIME - 1,
                _ => splitmix64(&mut rng),
            })
            .collect();
        let mut gpu_buf = orig.clone();
        let mut cpu_buf = orig.clone();

        let subs_before = certified_gpu.inner().gpu_submission_count();
        let r_ntt_gpu = goldilocks_ntt_with_receipt(
            &certified_gpu,
            &gpu_key,
            &mut gpu_buf,
            &tw,
            false,
            anchor,
        )
        .unwrap();
        let r_ntt_cpu =
            goldilocks_ntt_with_receipt(&cpu, &cpu_key, &mut cpu_buf, &tw, false, anchor).unwrap();
        assert_eq!(certified_gpu.inner().gpu_submission_count(), subs_before + 1);
        assert_eq!(gpu_buf, cpu_buf, "Forward GoldilocksNtt mismatch at N = 2^{log2_n}");
        assert_eq!(r_ntt_gpu.output_digest, r_ntt_cpu.output_digest);
        assert_eq!(registry.verify_keyed_receipt(&r_ntt_gpu, &gpu_key), Ok(()));

        let r_intt_gpu = goldilocks_ntt_with_receipt(
            &certified_gpu,
            &gpu_key,
            &mut gpu_buf,
            &tw,
            true,
            anchor,
        )
        .unwrap();
        let r_intt_cpu =
            goldilocks_ntt_with_receipt(&cpu, &cpu_key, &mut cpu_buf, &tw, true, anchor).unwrap();
        assert_eq!(gpu_buf, cpu_buf, "Inverse GoldilocksNtt mismatch at N = 2^{log2_n}");
        assert_eq!(r_intt_gpu.output_digest, r_intt_cpu.output_digest);
        assert_eq!(registry.verify_keyed_receipt(&r_intt_gpu, &gpu_key), Ok(()));
        for (idx, (&got, &raw)) in gpu_buf.iter().zip(&orig).enumerate() {
            assert_eq!(got, gl_reduce_u64(raw), "NTT roundtrip mismatch at N=2^{log2_n} idx={idx}");
        }
    }

    // -------------------------------------------------------------------------
    // Kernel 4: CosetLdeExt2 (`(1, 4)`, `(2^10, 4)`, `(2^14, 4)`, `(2^18, 4 -> 2^20)`)
    // -------------------------------------------------------------------------
    for &(log2_n, blowup, shift) in &[(0u32, 4usize, 7u64), (10, 4, 7), (14, 4, 42), (18, 4, 7)] {
        let n = 1usize << log2_n;
        let m = n * blowup;
        let evals: Vec<[u64; 2]> = (0..n)
            .map(|_| [splitmix64(&mut rng), splitmix64(&mut rng)])
            .collect();
        let mut gpu_out = vec![[0u64; 2]; m];
        let mut cpu_out = vec![[0u64; 2]; m];

        let subs_before = certified_gpu.inner().gpu_submission_count();
        let r_lde_gpu = coset_lde_ext2_with_receipt(
            &certified_gpu,
            &gpu_key,
            &evals,
            blowup,
            shift,
            anchor,
            &mut gpu_out,
        )
        .unwrap();
        let r_lde_cpu =
            coset_lde_ext2_with_receipt(&cpu, &cpu_key, &evals, blowup, shift, anchor, &mut cpu_out)
                .unwrap();
        assert_eq!(certified_gpu.inner().gpu_submission_count(), subs_before + 1);
        assert_eq!(
            gpu_out, cpu_out,
            "CosetLdeExt2 mismatch at N=2^{log2_n}, blowup={blowup}"
        );
        assert_eq!(r_lde_gpu.output_digest, r_lde_cpu.output_digest);
        assert_eq!(registry.verify_keyed_receipt(&r_lde_gpu, &gpu_key), Ok(()));
    }

    // -------------------------------------------------------------------------
    // Kernel 5: MerkleLayerPoseidon2 (`32,768` parents + offset `at` + full VRAM tree)
    // -------------------------------------------------------------------------
    let num_parents = 32_768usize;
    let children: Vec<[u64; 4]> = (0..num_parents * 2)
        .map(|_| core::array::from_fn(|_| splitmix64(&mut rng)))
        .collect();
    let pk_seed = [
        GOLDILOCKS_PRIME + 11,
        0x1234_5678_9ABC_DEF0,
        u64::MAX - 5,
        0xCAFE_F00D_DEAD_BEEF,
    ];
    let mut gpu_parents = vec![[0u64; 4]; num_parents];
    let mut cpu_parents = vec![[0u64; 4]; num_parents];
    let r_merkle_gpu = merkle_layer_poseidon2_with_receipt(
        &certified_gpu,
        &gpu_key,
        &children,
        &pk_seed,
        7,
        anchor,
        &mut gpu_parents,
    )
    .unwrap();
    let r_merkle_cpu = merkle_layer_poseidon2_with_receipt(
        &cpu,
        &cpu_key,
        &children,
        &pk_seed,
        7,
        anchor,
        &mut cpu_parents,
    )
    .unwrap();
    assert_eq!(gpu_parents, cpu_parents, "MerkleLayerPoseidon2 GPU != CPU");
    assert_eq!(r_merkle_gpu.output_digest, r_merkle_cpu.output_digest);
    assert_eq!(registry.verify_keyed_receipt(&r_merkle_gpu, &gpu_key), Ok(()));
    assert!(spot_check_merkle_layer(
        &children,
        &pk_seed,
        7,
        0,
        &gpu_parents,
        &r_merkle_gpu.mac,
        64,
    ));

    // Also verify non-zero `start_parent_idx` and full VRAM-resident multi-layer Merkle tree.
    let mut gpu_at = vec![[0u64; 4]; 257];
    let mut cpu_at = vec![[0u64; 4]; 257];
    certified_gpu
        .try_merkle_layer_poseidon2_at(&children[..514], &pk_seed, 13, 0x9988_7766, &mut gpu_at)
        .unwrap();
    cpu.try_merkle_layer_poseidon2_at(&children[..514], &pk_seed, 13, 0x9988_7766, &mut cpu_at)
        .unwrap();
    assert_eq!(gpu_at, cpu_at, "MerkleLayerPoseidon2 (`start_parent_idx != 0`) GPU != CPU");

    // Full 14-layer (`16,384` leaves) VRAM-resident tree vs CPU layer-by-layer reference.
    let tree_leaves = &children[..16_384];
    let gpu_root = certified_gpu
        .inner()
        .build_merkle_tree_poseidon2(tree_leaves, &pk_seed, 0)
        .unwrap();
    let mut cur_layer = tree_leaves.to_vec();
    let mut lvl = 0u32;
    while cur_layer.len() > 1 {
        let mut next = vec![[0u64; 4]; cur_layer.len() / 2];
        cpu.try_merkle_layer_poseidon2(&cur_layer, &pk_seed, lvl, &mut next)
            .unwrap();
        cur_layer = next;
        lvl += 1;
    }
    assert_eq!(gpu_root, cur_layer[0], "VRAM-resident Merkle tree root GPU != CPU");

    // -------------------------------------------------------------------------
    // Kernel 6: BdozGf2128BatchDot (`65,536` 2-lane GF(2^128) elements)
    // -------------------------------------------------------------------------
    for &count in &[1usize, 257, 4096, 65_536] {
        let shares: Vec<(u128, u128)> = (0..count)
            .map(|i| match i {
                0 => (u128::MAX, 1u128 << 127),
                _ => (
                    (splitmix64(&mut rng) as u128) | ((splitmix64(&mut rng) as u128) << 64),
                    (splitmix64(&mut rng) as u128) | ((splitmix64(&mut rng) as u128) << 64),
                ),
            })
            .collect();
        let weights: Vec<(u128, u128)> = (0..count)
            .map(|i| match i {
                0 => (1u128 << 127, u128::MAX),
                _ => (
                    (splitmix64(&mut rng) as u128) | ((splitmix64(&mut rng) as u128) << 64),
                    (splitmix64(&mut rng) as u128) | ((splitmix64(&mut rng) as u128) << 64),
                ),
            })
            .collect();

        let (gpu_dot, r_bdoz_gpu) = bdoz_gf2_128_batch_dot_with_receipt(
            &certified_gpu,
            &gpu_key,
            &shares,
            &weights,
            anchor,
        )
        .unwrap();
        let (cpu_dot, r_bdoz_cpu) =
            bdoz_gf2_128_batch_dot_with_receipt(&cpu, &cpu_key, &shares, &weights, anchor).unwrap();
        assert_eq!(gpu_dot, cpu_dot, "BdozGf2128BatchDot mismatch at count={count}");
        assert_eq!(r_bdoz_gpu.output_digest, r_bdoz_cpu.output_digest);
        assert_eq!(registry.verify_keyed_receipt(&r_bdoz_gpu, &gpu_key), Ok(()));
    }

    // -------------------------------------------------------------------------
    // Regression checks on live hardware:
    // 1. Authenticated NTT receipts bind twiddles (`NTT_IN.V2`) and separate `[1, ω]` vs `[1, ω⁻¹]`.
    // 2. Merkle position framing rejects out-of-range `> u32::MAX` indices on both GPU and CPU,
    //    and matches bit-for-bit at the `u32::MAX` boundary.
    // -------------------------------------------------------------------------
    let omega: u64 = 281_474_976_710_656; // 2^48, primitive 4th root of unity mod p
    let omega_inv = qsag_accel::goldilocks::gl_inv_or_zero(omega);
    let tw_a = [1u64, omega];
    let tw_b = [1u64, omega_inv];
    let orig4 = [0u64, 1, 0, 0];
    let mut g_buf_a = orig4;
    let mut g_buf_b = orig4;
    let r_ntt_a =
        goldilocks_ntt_with_receipt(&certified_gpu, &gpu_key, &mut g_buf_a, &tw_a, false, anchor)
            .unwrap();
    let r_ntt_b =
        goldilocks_ntt_with_receipt(&certified_gpu, &gpu_key, &mut g_buf_b, &tw_b, false, anchor)
            .unwrap();
    assert_eq!(g_buf_a, [1, omega, GOLDILOCKS_PRIME - 1, omega_inv]);
    assert_eq!(g_buf_b, [1, omega_inv, GOLDILOCKS_PRIME - 1, omega]);
    assert_eq!(r_ntt_a.input_digest, goldilocks_ntt_input_digest(&orig4, &tw_a));
    assert_eq!(r_ntt_b.input_digest, goldilocks_ntt_input_digest(&orig4, &tw_b));
    assert_ne!(r_ntt_a.input_digest, r_ntt_b.input_digest);
    assert_eq!(r_ntt_a.output_digest, goldilocks_ntt_output_digest(&g_buf_a));

    let pair_children = [[11u64, 22, 33, 44], [55u64, 66, 77, 88]];
    let mut g_parent = [[0u64; 4]; 1];
    let mut c_parent = [[0u64; 4]; 1];
    for bad_idx in [
        0xb3ad_a0b1_b0bb_bacfu64,
        0xb3ad_a0b0_b0bb_bad0u64,
        (u32::MAX as u64) + 1,
    ] {
        assert_eq!(
            certified_gpu.try_merkle_layer_poseidon2_at(
                &pair_children,
                &pk_seed,
                0,
                bad_idx,
                &mut g_parent
            ),
            Err(AccelError::LengthOverflow)
        );
    }
    certified_gpu
        .try_merkle_layer_poseidon2_at(
            &pair_children,
            &pk_seed,
            0,
            u32::MAX as u64,
            &mut g_parent,
        )
        .unwrap();
    cpu.try_merkle_layer_poseidon2_at(
        &pair_children,
        &pk_seed,
        0,
        u32::MAX as u64,
        &mut c_parent,
    )
    .unwrap();
    assert_eq!(g_parent, c_parent);
}
