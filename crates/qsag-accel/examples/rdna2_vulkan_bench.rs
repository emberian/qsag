//! Hardware benchmark comparing discrete RDNA2 / SPIR-V GPU (`VulkanSpirvBackend`) against
//! `CpuReferenceBackend` across all 6 certified `AcceleratorBackend` kernels:
//!
//! ```bash
//! cargo run --release --package qsag-accel --features std --example rdna2_vulkan_bench
//! ```

#[cfg(not(feature = "std"))]
fn main() {
    panic!("run rdna2_vulkan_bench with `--features std`");
}

#[cfg(feature = "std")]
fn main() {
    use std::time::Instant;

    use qsag_accel::goldilocks::precompute_goldilocks_twiddles;
    use qsag_accel::{
        AcceleratorBackend, BackendAttestationKey, CertifiedBackend, CpuReferenceBackend,
        KernelSlot, KernelTargetArch, VerifiedKernelDigestRegistry, VulkanSpirvBackend,
    };

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn hex_short(bytes: &[u8; 32]) -> String {
        let mut s = String::with_capacity(16);
        for &b in &bytes[..8] {
            use core::fmt::Write;
            let _ = write!(&mut s, "{b:02x}");
        }
        s
    }

    let gpu_raw = match VulkanSpirvBackend::try_new_audited() {
        Ok(b) => b,
        Err(err) => {
            panic!("Discrete Vulkan SPIR-V GPU unavailable: {err}");
        }
    };

    let info = *gpu_raw.device_info();
    println!(
        "LDS limit: {} bytes; Wave32 required: {}",
        info.max_compute_shared_memory_size, info.wave32_required
    );
    for (slot, stats) in info.pipelines.iter().enumerate() {
        println!("Pipeline {slot}: {stats:?}");
    }
    let (api_maj, api_min, api_pat) = info.api_version_triple();
    let (drv_maj, drv_min, drv_pat) = info.driver_version_triple();

    println!("==========================================================================");
    println!("  QSAG Certified Zero-Dependency Vulkan / SPIR-V RDNA2 GPU Benchmark");
    println!("==========================================================================");
    println!("  Device Name   : {}", info.device_name());
    println!(
        "  PCI IDs       : vendor=0x{:04x}, device=0x{:04x} (type={})",
        info.vendor_id, info.device_id, info.device_type
    );
    println!(
        "  Vulkan API    : {}.{}.{} (raw=0x{:08x})",
        api_maj, api_min, api_pat, info.api_version
    );
    println!(
        "  Driver Ver    : {}.{}.{} (raw=0x{:08x})",
        drv_maj, drv_min, drv_pat, info.driver_version
    );
    println!(
        "  Limits        : maxStorageBufferRange={} B, maxPushConstants={} B, maxWGInvocations={}",
        info.max_storage_buffer_range,
        info.max_push_constants_size,
        info.max_compute_work_group_invocations
    );
    let audit_anchor = info.audit_evidence_digest();
    println!("  Audit digest  : {}..", hex_short(&audit_anchor));
    println!("--------------------------------------------------------------------------");

    let measured_pins = VulkanSpirvBackend::measure_embedded_spirv_pins();
    let mut registry = VerifiedKernelDigestRegistry::<4>::with_cpu_reference_pins();
    registry
        .register_measured_profile(KernelTargetArch::SpirV15, measured_pins)
        .expect("register measured SPIR-V pins");

    for slot in KernelSlot::ALL {
        let pin = measured_pins[slot.index()];
        println!(
            "  Pin {:<22} sha256={}.. p2[0]=0x{:016x}",
            format!("{slot:?}"),
            hex_short(&pin.sha256_digest),
            pin.poseidon2_digest[0]
        );
    }
    println!("--------------------------------------------------------------------------");

    let gpu = CertifiedBackend::try_new_measured(gpu_raw, &registry, &measured_pins)
        .expect("certified GPU backend");
    let cpu = CpuReferenceBackend::new();
    let gpu_key = BackendAttestationKey::derive(&[0x33; 32], b"bench-rdna2-gpu");

    let mut rng = 0x1337_C0DE_CAFE_F00Du64;

    // -------------------------------------------------------------------------
    // 1. Width-12 Goldilocks Poseidon2 Permutation (`262,144` states)
    // -------------------------------------------------------------------------
    let p2_n = 262_144usize;
    let p2_init: Vec<[u64; 12]> = (0..p2_n)
        .map(|_| core::array::from_fn(|_| splitmix64(&mut rng)))
        .collect();
    let mut p2_gpu = p2_init.clone();
    // Warmup to establish persistent staging + VRAM workspace buffers.
    gpu.batch_poseidon2_perm12(&mut p2_gpu);

    p2_gpu.copy_from_slice(&p2_init);
    let t0 = Instant::now();
    gpu.batch_poseidon2_perm12(&mut p2_gpu);
    let dt_p2_gpu = t0.elapsed().as_secs_f64();

    let mut p2_cpu = p2_init;
    let t0 = Instant::now();
    cpu.batch_poseidon2_perm12(&mut p2_cpu);
    let dt_p2_cpu = t0.elapsed().as_secs_f64();
    assert_eq!(p2_gpu, p2_cpu);
    println!(
        "  [1] Poseidon2-12 ({p2_n} perms)  | GPU: {:>7.2} ms ({:>6.2} M perms/s) | CPU: {:>8.2} ms ({:>5.2} M perms/s) | {:>5.1}x",
        dt_p2_gpu * 1e3,
        (p2_n as f64 / 1e6) / dt_p2_gpu,
        dt_p2_cpu * 1e3,
        (p2_n as f64 / 1e6) / dt_p2_cpu,
        dt_p2_cpu / dt_p2_gpu
    );

    // -------------------------------------------------------------------------
    // 2. Batch Keccak-f[1600] (`262,144` states)
    // -------------------------------------------------------------------------
    let kec_n = 262_144usize;
    let kec_init: Vec<[u64; 25]> = (0..kec_n)
        .map(|_| core::array::from_fn(|_| splitmix64(&mut rng)))
        .collect();
    let mut kec_gpu = kec_init.clone();
    gpu.batch_keccak_f1600(&mut kec_gpu);

    kec_gpu.copy_from_slice(&kec_init);
    let t0 = Instant::now();
    gpu.batch_keccak_f1600(&mut kec_gpu);
    let dt_kec_gpu = t0.elapsed().as_secs_f64();

    let mut kec_cpu = kec_init;
    let t0 = Instant::now();
    cpu.batch_keccak_f1600(&mut kec_cpu);
    let dt_kec_cpu = t0.elapsed().as_secs_f64();
    assert_eq!(kec_gpu, kec_cpu);
    println!(
        "  [2] Keccak-f[1600] ({kec_n} perms)| GPU: {:>7.2} ms ({:>6.2} M perms/s) | CPU: {:>8.2} ms ({:>5.2} M perms/s) | {:>5.1}x",
        dt_kec_gpu * 1e3,
        (kec_n as f64 / 1e6) / dt_kec_gpu,
        dt_kec_cpu * 1e3,
        (kec_n as f64 / 1e6) / dt_kec_cpu,
        dt_kec_cpu / dt_kec_gpu
    );

    // -------------------------------------------------------------------------
    // 3. Goldilocks Radix-2 NTT (`N = 2^20 = 1,048,576`, VRAM-resident stages)
    // -------------------------------------------------------------------------
    let ntt_n = 1usize << 20;
    let tw = precompute_goldilocks_twiddles(ntt_n).unwrap();
    let ntt_init: Vec<u64> = (0..ntt_n).map(|_| splitmix64(&mut rng)).collect();
    let mut ntt_gpu = ntt_init.clone();
    gpu.goldilocks_ntt_inplace(&mut ntt_gpu, &tw, false)
        .unwrap();

    ntt_gpu.copy_from_slice(&ntt_init);
    let t0 = Instant::now();
    gpu.goldilocks_ntt_inplace(&mut ntt_gpu, &tw, false)
        .unwrap();
    let dt_ntt_gpu = t0.elapsed().as_secs_f64();

    let mut ntt_cpu = ntt_init;
    let t0 = Instant::now();
    cpu.goldilocks_ntt_inplace(&mut ntt_cpu, &tw, false)
        .unwrap();
    let dt_ntt_cpu = t0.elapsed().as_secs_f64();
    assert_eq!(ntt_gpu, ntt_cpu);
    println!(
        "  [3] Goldilocks NTT (N = 2^20)    | GPU: {:>7.2} ms                  | CPU: {:>8.2} ms                 | {:>5.1}x",
        dt_ntt_gpu * 1e3,
        dt_ntt_cpu * 1e3,
        dt_ntt_cpu / dt_ntt_gpu
    );

    // -------------------------------------------------------------------------
    // 5. Poseidon2 Merkle Tree (`2^20 = 1,048,576` leaves -> `1,048,575` hashes)
    // -------------------------------------------------------------------------
    let num_leaves = 1usize << 20;
    let pk_seed = [0x1122_3344u64, 0x5566_7788, 0x99AA_BBCC, 0xDDEE_FF01];
    let leaves: Vec<[u64; 4]> = (0..num_leaves)
        .map(|_| core::array::from_fn(|_| splitmix64(&mut rng)))
        .collect();

    // Warmup & measure single-submission VRAM-resident 20-layer tree on GPU:
    let _ = gpu
        .inner()
        .build_merkle_tree_poseidon2(&leaves, &pk_seed, 0)
        .unwrap();
    let t0 = Instant::now();
    let gpu_tree_root = gpu
        .inner()
        .build_merkle_tree_poseidon2(&leaves, &pk_seed, 0)
        .unwrap();
    let dt_merkle_vram = t0.elapsed().as_secs_f64();

    // Also measure layer-by-layer `AcceleratorBackend::try_merkle_layer_poseidon2` + receipt on layer 0:
    let mut layer0_parents = vec![[0u64; 4]; num_leaves / 2];
    let receipt = CpuReferenceBackend::merkle_layer_poseidon2_with_receipt(
        &gpu,
        &gpu_key,
        &leaves,
        &pk_seed,
        0,
        audit_anchor,
        &mut layer0_parents,
    )
    .unwrap();
    assert_eq!(registry.verify_keyed_receipt(&receipt, &gpu_key), Ok(()));

    let t0 = Instant::now();
    let mut cur = leaves;
    let mut lvl = 0u32;
    while cur.len() > 1 {
        let mut next = vec![[0u64; 4]; cur.len() / 2];
        cpu.try_merkle_layer_poseidon2(&cur, &pk_seed, lvl, &mut next)
            .unwrap();
        cur = next;
        lvl += 1;
    }
    let dt_merkle_cpu = t0.elapsed().as_secs_f64();
    assert_eq!(gpu_tree_root, cur[0]);
    let merkle_hashes = (num_leaves - 1) as f64;
    println!(
        "  [5] Merkle Tree (2^20 leaves)    | GPU: {:>7.2} ms ({:>6.2} M hash/s)  | CPU: {:>8.2} ms ({:>5.2} M hash/s)  | {:>5.1}x",
        dt_merkle_vram * 1e3,
        (merkle_hashes / 1e6) / dt_merkle_vram,
        dt_merkle_cpu * 1e3,
        (merkle_hashes / 1e6) / dt_merkle_cpu,
        dt_merkle_cpu / dt_merkle_vram
    );

    // -------------------------------------------------------------------------
    // 6. BDOZ 2-Lane GF(2^128) Batch Inner Product (`262,144` pairs)
    // -------------------------------------------------------------------------
    let bdoz_n = 262_144usize;
    let shares: Vec<(u128, u128)> = (0..bdoz_n)
        .map(|_| {
            (
                (splitmix64(&mut rng) as u128) | ((splitmix64(&mut rng) as u128) << 64),
                (splitmix64(&mut rng) as u128) | ((splitmix64(&mut rng) as u128) << 64),
            )
        })
        .collect();
    let weights: Vec<(u128, u128)> = (0..bdoz_n)
        .map(|_| {
            (
                (splitmix64(&mut rng) as u128) | ((splitmix64(&mut rng) as u128) << 64),
                (splitmix64(&mut rng) as u128) | ((splitmix64(&mut rng) as u128) << 64),
            )
        })
        .collect();
    let _ = gpu.bdoz_gf2_128_batch_dot(&shares, &weights).unwrap();

    let t0 = Instant::now();
    let dot_gpu = gpu.bdoz_gf2_128_batch_dot(&shares, &weights).unwrap();
    let dt_bdoz_gpu = t0.elapsed().as_secs_f64();

    let t0 = Instant::now();
    let dot_cpu = cpu.bdoz_gf2_128_batch_dot(&shares, &weights).unwrap();
    let dt_bdoz_cpu = t0.elapsed().as_secs_f64();
    assert_eq!(dot_gpu, dot_cpu);
    println!(
        "  [6] BDOZ GF(2^128) Dot ({bdoz_n})  | GPU: {:>7.2} ms ({:>6.2} M pairs/s) | CPU: {:>8.2} ms ({:>5.2} M pairs/s) | {:>5.1}x",
        dt_bdoz_gpu * 1e3,
        (bdoz_n as f64 / 1e6) / dt_bdoz_gpu,
        dt_bdoz_cpu * 1e3,
        (bdoz_n as f64 / 1e6) / dt_bdoz_cpu,
        dt_bdoz_cpu / dt_bdoz_gpu
    );

    // Rows 1 and 2 time the infallible trait methods, which answer from the CPU reference
    // when the device fails. A GPU figure is only a GPU figure if that never happened.
    let cpu_fallbacks = gpu.cpu_fallback_count();
    println!("  CPU fallbacks on the infallible GPU path: {cpu_fallbacks}");
    assert_eq!(cpu_fallbacks, 0, "a timed GPU row was answered by the CPU");

    println!("--------------------------------------------------------------------------");
    println!(
        "  [PASS] 100% bit-exact GPU == CPU across all 6 kernels + keyed receipt OK (GPU submissions = {})",
        gpu.inner().gpu_submission_count()
    );
    println!("==========================================================================");
}
