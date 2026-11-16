//! Live hardware verification for:
//! 1. Unified Poseidon2 Merkle GPU modes (`merkle_layer_poseidon2.comp` modes 1, 2, 3):
//!    - Mode 1: `qsag-agg` two-block full-`pk_seed` Poseidon2 sponge (`sig::merkle_node_hash`, `paper/qsag.typ:220`)
//!    - Mode 2: `qsag-agg` Poseidon2 WHIR Canopy internal node (`sponge::poseidon2_canopy_internal`, WHIR regimes 7 & 8)
//!    - Mode 3: `qsag-agg` fixed-tweak Weighted Jive (`zk_hem::recursive_whir::compress`)
//! 2. `num_vars = 25` (`K = 256` signers) and `num_vars = 26` (`K = 512` signers) 100% native
//!    VRAM WHIR sessions with 4-byte (`1,024`-entry) Kronecker tables (`whir_fold_sumcheck.comp` Mode 0).
//! 3. Keyed V5 `ProverExecutionReceipt` issuance & `VerifiedKernelDigestRegistry` verification
//!    across all 4 `ProverKernelSlot`s (`paper/qsag.typ:314, 460`).

#![cfg(feature = "std")]

use std::time::Instant;

use qsag_accel::goldilocks::{
    EXT4_ONE, EXT4_ZERO, GOLDILOCKS_PRIME, eq_kronecker_1024, ext4_add, ext4_mul, ext4_sub,
    geometric_kronecker_1024, gl_add, gl_mul, gl_reduce_u64, gl_sub, mono_kronecker_1024,
    pair_geometric_kronecker_2048,
};
use qsag_accel::keccak::{finalize_cshake256, init_cshake256};
use qsag_accel::poseidon2::{
    POSEIDON2_CANOPY_NODE_HI, POSEIDON2_CANOPY_ROOT_DOMAIN, POSEIDON2_CANOPY_SALT_DOMAIN,
    POSEIDON2_CONST_IV, POSEIDON2_FORS_NODE_DOMAIN, POSEIDON2_MERKLE_NODE_DOMAIN,
    Poseidon2Merkle2BlockAddr, merkle_layer_poseidon2_2block_at_cpu,
    merkle_layer_poseidon2_canopy_at_cpu, merkle_layer_poseidon2_fixed_tweak_cpu,
    poseidon2_canopy_root_cpu, poseidon2_canopy_tree_key_cpu, poseidon2_perm12,
};
use qsag_accel::{
    AcceleratorBackend, BackendAttestationKey, CertifiedBackend, CpuReferenceBackend,
    KernelTargetArch, ProverKernelSlot, VerifiedKernelDigestRegistry, VulkanError,
    VulkanSpirvBackend, prover_stage_io_digest,
};

type Ext4 = [u64; 4];

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn rand_gl(state: &mut u64) -> u64 {
    splitmix64(state) % GOLDILOCKS_PRIME
}

fn rand_ext4(state: &mut u64) -> Ext4 {
    core::array::from_fn(|_| rand_gl(state))
}

// The witness is indexed by the Boolean cube, not by a roots-of-unity domain.
// Evaluate its multilinear interpolation at (z, z^2, z^4, ...) directly, independently
// of the GPU's Mobius conversion, NTT and Kronecker expansion.
fn sparse_witness_ood(points: &[(usize, u64)], num_vars: usize, z: Ext4) -> Ext4 {
    let mut sum = EXT4_ZERO;
    for &(idx, value) in points {
        let mut term = [value, 0, 0, 0];
        let mut power = z;
        for bit in 0..num_vars {
            let basis = if idx & (1 << bit) == 0 {
                ext4_sub(EXT4_ONE, power)
            } else {
                power
            };
            term = ext4_mul(term, basis);
            power = ext4_mul(power, power);
        }
        sum = ext4_add(sum, term);
    }
    sum
}

/// Round-0 receipt input digest recomputed by a host that knows the witness and the public
/// arguments but nothing about how the engine chunks its uploads.
fn round0_input_digest(
    salt_seed: &[u8; 32],
    num_vars: usize,
    capacities: [usize; 3],
    sparse_witness: &[(usize, u64)],
) -> [u8; 32] {
    let slot = ProverKernelSlot::WhirLdeCommitment;
    let mut sp = init_cshake256(b"", slot.algorithm_domain());
    sp.absorb(&1u64.to_le_bytes());
    sp.absorb(&(num_vars as u64).to_le_bytes());
    let mut block = [0u8; 4096];
    for block_idx in 0..(8usize << num_vars) / block.len() {
        block.fill(0);
        let first_word = block_idx * (block.len() / 8);
        for &(idx, val) in sparse_witness {
            if let Some(at) = idx
                .checked_sub(first_word)
                .filter(|&at| at < block.len() / 8)
            {
                block[8 * at..8 * at + 8].copy_from_slice(&val.to_le_bytes());
            }
        }
        sp.absorb(&block);
    }
    finalize_cshake256(&mut sp, true);
    let mut witness_digest = [0u8; 32];
    sp.squeeze(&mut witness_digest);
    let caps = capacities.map(|c| (c as u64).to_le_bytes());
    prover_stage_io_digest(
        slot,
        0x01,
        0,
        &[salt_seed, &witness_digest, &caps[0], &caps[1], &caps[2]],
    )
}

fn backend() -> Option<VulkanSpirvBackend> {
    match VulkanSpirvBackend::try_new_audited() {
        Ok(gpu) => Some(gpu),
        Err(
            VulkanError::UnsupportedPlatform
            | VulkanError::LibraryLoadFailed
            | VulkanError::NoDiscreteGpuFound,
        ) => {
            assert!(
                std::env::var_os("QSAG_REQUIRE_GPU_AUDIT").is_none(),
                "required Vulkan GPU hardware unavailable"
            );
            None
        }
        Err(other) => panic!("unexpected Vulkan initialization error: {other}"),
    }
}

#[test]
fn merkle_shapes_singletons_and_last_layer_are_consistent() {
    let Some(gpu) = backend() else {
        return;
    };
    let seed = [1, 2, 3, 4];
    let leaves = [[5, 6, 7, 8]; 4];
    let addr = Poseidon2Merkle2BlockAddr {
        layer: 0xFFFE,
        tree_idx: u64::MAX,
        level: 0xFFFF,
        start_node_idx: u32::MAX as u64,
    };
    let mut parent = [[0; 4]; 1];
    gpu.try_merkle_layer_poseidon2_2block_at(
        &leaves[..2],
        POSEIDON2_MERKLE_NODE_DOMAIN,
        &seed,
        addr,
        &mut parent,
    )
    .unwrap();
    let mut reference = [[0; 4]; 1];
    merkle_layer_poseidon2_2block_at_cpu(
        &leaves[..2],
        POSEIDON2_MERKLE_NODE_DOMAIN,
        &seed,
        addr,
        &mut reference,
    )
    .unwrap();
    assert_eq!(parent, reference);
    assert!(
        gpu.try_merkle_layer_poseidon2_2block_at(
            &leaves,
            POSEIDON2_MERKLE_NODE_DOMAIN,
            &seed,
            addr,
            &mut [[0; 4]; 2]
        )
        .is_err()
    );
    assert!(
        gpu.try_merkle_layer_poseidon2_canopy_at(&leaves, &seed, u32::MAX as u64, &mut [[0; 4]; 2])
            .is_err()
    );
    assert!(
        gpu.try_merkle_layer_poseidon2_fixed_tweak(&leaves[..3], &seed, &mut parent)
            .is_err()
    );
    for n in [0, 3] {
        assert!(
            gpu.build_merkle_tree_poseidon2(&leaves[..n], &seed, 0)
                .is_err()
        );
        assert!(
            gpu.build_merkle_tree_poseidon2_2block(
                &leaves[..n],
                POSEIDON2_MERKLE_NODE_DOMAIN,
                &seed,
                0,
                0,
                0
            )
            .is_err()
        );
        assert!(
            gpu.build_canopy_tree_poseidon2(&leaves[..n], 0, seed, &mut vec![[0; 4]; 2 * n])
                .is_err()
        );
        assert!(
            gpu.build_canopy_tree_poseidon2_2block(
                &leaves[..n],
                POSEIDON2_MERKLE_NODE_DOMAIN,
                &seed,
                0,
                0,
                &mut vec![[0; 4]; 2 * n]
            )
            .is_err()
        );
    }
    let last = gpu
        .build_merkle_tree_poseidon2(&leaves[..2], &seed, u32::MAX)
        .unwrap();
    CpuReferenceBackend
        .try_merkle_layer_poseidon2_at(&leaves[..2], &seed, u32::MAX, 0, &mut reference)
        .unwrap();
    assert_eq!(last, reference[0]);
    assert!(
        gpu.build_merkle_tree_poseidon2(&leaves, &seed, u32::MAX)
            .is_err()
    );
    assert!(
        gpu.build_merkle_tree_poseidon2_2block(
            &leaves,
            POSEIDON2_MERKLE_NODE_DOMAIN,
            &seed,
            0,
            0,
            0xFFFF
        )
        .is_err()
    );
    let mut nodes = [[u64::MAX; 4]; 2];
    let root = gpu
        .build_canopy_tree_poseidon2(&leaves[..1], 255, seed, &mut nodes)
        .unwrap();
    assert_eq!(nodes, [[0; 4], leaves[0]]);
    assert_eq!(root, poseidon2_canopy_root_cpu(255, 0, seed, leaves[0]));
    assert_eq!(
        gpu.build_canopy_tree_poseidon2_2block(
            &leaves[..1],
            POSEIDON2_MERKLE_NODE_DOMAIN,
            &seed,
            0xFFFE,
            u64::MAX,
            &mut nodes
        )
        .unwrap(),
        leaves[0]
    );
    assert_eq!(nodes, [[0; 4], leaves[0]]);
}

/// Standalone specification of `qsag_agg::sig::merkle_node_hash` (`paper/qsag.typ:220`):
/// 2-block full-`pk_seed[0..4]` Poseidon2-12 node sponge binding `domain_tag`, `pk_seed`,
/// `(layer << 48) | (level << 32) | node_idx`, 64-bit `tree_idx`, `left[0..4]`, and `right[0..4]`.
#[allow(clippy::too_many_arguments)]
fn spec_qsag_agg_merkle_node_hash(
    domain_tag: u64,
    pk_seed: &[u64; 4],
    layer: u32,
    tree_idx: u64,
    level: u32,
    node_idx: u64,
    left: &[u64; 4],
    right: &[u64; 4],
) -> [u64; 4] {
    let meta0 = ((layer as u64) << 48) | ((level as u64) << 32) | (node_idx & 0xFFFF_FFFF);
    let mut st = [
        gl_reduce_u64(pk_seed[0]),
        gl_reduce_u64(pk_seed[1]),
        gl_reduce_u64(pk_seed[2]),
        gl_reduce_u64(pk_seed[3]),
        gl_reduce_u64(left[0]),
        gl_reduce_u64(left[1]),
        gl_reduce_u64(left[2]),
        gl_reduce_u64(left[3]),
        gl_reduce_u64(domain_tag),
        gl_reduce_u64(meta0),
        gl_reduce_u64(tree_idx & 0xFFFF_FFFF),
        gl_reduce_u64(tree_idx >> 32),
    ];
    poseidon2_perm12(&mut st);
    for i in 0..4 {
        st[i] = gl_add(st[i], right[i]);
    }
    st[4] = gl_add(st[4], 1);
    st[5] = gl_add(st[5], gl_reduce_u64(POSEIDON2_CONST_IV));
    poseidon2_perm12(&mut st);
    [st[0], st[1], st[2], st[3]]
}

/// Standalone specification of `qsag_agg::sponge::poseidon2_canopy_internal`:
/// Weighted Jive (`weights (1, 2, 4)`) with `tweak = [0x50324E44_00000000 | node_idx, tree_key[0..3]]`.
fn spec_qsag_agg_canopy_internal(
    tree_key: &[u64; 4],
    node_idx: u64,
    left: &[u64; 4],
    right: &[u64; 4],
) -> [u64; 4] {
    let tweak = [
        gl_reduce_u64(POSEIDON2_CANOPY_NODE_HI | (node_idx & 0xFFFF_FFFF)),
        gl_reduce_u64(tree_key[0]),
        gl_reduce_u64(tree_key[1]),
        gl_reduce_u64(tree_key[2]),
    ];
    let mut st = [
        left[0], left[1], left[2], left[3], right[0], right[1], right[2], right[3], tweak[0],
        tweak[1], tweak[2], tweak[3],
    ];
    poseidon2_perm12(&mut st);
    core::array::from_fn(|i| {
        let sum12 = gl_add(left[i], gl_mul(2, right[i]));
        gl_add(st[i], gl_add(sum12, gl_mul(4, tweak[i])))
    })
}

/// Standalone specification of `qsag_agg::zk_hem::recursive_whir::compress`.
fn spec_recursive_whir_compress(tweak: &[u64; 4], left: &[u64; 4], right: &[u64; 4]) -> [u64; 4] {
    let tw = tweak.map(gl_reduce_u64);
    let mut st = [
        left[0], left[1], left[2], left[3], right[0], right[1], right[2], right[3], tw[0], tw[1],
        tw[2], tw[3],
    ];
    poseidon2_perm12(&mut st);
    core::array::from_fn(|i| {
        let sum12 = gl_add(left[i], gl_mul(2, right[i]));
        gl_add(st[i], gl_add(sum12, gl_mul(4, tw[i])))
    })
}

#[test]
fn test_poseidon2_2block_canopy_and_fixed_tweak_gpu_parity_and_speedup() {
    let Some(gpu) = backend() else {
        return;
    };
    let mut rng = 0xC4A0_9912_55AA_7711u64;
    let pk_seed = rand_ext4(&mut rng);

    // 1. Mode 1: Two-Block Poseidon2 Node Sponge (`sig::merkle_node_hash`, `paper/qsag.typ:220`).
    for &(domain_tag, layer, tree_idx, level, start_node_idx, num_parents) in &[
        (
            POSEIDON2_MERKLE_NODE_DOMAIN,
            0u32,
            0x1234_5678_9ABCu64,
            0u32,
            0u64,
            1usize,
        ),
        (
            POSEIDON2_MERKLE_NODE_DOMAIN,
            3,
            0xCAFE_BABE_0001,
            7,
            19,
            257,
        ),
        (
            POSEIDON2_FORS_NODE_DOMAIN,
            0,
            0xDEAD_BEEF_9999,
            11,
            512,
            16_384,
        ),
    ] {
        let children: Vec<Ext4> = (0..2 * num_parents).map(|_| rand_ext4(&mut rng)).collect();
        let addr = Poseidon2Merkle2BlockAddr {
            layer,
            tree_idx,
            level,
            start_node_idx,
        };
        let mut gpu_out = vec![[0u64; 4]; num_parents];
        let mut cpu_out = vec![[0u64; 4]; num_parents];
        gpu.try_merkle_layer_poseidon2_2block_at(
            &children,
            domain_tag,
            &pk_seed,
            addr,
            &mut gpu_out,
        )
        .expect("GPU 2-block Merkle layer");
        merkle_layer_poseidon2_2block_at_cpu(&children, domain_tag, &pk_seed, addr, &mut cpu_out)
            .expect("CPU 2-block Merkle layer");
        assert_eq!(gpu_out, cpu_out, "GPU vs CPU 2-block layer mismatch");
        for i in [0, num_parents / 2, num_parents - 1] {
            let want = spec_qsag_agg_merkle_node_hash(
                domain_tag,
                &pk_seed,
                layer,
                tree_idx,
                level,
                start_node_idx + (i as u64),
                &children[2 * i],
                &children[2 * i + 1],
            );
            assert_eq!(gpu_out[i], want, "spec mismatch at parent {i}");
        }
    }

    // Full 2-block Merkle tree (`N = 2^18 = 262,144` leaves) in a single GPU submission vs CPU.
    {
        let n_leaves = 1usize << 18;
        let leaves: Vec<Ext4> = (0..n_leaves).map(|_| rand_ext4(&mut rng)).collect();
        let domain_tag = POSEIDON2_MERKLE_NODE_DOMAIN;
        let layer = 2u32;
        let tree_idx = 0x4242_1337u64;

        // Warmup buffer sizing so steady-state GPU vs CPU timing is measured cleanly.
        gpu.build_merkle_tree_poseidon2_2block(&leaves, domain_tag, &pk_seed, layer, tree_idx, 0)
            .expect("warmup 2-block full tree");

        let t_gpu = Instant::now();
        let gpu_root = gpu
            .build_merkle_tree_poseidon2_2block(&leaves, domain_tag, &pk_seed, layer, tree_idx, 0)
            .expect("GPU 2-block full tree");
        let gpu_ms = t_gpu.elapsed().as_secs_f64() * 1000.0;

        let t_cpu = Instant::now();
        let mut cur = leaves.clone();
        for lvl in 0..18u32 {
            let addr = Poseidon2Merkle2BlockAddr {
                layer,
                tree_idx,
                level: lvl,
                start_node_idx: 0,
            };
            let mut next = vec![[0u64; 4]; cur.len() / 2];
            merkle_layer_poseidon2_2block_at_cpu(&cur, domain_tag, &pk_seed, addr, &mut next)
                .expect("CPU 2-block tree layer");
            cur = next;
        }
        let cpu_ms = t_cpu.elapsed().as_secs_f64() * 1000.0;
        assert_eq!(gpu_root, cur[0], "2-block full tree root mismatch");

        // Also check 1-indexed 2-block Canopy tree on `2^14` leaves.
        let small_n = 1usize << 14;
        let mut canopy_nodes = vec![[0u64; 4]; 2 * small_n];
        let canopy_top = gpu
            .build_canopy_tree_poseidon2_2block(
                &leaves[..small_n],
                domain_tag,
                &pk_seed,
                1,
                99,
                &mut canopy_nodes,
            )
            .expect("GPU 2-block Canopy tree");
        let direct_root = gpu
            .build_merkle_tree_poseidon2_2block(&leaves[..small_n], domain_tag, &pk_seed, 1, 99, 0)
            .expect("GPU 2-block direct root");
        assert_eq!(canopy_top, direct_root);
        assert_eq!(canopy_nodes[1], direct_root);
        eprintln!(
            "BENCH_2BLOCK_MERKLE_262K gpu_ms={gpu_ms:.3} cpu_seq_ms={cpu_ms:.3} speedup={:.1}x",
            cpu_ms / gpu_ms.max(1e-6)
        );
    }

    // 2. Mode 2: Poseidon2 WHIR Canopy (`sponge::poseidon2_canopy_internal`, WHIR regimes 7 & 8)
    //    at `N = 2^20 = 1,048,576` leaves (`64 MiB` Canopy tree in 1 submission).
    {
        let stage_idx = 1u8;
        let tree_salt = rand_ext4(&mut rng);
        assert_eq!(POSEIDON2_CANOPY_SALT_DOMAIN, 0x5032_434E_534C_5401);
        assert_eq!(POSEIDON2_CANOPY_ROOT_DOMAIN, 0x5032_434E_524F_4F54);

        let n_leaves = 1usize << 20; // 1,048,576 leaves -> 2,097,152 Canopy nodes (64 MiB)
        let log_leaves = 20u8;
        let tree_key = poseidon2_canopy_tree_key_cpu(stage_idx, log_leaves, tree_salt);
        let leaves: Vec<Ext4> = (0..n_leaves).map(|_| rand_ext4(&mut rng)).collect();
        let mut gpu_nodes = vec![[0u64; 4]; 2 * n_leaves];

        // Pre-size VRAM / staging via a warmup pass so steady-state GPU vs CPU timing is clean.
        let mut warm_nodes = vec![[0u64; 4]; 2 * n_leaves];
        gpu.build_canopy_tree_poseidon2(&leaves, stage_idx, tree_salt, &mut warm_nodes)
            .expect("warmup Canopy tree");

        let t_gpu = Instant::now();
        let gpu_root = gpu
            .build_canopy_tree_poseidon2(&leaves, stage_idx, tree_salt, &mut gpu_nodes)
            .expect("GPU Poseidon2 WHIR Canopy tree (2^20 leaves)");
        let gpu_ms = t_gpu.elapsed().as_secs_f64() * 1000.0;

        let t_cpu = Instant::now();
        let mut cpu_nodes = vec![[0u64; 4]; 2 * n_leaves];
        cpu_nodes[n_leaves..2 * n_leaves].copy_from_slice(&leaves);
        let mut half = n_leaves >> 1;
        while half >= 1 {
            let (upper, lower) = cpu_nodes.split_at_mut(2 * half);
            merkle_layer_poseidon2_canopy_at_cpu(
                &lower[..2 * half],
                &tree_key,
                half as u64,
                &mut upper[half..2 * half],
            )
            .expect("CPU Canopy layer");
            half >>= 1;
        }
        let cpu_root = poseidon2_canopy_root_cpu(stage_idx, log_leaves, tree_salt, cpu_nodes[1]);
        let cpu_ms = t_cpu.elapsed().as_secs_f64() * 1000.0;

        assert_eq!(gpu_root, cpu_root, "WHIR Canopy commitment root mismatch");
        assert_eq!(gpu_nodes[1], cpu_nodes[1], "WHIR Canopy top_node mismatch");
        for idx in [
            1usize,
            2,
            3,
            511,
            512,
            n_leaves - 1,
            n_leaves,
            2 * n_leaves - 1,
        ] {
            assert_eq!(gpu_nodes[idx], cpu_nodes[idx], "Canopy node {idx} mismatch");
        }
        assert_eq!(
            gpu_nodes[1],
            spec_qsag_agg_canopy_internal(&tree_key, 1, &gpu_nodes[2], &gpu_nodes[3])
        );
        eprintln!(
            "BENCH_CANOPY_POSEIDON2_1M gpu_ms={gpu_ms:.3} cpu_seq_ms={cpu_ms:.3} speedup={:.1}x",
            cpu_ms / gpu_ms.max(1e-6)
        );
    }

    // 3. Mode 3: Fixed-tweak Weighted Jive (`zk_hem::recursive_whir::compress`) + CertifiedBackend.
    {
        let tweak = [0x5A4B_4845_4D5F_4D54u64, 0, 0, 0];
        let num_parents = 32_768usize;
        let children: Vec<Ext4> = (0..2 * num_parents).map(|_| rand_ext4(&mut rng)).collect();
        let mut gpu_out = vec![[0u64; 4]; num_parents];
        let mut cpu_out = vec![[0u64; 4]; num_parents];

        let reg = VerifiedKernelDigestRegistry::<4>::with_cpu_and_spirv_pins();
        let pins = VulkanSpirvBackend::measure_embedded_spirv_pins();
        let cert = CertifiedBackend::try_new_measured(gpu, &reg, &pins).expect("certified GPU");

        cert.try_merkle_layer_poseidon2_fixed_tweak(&children, &tweak, &mut gpu_out)
            .expect("GPU fixed-tweak Merkle layer");
        merkle_layer_poseidon2_fixed_tweak_cpu(&children, &tweak, &mut cpu_out)
            .expect("CPU fixed-tweak Merkle layer");
        assert_eq!(gpu_out, cpu_out);
        assert_eq!(
            gpu_out[num_parents - 1],
            spec_recursive_whir_compress(
                &tweak,
                &children[2 * (num_parents - 1)],
                &children[2 * (num_parents - 1) + 1]
            )
        );
        assert_eq!(
            CpuReferenceBackend.target_arch(),
            KernelTargetArch::CpuReference
        );
    }
}

/// Evaluate multilinear equality kernel `eq(r, idx)` at hypercube vertex `idx` (`0 <= idx < 2^nv`).
/// Matches `eq_kronecker_1024(r)`: bit `b` (`0 <= b < nv`) corresponds to `r[b]`.
fn eval_eq_at_index(r: &[Ext4], idx: usize) -> Ext4 {
    let mut acc = EXT4_ONE;
    for (b, &r_var) in r.iter().enumerate() {
        let factor = if ((idx >> b) & 1) == 1 {
            r_var
        } else {
            ext4_sub(EXT4_ONE, r_var)
        };
        acc = ext4_mul(acc, factor);
    }
    acc
}

#[test]
fn test_whir_nv25_and_nv26_vram_session_and_prover_v5_receipts() {
    let Some(gpu) = backend() else {
        return;
    };
    let reg = VerifiedKernelDigestRegistry::<4>::with_cpu_and_spirv_pins();
    let prover_pins = VulkanSpirvBackend::measure_embedded_prover_spirv_pins();
    assert_eq!(
        reg.verify_loaded_prover_profile(KernelTargetArch::SpirV15, &prover_pins),
        Ok(())
    );

    let key = BackendAttestationKey::derive(&[0xE4u8; 32], b"rx6750xt-subcarbon-e4");
    let anchor = [0x25u8; 32];
    let hw_digest = gpu.hardware_audit_digest();
    let mut rng = 0x2526_A11C_E5EE_D001u64;

    let session = gpu.try_acquire_prover_session()
        .expect("acquire prover session");

    // =========================================================================
    // Part A: `num_vars = 25` (`K = 256` signers) — 100% Native VRAM + V5 Receipts
    // =========================================================================
    let nv = 25usize;
    let c_len = 1usize << nv; // 33,554,432 base-field words (256 MiB)
    let blowup = 4usize; // 2^27 = 134,217,728 LDE codeword words (1.0 GiB)
    let group_arity = 64usize; // 2^21 = 2,097,152 Round-0 Canopy groups (128 MiB tree)
    let stage1_domain = 1usize << (nv - 4 + 2); // 2^23 Ext4 = 256 MiB
    let stage1_groups = stage1_domain / 16; // 2^19 groups
    let air_rows = 16usize;
    let extra_witness_words = air_rows * 256;
    let salt_seed = [0x91u8; 32];

    let sparse_eval_pts: [(usize, u64); 4] = [
        (0, rand_gl(&mut rng)),
        (3, rand_gl(&mut rng)),
        ((1usize << 24) + 14, rand_gl(&mut rng)), // even index -> contributes to ev0 with k3 == 1!
        ((1usize << 25) - 1, rand_gl(&mut rng)), // odd top index -> contributes to ev2 with k3 == 1!
    ];

    let t_r0 = Instant::now();
    let (top_r0, rec_r0) = gpu
        .prover_whir_commit_round0_with_receipt(
            &key,
            anchor,
            1,
            &salt_seed,
            nv,
            blowup,
            group_arity,
            stage1_domain,
            stage1_groups,
            extra_witness_words,
            |_poly_idx, pos, dst| {
                dst.fill(0);
                for &(idx, val) in &sparse_eval_pts {
                    if idx >= pos && idx < pos + dst.len() {
                        dst[idx - pos] = val;
                    }
                }
            },
        )
        .expect("nv=25 commit_round0_with_receipt");
    let r0_ms = t_r0.elapsed().as_secs_f64() * 1000.0;
    assert_ne!(top_r0, [0u8; 32]);
    assert_eq!(rec_r0.hardware_audit_digest, hw_digest);
    assert_eq!(reg.verify_prover_keyed_receipt(&rec_r0, &key), Ok(()));
    // This witness is uploaded in many staging chunks; the digest must not see them.
    assert_eq!(
        rec_r0.input_digest,
        round0_input_digest(
            &salt_seed,
            nv,
            [stage1_domain, stage1_groups, extra_witness_words],
            &sparse_eval_pts,
        )
    );
    assert_eq!(
        rec_r0.descriptor.slot(),
        ProverKernelSlot::WhirLdeCommitment
    );

    let r_chal: Vec<Ext4> = (0..nv).map(|_| rand_ext4(&mut rng)).collect();
    let eq_1024 = eq_kronecker_1024(&r_chal);
    let lambda = [rand_ext4(&mut rng)];
    let t_sc = Instant::now();
    gpu.prover_whir_batch_sumcheck_init(&eq_1024, &lambda, nv)
        .expect("nv=25 batch_sumcheck_init (1024-entry table)");
    let (ev0, ev2) = gpu
        .prover_whir_batch_sumcheck_eval(0, c_len, 1, 0)
        .expect("nv=25 batch_sumcheck_eval");
    let sc_ms = t_sc.elapsed().as_secs_f64() * 1000.0;

    let mut want_ev0 = EXT4_ZERO;
    let mut want_ev2 = EXT4_ZERO;
    let pairs_visited = [0usize, 1, (1usize << 23) + 7, (1usize << 24) - 1];
    for &pair_i in &pairs_visited {
        let i0 = 2 * pair_i;
        let i1 = 2 * pair_i + 1;
        let t0 = sparse_eval_pts
            .iter()
            .find(|&&(idx, _)| idx == i0)
            .map_or(0, |&(_, v)| v);
        let t1 = sparse_eval_pts
            .iter()
            .find(|&&(idx, _)| idx == i1)
            .map_or(0, |&(_, v)| v);
        let k0 = eval_eq_at_index(&r_chal, i0);
        let k1 = eval_eq_at_index(&r_chal, i1);
        want_ev0 = ext4_add(want_ev0, k0.map(|x| gl_mul(x, t0)));
        let t_at_2 = gl_sub(gl_add(t1, t1), t0);
        let k_at_2 = ext4_sub(ext4_add(k1, k1), k0);
        want_ev2 = ext4_add(want_ev2, k_at_2.map(|x| gl_mul(x, t_at_2)));
    }
    want_ev0 = ext4_mul(lambda[0], want_ev0);
    want_ev2 = ext4_mul(lambda[0], want_ev2);
    assert_eq!(
        ev0, want_ev0,
        "nv=25 batch_sumcheck ev0 mismatch (byte-3 Kronecker)"
    );
    assert_eq!(
        ev2, want_ev2,
        "nv=25 batch_sumcheck ev2 mismatch (byte-3 Kronecker)"
    );

    let z0 = rand_ext4(&mut rng);
    let z1 = rand_ext4(&mut rng);
    let z_ood_2048 = pair_geometric_kronecker_2048(EXT4_ONE, z0, EXT4_ONE, z1);
    let z0_pows: Vec<Ext4> = (0..nv)
        .scan(z0, |st, _| {
            let cur = *st;
            *st = ext4_mul(*st, *st);
            Some(cur)
        })
        .collect();
    let mono_z0_1024 = mono_kronecker_1024(&z0_pows);
    let geom_z0_1024 = geometric_kronecker_1024(EXT4_ONE, z0);
    assert_eq!(&mono_z0_1024[..768], &geom_z0_1024[..768]);
    assert_eq!(mono_z0_1024[768], geom_z0_1024[768]);
    assert_eq!(mono_z0_1024[769], geom_z0_1024[769]); // k3 == 1 (`gid` bit 24 set)

    let mut dot_z0 = [EXT4_ZERO; 1];
    gpu.prover_whir_expand_monomial_and_dot_1024(&mono_z0_1024, nv, 0, &mut dot_z0)
        .expect("nv=25 expand_monomial_and_dot_1024");

    let (evals_single, rec_open_single) = gpu
        .prover_whir_open_init_with_receipt(&key, anchor, nv, true, &[], &z_ood_2048)
        .expect("nv=25 open_init_with_receipt (single)");
    assert_eq!(
        evals_single[0], dot_z0[0],
        "nv=25 open_init vs expand_monomial_and_dot_1024 mismatch"
    );
    assert_eq!(
        reg.verify_prover_keyed_receipt(&rec_open_single, &key),
        Ok(())
    );

    let poly_w = rand_ext4(&mut rng);
    let mask_w = rand_ext4(&mut rng);
    let weights = [[poly_w, mask_w]];
    let t_open = Instant::now();
    let (evals_weighted, rec_open) = gpu
        .prover_whir_open_init_with_receipt(&key, anchor, nv, false, &weights, &z_ood_2048)
        .expect("nv=25 open_init_with_receipt (weighted + mask at 2^25)");
    let open_ms = t_open.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(reg.verify_prover_keyed_receipt(&rec_open, &key), Ok(()));
    assert_eq!(
        rec_open.descriptor.slot(),
        ProverKernelSlot::WhirFoldSumcheck
    );

    // Algebraic check of `P(z) * (poly_w + mask_w * z)` across all `2^25 + 1` coefficients
    // (`0 <= gid <= 2^25`, exercising `k3 = 0, 1, 2` including the shifted top coefficient at `gid = 2^25`):
    for (t, z_t) in [(0usize, z0), (1usize, z1)] {
        let factor = ext4_add(poly_w, ext4_mul(mask_w, z_t));
        let single_expected = sparse_witness_ood(&sparse_eval_pts, nv, z_t);
        assert_eq!(
            evals_single[t], single_expected,
            "nv=25 independent Mobius/OOD oracle"
        );
        let expected = ext4_mul(factor, single_expected);
        assert_eq!(
            evals_weighted[t], expected,
            "nv=25 weighted + shifted-X OOD evaluation {t} mismatch (gid = 0..=2^25, k3 = 0..=2)"
        );
    }

    let xi0 = rand_ext4(&mut rng);
    let xi1 = rand_ext4(&mut rng);
    let xi_z_2048 = pair_geometric_kronecker_2048(xi0, z0, xi1, z1);
    let k_len_0 = c_len + 2;
    gpu.prover_whir_add_ood_claims_1024(k_len_0, 0, &xi_z_2048)
        .expect("nv=25 add_ood_claims_1024");

    let t_fold = Instant::now();
    let ping_off = (c_len + 2) as u32;
    let mut cur_c_len = c_len + 2;
    let mut cur_k_len = c_len + 2;
    let mut c_src = 0u32;
    let mut k_src = 0u32;
    for r in 0..4usize {
        let pairs_ck = cur_c_len.min(cur_k_len) / 2;
        let pairs_c = cur_c_len / 2;
        let k_half = (cur_k_len.div_ceil(2)) as u32;
        let dst = if r % 2 == 0 { ping_off } else { 0 };
        let (_wa, rec_a) = gpu
            .prover_whir_fold_pass_a_with_receipt(&key, anchor, pairs_ck, c_src, k_src)
            .expect("nv=25 fold_pass_a");
        assert_eq!(reg.verify_prover_keyed_receipt(&rec_a, &key), Ok(()));
        let phi = rand_ext4(&mut rng);
        let (_wb, rec_b) = gpu
            .prover_whir_fold_pass_b_with_receipt(
                &key, anchor, pairs_c, c_src, k_src, k_half, dst, phi,
            )
            .expect("nv=25 fold_pass_b");
        assert_eq!(reg.verify_prover_keyed_receipt(&rec_b, &key), Ok(()));
        let m = cur_c_len.div_ceil(2);
        let norm = r == 3;
        let rec_c = gpu
            .prover_whir_fold_pass_c_with_receipt(
                &key,
                anchor,
                m,
                c_src,
                dst,
                rand_ext4(&mut rng),
                rand_ext4(&mut rng),
                rand_ext4(&mut rng),
                norm,
                if norm { m.max(k_half as usize) } else { 0 },
            )
            .expect("nv=25 fold_pass_c");
        assert_eq!(reg.verify_prover_keyed_receipt(&rec_c, &key), Ok(()));
        cur_c_len = m;
        cur_k_len = k_half as usize;
        c_src = if norm { 0 } else { dst };
        k_src = if norm { 0 } else { dst };
    }
    let fold4_ms = t_fold.elapsed().as_secs_f64() * 1000.0;

    let t_stg1 = Instant::now();
    let (top_s1, rec_s1) = gpu
        .prover_whir_commit_stage_with_receipt(&key, anchor, 1, cur_c_len, stage1_domain, 16)
        .expect("nv=25 commit_stage(1) with receipt");
    let stg1_ms = t_stg1.elapsed().as_secs_f64() * 1000.0;
    assert_ne!(top_s1, [0u8; 32]);
    assert_eq!(reg.verify_prover_keyed_receipt(&rec_s1, &key), Ok(()));

    let q_r0 = [0u64, 17, (1 << 20) + 5, (1 << 21) - 1];
    let sib_r0 = [2u64, 3, (1 << 21) + 1];
    let mut out_q_r0 = vec![0u64; 2 * q_r0.len() + group_arity * q_r0.len() + 4 * sib_r0.len()];
    let rec_g0 = gpu
        .prover_whir_gather_queries_with_receipt(
            &key,
            anchor,
            0,
            group_arity,
            1,
            1usize << 21,
            &q_r0,
            &sib_r0,
            &mut out_q_r0,
        )
        .expect("nv=25 gather_queries(stage=0) with receipt");
    assert_eq!(reg.verify_prover_keyed_receipt(&rec_g0, &key), Ok(()));

    let q_s1 = [0u64, (1 << 19) - 1];
    let sib_s1 = [2u64, 3];
    let mut out_q_s1 = vec![0u64; 4 * 16 * q_s1.len() + 4 * sib_s1.len()];
    let rec_g1 = gpu
        .prover_whir_gather_queries_with_receipt(
            &key,
            anchor,
            1,
            16,
            1,
            stage1_groups,
            &q_s1,
            &sib_s1,
            &mut out_q_s1,
        )
        .expect("nv=25 gather_queries(stage=1) with receipt");
    assert_eq!(reg.verify_prover_keyed_receipt(&rec_g1, &key), Ok(()));

    // Exercise AIR `AirRowGroupA` + `AirRowGroupB` V5 receipts inside the same session.
    {
        let mut statics: Vec<Ext4> = (0..250 + 44).map(|_| rand_ext4(&mut rng)).collect();
        statics.push([0, 1, 2, 3]);
        statics.push([4, 5, 6, 7]);
        let shifts: Vec<Ext4> = (0..3 * air_rows).map(|_| rand_ext4(&mut rng)).collect();
        let cols_base = c_len as u32;
        let rec_air_init = gpu
            .prover_air_init_shard_with_receipt(
                &key, anchor, 0, cols_base, air_rows, &shifts, &statics,
            )
            .expect("AIR init_shard_with_receipt");
        assert_eq!(reg.verify_prover_keyed_receipt(&rec_air_init, &key), Ok(()));
        assert_eq!(
            rec_air_init.descriptor.slot(),
            ProverKernelSlot::AirRowGroupA
        );

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
        let (_air_evals, [rec_ga, rec_gb]) = gpu
            .prover_air_eval_round_with_receipt(
                &key,
                anchor,
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
            .expect("AIR eval_round_with_receipt");
        assert_eq!(rec_ga.descriptor.slot(), ProverKernelSlot::AirRowGroupA);
        assert_eq!(rec_gb.descriptor.slot(), ProverKernelSlot::AirRowGroupB);
        assert_eq!(reg.verify_prover_keyed_receipt(&rec_ga, &key), Ok(()));
        assert_eq!(reg.verify_prover_keyed_receipt(&rec_gb, &key), Ok(()));

        // Even a dimension unused by this branch must be framed in each receipt:
        // changing cur_s keeps Group A's descriptor and numerical result unchanged.
        let (same_evals, [changed_ga, changed_gb]) = gpu
            .prover_air_eval_round_with_receipt(
                &key,
                anchor,
                true,
                air_rows,
                air_rows,
                2,
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
            .expect("AIR receipt with alternate signer dimension");
        assert_eq!(same_evals, _air_evals);
        assert_eq!(changed_ga.descriptor, rec_ga.descriptor);
        assert_ne!(changed_ga.input_digest, rec_ga.input_digest);
        assert_ne!(changed_ga.mac, rec_ga.mac);
        assert_eq!(reg.verify_prover_keyed_receipt(&changed_ga, &key), Ok(()));
        assert_eq!(reg.verify_prover_keyed_receipt(&changed_gb, &key), Ok(()));

        let rec_air_fold = gpu
            .prover_air_fold_round_with_receipt(
                &key,
                anchor,
                true,
                air_rows,
                cols_base,
                0,
                0,
                (3 * air_rows) as u32,
                rand_ext4(&mut rng),
            )
            .expect("AIR fold_round_with_receipt");
        assert_eq!(reg.verify_prover_keyed_receipt(&rec_air_fold, &key), Ok(()));
    }

    eprintln!(
        "BENCH_WHIR_NV25_VRAM commit_r0_ms={r0_ms:.2} batch_sc_r0_ms={sc_ms:.2} open_init_ms={open_ms:.2} fold4_ms={fold4_ms:.2} commit_stg1_ms={stg1_ms:.2}"
    );

    // Scrub `nv = 25` arena before allocating the `~9.9 GiB` `nv = 26` arena on 12 GiB RX 6750 XT.
    drop(session);
    let session = gpu.try_acquire_prover_session()
        .expect("re-acquire for nv=26");

    // =========================================================================
    // Part B: `num_vars = 26` (`K = 512` signers, max buffer `3.00 GiB < 4 GiB`)
    // =========================================================================
    let nv26 = 26usize;
    let stg1_dom26 = 1usize << (nv26 - 4 + 2); // 2^24 Ext4 = 512 MiB
    let stg1_grp26 = stg1_dom26 / 16; // 2^20 groups
    let t_26 = Instant::now();
    match gpu.prover_whir_commit_round0_with_receipt(
        &key,
        anchor,
        1,
        &salt_seed,
        nv26,
        4,
        64,
        stg1_dom26,
        stg1_grp26,
        0,
        |_poly_idx, pos, dst| {
            dst.fill(0);
            if pos == 0 {
                dst[0] = 42;
            }
        },
    ) {
        Ok((top26, rec26)) => {
            let r26_ms = t_26.elapsed().as_secs_f64() * 1000.0;
            assert_ne!(top26, [0u8; 32]);
            assert_eq!(reg.verify_prover_keyed_receipt(&rec26, &key), Ok(()));

            // Verify `open_init_with_receipt` at `nv = 26` (`coeff_len = 2^26 + 2 = 67,108,866`,
            // exercising `k3 = 4` at `gid = 2^26`!).
            let (ev26_single, _) = gpu
                .prover_whir_open_init_with_receipt(&key, anchor, nv26, true, &[], &z_ood_2048)
                .expect("nv=26 open_init single");
            let (ev26_masked, rec26_open) = gpu
                .prover_whir_open_init_with_receipt(
                    &key,
                    anchor,
                    nv26,
                    false,
                    &weights,
                    &z_ood_2048,
                )
                .expect("nv=26 open_init weighted+masked");
            assert_eq!(reg.verify_prover_keyed_receipt(&rec26_open, &key), Ok(()));
            let mut legacy_ood = [EXT4_ZERO; 1536];
            legacy_ood[..768].copy_from_slice(&z_ood_2048[..768]);
            legacy_ood[768..].copy_from_slice(&z_ood_2048[1024..1792]);
            let legacy_evals = gpu
                .prover_whir_eval_univariate_2((1 << nv26) + 2, 0, &legacy_ood)
                .expect("nv=26 legacy geometric extension");
            for (t, z_t) in [(0usize, z0), (1usize, z1)] {
                let factor = ext4_add(poly_w, ext4_mul(mask_w, z_t));
                // An impulse at Boolean index zero has coefficients
                // 42 * (-1)^popcount(i), hence P(z) = 42 * product_j (1 - z^(2^j)).
                let single_expected = sparse_witness_ood(&[(0, 42)], nv26, z_t);
                assert_eq!(
                    ev26_single[t], single_expected,
                    "nv=26 independent Mobius/OOD oracle"
                );
                let expected = ext4_mul(factor, single_expected);
                assert_eq!(legacy_evals[t], expected, "nv=26 legacy table parity");
                assert_eq!(
                    ev26_masked[t], expected,
                    "nv=26 OOD evaluation {t} mismatch across gid=0..=2^26 (k3=0..=4)"
                );
            }
            eprintln!("BENCH_WHIR_NV26_VRAM commit_r0_ms={r26_ms:.2}");
        }
        Err(VulkanError::BufferExceedsMaxStorageRange { requested, limit }) => {
            panic!("nv=26 exceeded maxStorageBufferRange: requested={requested} > limit={limit}");
        }
        Err(VulkanError::VkResult {
            op: "vkAllocateMemory",
            code: -2,
        }) => {
            assert!(
                std::env::var_os("QSAG_REQUIRE_GPU_AUDIT").is_none(),
                "mandatory nv=26 GPU audit cannot skip allocation failure"
            );
            eprintln!(
                "NOTE: nv=26 (`~9.9 GiB` VRAM) skipped due to concurrent VRAM usage on 12 GiB GPU"
            );
        }
        Err(other) => panic!("unexpected nv=26 error: {other}"),
    }

    drop(session);
}
