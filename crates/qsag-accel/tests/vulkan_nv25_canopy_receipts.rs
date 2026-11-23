//! Live hardware verification for unified Poseidon2 Merkle GPU modes
//! (`merkle_layer_poseidon2.comp` modes 1, 2, 3) and Quintic `Fp5` Kronecker tables:
//! - Mode 1: `qsag-agg` two-block full-`pk_seed` Poseidon2 sponge (`sig::merkle_node_hash`)
//! - Mode 2: `qsag-agg` Poseidon2 WHIR Canopy internal node (`sponge::poseidon2_canopy_internal`)
//! - Mode 3: `qsag-agg` fixed-tweak Weighted Jive (`zk_hem::recursive_ivc::matrix::compress`)

#![cfg(feature = "std")]

use std::time::Instant;

use qsag_accel::goldilocks::{
    FP5_ONE, FP5_ZERO, GOLDILOCKS_PRIME, eq_kronecker_fp5_1024, fp5_add, fp5_mul, fp5_sub, gl_add,
    gl_mul, gl_reduce_u64,
};
use qsag_accel::poseidon2::{
    POSEIDON2_CANOPY_NODE_HI, POSEIDON2_CANOPY_ROOT_DOMAIN, POSEIDON2_CANOPY_SALT_DOMAIN,
    POSEIDON2_CONST_IV, POSEIDON2_FORS_NODE_DOMAIN, POSEIDON2_MERKLE_NODE_DOMAIN,
    Poseidon2Merkle2BlockAddr, merkle_layer_poseidon2_2block_at_cpu,
    merkle_layer_poseidon2_canopy_at_cpu, merkle_layer_poseidon2_fixed_tweak_cpu,
    poseidon2_canopy_root_cpu, poseidon2_canopy_tree_key_cpu, poseidon2_perm12,
};
use qsag_accel::{
    AcceleratorBackend, CertifiedBackend, CpuReferenceBackend, KernelTargetArch,
    VerifiedKernelDigestRegistry, VulkanError, VulkanSpirvBackend,
};

type NodeDigest = [u64; 4];
type Fp5 = [u64; 5];

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

fn rand_digest(state: &mut u64) -> NodeDigest {
    core::array::from_fn(|_| rand_gl(state))
}

fn rand_fp5(state: &mut u64) -> Fp5 {
    core::array::from_fn(|_| rand_gl(state))
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

fn spec_fixed_tweak_compress(tweak: &[u64; 4], left: &[u64; 4], right: &[u64; 4]) -> [u64; 4] {
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
    let pk_seed = rand_digest(&mut rng);

    // 1. Mode 1: Two-Block Poseidon2 Node Sponge (`sig::merkle_node_hash`).
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
        let children: Vec<NodeDigest> =
            (0..2 * num_parents).map(|_| rand_digest(&mut rng)).collect();
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
        let leaves: Vec<NodeDigest> = (0..n_leaves).map(|_| rand_digest(&mut rng)).collect();
        let domain_tag = POSEIDON2_MERKLE_NODE_DOMAIN;
        let layer = 2u32;
        let tree_idx = 0x4242_1337u64;

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

    // 2. Mode 2: Poseidon2 WHIR Canopy (`N = 2^20 = 1,048,576` leaves, `64 MiB` Canopy tree).
    {
        let stage_idx = 1u8;
        let tree_salt = rand_digest(&mut rng);
        assert_eq!(POSEIDON2_CANOPY_SALT_DOMAIN, 0x5032_434E_534C_5401);
        assert_eq!(POSEIDON2_CANOPY_ROOT_DOMAIN, 0x5032_434E_524F_4F54);

        let n_leaves = 1usize << 20;
        let log_leaves = 20u8;
        let tree_key = poseidon2_canopy_tree_key_cpu(stage_idx, log_leaves, tree_salt);
        let leaves: Vec<NodeDigest> = (0..n_leaves).map(|_| rand_digest(&mut rng)).collect();
        let mut gpu_nodes = vec![[0u64; 4]; 2 * n_leaves];

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

    // 3. Mode 3: Fixed-tweak Weighted Jive + CertifiedBackend.
    {
        let tweak = [0x5A4B_4845_4D5F_4D54u64, 0, 0, 0];
        let num_parents = 32_768usize;
        let children: Vec<NodeDigest> =
            (0..2 * num_parents).map(|_| rand_digest(&mut rng)).collect();
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
            spec_fixed_tweak_compress(
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

#[test]
fn fp5_kronecker_equality_matches_direct_product() {
    let mut rng = 0x55AA_1234_9988_7766u64;
    let r: Vec<Fp5> = (0..25).map(|_| rand_fp5(&mut rng)).collect();
    let table = eq_kronecker_fp5_1024(&r);
    for idx in [0usize, 1, 255, 256, 65_537, (1usize << 25) - 1] {
        let from_table = fp5_mul(
            fp5_mul(table[idx & 0xFF], table[256 + ((idx >> 8) & 0xFF)]),
            fp5_mul(
                table[512 + ((idx >> 16) & 0xFF)],
                table[768 + ((idx >> 24) & 0xFF)],
            ),
        );
        let mut direct = FP5_ONE;
        for (b, &rv) in r.iter().enumerate() {
            let factor = if ((idx >> b) & 1) == 1 {
                rv
            } else {
                fp5_sub(FP5_ONE, rv)
            };
            direct = fp5_mul(direct, factor);
        }
        assert_eq!(from_table, direct);
        assert_eq!(fp5_add(from_table, FP5_ZERO), direct);
    }
}
