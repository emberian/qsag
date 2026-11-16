//! Scalar-oracle checks spanning serial/parallel thresholds and uneven SIMD/chunk tails.
use qsag_accel::gf2_128::{bdoz_gf2_128_batch_dot_cpu, gf2_128_mul_const};
use qsag_accel::goldilocks::{
    GOLDILOCKS_PRIME, coset_lde_ext2_cpu, gl_add, gl_inv_or_zero, gl_mul, gl_pow_pub,
    gl_reduce_u64, gl_sub, goldilocks_ntt_alloc_free, goldilocks_ntt_cpu,
    goldilocks_primitive_root,
};
use qsag_accel::{
    CpuReferenceBackend, KernelSlot, KernelTargetArch, ProverKernelSlot,
    VerifiedKernelDigestRegistry, VulkanError, VulkanSpirvBackend,
};

fn data(n: usize) -> Vec<u64> {
    let mut s = 0x92d6_8ca2_918a_441fu64;
    (0..n)
        .map(|i| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            if i % 17 == 0 { u64::MAX } else { s }
        })
        .collect()
}

// Independent serial recurrence, intentionally not using the optimized stage helper.
fn serial_ntt(a: &mut [u64], inverse: bool) {
    let n = a.len();
    a.iter_mut().for_each(|x| *x = gl_reduce_u64(*x));
    if n == 1 {
        return;
    }
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - n.trailing_zeros());
        if i < j {
            a.swap(i, j);
        }
    }
    for stage in 1..=n.trailing_zeros() {
        let len = 1 << stage;
        let root = goldilocks_primitive_root(stage).unwrap();
        let root = if inverse { gl_inv_or_zero(root) } else { root };
        for block in a.chunks_mut(len) {
            let mut w = 1;
            for j in 0..len / 2 {
                let u = block[j];
                let v = gl_mul(block[j + len / 2], w);
                block[j] = gl_add(u, v);
                block[j + len / 2] = gl_sub(u, v);
                w = gl_mul(w, root);
            }
        }
    }
    if inverse {
        let scale = gl_inv_or_zero(n as u64);
        a.iter_mut().for_each(|x| *x = gl_mul(*x, scale));
    }
}

#[test]
fn ntt_serial_oracle_across_worker_and_lane_boundaries() {
    for log_n in [0, 1, 2, 3, 8, 15, 16, 17, 20] {
        let n = 1 << log_n;
        let input = data(n);
        let root = goldilocks_primitive_root(log_n).unwrap();
        let twiddles: Vec<_> = (0..n / 2).map(|i| gl_pow_pub(root, i as u64)).collect();
        for inverse in [false, true] {
            let mut expected = input.clone();
            serial_ntt(&mut expected, inverse);
            let mut table = input.clone();
            goldilocks_ntt_cpu(&mut table, &twiddles, inverse).unwrap();
            assert_eq!(table, expected, "table n={n} inverse={inverse}");
            let mut direct = input.clone();
            goldilocks_ntt_alloc_free(&mut direct, inverse).unwrap();
            assert_eq!(direct, expected, "direct n={n} inverse={inverse}");
        }
    }
}

#[test]
fn fused_ext2_lde_matches_separate_scalar_coordinates() {
    for (n, blowup) in [(1, 1), (4, 4), (1024, 2), (32768, 2), (65536, 2)] {
        let raw = data(n * 2);
        let evals: Vec<_> = raw.as_chunks::<2>().0.to_vec();
        for shift in [0, 7, GOLDILOCKS_PRIME, u64::MAX] {
            let mut expected = vec![[0; 2]; n * blowup];
            for coord in 0..2 {
                let mut values: Vec<_> = evals.iter().map(|x| x[coord]).collect();
                serial_ntt(&mut values, true);
                let mut power = 1;
                for x in &mut values {
                    *x = gl_mul(*x, power);
                    power = gl_mul(power, shift);
                }
                values.resize(n * blowup, 0);
                serial_ntt(&mut values, false);
                for (out, value) in expected.iter_mut().zip(values) {
                    out[coord] = value;
                }
            }
            let mut actual = vec![[0; 2]; n * blowup];
            coset_lde_ext2_cpu(&evals, blowup, shift, &mut actual).unwrap();
            assert_eq!(actual, expected, "n={n} shift={shift}");
        }
    }
}

#[test]
fn bdoz_parallel_and_simd_tails_match_bitwise_oracle() {
    let raw = data(262147 * 8);
    let pairs: Vec<_> = raw
        .as_chunks::<4>()
        .0
        .iter()
        .map(|x| {
            (
                u128::from(x[0]) | (u128::from(x[1]) << 64),
                u128::from(x[2]) | (u128::from(x[3]) << 64),
            )
        })
        .collect();
    let (shares, weights) = pairs.split_at(262147);
    for n in [0, 1, 255, 256, 257, 131071, 262144, 262147] {
        let expected = shares[..n]
            .iter()
            .zip(&weights[..n])
            .fold((0, 0), |acc, (s, w)| {
                (
                    acc.0 ^ gf2_128_mul_const(s.0, w.0),
                    acc.1 ^ gf2_128_mul_const(s.1, w.1),
                )
            });
        assert_eq!(
            bdoz_gf2_128_batch_dot_cpu(&shares[..n], &weights[..n]),
            Ok(expected)
        );
    }
    assert!(bdoz_gf2_128_batch_dot_cpu(shares, &weights[..1]).is_err());
}

#[test]
fn canonical_registry_pins_actual_compiled_modules_without_requiring_a_device() {
    let registry = VerifiedKernelDigestRegistry::<2>::with_cpu_and_canonical_gpu_pins();
    for pin in VulkanSpirvBackend::measure_embedded_spirv_pins() {
        assert_eq!(
            registry.lookup_pin(KernelTargetArch::SpirV15, pin.slot),
            Ok(&pin)
        );
    }
    for slot in KernelSlot::ALL {
        assert_eq!(
            registry.lookup_pin(KernelTargetArch::CpuReference, slot),
            Ok(&CpuReferenceBackend::canonical_pin(slot))
        );
    }
    // Existing fallible probe remains separate from deterministic artifact approval.
    if !cfg!(all(
        feature = "std",
        target_os = "linux",
        target_pointer_width = "64"
    )) {
        assert!(matches!(
            VulkanSpirvBackend::try_new(),
            Err(VulkanError::UnsupportedPlatform)
        ));
    }
}

// SHA-256 pins of the ten embedded modules, computed outside Rust from the word tables (domain
// label, slot and architecture bytes, little-endian length, module bytes). Regenerating a shader
// changes its line here, so a pin change is reviewable without reading the SPIR-V diff.
#[test]
fn canonical_spirv_pin_digests_are_frozen() {
    fn hex(digest: [u8; 32]) -> String {
        digest.iter().map(|b| format!("{b:02x}")).collect()
    }
    let kernels = [
        (
            KernelSlot::BatchKeccakF1600,
            "6cbc26801f4122a4bf2c962d93f5543666db83c9024309ad413f91cdf5a84ce6",
        ),
        (
            KernelSlot::BatchPoseidon2Perm12,
            "38e2637c04432bcbe92df4b5b1dbe71a8d34e8754f7e0d0a2168f4ef65221c68",
        ),
        (
            KernelSlot::GoldilocksNtt,
            "9e98cc9840271daaccd678d32f1125edc381c83c7aace90d71b3a17f16ea908a",
        ),
        (
            KernelSlot::CosetLdeExt2,
            "bc42c559f07ff189beb41ebde1a6155367db174e5350401f90a5f73e47929efb",
        ),
        (
            KernelSlot::MerkleLayerPoseidon2,
            "2c0b53d67a739eb4aed21d4337957128af2215df9fb9f3be5e157eff37da1c19",
        ),
        (
            KernelSlot::BdozGf2128BatchDot,
            "3c8f480f2970dbbd83e25af4936ba675739bb4b6e4075a138ed4ab6d636d0c43",
        ),
    ];
    assert_eq!(kernels.map(|(slot, _)| slot), KernelSlot::ALL);
    for (slot, expected) in kernels {
        let pin = VulkanSpirvBackend::canonical_pin(slot);
        assert_eq!(hex(pin.sha256_digest), expected, "{slot:?}");
    }
    let prover = [
        (
            ProverKernelSlot::WhirLdeCommitment,
            "25fd8ffe3b4b4b7327aac2e620c3b039b3fba5dad760e7ef17fa470bf8ab5d94",
        ),
        (
            ProverKernelSlot::WhirFoldSumcheck,
            "291f84c5249ebce359f072744353eede299d075388c4b05e7583bb9da19db952",
        ),
        (
            ProverKernelSlot::AirRowGroupA,
            "147e99f14ec62bda0bdd0782a42ec3bc600c11bf811396e612c03467736cdcb1",
        ),
        (
            ProverKernelSlot::AirRowGroupB,
            "3471e16328ed2f3566ce946dd4cde7aced74edf23884355964dc9d9cd8cdfaa0",
        ),
    ];
    assert_eq!(prover.map(|(slot, _)| slot), ProverKernelSlot::ALL);
    for (slot, expected) in prover {
        let pin = VulkanSpirvBackend::canonical_prover_pin(slot);
        assert_eq!(hex(pin.sha256_digest), expected, "{slot:?}");
    }
}

#[test]
#[should_panic(expected = "at least two profiles")]
fn canonical_registry_cannot_silently_drop_gpu_pins() {
    let _ = VerifiedKernelDigestRegistry::<1>::with_cpu_and_canonical_gpu_pins();
}

/// Opt-in wall-clock check; timing assertions would be unstable on shared build hosts.
#[test]
#[ignore = "manual performance comparison on the build host"]
fn ntt_throughput_against_scalar_recurrence() {
    use std::{hint::black_box, time::Instant};
    let n = 1 << 20;
    let input = data(n);
    let mut reference = input.clone();
    let start = Instant::now();
    serial_ntt(black_box(&mut reference), false);
    let serial = start.elapsed();
    let mut actual = input;
    let start = Instant::now();
    goldilocks_ntt_alloc_free(black_box(&mut actual), false).unwrap();
    let optimized = start.elapsed();
    assert_eq!(actual, reference);
    eprintln!(
        "NTT n={n} std={} scalar={serial:?} optimized={optimized:?}",
        cfg!(feature = "std")
    );
}

#[test]
#[ignore = "manual performance comparison on the build host"]
fn bdoz_throughput_against_serial_simd_batches() {
    use std::{hint::black_box, time::Instant};
    for n in [32768, 131072, 262144, 1048576] {
        let raw = data(n * 4);
        let shares: Vec<_> = raw
            .as_chunks::<4>()
            .0
            .iter()
            .map(|x| {
                (
                    u128::from(x[0]) | (u128::from(x[1]) << 64),
                    u128::from(x[2]) | (u128::from(x[3]) << 64),
                )
            })
            .collect();
        let weights = &shares;
        let start = Instant::now();
        let expected =
            shares
                .chunks(16384)
                .zip(weights.chunks(16384))
                .fold((0, 0), |acc, (s, w)| {
                    let part = bdoz_gf2_128_batch_dot_cpu(black_box(s), black_box(w)).unwrap();
                    (acc.0 ^ part.0, acc.1 ^ part.1)
                });
        let serial = start.elapsed();
        let start = Instant::now();
        let actual = bdoz_gf2_128_batch_dot_cpu(black_box(&shares), black_box(weights)).unwrap();
        let parallel = start.elapsed();
        assert_eq!(actual, expected);
        eprintln!("BDOZ n={n} serial SIMD={serial:?} parallel={parallel:?}");
    }
}
