//! Plugging a custom hardware or GPU backend into `qsag-accel`.
//!
//! ```bash
//! cargo run --release -p qsag-cli --example custom_accel_backend
//! ```
//!
//! 1. Implements `AcceleratorBackend` for a stand-in SPIR-V backend (`KernelTargetArch::SpirV15`).
//! 2. Pins each kernel artifact (`CertifiedKernelPin`) and registers the approved profile.
//! 3. Shows that an unmeasured backend and a tampered artifact are both rejected, while
//!    loader-measured pins that match the registry are accepted.
//! 4. Runs a Merkle layer through the backend, spot-checks it on the CPU, and issues a keyed
//!    execution receipt that only the holder of the backend's attestation key could have made.
//! 5. Shows the typed error a kernel returns for a malformed job instead of panicking.

use qsag_accel::{
    AccelError, AcceleratorBackend, BackendAttestationKey, CertifiedBackend, CertifiedKernelPin,
    CpuReferenceBackend, KernelRegistryError, KernelSlot, KernelTargetArch,
    VerifiedKernelDigestRegistry, merkle_layer_output_digest, spot_check_merkle_layer,
};

/// Example custom SPIR-V 1.5 compute backend delegating arithmetic to `CpuReferenceBackend`
/// while pinning distinct shader binary artifacts per `KernelSlot`.
struct SimulatedSpirvBackend {
    pins: [CertifiedKernelPin; KernelSlot::COUNT],
    cpu_fallback: CpuReferenceBackend,
}

impl SimulatedSpirvBackend {
    fn from_shader_binaries(blobs: [&[u8]; KernelSlot::COUNT]) -> Self {
        let pins = core::array::from_fn(|idx| {
            CertifiedKernelPin::from_kernel_artifact(
                KernelSlot::ALL[idx],
                KernelTargetArch::SpirV15,
                blobs[idx],
            )
        });
        Self {
            pins,
            cpu_fallback: CpuReferenceBackend::new(),
        }
    }
}

impl AcceleratorBackend for SimulatedSpirvBackend {
    fn target_arch(&self) -> KernelTargetArch {
        KernelTargetArch::SpirV15
    }

    fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
        self.pins[slot as usize]
    }

    fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]) {
        self.cpu_fallback.batch_keccak_f1600(states);
    }

    fn batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]) {
        self.cpu_fallback.batch_poseidon2_perm12(states);
    }

    fn goldilocks_ntt_inplace(
        &self,
        buf: &mut [u64],
        twiddles: &[u64],
        inverse: bool,
    ) -> Result<(), AccelError> {
        self.cpu_fallback
            .goldilocks_ntt_inplace(buf, twiddles, inverse)
    }

    fn coset_lde_ext2(
        &self,
        evals: &[[u64; 2]],
        blowup: usize,
        shift: u64,
        out: &mut [[u64; 2]],
    ) -> Result<(), AccelError> {
        self.cpu_fallback.coset_lde_ext2(evals, blowup, shift, out)
    }

    fn try_merkle_layer_poseidon2_at(
        &self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        self.cpu_fallback.try_merkle_layer_poseidon2_at(
            children,
            pk_seed,
            layer,
            start_parent_idx,
            out_parents,
        )
    }

    fn bdoz_gf2_128_batch_dot(
        &self,
        shares: &[(u128, u128)],
        weights: &[(u128, u128)],
    ) -> Result<(u128, u128), AccelError> {
        self.cpu_fallback.bdoz_gf2_128_batch_dot(shares, weights)
    }
}

fn main() {
    let approved_shaders: [&[u8]; KernelSlot::COUNT] = [
        b"SPIRV16::qsag_keccak_f1600_v1.spv",
        b"SPIRV16::qsag_poseidon2_perm12_v1.spv",
        b"SPIRV16::qsag_goldilocks_ntt_v1.spv",
        b"SPIRV16::qsag_coset_lde_ext2_v1.spv",
        b"SPIRV16::qsag_merkle_poseidon2_v1.spv",
        b"SPIRV16::qsag_bdoz_gf2_128_dot_v1.spv",
    ];

    // 1. Register approved shader pins in `VerifiedKernelDigestRegistry`.
    let approved_pins: [CertifiedKernelPin; KernelSlot::COUNT] = core::array::from_fn(|i| {
        CertifiedKernelPin::from_kernel_artifact(
            KernelSlot::ALL[i],
            KernelTargetArch::SpirV15,
            approved_shaders[i],
        )
    });
    let mut registry = VerifiedKernelDigestRegistry::<4>::with_cpu_reference_pins();
    registry
        .register_measured_profile(KernelTargetArch::SpirV15, approved_pins)
        .expect("registering approved SPIR-V 1.5 kernel profile must succeed");

    // 2. Negative checks: non-CPU backends require independent loader measurements, and tampered
    //    shader binaries fail with `PinMismatch` on the exact corrupted `KernelSlot`.
    let unmeasured = CertifiedBackend::try_new(
        SimulatedSpirvBackend::from_shader_binaries(approved_shaders),
        &registry,
    );
    assert_eq!(
        unmeasured.err(),
        Some(KernelRegistryError::LoaderMeasurementRequired)
    );

    let mut tampered_loader_pins = approved_pins;
    tampered_loader_pins[KernelSlot::MerkleLayerPoseidon2 as usize] =
        CertifiedKernelPin::from_kernel_artifact(
            KernelSlot::MerkleLayerPoseidon2,
            KernelTargetArch::SpirV15,
            b"SPIRV16::TAMPERED_MERKLE_SHADER.spv",
        );
    let rogue = CertifiedBackend::try_new_measured(
        SimulatedSpirvBackend::from_shader_binaries(approved_shaders),
        &registry,
        &tampered_loader_pins,
    );
    assert_eq!(
        rogue.err(),
        Some(KernelRegistryError::PinMismatch {
            slot: KernelSlot::MerkleLayerPoseidon2
        })
    );
    println!("  [ok] Unmeasured & tampered SPIR-V kernel profiles deterministically rejected");

    // 3. Construct certified backend from loader-measured pins and run Merkle layer compression.
    let certified = CertifiedBackend::try_new_measured(
        SimulatedSpirvBackend::from_shader_binaries(approved_shaders),
        &registry,
        &approved_pins,
    )
    .expect("certified SPIR-V backend must initialize when loader pins match registry");

    let children: [[u64; 4]; 8] = core::array::from_fn(|i| {
        let base = (i as u64 + 1) * 101;
        [base, base + 1, base + 2, base + 3]
    });
    let pk_seed = [0x1111_2222u64, 0x3333_4444, 0x5555_6666, 0x7777_8888];
    let layer = 4u32;
    let transcript_anchor = [0x7A; 32];
    let mut parents = [[0u64; 4]; 4];

    // 4. The host that operates the device holds the attestation key; the device never does.
    let attestation_key = BackendAttestationKey::derive(&[0xC3; 32], b"rack-7/gpu-2");
    let receipt = CpuReferenceBackend::merkle_layer_poseidon2_with_receipt(
        &certified,
        &attestation_key,
        &children,
        &pk_seed,
        layer,
        transcript_anchor,
        &mut parents,
    )
    .expect("children and parents have matching lengths");
    assert_eq!(
        registry.verify_keyed_receipt(&receipt, &attestation_key),
        Ok(())
    );
    assert_eq!(receipt.output_digest, merkle_layer_output_digest(&parents));

    // The sampling challenge is derived from the receipt, i.e. after the device fixed its output.
    assert!(spot_check_merkle_layer(
        &children,
        &pk_seed,
        layer,
        0,
        &parents,
        &receipt.mac,
        2
    ));

    // A receipt is rejected under any other key, and after any change to what it reports.
    let other_key = BackendAttestationKey::derive(&[0xC3; 32], b"rack-7/gpu-3");
    let failed = Err(KernelRegistryError::ReceiptAuthenticationFailed);
    assert_eq!(registry.verify_keyed_receipt(&receipt, &other_key), failed);
    let mut altered = receipt;
    altered.output_digest[0] ^= 1;
    assert_eq!(
        registry.verify_keyed_receipt(&altered, &attestation_key),
        failed
    );
    println!("  [ok] Keyed execution receipt verified; wrong key and altered output rejected");

    // 5. A malformed job is a typed error, not a panic.
    let mut too_few_parents = [[0u64; 4]; 3];
    assert_eq!(
        certified.try_merkle_layer_poseidon2(&children, &pk_seed, layer, &mut too_few_parents),
        Err(AccelError::LengthMismatch {
            what: "Merkle layer children",
            expected: 6,
            actual: 8,
        })
    );
    println!("  [ok] Malformed Merkle job returned AccelError::LengthMismatch");
}
