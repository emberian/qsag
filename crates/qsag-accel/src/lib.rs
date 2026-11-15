#![no_std]
//! Zero-dependency `#![no_std]` certified hardware & GPU accelerator trait (`AcceleratorBackend`),
//! constant-time CPU reference backend (`CpuReferenceBackend`), certified RDNA2 / SPIR-V Vulkan
//! discrete GPU backend (`VulkanSpirvBackend`), transcript-bound reports,
//! and verified kernel digest registry (`VerifiedKernelDigestRegistry`).

#![cfg_attr(
    not(all(feature = "std", target_os = "linux", target_pointer_width = "64")),
    forbid(unsafe_code)
)]
#![cfg_attr(
    all(feature = "std", target_os = "linux", target_pointer_width = "64"),
    deny(unsafe_code)
)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod ct;
pub mod gf2_128;
pub mod goldilocks;
pub mod keccak;
pub mod poseidon2;
pub mod sha2;
pub mod spirv_kernels;
pub mod vulkan;
#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
#[allow(unsafe_code)]
mod vulkan_ffi;

pub use vulkan::{
    AIR_MAX_OP_TERMS, AIR_OP_GAMMA_BASE_EXT4, BatchExecution, CpuFallbackEvent, PipelineTelemetry,
    VulkanDeviceInfo, VulkanError, VulkanSpirvBackend, air_op_term_count,
};

use ct::{RedactedSecret, ct_eq_bytes_mask, ct_eq_mask_u64};
use gf2_128::bdoz_gf2_128_batch_dot_cpu;
use goldilocks::{coset_lde_ext2_cpu, gl_reduce_u64, goldilocks_ntt_cpu};
use keccak::cshake256_framed_32;
use poseidon2::{merkle_layer_poseidon2_at_cpu, poseidon2_hash_framed_limbs4, poseidon2_perm12};
use sha2::sha256;

// Sizes and scheduling depend only on public lengths, never on field values.
#[cfg(feature = "std")]
fn cpu_workers(len: usize, min_chunk: usize) -> usize {
    if len / min_chunk < 2 {
        return 1;
    }
    std::thread::available_parallelism()
        .map_or(1, usize::from)
        .min(len / min_chunk)
}

/// Run every job on up to `workers` threads, the caller's included. A worker the OS refuses to
/// start only lowers the parallelism: the threads that do exist still drain every job.
#[cfg(feature = "std")]
fn cpu_drain<J: Send>(
    workers: usize,
    jobs: impl Iterator<Item = J> + Send,
    run: impl Fn(J) + Sync,
) {
    let jobs = std::sync::Mutex::new(jobs);
    let drain = || {
        loop {
            // The guard is released before `run`, so a panicking job cannot poison the queue.
            let job = jobs
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .next();
            match job {
                Some(job) => run(job),
                None => break,
            }
        }
    };
    std::thread::scope(|scope| {
        for _ in 1..workers {
            if std::thread::Builder::new()
                .spawn_scoped(scope, drain)
                .is_err()
            {
                break;
            }
        }
        drain();
    });
}

fn cpu_chunks_mut<T: Send>(
    items: &mut [T],
    min_chunk: usize,
    run: impl Fn(usize, &mut [T]) + Sync,
) {
    #[cfg(feature = "std")]
    {
        let workers = cpu_workers(items.len(), min_chunk);
        if workers > 1 {
            let chunk_len = items.len().div_ceil(workers);
            cpu_drain(
                workers,
                items.chunks_mut(chunk_len).enumerate(),
                |(i, chunk)| run(i * chunk_len, chunk),
            );
            return;
        }
    }
    let _ = min_chunk;
    run(0, items);
}

/// Shape or parameter error reported by a kernel instead of panicking on caller-supplied slices.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AccelError {
    /// A slice had the wrong length for the job (`what` names the offending argument).
    LengthMismatch {
        what: &'static str,
        expected: usize,
        actual: usize,
    },
    /// A transform length or blowup factor was zero or not a power of two.
    NotPowerOfTwo { what: &'static str, len: usize },
    /// A transform domain exceeded the field's $2^{32}$ two-adic subgroup.
    DomainTooLarge { log2_len: u32 },
    /// A derived length overflowed `usize`.
    LengthOverflow,
    /// Public NTT twiddles are not successive powers of a primitive root of the transform length.
    InvalidTwiddles,
    /// The accelerator failed to execute the job (device, driver, or lock failure). No output
    /// was produced and no CPU fallback ran.
    BackendFailure,
    /// A receipt was requested for a job descriptor that does not belong to the pinned kernel slot.
    KernelSlotMismatch {
        pin: KernelSlot,
        descriptor: KernelSlot,
    },
    /// The backend refused a secret-bearing kernel slot because it holds no driver evidence
    /// (required subgroup size, zero scratch, zero spills) for its compiled pipelines. Nothing
    /// was sent to the device.
    SecretSlotUnaudited { slot: KernelSlot },
}

impl core::fmt::Display for AccelError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::LengthMismatch {
                what,
                expected,
                actual,
            } => write!(f, "{what}: expected length {expected}, got {actual}"),
            Self::NotPowerOfTwo { what, len } => {
                write!(f, "{what}: length {len} is not a nonzero power of two")
            }
            Self::DomainTooLarge { log2_len } => {
                write!(
                    f,
                    "transform domain 2^{log2_len} exceeds the 2^32 two-adic subgroup"
                )
            }
            Self::LengthOverflow => f.write_str("derived length overflows usize"),
            Self::InvalidTwiddles => {
                f.write_str("NTT twiddles are not successive powers of a primitive root")
            }
            Self::BackendFailure => f.write_str("accelerator backend failed to execute the job"),
            Self::KernelSlotMismatch { pin, descriptor } => write!(
                f,
                "kernel pin is for slot {pin:?} but the job descriptor is for slot {descriptor:?}"
            ),
            Self::SecretSlotUnaudited { slot } => write!(
                f,
                "backend has no pipeline audit evidence and refuses secret-bearing slot {slot:?}"
            ),
        }
    }
}

impl core::error::Error for AccelError {}

/// Hardware/compute target architecture identifier for kernel digest pinning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum KernelTargetArch {
    /// Constant-time portable Rust CPU reference evaluation.
    CpuReference = 0x01,
    /// Certified RDNA2 / RDNA3 Wave32 ISA compute kernel.
    Rdna2Wave32 = 0x02,
    // 0x03 is retired. It was issued as `SpirV16` for modules whose header says SPIR-V 1.5;
    // pins and receipts carrying it must not verify against anything current.
    /// Certified FPGA / ASIC fixed-function datapath.
    CustomHardware = 0x04,
    /// Certified Vulkan SPIR-V 1.5 compute shader module (header version word `0x0001_0500`).
    SpirV15 = 0x05,
}

impl KernelTargetArch {
    /// The SPIR-V header version word (module word 1) this label asserts, if it is a SPIR-V
    /// label at all.
    pub const fn spirv_version_word(self) -> Option<u32> {
        match self {
            Self::SpirV15 => Some(0x0001_0500),
            Self::CpuReference | Self::Rdna2Wave32 | Self::CustomHardware => None,
        }
    }
}

/// Enumerates the 6 certified batch compute kernels in [`AcceleratorBackend`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum KernelSlot {
    BatchKeccakF1600 = 0,
    BatchPoseidon2Perm12 = 1,
    GoldilocksNtt = 2,
    CosetLdeExt2 = 3,
    MerkleLayerPoseidon2 = 4,
    BdozGf2128BatchDot = 5,
}

impl KernelSlot {
    pub const COUNT: usize = 6;

    /// Algorithm domain label bound into every keyed [`ExecutionReceipt`] for this slot.
    pub const fn algorithm_domain(self) -> &'static [u8] {
        match self {
            Self::BatchKeccakF1600 => b"QSAG.ACCEL.ALG.KECCAK_F1600.V1",
            // V1 versions the attestation framing, not the permutation. The hardened
            // canonical Poseidon2-12 is bound by the test vectors; Lean pins this label.
            Self::BatchPoseidon2Perm12 => b"QSAG.ACCEL.ALG.POSEIDON2_PERM12.V1",
            Self::GoldilocksNtt => b"QSAG.ACCEL.ALG.GOLDILOCKS_NTT.V1",
            Self::CosetLdeExt2 => b"QSAG.ACCEL.ALG.COSET_LDE_EXT2.V1",
            Self::MerkleLayerPoseidon2 => b"QSAG.ACCEL.ALG.MERKLE_POSEIDON2.V1",
            Self::BdozGf2128BatchDot => b"QSAG.ACCEL.ALG.BDOZ_GF2_128_DOT.V1",
        }
    }
    pub const ALL: [Self; 6] = [
        Self::BatchKeccakF1600,
        Self::BatchPoseidon2Perm12,
        Self::GoldilocksNtt,
        Self::CosetLdeExt2,
        Self::MerkleLayerPoseidon2,
        Self::BdozGf2128BatchDot,
    ];
}

/// Batch job descriptor recording exact dimensions & algebraic parameters of a kernel invocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BatchJobDescriptor {
    KeccakF1600 {
        num_states: usize,
    },
    Poseidon2Perm12 {
        num_states: usize,
    },
    GoldilocksNtt {
        length: usize,
        inverse: bool,
    },
    CosetLdeExt2 {
        domain_len: usize,
        blowup: usize,
        shift: u64,
    },
    MerkleLayerPoseidon2 {
        num_parents: usize,
        pk_seed: [u64; 4],
        layer: u32,
    },
    BdozGf2128BatchDot {
        num_elements: usize,
    },
}

impl BatchJobDescriptor {
    pub const fn slot(&self) -> KernelSlot {
        match self {
            Self::KeccakF1600 { .. } => KernelSlot::BatchKeccakF1600,
            Self::Poseidon2Perm12 { .. } => KernelSlot::BatchPoseidon2Perm12,
            Self::GoldilocksNtt { .. } => KernelSlot::GoldilocksNtt,
            Self::CosetLdeExt2 { .. } => KernelSlot::CosetLdeExt2,
            Self::MerkleLayerPoseidon2 { .. } => KernelSlot::MerkleLayerPoseidon2,
            Self::BdozGf2128BatchDot { .. } => KernelSlot::BdozGf2128BatchDot,
        }
    }

    /// Canonical 56-byte big-endian encoding of the job descriptor for transcript binding.
    pub fn to_canonical_bytes(&self) -> [u8; 56] {
        let mut out = [0u8; 56];
        out[0] = self.slot() as u8;
        match *self {
            Self::KeccakF1600 { num_states } => {
                out[8..16].copy_from_slice(&(num_states as u64).to_be_bytes());
            }
            Self::Poseidon2Perm12 { num_states } => {
                out[8..16].copy_from_slice(&(num_states as u64).to_be_bytes());
            }
            Self::GoldilocksNtt { length, inverse } => {
                out[1] = inverse as u8;
                out[8..16].copy_from_slice(&(length as u64).to_be_bytes());
            }
            Self::CosetLdeExt2 {
                domain_len,
                blowup,
                shift,
            } => {
                out[8..16].copy_from_slice(&(domain_len as u64).to_be_bytes());
                out[16..24].copy_from_slice(&(blowup as u64).to_be_bytes());
                out[24..32].copy_from_slice(&gl_reduce_u64(shift).to_be_bytes());
            }
            Self::MerkleLayerPoseidon2 {
                num_parents,
                pk_seed,
                layer,
            } => {
                out[4..8].copy_from_slice(&layer.to_be_bytes());
                out[8..16].copy_from_slice(&(num_parents as u64).to_be_bytes());
                for (i, &limb) in pk_seed.iter().enumerate() {
                    out[16 + i * 8..24 + i * 8].copy_from_slice(&gl_reduce_u64(limb).to_be_bytes());
                }
            }
            Self::BdozGf2128BatchDot { num_elements } => {
                out[8..16].copy_from_slice(&(num_elements as u64).to_be_bytes());
            }
        }
        out
    }
}

/// Dual-hash certified binary/shader pin for a single [`KernelSlot`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CertifiedKernelPin {
    pub slot: KernelSlot,
    pub target_arch: KernelTargetArch,
    /// SHA-256 digest of the certified machine-code / SPIR-V / ISA binary blob.
    pub sha256_digest: [u8; 32],
    /// Algebraic Width-12 Goldilocks Poseidon2 digest (4 canonical limbs) for in-circuit verification.
    pub poseidon2_digest: [u64; 4],
}

impl CertifiedKernelPin {
    /// Construct a pin deterministically from a certified kernel binary / ISA artifact slice.
    pub fn from_kernel_artifact(
        slot: KernelSlot,
        target_arch: KernelTargetArch,
        artifact_bytes: &[u8],
    ) -> Self {
        let header = [slot as u8, target_arch as u8];
        let sha256_digest = {
            let mut h = sha2::Sha256Hasher::new();
            h.update(b"QSAG.ACCEL.KERNEL.SHA256.V1");
            h.update(&header);
            h.update(&(artifact_bytes.len() as u64).to_le_bytes());
            h.update(artifact_bytes);
            h.finalize()
        };
        let poseidon2_digest = poseidon2_hash_framed_limbs4(
            0x4B52_4E4C_5F50_494E, // "KRNL_PIN"
            &[b"QSAG.ACCEL.KERNEL.P2.V1", &header, artifact_bytes],
        );
        Self {
            slot,
            target_arch,
            sha256_digest,
            poseidon2_digest,
        }
    }
}

/// Enumerates the 4 certified VRAM-resident WHIR/Hem & AIR row-sumcheck compute pipelines.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ProverKernelSlot {
    WhirLdeCommitment = 0,
    WhirFoldSumcheck = 1,
    AirRowGroupA = 2,
    AirRowGroupB = 3,
}

impl ProverKernelSlot {
    pub const COUNT: usize = 4;

    /// Algorithm domain label bound into certified prover kernel pins and audit digests.
    pub const fn algorithm_domain(self) -> &'static [u8] {
        match self {
            Self::WhirLdeCommitment => b"QSAG.ACCEL.PROVER.WHIR_LDE_COMMIT.V1",
            Self::WhirFoldSumcheck => b"QSAG.ACCEL.PROVER.WHIR_FOLD_SUMCHECK.V1",
            Self::AirRowGroupA => b"QSAG.ACCEL.PROVER.AIR_ROW_GROUP_A.V1",
            Self::AirRowGroupB => b"QSAG.ACCEL.PROVER.AIR_ROW_GROUP_B.V1",
        }
    }

    pub const ALL: [Self; 4] = [
        Self::WhirLdeCommitment,
        Self::WhirFoldSumcheck,
        Self::AirRowGroupA,
        Self::AirRowGroupB,
    ];
}

/// Dual-hash certified binary/shader pin for a single [`ProverKernelSlot`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CertifiedProverKernelPin {
    pub slot: ProverKernelSlot,
    pub target_arch: KernelTargetArch,
    /// SHA-256 digest of the certified SPIR-V binary blob.
    pub sha256_digest: [u8; 32],
    /// Algebraic Width-12 Goldilocks Poseidon2 digest (4 canonical limbs).
    pub poseidon2_digest: [u64; 4],
}

impl CertifiedProverKernelPin {
    /// Construct a prover kernel pin deterministically from a certified SPIR-V artifact slice.
    pub fn from_kernel_artifact(
        slot: ProverKernelSlot,
        target_arch: KernelTargetArch,
        artifact_bytes: &[u8],
    ) -> Self {
        let header = [0x80u8 | (slot as u8), target_arch as u8];
        let sha256_digest = {
            let mut h = sha2::Sha256Hasher::new();
            h.update(b"QSAG.ACCEL.PROVER_KERNEL.SHA256.V1");
            h.update(&header);
            h.update(&(artifact_bytes.len() as u64).to_le_bytes());
            h.update(artifact_bytes);
            h.finalize()
        };
        let poseidon2_digest = poseidon2_hash_framed_limbs4(
            0x5052_5652_5F50_494E, // "PRVR_PIN"
            &[b"QSAG.ACCEL.PROVER_KERNEL.P2.V1", &header, artifact_bytes],
        );
        Self {
            slot,
            target_arch,
            sha256_digest,
            poseidon2_digest,
        }
    }
}

/// Secret MAC key identifying one backend instance to the host that operates it.
///
/// The key stays with the trusted host or loader, never with the accelerator whose output is
/// being reported. `backend_id` is a public identifier bound into every receipt MAC.
pub struct BackendAttestationKey {
    backend_id: [u8; 32],
    key: RedactedSecret<32>,
}

impl BackendAttestationKey {
    /// Wrap an existing 32-byte MAC key for the backend named by `backend_id`.
    pub const fn new(backend_id: [u8; 32], key: [u8; 32]) -> Self {
        Self {
            backend_id,
            key: RedactedSecret::new(key),
        }
    }

    /// Derive a per-backend key from a host master secret and a public backend label.
    pub fn derive(master_secret: &[u8; 32], backend_label: &[u8]) -> Self {
        let backend_id = cshake256_framed_32(b"QSAG.ACCEL.BACKEND_ID.V1", &[backend_label]);
        let key = cshake256_framed_32(
            b"QSAG.ACCEL.BACKEND_ATTESTATION_KEY.V1",
            &[master_secret, &backend_id],
        );
        Self::new(backend_id, key)
    }

    pub const fn backend_id(&self) -> &[u8; 32] {
        &self.backend_id
    }
}

impl core::fmt::Debug for BackendAttestationKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BackendAttestationKey")
            .field("backend_id", &self.backend_id)
            .field("key", &self.key)
            .finish()
    }
}

/// Keyed report that the holder of a [`BackendAttestationKey`] ran one kernel job on one backend
/// and observed these input and output digests.
///
/// `mac` is `cSHAKE256` keyed with the attestation key over the backend ID, the slot's algorithm
/// domain, the target architecture, the canonical job descriptor, both kernel digests, the
/// transcript anchor, the input digest, and the output digest. A valid MAC proves which key holder
/// issued the report; it is not a proof that the backend computed correctly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExecutionReceipt {
    pub backend_id: [u8; 32],
    pub arch: KernelTargetArch,
    pub descriptor: BatchJobDescriptor,
    pub kernel_sha256: [u8; 32],
    pub kernel_poseidon2: [u64; 4],
    pub transcript_anchor: [u8; 32],
    /// Hardware telemetry digest; zero denotes a software-only receipt.
    pub hardware_audit_digest: [u8; 32],
    pub input_digest: [u8; 32],
    pub output_digest: [u8; 32],
    pub mac: [u8; 32],
}

impl ExecutionReceipt {
    fn mac_over_fields(&self, key: &BackendAttestationKey) -> [u8; 32] {
        let slot = self.descriptor.slot();
        let mut p2_bytes = [0u8; 32];
        for (chunk, limb) in p2_bytes
            .as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(&self.kernel_poseidon2)
        {
            *chunk = limb.to_le_bytes();
        }
        cshake256_framed_32(
            b"QSAG.ACCEL.KEYED_RECEIPT.V5",
            &[
                key.key.expose(),
                &self.backend_id,
                slot.algorithm_domain(),
                &[self.arch as u8],
                &self.descriptor.to_canonical_bytes(),
                &self.kernel_sha256,
                &p2_bytes,
                &self.transcript_anchor,
                &self.hardware_audit_digest,
                &self.input_digest,
                &self.output_digest,
            ],
        )
    }

    /// Issue a keyed receipt for `descriptor` executed by the kernel identified by `pin`.
    pub fn compute_keyed(
        key: &BackendAttestationKey,
        pin: &CertifiedKernelPin,
        descriptor: BatchJobDescriptor,
        transcript_anchor: [u8; 32],
        input_digest: [u8; 32],
        output_digest: [u8; 32],
    ) -> Result<Self, AccelError> {
        Self::compute_audited(
            key,
            pin,
            descriptor,
            transcript_anchor,
            input_digest,
            output_digest,
            [0; 32],
        )
    }

    /// Issue a receipt binding the executing backend's hardware audit evidence.
    #[allow(clippy::too_many_arguments)]
    pub fn compute_audited(
        key: &BackendAttestationKey,
        pin: &CertifiedKernelPin,
        descriptor: BatchJobDescriptor,
        transcript_anchor: [u8; 32],
        input_digest: [u8; 32],
        output_digest: [u8; 32],
        hardware_audit_digest: [u8; 32],
    ) -> Result<Self, AccelError> {
        if pin.target_arch == KernelTargetArch::SpirV15 && hardware_audit_digest == [0; 32] {
            return Err(AccelError::SecretSlotUnaudited { slot: pin.slot });
        }
        if pin.slot != descriptor.slot() {
            return Err(AccelError::KernelSlotMismatch {
                pin: pin.slot,
                descriptor: descriptor.slot(),
            });
        }
        let mut receipt = Self {
            backend_id: key.backend_id,
            arch: pin.target_arch,
            descriptor,
            kernel_sha256: pin.sha256_digest,
            kernel_poseidon2: pin.poseidon2_digest,
            transcript_anchor,
            hardware_audit_digest,
            input_digest,
            output_digest,
            mac: [0u8; 32],
        };
        receipt.mac = receipt.mac_over_fields(key);
        Ok(receipt)
    }

    /// All-ones mask iff the receipt names `key`'s backend, carries `pin`'s kernel digests, and its
    /// MAC verifies under `key`. Every comparison is evaluated; none short-circuits.
    fn verification_mask(&self, key: &BackendAttestationKey, pin: &CertifiedKernelPin) -> u64 {
        let mut ok = ct_eq_mask_u64(self.arch as u64, pin.target_arch as u64)
            & ct_eq_mask_u64(self.descriptor.slot() as u64, pin.slot as u64)
            & ct_eq_bytes_mask(&self.backend_id, &key.backend_id)
            & ct_eq_bytes_mask(&self.kernel_sha256, &pin.sha256_digest);
        for (&actual, &expected) in self.kernel_poseidon2.iter().zip(&pin.poseidon2_digest) {
            ok &= ct_eq_mask_u64(actual, expected);
        }
        ok & ct_eq_bytes_mask(&self.mac, &self.mac_over_fields(key))
    }
}

/// Zero-dependency `#![no_std]` hardware/GPU accelerator trait.
///
/// External certified RDNA2 / SPIR-V / FPGA host crates implement this trait without forcing
/// `wgpu`, `ash`, or OS GPU driver dependencies into core post-quantum cryptography crates.
pub trait AcceleratorBackend: Send + Sync {
    /// Hardware audit evidence bound by receipt helpers. Software backends use zero.
    fn hardware_audit_digest(&self) -> [u8; 32] {
        [0; 32]
    }

    /// Target architecture reported by this backend.
    fn target_arch(&self) -> KernelTargetArch;

    /// Certified kernel pin for `slot`.
    fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin;

    /// Number of explicitly fallback-enabled calls answered by the CPU reference after
    /// hardware failure. Pinned calls never fall back. Vulkan's legacy infallible methods
    /// panic on failure; its `*_with_cpu_fallback` methods return per-call outcomes.
    fn cpu_fallback_count(&self) -> u64 {
        0
    }

    /// Parallel 24-round `Keccak-f[1600]` across `states` (accelerating WOTS+/FORS/FTS chains & OT).
    fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]);

    /// Fallible `Keccak-f[1600]` batch execution returning the exact [`CertifiedKernelPin`] of the
    /// kernel that actually executed (`Err` if hardware execution failed instead of misattributing
    /// a CPU fallback to a hardware kernel pin).
    fn try_batch_keccak_f1600_pinned(
        &self,
        states: &mut [[u64; 25]],
    ) -> Result<CertifiedKernelPin, AccelError> {
        self.batch_keccak_f1600(states);
        Ok(self.kernel_pin(KernelSlot::BatchKeccakF1600))
    }

    /// Parallel Width-12 canonical Goldilocks `Poseidon2` (`p = 2^64 - 2^32 + 1`) across `states`.
    fn batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]);

    /// Fallible Width-12 `Poseidon2` batch execution returning the exact [`CertifiedKernelPin`] of
    /// the kernel that actually executed (`Err` if hardware execution failed instead of
    /// misattributing a CPU fallback to a hardware kernel pin).
    fn try_batch_poseidon2_perm12_pinned(
        &self,
        states: &mut [[u64; 12]],
    ) -> Result<CertifiedKernelPin, AccelError> {
        self.batch_poseidon2_perm12(states);
        Ok(self.kernel_pin(KernelSlot::BatchPoseidon2Perm12))
    }

    /// In-place radix-2 Goldilocks NTT (`inverse == false`) and inverse NTT (`inverse == true`).
    ///
    /// Public `twiddles` must be successive powers of a primitive root, as produced by
    /// [`goldilocks::precompute_goldilocks_twiddles`].
    /// `buf.len()` must be a power of two and `twiddles.len() == buf.len() / 2`; otherwise an
    /// [`AccelError`] is returned and `buf` is left untouched.
    fn goldilocks_ntt_inplace(
        &self,
        buf: &mut [u64],
        twiddles: &[u64],
        inverse: bool,
    ) -> Result<(), AccelError>;

    /// Shifted-coset Reed-Solomon LDE over $\mathbb{F}_{p^2}$ (`out.len() == evals.len() * blowup`).
    fn coset_lde_ext2(
        &self,
        evals: &[[u64; 2]],
        blowup: usize,
        shift: u64,
        out: &mut [[u64; 2]],
    ) -> Result<(), AccelError>;

    /// Batch Poseidon2 Merkle compression binding **all 4 limbs `pk_seed[0..4]`** and `layer`
    /// starting at parent index `0` (`children.len() == 2 * out_parents.len()`).
    fn try_merkle_layer_poseidon2(
        &self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        self.try_merkle_layer_poseidon2_at(children, pk_seed, layer, 0, out_parents)
    }

    /// Position-tweaked batch Poseidon2 Merkle compression binding **all 4 limbs `pk_seed[0..4]`**,
    /// `layer`, and global parent index `start_parent_idx + parent_idx`
    /// (`children.len() == 2 * out_parents.len()`; supported parent indices lie in `0..=u32::MAX`).
    fn try_merkle_layer_poseidon2_at(
        &self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError>;

    /// Fallible alias for [`Self::try_merkle_layer_poseidon2`] (`0` panics).
    fn merkle_layer_poseidon2(
        &self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        self.try_merkle_layer_poseidon2(children, pk_seed, layer, out_parents)
    }

    /// Fallible alias for [`Self::try_merkle_layer_poseidon2_at`] (`0` panics).
    fn merkle_layer_poseidon2_at(
        &self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        self.try_merkle_layer_poseidon2_at(children, pk_seed, layer, start_parent_idx, out_parents)
    }

    /// 2-lane BDOZ GF($2^{128}$) inner product over $\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)$
    /// (`shares.len() == weights.len()`).
    fn bdoz_gf2_128_batch_dot(
        &self,
        shares: &[(u128, u128)],
        weights: &[(u128, u128)],
    ) -> Result<(u128, u128), AccelError>;
}

/// 100% constant-time, branchless CPU reference implementation of [`AcceleratorBackend`].
#[derive(Clone, Copy, Debug, Default)]
pub struct CpuReferenceBackend;

impl CpuReferenceBackend {
    pub const fn new() -> Self {
        Self
    }

    pub fn canonical_pin(slot: KernelSlot) -> CertifiedKernelPin {
        let tag: &[u8] = match slot {
            KernelSlot::BatchKeccakF1600 => b"QSAG.CPU_REF.KECCAK_F1600.V1",
            // Framing version; canonical Poseidon2-12 profile, also registered in Lean.
            KernelSlot::BatchPoseidon2Perm12 => b"QSAG.CPU_REF.POSEIDON2_PERM12.V1",
            KernelSlot::GoldilocksNtt => b"QSAG.CPU_REF.GOLDILOCKS_NTT.V1",
            KernelSlot::CosetLdeExt2 => b"QSAG.CPU_REF.COSET_LDE_EXT2.V1",
            KernelSlot::MerkleLayerPoseidon2 => b"QSAG.CPU_REF.MERKLE_POSEIDON2.V1",
            KernelSlot::BdozGf2128BatchDot => b"QSAG.CPU_REF.BDOZ_GF2_128_DOT.V1",
        };
        CertifiedKernelPin::from_kernel_artifact(slot, KernelTargetArch::CpuReference, tag)
    }

    /// Evaluate a Poseidon2 Merkle layer on `backend` and issue a keyed receipt binding the
    /// backend's kernel pin, the job descriptor, `transcript_anchor`, and digests of `children`
    /// and `out_parents`. Same as [`vulkan::merkle_layer_poseidon2_with_receipt`].
    pub fn merkle_layer_poseidon2_with_receipt<B: AcceleratorBackend>(
        backend: &B,
        key: &BackendAttestationKey,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        transcript_anchor: [u8; 32],
        out_parents: &mut [[u64; 4]],
    ) -> Result<ExecutionReceipt, AccelError> {
        vulkan::merkle_layer_poseidon2_with_receipt(
            backend,
            key,
            children,
            pk_seed,
            layer,
            transcript_anchor,
            out_parents,
        )
    }
}

/// Digest of a Merkle layer's children as bound into `ExecutionReceipt::input_digest`.
pub fn merkle_layer_input_digest(children: &[[u64; 4]]) -> [u8; 32] {
    hash_u64_rows(b"QSAG.ACCEL.MERKLE_IN.V1", children)
}

/// Digest of a Merkle layer's parents as bound into `ExecutionReceipt::output_digest`.
pub fn merkle_layer_output_digest(parents: &[[u64; 4]]) -> [u8; 32] {
    hash_u64_rows(b"QSAG.ACCEL.MERKLE_OUT.V1", parents)
}

/// `cSHAKE256` under `cust` of `count` (little-endian `u64`) followed by `words` (little-endian).
pub(crate) fn hash_counted_u64s(cust: &[u8], count: usize, words: &[u64]) -> [u8; 32] {
    let mut sp = keccak::init_cshake256(b"", cust);
    sp.absorb(&(count as u64).to_le_bytes());
    for &word in words {
        sp.absorb(&word.to_le_bytes());
    }
    keccak::finalize_cshake256(&mut sp, true);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// Digest of fixed-width limb rows: the row count, then every limb in row order.
pub(crate) fn hash_u64_rows<const W: usize>(cust: &[u8], rows: &[[u64; W]]) -> [u8; 32] {
    hash_counted_u64s(cust, rows.len(), rows.as_flattened())
}

impl AcceleratorBackend for CpuReferenceBackend {
    fn target_arch(&self) -> KernelTargetArch {
        KernelTargetArch::CpuReference
    }

    fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
        Self::canonical_pin(slot)
    }

    fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]) {
        qsag_asm::keccak_f1600_batch(states);
    }

    fn batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]) {
        for st in states.iter_mut() {
            poseidon2_perm12(st);
        }
    }

    fn goldilocks_ntt_inplace(
        &self,
        buf: &mut [u64],
        twiddles: &[u64],
        inverse: bool,
    ) -> Result<(), AccelError> {
        goldilocks_ntt_cpu(buf, twiddles, inverse)
    }

    fn coset_lde_ext2(
        &self,
        evals: &[[u64; 2]],
        blowup: usize,
        shift: u64,
        out: &mut [[u64; 2]],
    ) -> Result<(), AccelError> {
        coset_lde_ext2_cpu(evals, blowup, shift, out)
    }

    fn try_merkle_layer_poseidon2_at(
        &self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        merkle_layer_poseidon2_at_cpu(children, pk_seed, layer, start_parent_idx, out_parents)
    }

    fn bdoz_gf2_128_batch_dot(
        &self,
        shares: &[(u128, u128)],
        weights: &[(u128, u128)],
    ) -> Result<(u128, u128), AccelError> {
        bdoz_gf2_128_batch_dot_cpu(shares, weights)
    }
}

/// Fixed-capacity `#![no_std]` registry pinning SHA-256 & Poseidon2 digests of certified
/// CPU, RDNA2 Wave32, and SPIR-V 1.5 GPU compute kernels (`MAX_PROFILES` architectures).
#[derive(Clone, Debug)]
pub struct VerifiedKernelDigestRegistry<const MAX_PROFILES: usize = 4> {
    profiles: [Option<(KernelTargetArch, [CertifiedKernelPin; KernelSlot::COUNT])>; MAX_PROFILES],
    len: usize,
}

/// Error returned when an external accelerator presents an uncertified or mismatched kernel digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelRegistryError {
    RegistryFull,
    LoaderMeasurementRequired,
    UnsupportedTargetArch(KernelTargetArch),
    PinMismatch {
        slot: KernelSlot,
    },
    /// The receipt's backend ID, kernel digests, or MAC did not verify under the supplied key.
    ReceiptAuthenticationFailed,
}

impl<const MAX_PROFILES: usize> Default for VerifiedKernelDigestRegistry<MAX_PROFILES> {
    fn default() -> Self {
        Self::with_cpu_reference_pins()
    }
}

impl<const MAX_PROFILES: usize> VerifiedKernelDigestRegistry<MAX_PROFILES> {
    pub const fn empty() -> Self {
        Self {
            profiles: [None; MAX_PROFILES],
            len: 0,
        }
    }

    /// Pins only the portable reference implementation's version metadata.
    /// CPU pins are identifiers, not measurements of the running process.
    pub fn with_cpu_reference_pins() -> Self {
        let mut reg = Self::empty();
        let pins = KernelSlot::ALL.map(CpuReferenceBackend::canonical_pin);
        let _ = reg.register_arch_pins(KernelTargetArch::CpuReference, pins);
        reg
    }

    /// Approve the CPU reference metadata and the compiled canonical SPIR-V module digests.
    /// This is deterministic even without a Vulkan device. Probe availability separately with
    /// [`VulkanSpirvBackend::try_new`], which reports loader, device, and audit errors explicitly.
    ///
    /// # Panics
    /// Panics if `MAX_PROFILES < 2`; never silently returns a CPU-only registry.
    pub fn with_cpu_and_canonical_gpu_pins() -> Self {
        Self::with_cpu_and_spirv_pins()
    }

    /// Registry pre-populated with both the portable CPU reference profile and the deterministic
    /// embedded `KernelTargetArch::SpirV15` compute shader pins (`MAX_PROFILES >= 2`).
    ///
    /// # Panics
    /// Panics if fewer than two profiles fit in this registry.
    pub fn with_cpu_and_spirv_pins() -> Self {
        let mut reg = Self::with_cpu_reference_pins();
        reg.register_arch_pins(
            KernelTargetArch::SpirV15,
            spirv_kernels::canonical_spirv_pins(),
        )
        .expect("CPU and SPIR-V registry requires at least two profiles");
        reg
    }

    /// Register trusted measurements supplied by the caller's artifact approval process.
    /// This does not prove correctness of the artifact or of any returned results.
    pub fn register_measured_profile(
        &mut self,
        arch: KernelTargetArch,
        pins: [CertifiedKernelPin; KernelSlot::COUNT],
    ) -> Result<(), KernelRegistryError> {
        self.register_arch_pins(arch, pins)
    }

    /// Compare independently loader-measured artifacts with approved pins.
    /// The loader must measure the bytes it loads, and protect the measurement channel.
    pub fn verify_loaded_profile(
        &self,
        arch: KernelTargetArch,
        measured: &[CertifiedKernelPin; KernelSlot::COUNT],
    ) -> Result<(), KernelRegistryError> {
        for (slot, actual) in KernelSlot::ALL.iter().zip(measured) {
            let expected = self.lookup_pin(arch, *slot)?;
            if actual.slot != *slot
                || actual.target_arch != arch
                || ct_eq_bytes_mask(&expected.sha256_digest, &actual.sha256_digest) == 0
                || expected.poseidon2_digest != actual.poseidon2_digest
            {
                return Err(KernelRegistryError::PinMismatch { slot: *slot });
            }
        }
        Ok(())
    }

    /// Verify a keyed receipt against this registry's approved pin for the receipt's
    /// `(arch, slot)` and against `key`.
    ///
    /// Succeeds only if the receipt names `key`'s backend, carries exactly the approved kernel
    /// digests, and its MAC over every field verifies. Authentication proves which key holder
    /// issued the report, not that the reported computation is correct.
    pub fn verify_keyed_receipt(
        &self,
        receipt: &ExecutionReceipt,
        key: &BackendAttestationKey,
    ) -> Result<(), KernelRegistryError> {
        let pin = self.lookup_pin(receipt.arch, receipt.descriptor.slot())?;
        if receipt.verification_mask(key, pin) == u64::MAX {
            Ok(())
        } else {
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        }
    }

    pub fn register_arch_pins(
        &mut self,
        arch: KernelTargetArch,
        pins: [CertifiedKernelPin; KernelSlot::COUNT],
    ) -> Result<(), KernelRegistryError> {
        for (idx, pin) in pins.iter().enumerate() {
            if pin.target_arch != arch || (pin.slot as usize) != idx {
                return Err(KernelRegistryError::PinMismatch {
                    slot: KernelSlot::ALL[idx],
                });
            }
        }
        for (existing_arch, existing_pins) in self.profiles.iter_mut().take(self.len).flatten() {
            if *existing_arch == arch {
                *existing_pins = pins;
                return Ok(());
            }
        }
        if self.len >= MAX_PROFILES {
            return Err(KernelRegistryError::RegistryFull);
        }
        self.profiles[self.len] = Some((arch, pins));
        self.len += 1;
        Ok(())
    }

    pub fn lookup_pin(
        &self,
        arch: KernelTargetArch,
        slot: KernelSlot,
    ) -> Result<&CertifiedKernelPin, KernelRegistryError> {
        for entry in self.profiles.iter().take(self.len).flatten() {
            if entry.0 == arch {
                return Ok(&entry.1[slot as usize]);
            }
        }
        Err(KernelRegistryError::UnsupportedTargetArch(arch))
    }

    /// Compare self-reported metadata only. Use independent loader measurements for hardware.
    pub fn verify_backend<B: AcceleratorBackend>(
        &self,
        backend: &B,
    ) -> Result<(), KernelRegistryError> {
        let arch = backend.target_arch();
        for slot in KernelSlot::ALL {
            let expected = self.lookup_pin(arch, slot)?;
            let actual = backend.kernel_pin(slot);
            let mut digests_ok = ct_eq_bytes_mask(&expected.sha256_digest, &actual.sha256_digest);
            for (&e, &a) in expected
                .poseidon2_digest
                .iter()
                .zip(&actual.poseidon2_digest)
            {
                digests_ok &= ct_eq_mask_u64(e, a);
            }
            if digests_ok != u64::MAX || actual.slot != slot || actual.target_arch != arch {
                return Err(KernelRegistryError::PinMismatch { slot });
            }
        }
        Ok(())
    }
}

/// Wrapper checking approved metadata and, for external hardware, loader measurements.
/// It provides no mathematical proof of backend correctness.
pub struct CertifiedBackend<B: AcceleratorBackend> {
    inner: B,
}

impl<B: AcceleratorBackend> CertifiedBackend<B> {
    pub fn try_new<const M: usize>(
        backend: B,
        registry: &VerifiedKernelDigestRegistry<M>,
    ) -> Result<Self, KernelRegistryError> {
        if backend.target_arch() != KernelTargetArch::CpuReference {
            return Err(KernelRegistryError::LoaderMeasurementRequired);
        }
        registry.verify_backend(&backend)?;
        Ok(Self { inner: backend })
    }

    /// The caller supplies measurements from its trusted loader, independently of B.
    pub fn try_new_measured<const M: usize>(
        backend: B,
        registry: &VerifiedKernelDigestRegistry<M>,
        measured: &[CertifiedKernelPin; KernelSlot::COUNT],
    ) -> Result<Self, KernelRegistryError> {
        registry.verify_loaded_profile(backend.target_arch(), measured)?;
        registry.verify_backend(&backend)?;
        Ok(Self { inner: backend })
    }

    pub const fn inner(&self) -> &B {
        &self.inner
    }
}

impl<B: AcceleratorBackend> AcceleratorBackend for CertifiedBackend<B> {
    fn hardware_audit_digest(&self) -> [u8; 32] {
        self.inner.hardware_audit_digest()
    }

    fn target_arch(&self) -> KernelTargetArch {
        self.inner.target_arch()
    }
    fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
        self.inner.kernel_pin(slot)
    }
    fn cpu_fallback_count(&self) -> u64 {
        self.inner.cpu_fallback_count()
    }
    fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]) {
        self.inner.batch_keccak_f1600(states);
    }
    fn try_batch_keccak_f1600_pinned(
        &self,
        states: &mut [[u64; 25]],
    ) -> Result<CertifiedKernelPin, AccelError> {
        self.inner.try_batch_keccak_f1600_pinned(states)
    }
    fn batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]) {
        self.inner.batch_poseidon2_perm12(states);
    }
    fn try_batch_poseidon2_perm12_pinned(
        &self,
        states: &mut [[u64; 12]],
    ) -> Result<CertifiedKernelPin, AccelError> {
        self.inner.try_batch_poseidon2_perm12_pinned(states)
    }
    fn goldilocks_ntt_inplace(
        &self,
        buf: &mut [u64],
        twiddles: &[u64],
        inverse: bool,
    ) -> Result<(), AccelError> {
        self.inner.goldilocks_ntt_inplace(buf, twiddles, inverse)
    }
    fn coset_lde_ext2(
        &self,
        evals: &[[u64; 2]],
        blowup: usize,
        shift: u64,
        out: &mut [[u64; 2]],
    ) -> Result<(), AccelError> {
        self.inner.coset_lde_ext2(evals, blowup, shift, out)
    }
    fn try_merkle_layer_poseidon2_at(
        &self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        self.inner.try_merkle_layer_poseidon2_at(
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
        self.inner.bdoz_gf2_128_batch_dot(shares, weights)
    }
}

/// Convenience helper checking SHA-256 digest equality in constant time.
pub fn verify_sha256_pin(artifact: &[u8], expected: &[u8; 32]) -> bool {
    let actual = sha256(artifact);
    ct_eq_bytes_mask(&actual, expected) == u64::MAX
}

impl core::fmt::Display for KernelRegistryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::RegistryFull => f.write_str("kernel digest registry is full"),
            Self::LoaderMeasurementRequired => {
                f.write_str("non-CPU backends require independent loader measurements")
            }
            Self::UnsupportedTargetArch(arch) => {
                write!(
                    f,
                    "no approved kernel pins for target architecture {arch:?}"
                )
            }
            Self::PinMismatch { slot } => write!(f, "kernel pin mismatch for slot {slot:?}"),
            Self::ReceiptAuthenticationFailed => {
                f.write_str("execution receipt failed keyed authentication")
            }
        }
    }
}

impl core::error::Error for KernelRegistryError {}

/// Deterministically recompute sampled Merkle parents on the CPU.
/// Choose the challenge after the device fixes its output. Known-ahead samples can
/// be evaded; checking all parents gives full equality for this operation only.
pub fn spot_check_merkle_layer(
    children: &[[u64; 4]],
    pk_seed: &[u64; 4],
    layer: u32,
    start_parent_idx: u64,
    parents: &[[u64; 4]],
    challenge: &[u8; 32],
    checks: usize,
) -> bool {
    if parents.is_empty()
        || children.len() != parents.len().saturating_mul(2)
        || checks == 0
        || start_parent_idx.checked_add(parents.len() as u64).is_none()
    {
        return false;
    }
    for sample in 0..checks.min(parents.len()) {
        let idx = if checks >= parents.len() {
            sample
        } else {
            let digest = cshake256_framed_32(
                b"QSAG.ACCEL.MERKLE_SAMPLE.V1",
                &[challenge, &(sample as u64).to_be_bytes()],
            );
            let mut word = [0u8; 8];
            word.copy_from_slice(&digest[..8]);
            (u64::from_le_bytes(word) % parents.len() as u64) as usize
        };
        let mut expected = [[0; 4]; 1];
        if merkle_layer_poseidon2_at_cpu(
            &children[2 * idx..2 * idx + 2],
            pk_seed,
            layer,
            start_parent_idx + idx as u64,
            &mut expected,
        )
        .is_err()
            || expected[0] != parents[idx]
        {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf2_128::{gf2_128_inv_or_zero, gf2_128_mul};
    use crate::goldilocks::{
        GOLDILOCKS_PRIME, ext2_add, ext2_inv_or_zero, ext2_mul, gl_add, gl_inv_or_zero, gl_mul,
        gl_reduce128, goldilocks_primitive_root, pack_bytes32_to_limbs56,
        unpack_limbs56_to_bytes32,
    };

    #[test]
    fn test_goldilocks_corner_cases_and_inversion() {
        let p = GOLDILOCKS_PRIME;
        assert_eq!(gl_add(p - 1, 1), 0);
        assert_eq!(gl_add(p - 1, p - 1), p - 2);
        assert_eq!(gl_mul(p - 1, p - 1), 1);
        assert_eq!(
            gl_reduce128(u128::MAX),
            gl_reduce128(u128::MAX % (p as u128))
        );

        for x in [1u64, 2, 7, 123456789, p - 2, p - 1] {
            let inv = gl_inv_or_zero(x);
            assert_eq!(gl_mul(x, inv), 1);
        }
        assert_eq!(gl_inv_or_zero(0), 0);

        let a = [123_456_789u64, p - 42];
        let a_inv = ext2_inv_or_zero(a);
        assert_eq!(ext2_mul(a, a_inv), [1, 0]);
        assert_eq!(ext2_inv_or_zero([0, 0]), [0, 0]);
    }

    #[test]
    fn test_canonical_5limb_56bit_digest_roundtrip_and_non_aliasing() {
        let mut digest = [0xFFu8; 32];
        let limbs = pack_bytes32_to_limbs56(&digest);
        for &l in &limbs {
            assert!(l < (1u64 << 56));
            assert!(l < GOLDILOCKS_PRIME);
        }
        assert_eq!(unpack_limbs56_to_bytes32(&limbs), Some(digest));

        // Mutating byte 0 from p-alias values produces distinct 56-bit limbs (zero mod-p collision).
        let mut digest2 = digest;
        digest2[0] ^= 0x01;
        assert_ne!(limbs, pack_bytes32_to_limbs56(&digest2));

        // Non-canonical >= 2^56 limb or corrupted delimiter must be rejected.
        let mut bad = limbs;
        bad[0] = 1u64 << 56;
        assert_eq!(unpack_limbs56_to_bytes32(&bad), None);
        let mut bad_delim = limbs;
        bad_delim[4] ^= 1;
        assert_eq!(unpack_limbs56_to_bytes32(&bad_delim), None);
        digest.fill(0);
        assert_eq!(
            unpack_limbs56_to_bytes32(&pack_bytes32_to_limbs56(&digest)),
            Some([0u8; 32])
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_ntt_roundtrip_and_coset_lde_horner_identity() {
        let backend = CpuReferenceBackend::new();
        let n = 16usize;
        let tw = goldilocks::precompute_goldilocks_twiddles(n).unwrap();
        let coeffs: [u64; 16] = core::array::from_fn(|i| (i as u64 * 97 + 13) % GOLDILOCKS_PRIME);
        let mut buf = coeffs;

        backend
            .goldilocks_ntt_inplace(&mut buf, &tw, false)
            .unwrap();
        // Check against direct polynomial evaluation at omega^k
        let omega_n = goldilocks_primitive_root(4).unwrap();
        let mut wk = 1u64;
        for &ev in &buf {
            let mut expected = 0u64;
            let mut x_pow = 1u64;
            for &c in &coeffs {
                expected = gl_add(expected, gl_mul(c, x_pow));
                x_pow = gl_mul(x_pow, wk);
            }
            assert_eq!(ev, expected);
            wk = gl_mul(wk, omega_n);
        }

        backend.goldilocks_ntt_inplace(&mut buf, &tw, true).unwrap();
        assert_eq!(buf, coeffs);

        // Verify coset_lde_ext2 against direct Horner evaluation over F_{p^2}!
        let coeffs_ext2: [[u64; 2]; 8] =
            core::array::from_fn(|i| [(i as u64 + 3) * 19, (i as u64 + 1) * 41]);
        let omega_8 = goldilocks_primitive_root(3).unwrap();
        let mut evals_h = [[0u64; 2]; 8];
        let mut x = 1u64;
        for slot in &mut evals_h {
            let mut acc = [0u64, 0u64];
            for &c in coeffs_ext2.iter().rev() {
                acc = ext2_add(goldilocks::ext2_scale_base(acc, x), c);
            }
            *slot = acc;
            x = gl_mul(x, omega_8);
        }

        let blowup = 4usize;
        let shift = 7u64;
        let mut lde_out = [[0u64; 2]; 32];
        backend
            .coset_lde_ext2(&evals_h, blowup, shift, &mut lde_out)
            .unwrap();

        let omega_32 = goldilocks_primitive_root(5).unwrap();
        let mut w_i = 1u64;
        for &lde_val in &lde_out {
            let pt = gl_mul(shift, w_i);
            let mut expected = [0u64, 0u64];
            for &c in coeffs_ext2.iter().rev() {
                expected = ext2_add(goldilocks::ext2_scale_base(expected, pt), c);
            }
            assert_eq!(lde_val, expected);
            w_i = gl_mul(w_i, omega_32);
        }
    }

    #[test]
    fn test_merkle_poseidon2_binds_all_four_pk_seed_limbs_and_receipt() {
        let registry: VerifiedKernelDigestRegistry<4> = VerifiedKernelDigestRegistry::default();
        let backend = CertifiedBackend::try_new(CpuReferenceBackend::new(), &registry).unwrap();

        let children = [
            [11u64, 22, 33, 44],
            [55u64, 66, 77, 88],
            [99u64, 111, 222, 333],
            [444u64, 555, 666, 777],
        ];
        let base_seed = [1001u64, 2002, 3003, 4004];
        let anchor = [0x42u8; 32];
        let mut base_out = [[0u64; 4]; 2];
        let key = BackendAttestationKey::derive(&[0x17; 32], b"cpu-reference-0");
        let receipt = CpuReferenceBackend::merkle_layer_poseidon2_with_receipt(
            &backend,
            &key,
            &children,
            &base_seed,
            3,
            anchor,
            &mut base_out,
        )
        .unwrap();
        assert_eq!(registry.verify_keyed_receipt(&receipt, &key), Ok(()));
        assert_eq!(receipt.input_digest, merkle_layer_input_digest(&children));
        assert_eq!(receipt.output_digest, merkle_layer_output_digest(&base_out));

        // Mutating ANY of pk_seed[0], pk_seed[1], pk_seed[2], or pk_seed[3] MUST change parent digests!
        for limb_idx in 0..4 {
            let mut alt_seed = base_seed;
            alt_seed[limb_idx] += 1;
            let mut alt_out = [[0u64; 4]; 2];
            backend
                .try_merkle_layer_poseidon2(&children, &alt_seed, 3, &mut alt_out)
                .unwrap();
            assert_ne!(base_out, alt_out, "pk_seed[{limb_idx}] was ignored!");
        }
    }

    #[test]
    fn test_gf2_128_inversion_and_bdoz_dot() {
        let a = 0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210u128;
        let inv = gf2_128_inv_or_zero(a);
        assert_eq!(gf2_128_mul(a, inv), 1u128);
        assert_eq!(gf2_128_inv_or_zero(0), 0);

        let backend = CpuReferenceBackend::new();
        let s_a = [(11u128, 22u128), (33u128, 44u128)];
        let s_b = [(55u128, 66u128), (77u128, 88u128)];
        let s_xor = [(11u128 ^ 55, 22u128 ^ 66), (33u128 ^ 77, 44u128 ^ 88)];
        let w = [
            (0xAA55_1234u128, 0x9988_7766u128),
            (0xDEAD_BEEFu128, 0xCAFE_BABEu128),
        ];
        let d_a = backend.bdoz_gf2_128_batch_dot(&s_a, &w).unwrap();
        let d_b = backend.bdoz_gf2_128_batch_dot(&s_b, &w).unwrap();
        let d_xor = backend.bdoz_gf2_128_batch_dot(&s_xor, &w).unwrap();
        assert_eq!((d_a.0 ^ d_b.0, d_a.1 ^ d_b.1), d_xor);
    }

    #[test]
    fn test_standard_hash_vectors_sha256_sha512_ripemd160_sha3_keccak() {
        // NIST SHA-256("abc")
        let s256 = sha2::sha256(b"abc");
        assert_eq!(
            s256,
            [
                0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae,
                0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61,
                0xf2, 0x00, 0x15, 0xad,
            ]
        );
        // RIPEMD-160("abc") = 8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
        let r160 = sha2::ripemd160(b"abc");
        assert_eq!(
            r160,
            [
                0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04, 0x4a, 0x8e, 0x98, 0xc6,
                0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc,
            ]
        );
        // SHA3-256("") = a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a
        let s3 = keccak::sha3_256(b"");
        assert_eq!(
            s3,
            [
                0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61,
                0xd6, 0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa, 0x82, 0xd8, 0x0a, 0x4b,
                0x80, 0xf8, 0x43, 0x4a,
            ]
        );
        // Keccak-256("") = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
        let k256 = keccak::keccak256(b"");
        assert_eq!(
            k256,
            [
                0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7,
                0x03, 0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b, 0x7b, 0xfa, 0xd8, 0x04,
                0x5d, 0x85, 0xa4, 0x70,
            ]
        );
    }

    #[test]
    fn test_uncertified_backend_rejected_by_registry() {
        struct RogueGpuBackend;
        impl AcceleratorBackend for RogueGpuBackend {
            fn target_arch(&self) -> KernelTargetArch {
                KernelTargetArch::Rdna2Wave32
            }
            fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
                CertifiedKernelPin::from_kernel_artifact(
                    slot,
                    KernelTargetArch::Rdna2Wave32,
                    b"TAMPERED_SHADER",
                )
            }
            fn batch_keccak_f1600(&self, s: &mut [[u64; 25]]) {
                CpuReferenceBackend.batch_keccak_f1600(s);
            }
            fn batch_poseidon2_perm12(&self, s: &mut [[u64; 12]]) {
                CpuReferenceBackend.batch_poseidon2_perm12(s);
            }
            fn goldilocks_ntt_inplace(
                &self,
                b: &mut [u64],
                t: &[u64],
                i: bool,
            ) -> Result<(), AccelError> {
                CpuReferenceBackend.goldilocks_ntt_inplace(b, t, i)
            }
            fn coset_lde_ext2(
                &self,
                e: &[[u64; 2]],
                b: usize,
                s: u64,
                o: &mut [[u64; 2]],
            ) -> Result<(), AccelError> {
                CpuReferenceBackend.coset_lde_ext2(e, b, s, o)
            }
            fn try_merkle_layer_poseidon2_at(
                &self,
                c: &[[u64; 4]],
                p: &[u64; 4],
                l: u32,
                s: u64,
                o: &mut [[u64; 4]],
            ) -> Result<(), AccelError> {
                CpuReferenceBackend.try_merkle_layer_poseidon2_at(c, p, l, s, o)
            }
            fn bdoz_gf2_128_batch_dot(
                &self,
                s: &[(u128, u128)],
                w: &[(u128, u128)],
            ) -> Result<(u128, u128), AccelError> {
                CpuReferenceBackend.bdoz_gf2_128_batch_dot(s, w)
            }
        }

        let reg: VerifiedKernelDigestRegistry<4> = VerifiedKernelDigestRegistry::default();
        let res = CertifiedBackend::try_new(RogueGpuBackend, &reg);
        assert!(matches!(
            res,
            Err(KernelRegistryError::LoaderMeasurementRequired)
        ));
    }

    fn sample_receipt(key: &BackendAttestationKey) -> ExecutionReceipt {
        let pin = CpuReferenceBackend::canonical_pin(KernelSlot::BatchKeccakF1600);
        let job = BatchJobDescriptor::KeccakF1600 { num_states: 1 };
        ExecutionReceipt::compute_keyed(key, &pin, job, [1; 32], [2; 32], [3; 32]).unwrap()
    }

    #[test]
    fn hardware_receipt_requires_and_authenticates_audit_evidence() {
        let key = BackendAttestationKey::derive(&[29; 32], b"audited-device");
        let pin = spirv_kernels::canonical_spirv_pin(KernelSlot::BatchKeccakF1600);
        let job = BatchJobDescriptor::KeccakF1600 { num_states: 1 };
        assert_eq!(
            ExecutionReceipt::compute_keyed(&key, &pin, job, [1; 32], [2; 32], [3; 32]),
            Err(AccelError::SecretSlotUnaudited { slot: pin.slot })
        );
        let mut receipt =
            ExecutionReceipt::compute_audited(&key, &pin, job, [1; 32], [2; 32], [3; 32], [4; 32])
                .unwrap();
        assert_eq!(receipt.verification_mask(&key, &pin), u64::MAX);
        receipt.hardware_audit_digest[0] ^= 1;
        assert_eq!(receipt.verification_mask(&key, &pin), 0);
    }

    #[test]
    fn keyed_receipt_verifies_only_under_its_own_key_and_backend() {
        let reg = VerifiedKernelDigestRegistry::<4>::default();
        let key = BackendAttestationKey::derive(&[29; 32], b"backend-a");
        let receipt = sample_receipt(&key);
        assert_eq!(reg.verify_keyed_receipt(&receipt, &key), Ok(()));

        let failed = Err(KernelRegistryError::ReceiptAuthenticationFailed);
        // Same master secret, different backend label: different ID and different key.
        let sibling = BackendAttestationKey::derive(&[29; 32], b"backend-b");
        assert_eq!(reg.verify_keyed_receipt(&receipt, &sibling), failed);
        // Different master secret, same label.
        let stranger = BackendAttestationKey::derive(&[30; 32], b"backend-a");
        assert_eq!(reg.verify_keyed_receipt(&receipt, &stranger), failed);
        // Same key bytes presented under another backend ID.
        let relabeled = BackendAttestationKey::new([0xEE; 32], *key.key.expose());
        assert_eq!(reg.verify_keyed_receipt(&receipt, &relabeled), failed);
        // A receipt self-issued by a party that knows the backend ID but not the key.
        let forger = BackendAttestationKey::new(*key.backend_id(), [0u8; 32]);
        assert_eq!(
            reg.verify_keyed_receipt(&sample_receipt(&forger), &key),
            failed
        );
    }

    #[test]
    fn keyed_receipt_rejects_tampering_of_every_bound_field() {
        let reg = VerifiedKernelDigestRegistry::<4>::default();
        let key = BackendAttestationKey::derive(&[29; 32], b"backend-a");
        let good = sample_receipt(&key);
        let failed = Err(KernelRegistryError::ReceiptAuthenticationFailed);
        let tamper: [fn(&mut ExecutionReceipt); 10] = [
            |r| r.backend_id[31] ^= 1,
            |r| r.descriptor = BatchJobDescriptor::KeccakF1600 { num_states: 2 },
            |r| r.descriptor = BatchJobDescriptor::Poseidon2Perm12 { num_states: 1 },
            |r| r.kernel_sha256[0] ^= 1,
            |r| r.kernel_poseidon2[3] ^= 1,
            |r| r.transcript_anchor[7] ^= 0x80,
            |r| r.hardware_audit_digest[7] ^= 0x80,
            |r| r.input_digest[0] ^= 1,
            |r| r.output_digest[0] ^= 1,
            |r| r.mac[15] ^= 1,
        ];
        for (i, f) in tamper.iter().enumerate() {
            let mut bad = good;
            f(&mut bad);
            assert_eq!(
                reg.verify_keyed_receipt(&bad, &key),
                failed,
                "tamper case {i}"
            );
        }
        let mut wrong_arch = good;
        wrong_arch.arch = KernelTargetArch::SpirV15;
        assert_eq!(
            reg.verify_keyed_receipt(&wrong_arch, &key),
            Err(KernelRegistryError::UnsupportedTargetArch(
                KernelTargetArch::SpirV15
            ))
        );
    }

    #[test]
    fn spirv_label_names_the_embedded_header_version_and_retires_the_old_byte() {
        assert_eq!(KernelTargetArch::SpirV15 as u8, 0x05);
        for arch in [
            KernelTargetArch::CpuReference,
            KernelTargetArch::Rdna2Wave32,
            KernelTargetArch::CustomHardware,
            KernelTargetArch::SpirV15,
        ] {
            assert_ne!(
                arch as u8, 0x03,
                "{arch:?} reuses the retired SPIR-V 1.6 byte"
            );
        }
        for slot in KernelSlot::ALL {
            let bytes = spirv_kernels::spirv_kernel_bytes(slot);
            let version = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
            let pin = spirv_kernels::canonical_spirv_pin(slot);
            assert_eq!(pin.target_arch, KernelTargetArch::SpirV15);
            assert_eq!(
                pin.target_arch.spirv_version_word(),
                Some(version),
                "{slot:?}: pin label disagrees with the module header"
            );
        }
        assert_eq!(KernelTargetArch::CpuReference.spirv_version_word(), None);
    }

    #[test]
    fn receipt_issued_under_the_previous_domain_no_longer_verifies() {
        let reg = VerifiedKernelDigestRegistry::<4>::default();
        let key = BackendAttestationKey::derive(&[29; 32], b"backend-a");
        let good = sample_receipt(&key);
        assert_eq!(reg.verify_keyed_receipt(&good, &key), Ok(()));

        let mut p2_bytes = [0u8; 32];
        for (chunk, limb) in p2_bytes
            .as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(&good.kernel_poseidon2)
        {
            *chunk = limb.to_le_bytes();
        }
        let mac_under = |domain: &[u8]| {
            cshake256_framed_32(
                domain,
                &[
                    key.key.expose(),
                    &good.backend_id,
                    good.descriptor.slot().algorithm_domain(),
                    &[good.arch as u8],
                    &good.descriptor.to_canonical_bytes(),
                    &good.kernel_sha256,
                    &p2_bytes,
                    &good.transcript_anchor,
                    &good.hardware_audit_digest,
                    &good.input_digest,
                    &good.output_digest,
                ],
            )
        };
        // The field layout below is the live one, so only the domain differs from a V3 receipt.
        assert_eq!(mac_under(b"QSAG.ACCEL.KEYED_RECEIPT.V5"), good.mac);
        let mut old = good;
        old.mac = mac_under(b"QSAG.ACCEL.KEYED_RECEIPT.V3");
        assert_eq!(
            reg.verify_keyed_receipt(&old, &key),
            Err(KernelRegistryError::ReceiptAuthenticationFailed)
        );
    }

    #[test]
    fn cpu_fallback_count_defaults_to_zero_and_survives_certification() {
        struct Counting(u64);
        impl AcceleratorBackend for Counting {
            fn target_arch(&self) -> KernelTargetArch {
                KernelTargetArch::CpuReference
            }
            fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
                CpuReferenceBackend::canonical_pin(slot)
            }
            fn cpu_fallback_count(&self) -> u64 {
                self.0
            }
            fn batch_keccak_f1600(&self, s: &mut [[u64; 25]]) {
                CpuReferenceBackend.batch_keccak_f1600(s);
            }
            fn batch_poseidon2_perm12(&self, s: &mut [[u64; 12]]) {
                CpuReferenceBackend.batch_poseidon2_perm12(s);
            }
            fn goldilocks_ntt_inplace(
                &self,
                b: &mut [u64],
                t: &[u64],
                i: bool,
            ) -> Result<(), AccelError> {
                CpuReferenceBackend.goldilocks_ntt_inplace(b, t, i)
            }
            fn coset_lde_ext2(
                &self,
                e: &[[u64; 2]],
                b: usize,
                s: u64,
                o: &mut [[u64; 2]],
            ) -> Result<(), AccelError> {
                CpuReferenceBackend.coset_lde_ext2(e, b, s, o)
            }
            fn try_merkle_layer_poseidon2_at(
                &self,
                c: &[[u64; 4]],
                k: &[u64; 4],
                l: u32,
                i: u64,
                o: &mut [[u64; 4]],
            ) -> Result<(), AccelError> {
                CpuReferenceBackend.try_merkle_layer_poseidon2_at(c, k, l, i, o)
            }
            fn bdoz_gf2_128_batch_dot(
                &self,
                s: &[(u128, u128)],
                w: &[(u128, u128)],
            ) -> Result<(u128, u128), AccelError> {
                CpuReferenceBackend.bdoz_gf2_128_batch_dot(s, w)
            }
        }

        assert_eq!(CpuReferenceBackend.cpu_fallback_count(), 0);
        let reg = VerifiedKernelDigestRegistry::<4>::default();
        let certified = CertifiedBackend::try_new(Counting(7), &reg).expect("cpu-pinned mock");
        assert_eq!(certified.cpu_fallback_count(), 7);
    }

    #[test]
    fn receipt_macs_are_domain_separated_by_algorithm_slot() {
        let key = BackendAttestationKey::derive(&[29; 32], b"backend-a");
        for (i, a) in KernelSlot::ALL.iter().enumerate() {
            for b in &KernelSlot::ALL[i + 1..] {
                assert_ne!(a.algorithm_domain(), b.algorithm_domain());
            }
        }
        let pin = CpuReferenceBackend::canonical_pin(KernelSlot::BatchKeccakF1600);
        assert_eq!(
            ExecutionReceipt::compute_keyed(
                &key,
                &pin,
                BatchJobDescriptor::GoldilocksNtt {
                    length: 8,
                    inverse: false
                },
                [0; 32],
                [0; 32],
                [0; 32],
            ),
            Err(AccelError::KernelSlotMismatch {
                pin: KernelSlot::BatchKeccakF1600,
                descriptor: KernelSlot::GoldilocksNtt,
            })
        );
        assert_eq!(
            std::format!("{key:?}").matches("REDACTED").count(),
            1,
            "attestation key bytes must not be printed"
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn cpu_drain_runs_every_job_exactly_once_at_any_worker_count() {
        use core::sync::atomic::{AtomicU32, Ordering};
        for (jobs, workers) in [(0usize, 4usize), (1, 4), (3, 16), (64, 1), (1000, 7)] {
            let seen: std::vec::Vec<AtomicU32> = (0..jobs).map(|_| AtomicU32::new(0)).collect();
            cpu_drain(workers, 0..jobs, |i| {
                seen[i].fetch_add(1, Ordering::Relaxed);
            });
            assert!(
                seen.iter().all(|n| n.load(Ordering::Relaxed) == 1),
                "jobs={jobs} workers={workers}"
            );
        }
        // Uneven tails keep their offsets.
        let mut items = std::vec![0usize; 100_003];
        cpu_chunks_mut(&mut items, 1000, |offset, chunk| {
            for (i, x) in chunk.iter_mut().enumerate() {
                *x = offset + i;
            }
        });
        assert!(items.iter().enumerate().all(|(i, &x)| i == x));
    }

    #[test]
    fn kernels_return_typed_errors_for_malformed_shapes() {
        let backend = CpuReferenceBackend::new();
        let seed = [1u64, 2, 3, 4];
        let mut parents = [[0u64; 4]; 2];
        assert_eq!(
            backend.try_merkle_layer_poseidon2(&[[0u64; 4]; 3], &seed, 0, &mut parents),
            Err(AccelError::LengthMismatch {
                what: "Merkle layer children",
                expected: 4,
                actual: 3,
            })
        );
        assert_eq!(
            backend.merkle_layer_poseidon2(&[[0u64; 4]; 3], &seed, 0, &mut parents),
            Err(AccelError::LengthMismatch {
                what: "Merkle layer children",
                expected: 4,
                actual: 3,
            })
        );
        assert_eq!(
            backend.merkle_layer_poseidon2_at(&[[0u64; 4]; 3], &seed, 0, 0, &mut parents),
            Err(AccelError::LengthMismatch {
                what: "Merkle layer children",
                expected: 4,
                actual: 3,
            })
        );
        assert_eq!(parents, [[0u64; 4]; 2]);

        let mut buf = [5u64, 6, 7];
        assert_eq!(
            backend.goldilocks_ntt_inplace(&mut buf, &[1], false),
            Err(AccelError::NotPowerOfTwo {
                what: "NTT buffer",
                len: 3,
            })
        );
        let mut buf4 = [5u64, 6, 7, 8];
        assert_eq!(
            backend.goldilocks_ntt_inplace(&mut buf4, &[1], true),
            Err(AccelError::LengthMismatch {
                what: "NTT twiddles",
                expected: 2,
                actual: 1,
            })
        );
        assert_eq!(buf4, [5, 6, 7, 8]);
        assert_eq!(
            goldilocks::goldilocks_ntt_alloc_free(&mut [], false),
            Err(AccelError::NotPowerOfTwo {
                what: "NTT buffer",
                len: 0,
            })
        );
        assert_eq!(
            goldilocks_primitive_root(33),
            Err(AccelError::DomainTooLarge { log2_len: 33 })
        );

        let evals = [[1u64, 0]; 4];
        let mut out = [[0u64; 2]; 8];
        assert_eq!(
            backend.coset_lde_ext2(&evals, 3, 7, &mut out),
            Err(AccelError::NotPowerOfTwo {
                what: "LDE blowup",
                len: 3,
            })
        );
        assert_eq!(
            backend.coset_lde_ext2(&evals, 4, 7, &mut out),
            Err(AccelError::LengthMismatch {
                what: "LDE output",
                expected: 16,
                actual: 8,
            })
        );
        assert_eq!(
            backend.coset_lde_ext2(&evals[..3], 2, 7, &mut out),
            Err(AccelError::NotPowerOfTwo {
                what: "LDE evaluation domain",
                len: 3,
            })
        );
        // Empty and zero-factor transforms are shape errors on every entry point; a refused LDE
        // leaves `out` untouched.
        assert_eq!(
            backend.goldilocks_ntt_inplace(&mut [], &[], false),
            Err(AccelError::NotPowerOfTwo {
                what: "NTT buffer",
                len: 0,
            })
        );
        assert_eq!(
            backend.coset_lde_ext2(&[], 2, 7, &mut []),
            Err(AccelError::NotPowerOfTwo {
                what: "LDE evaluation domain",
                len: 0,
            })
        );
        assert_eq!(
            backend.coset_lde_ext2(&evals, 0, 7, &mut []),
            Err(AccelError::NotPowerOfTwo {
                what: "LDE blowup",
                len: 0,
            })
        );
        assert_eq!(out, [[0u64; 2]; 8]);
        // One-point transforms only canonicalize.
        let mut one = [u64::MAX];
        assert_eq!(backend.goldilocks_ntt_inplace(&mut one, &[], true), Ok(()));
        assert_eq!(one, [u64::MAX - GOLDILOCKS_PRIME]);
        let mut one_out = [[0u64; 2]];
        assert_eq!(
            backend.coset_lde_ext2(&[[GOLDILOCKS_PRIME + 5, 9]], 1, 0, &mut one_out),
            Ok(())
        );
        assert_eq!(one_out, [[5, 9]]);
        assert_eq!(backend.bdoz_gf2_128_batch_dot(&[], &[]), Ok((0, 0)));
        let mut no_parents: [[u64; 4]; 0] = [];
        assert_eq!(
            backend.try_merkle_layer_poseidon2_at(&[], &seed, 0, u32::MAX as u64, &mut no_parents),
            Ok(())
        );
        assert_eq!(
            backend.try_merkle_layer_poseidon2_at(&[], &seed, 0, 1 << 32, &mut no_parents),
            Err(AccelError::LengthOverflow)
        );
        assert_eq!(
            backend.bdoz_gf2_128_batch_dot(&[(1, 2)], &[]),
            Err(AccelError::LengthMismatch {
                what: "BDOZ batch dot weights",
                expected: 1,
                actual: 0,
            })
        );
        assert!(!spot_check_merkle_layer(
            &[[0; 4]; 3],
            &seed,
            0,
            0,
            &parents,
            &[0; 32],
            2
        ));
    }
}
