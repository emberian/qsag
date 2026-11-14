#![no_std]
//! Zero-dependency `#![no_std]` certified hardware & GPU accelerator trait (`AcceleratorBackend`),
//! constant-time CPU reference backend (`CpuReferenceBackend`), transcript-bound reports,
//! and verified kernel digest registry (`VerifiedKernelDigestRegistry`).

#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod ct;
pub mod gf2_128;
pub mod goldilocks;
pub mod keccak;
pub mod poseidon2;
pub mod sha2;

use ct::{RedactedSecret, ct_eq_bytes_mask, ct_eq_mask_u64};
use gf2_128::bdoz_gf2_128_batch_dot_cpu;
use goldilocks::{coset_lde_ext2_cpu, gl_reduce_u64, goldilocks_ntt_cpu};
use keccak::{cshake256_framed_32, keccak_f1600};
use poseidon2::{merkle_layer_poseidon2_at_cpu, poseidon2_hash_framed_limbs4, poseidon2_perm12};
use sha2::sha256;

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
    /// A receipt was requested for a job descriptor that does not belong to the pinned kernel slot.
    KernelSlotMismatch {
        pin: KernelSlot,
        descriptor: KernelSlot,
    },
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
            Self::KernelSlotMismatch { pin, descriptor } => write!(
                f,
                "kernel pin is for slot {pin:?} but the job descriptor is for slot {descriptor:?}"
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
    /// Certified Vulkan / WebGPU SPIR-V 1.6 compute shader module.
    SpirV16 = 0x03,
    /// Certified FPGA / ASIC fixed-function datapath.
    CustomHardware = 0x04,
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
    pub input_digest: [u8; 32],
    pub output_digest: [u8; 32],
    pub mac: [u8; 32],
}

impl ExecutionReceipt {
    fn mac_over_fields(&self, key: &BackendAttestationKey) -> [u8; 32] {
        let slot = self.descriptor.slot();
        let mut p2_bytes = [0u8; 32];
        for (chunk, limb) in p2_bytes.chunks_exact_mut(8).zip(&self.kernel_poseidon2) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        cshake256_framed_32(
            b"QSAG.ACCEL.KEYED_RECEIPT.V3",
            &[
                key.key.expose(),
                &self.backend_id,
                slot.algorithm_domain(),
                &[self.arch as u8],
                &self.descriptor.to_canonical_bytes(),
                &self.kernel_sha256,
                &p2_bytes,
                &self.transcript_anchor,
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
    /// Target architecture reported by this backend.
    fn target_arch(&self) -> KernelTargetArch;

    /// Certified kernel pin for `slot`.
    fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin;

    /// Parallel 24-round `Keccak-f[1600]` across `states` (accelerating WOTS+/FORS/FTS chains & OT).
    fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]);

    /// Parallel Width-12 canonical Goldilocks `Poseidon2` (`p = 2^64 - 2^32 + 1`) across `states`.
    fn batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]);

    /// In-place radix-2 Goldilocks NTT (`inverse == false`) and inverse NTT (`inverse == true`).
    ///
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
    /// (`children.len() == 2 * out_parents.len()`).
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
    /// and `out_parents`.
    pub fn merkle_layer_poseidon2_with_receipt<B: AcceleratorBackend>(
        backend: &B,
        key: &BackendAttestationKey,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        transcript_anchor: [u8; 32],
        out_parents: &mut [[u64; 4]],
    ) -> Result<ExecutionReceipt, AccelError> {
        let input_digest = hash_u64_quads(b"QSAG.ACCEL.MERKLE_IN.V1", children);
        backend.try_merkle_layer_poseidon2(children, pk_seed, layer, out_parents)?;
        let output_digest = hash_u64_quads(b"QSAG.ACCEL.MERKLE_OUT.V1", out_parents);
        let pin = backend.kernel_pin(KernelSlot::MerkleLayerPoseidon2);
        let desc = BatchJobDescriptor::MerkleLayerPoseidon2 {
            num_parents: out_parents.len(),
            pk_seed: *pk_seed,
            layer,
        };
        ExecutionReceipt::compute_keyed(
            key,
            &pin,
            desc,
            transcript_anchor,
            input_digest,
            output_digest,
        )
    }
}

/// Digest of a Merkle layer's children as bound into `ExecutionReceipt::input_digest`.
pub fn merkle_layer_input_digest(children: &[[u64; 4]]) -> [u8; 32] {
    hash_u64_quads(b"QSAG.ACCEL.MERKLE_IN.V1", children)
}

/// Digest of a Merkle layer's parents as bound into `ExecutionReceipt::output_digest`.
pub fn merkle_layer_output_digest(parents: &[[u64; 4]]) -> [u8; 32] {
    hash_u64_quads(b"QSAG.ACCEL.MERKLE_OUT.V1", parents)
}

fn hash_u64_quads(cust: &[u8], quads: &[[u64; 4]]) -> [u8; 32] {
    let mut sp = keccak::init_cshake256(b"", cust);
    sp.absorb(&(quads.len() as u64).to_le_bytes());
    for q in quads {
        for &limb in q {
            sp.absorb(&limb.to_le_bytes());
        }
    }
    keccak::finalize_cshake256(&mut sp, true);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

impl AcceleratorBackend for CpuReferenceBackend {
    fn target_arch(&self) -> KernelTargetArch {
        KernelTargetArch::CpuReference
    }

    fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
        Self::canonical_pin(slot)
    }

    fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]) {
        for st in states.iter_mut() {
            keccak_f1600(st);
        }
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
/// CPU, RDNA2 Wave32, and SPIR-V 1.6 GPU compute kernels (`MAX_PROFILES` architectures).
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

    /// Compatibility constructor. No GPU artifacts are bundled or implicitly trusted.
    pub fn with_cpu_and_canonical_gpu_pins() -> Self {
        Self::with_cpu_reference_pins()
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
