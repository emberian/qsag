//! Certified zero-dependency Vulkan / SPIR-V discrete GPU backend (`VulkanSpirvBackend`,
//! aliased as `VulkanRdna2Backend`) implementing [`AcceleratorBackend`] (`KernelTargetArch::SpirV16`).
//!
//! On 64-bit Linux with `feature = "std"`, `VulkanSpirvBackend::try_new()` dynamically loads
//! `libvulkan.so.1`, selects a discrete GPU (`VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU`) supporting
//! native 64-bit integer shaders (`shaderInt64`), allocates `DEVICE_LOCAL` VRAM storage buffers,
//! compiles all 6 deterministic SPIR-V compute kernels, and pins their SHA-256 and Width-12
//! Goldilocks Poseidon2 digests.
//!
//! On non-Linux targets, 32-bit targets, or `#![no_std]` builds without `std`, `try_new()` cleanly
//! returns `Err(VulkanError::UnsupportedPlatform)` with zero external crate dependencies.

#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
use core::sync::atomic::{AtomicU64, Ordering};

use crate::goldilocks::{GOLDILOCKS_TWO_ADICITY, check_goldilocks_twiddles};
use crate::keccak::{cshake256_framed_32, finalize_cshake256, init_cshake256};
use crate::spirv_kernels::{canonical_spirv_pin, canonical_spirv_pins, spirv_kernel_bytes};
use crate::{
    AccelError, AcceleratorBackend, BackendAttestationKey, BatchJobDescriptor, CertifiedKernelPin,
    ExecutionReceipt, KernelSlot, KernelTargetArch, merkle_layer_input_digest,
    merkle_layer_output_digest,
};

#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
use crate::CpuReferenceBackend;
#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
use crate::vulkan_ffi::RawVulkanEngine;

/// Errors returned during Vulkan device discovery, pipeline creation, or GPU kernel execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VulkanError {
    /// Target OS, pointer width, or crate feature configuration does not enable the Linux Vulkan loader.
    UnsupportedPlatform,
    /// Fixed shader resources exceed device limits.
    UnsupportedDeviceLimits,
    /// Driver executable telemetry rejected the compiled pipeline.
    PipelineAuditFailed(&'static str),
    /// Executable properties disagree with the required subgroup size.
    UnexpectedSubgroupSize {
        slot: KernelSlot,
        required: u32,
        reported: u32,
    },
    /// `dlopen("libvulkan.so.1")` failed (no Vulkan loader installed or accessible).
    LibraryLoadFailed,
    /// A required core Vulkan entry point was not exported by the loader or ICD.
    SymbolMissing(&'static str),
    /// A Vulkan API call returned a non-`VK_SUCCESS` status code.
    VkResult { op: &'static str, code: i32 },
    /// No `VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU` device was reported by the Vulkan instance.
    NoDiscreteGpuFound,
    /// Discrete GPU does not advertise `VkPhysicalDeviceFeatures::shaderInt64`.
    MissingShaderInt64,
    /// Physical device exposes no compute-capable queue family.
    NoComputeQueueFamily,
    /// Physical device exposes no memory heap matching required buffer property flags.
    NoSuitableMemoryType { what: &'static str },
    /// Requested storage buffer exceeds `limits.maxStorageBufferRange`.
    BufferExceedsMaxStorageRange { requested: u64, limit: u64 },
    /// Mutex guarding the device queue workspace was poisoned.
    WorkspacePoisoned,
    /// Caller-supplied slice dimensions failed shape validation before GPU dispatch.
    Accel(AccelError),
}

impl core::fmt::Display for VulkanError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::UnsupportedDeviceLimits => {
                f.write_str("device limits cannot support the embedded shaders")
            }
            Self::UnexpectedSubgroupSize {
                slot,
                required,
                reported,
            } => write!(
                f,
                "{slot:?}: required subgroup {required}, driver reported {reported}"
            ),
            Self::PipelineAuditFailed(reason) => write!(f, "pipeline audit failed: {reason}"),
            Self::UnsupportedPlatform => {
                f.write_str("Vulkan SPIR-V backend requires 64-bit Linux with feature `std`")
            }
            Self::LibraryLoadFailed => f.write_str("failed to dlopen `libvulkan.so.1`"),
            Self::SymbolMissing(sym) => write!(f, "missing Vulkan entry point `{sym}`"),
            Self::VkResult { op, code } => write!(f, "{op} failed with VkResult {code}"),
            Self::NoDiscreteGpuFound => {
                f.write_str("no discrete Vulkan GPU (`VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU`) found")
            }
            Self::MissingShaderInt64 => {
                f.write_str("discrete Vulkan GPU does not support `shaderInt64`")
            }
            Self::NoComputeQueueFamily => f.write_str("no Vulkan compute queue family available"),
            Self::NoSuitableMemoryType { what } => {
                write!(f, "no suitable Vulkan memory type for {what}")
            }
            Self::BufferExceedsMaxStorageRange { requested, limit } => write!(
                f,
                "buffer size {requested} bytes exceeds maxStorageBufferRange ({limit} bytes)"
            ),
            Self::WorkspacePoisoned => f.write_str("Vulkan workspace mutex poisoned"),
            Self::Accel(err) => core::fmt::Display::fmt(&err, f),
        }
    }
}

impl core::error::Error for VulkanError {}

impl From<AccelError> for VulkanError {
    fn from(value: AccelError) -> Self {
        Self::Accel(value)
    }
}

/// Driver-reported executable statistics. `None` means unavailable, never zero.
/// Zero scratch is a compiler report, not a proof of hardware constant-time execution.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PipelineTelemetry {
    pub subgroup_size: Option<u32>,
    pub scratch_bytes: Option<u64>,
    pub vgprs: Option<u64>,
    pub sgprs: Option<u64>,
    pub lds_bytes: Option<u64>,
    /// RADV reports these for its LLVM backend; ACO spills surface as `scratch_bytes`.
    pub spilled_vgprs: Option<u64>,
    pub spilled_sgprs: Option<u64>,
}

/// Hardware identity and compute limits reported by `vkGetPhysicalDeviceProperties`.
#[derive(Clone, Copy)]
pub struct VulkanDeviceInfo {
    pub(crate) name_bytes: [u8; 256],
    pub(crate) name_len: usize,
    pub max_compute_shared_memory_size: u32,
    pub wave32_required: bool,
    pub pipelines: [PipelineTelemetry; KernelSlot::COUNT],
    pub vendor_id: u32,
    pub device_id: u32,
    pub driver_version: u32,
    pub api_version: u32,
    pub device_type: u32,
    pub max_push_constants_size: u32,
    pub max_storage_buffer_range: u32,
    pub max_compute_work_group_invocations: u32,
}

impl VulkanDeviceInfo {
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    pub(crate) fn sanitize_device_name(raw_name: &[u8]) -> ([u8; 256], usize) {
        let mut name_bytes = [0u8; 256];
        let copy_len = raw_name.len().min(256);
        name_bytes[..copy_len].copy_from_slice(&raw_name[..copy_len]);
        // Sanitize to valid UTF-8 ASCII fallback if driver returned non-UTF-8 bytes.
        if core::str::from_utf8(&name_bytes[..copy_len]).is_err() {
            for b in &mut name_bytes[..copy_len] {
                if !b.is_ascii() {
                    *b = b'?';
                }
            }
        }
        (name_bytes, copy_len)
    }

    /// UTF-8 physical device name reported by the Vulkan driver (e.g. `"AMD Radeon RX 6750 XT"`).
    pub fn device_name(&self) -> &str {
        core::str::from_utf8(&self.name_bytes[..self.name_len]).unwrap_or("Unknown Vulkan GPU")
    }

    /// Digest of the driver identity and per-pipeline executable telemetry this backend was
    /// built on. A host that folds it into a receipt's `transcript_anchor` makes the receipt
    /// name the driver state (Wave32, scratch, spill, LDS figures) it reports having run on.
    /// Like the receipt itself this is a report by the key holder, not a proof.
    pub fn audit_evidence_digest(&self) -> [u8; 32] {
        const PER_PIPELINE: usize = 7 * 9;
        let mut body = [0u8; 17 + KernelSlot::COUNT * PER_PIPELINE];
        body[0..4].copy_from_slice(&self.vendor_id.to_le_bytes());
        body[4..8].copy_from_slice(&self.device_id.to_le_bytes());
        body[8..12].copy_from_slice(&self.driver_version.to_le_bytes());
        body[12..16].copy_from_slice(&self.api_version.to_le_bytes());
        body[16] = self.wave32_required as u8;
        for (chunk, stats) in body[17..]
            .chunks_exact_mut(PER_PIPELINE)
            .zip(&self.pipelines)
        {
            let fields = [
                stats.subgroup_size.map(u64::from),
                stats.scratch_bytes,
                stats.vgprs,
                stats.sgprs,
                stats.lds_bytes,
                stats.spilled_vgprs,
                stats.spilled_sgprs,
            ];
            for (slot, field) in chunk.chunks_exact_mut(9).zip(fields) {
                slot[0] = field.is_some() as u8;
                slot[1..].copy_from_slice(&field.unwrap_or(0).to_le_bytes());
            }
        }
        cshake256_framed_32(
            b"QSAG.ACCEL.VULKAN_AUDIT_EVIDENCE.V1",
            &[&self.name_bytes[..self.name_len], &body],
        )
    }

    /// Decoded `(major, minor, patch)` Vulkan API version tuple.
    pub const fn api_version_triple(&self) -> (u32, u32, u32) {
        (
            (self.api_version >> 22) & 0x7F,
            (self.api_version >> 12) & 0x3FF,
            self.api_version & 0xFFF,
        )
    }

    /// Decoded `(major, minor, patch)` driver version tuple.
    pub const fn driver_version_triple(&self) -> (u32, u32, u32) {
        (
            (self.driver_version >> 22) & 0x7F,
            (self.driver_version >> 12) & 0x3FF,
            self.driver_version & 0xFFF,
        )
    }
}

impl core::fmt::Debug for VulkanDeviceInfo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("VulkanDeviceInfo")
            .field("device_name", &self.device_name())
            .field("vendor_id", &self.vendor_id)
            .field("device_id", &self.device_id)
            .field("driver_version", &self.driver_version)
            .field("api_version", &self.api_version)
            .field("device_type", &self.device_type)
            .field("max_push_constants_size", &self.max_push_constants_size)
            .field("max_storage_buffer_range", &self.max_storage_buffer_range)
            .field(
                "max_compute_work_group_invocations",
                &self.max_compute_work_group_invocations,
            )
            .finish()
    }
}

/// Hardware discrete GPU compute backend executing certified 64-bit SPIR-V shaders in `DEVICE_LOCAL`
/// GDDR6 / Infinity Cache VRAM (`KernelTargetArch::SpirV16`).
pub struct VulkanSpirvBackend {
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    info: VulkanDeviceInfo,
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    pins: [CertifiedKernelPin; KernelSlot::COUNT],
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    engine: std::sync::Mutex<RawVulkanEngine>,
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    gpu_submissions: AtomicU64,
    #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
    _uninhabited: core::convert::Infallible,
}

/// Type alias highlighting RDNA2 Wave32/Wave64 discrete GPU acceleration via Vulkan SPIR-V.
pub type VulkanRdna2Backend = VulkanSpirvBackend;

impl core::fmt::Debug for VulkanSpirvBackend {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            f.debug_struct("VulkanSpirvBackend")
                .field("info", &self.info)
                .field(
                    "gpu_submissions",
                    &self.gpu_submissions.load(Ordering::Relaxed),
                )
                .finish()
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = f;
            match self._uninhabited {}
        }
    }
}

/// Shape errors pass through; every device, driver, or lock failure is a backend failure.
#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
fn accel_error(err: VulkanError) -> AccelError {
    match err {
        VulkanError::Accel(shape) => shape,
        _ => AccelError::BackendFailure,
    }
}

#[inline]
const fn check_ntt_log2(what: &'static str, len: usize) -> Result<u32, AccelError> {
    if !len.is_power_of_two() {
        return Err(AccelError::NotPowerOfTwo { what, len });
    }
    let log2_len = len.trailing_zeros();
    if log2_len > GOLDILOCKS_TWO_ADICITY {
        return Err(AccelError::DomainTooLarge { log2_len });
    }
    Ok(log2_len)
}

impl VulkanSpirvBackend {
    /// Discover a discrete Vulkan GPU with `shaderInt64`, compile all 6 embedded SPIR-V compute
    /// pipelines, and allocate persistent host-cached staging + `DEVICE_LOCAL` VRAM buffers.
    pub fn try_new() -> Result<Self, VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            let (engine, info) = RawVulkanEngine::try_new()?;
            let pins = canonical_spirv_pins();
            Ok(Self {
                info,
                pins,
                engine: std::sync::Mutex::new(engine),
                gpu_submissions: AtomicU64::new(0),
            })
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            Err(VulkanError::UnsupportedPlatform)
        }
    }

    /// Require driver-confirmed Wave32 and zero scratch for every executable.
    /// Unlike `try_new`, unavailable telemetry is an error. This checks compiler
    /// reports, not a formal constant-time or physical side-channel proof.
    pub fn try_new_audited() -> Result<Self, VulkanError> {
        let backend = Self::try_new()?;
        let info = backend.device_info();
        if !info.wave32_required
            || info
                .pipelines
                .iter()
                .any(|stats| {
                    stats.subgroup_size != Some(32)
                        || stats.scratch_bytes != Some(0)
                        || stats.spilled_vgprs.is_some_and(|n| n != 0)
                        || stats.spilled_sgprs.is_some_and(|n| n != 0)
                })
        {
            return Err(VulkanError::PipelineAuditFailed(
                "Wave32/zero-scratch evidence unavailable",
            ));
        }
        Ok(backend)
    }

    /// Canonical `KernelTargetArch::SpirV16` pin for `slot` computed from its embedded SPIR-V binary.
    pub fn canonical_pin(slot: KernelSlot) -> CertifiedKernelPin {
        canonical_spirv_pin(slot)
    }

    /// Canonical `KernelTargetArch::SpirV16` pins for all 6 [`KernelSlot`]s.
    pub fn canonical_pins() -> [CertifiedKernelPin; KernelSlot::COUNT] {
        canonical_spirv_pins()
    }

    /// Independently measure all 6 embedded SPIR-V binaries for `CertifiedBackend::try_new_measured`.
    pub fn measure_embedded_spirv_pins() -> [CertifiedKernelPin; KernelSlot::COUNT] {
        KernelSlot::ALL.map(|slot| {
            CertifiedKernelPin::from_kernel_artifact(
                slot,
                KernelTargetArch::SpirV16,
                spirv_kernel_bytes(slot),
            )
        })
    }

    /// Hardware properties of the bound discrete Vulkan GPU.
    pub fn device_info(&self) -> &VulkanDeviceInfo {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            &self.info
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            match self._uninhabited {}
        }
    }

    /// Physical device name reported by the Vulkan driver.
    pub fn device_name(&self) -> &str {
        self.device_info().device_name()
    }

    /// PCI vendor ID reported by the Vulkan driver (`0x1002` for AMD).
    pub fn vendor_id(&self) -> u32 {
        self.device_info().vendor_id
    }

    /// Driver version word reported by the Vulkan driver.
    pub fn driver_version(&self) -> u32 {
        self.device_info().driver_version
    }

    /// Total number of `VkCommandBuffer` submissions executed on the physical GPU by this instance.
    pub fn gpu_submission_count(&self) -> u64 {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.gpu_submissions.load(Ordering::Relaxed)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            match self._uninhabited {}
        }
    }

    /// Fallible GPU batch `Keccak-f[1600]` dispatch.
    pub fn try_batch_keccak_f1600(&self, states: &mut [[u64; 25]]) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            if states.is_empty() {
                return Ok(());
            }
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_batch_keccak(states)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    /// Fallible GPU batch Width-12 Goldilocks `Poseidon2` dispatch.
    pub fn try_batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            if states.is_empty() {
                return Ok(());
            }
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_batch_poseidon2(states)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    /// Build a complete binary Poseidon2 Merkle tree of `leaves.len() = 2^H` leaves completely
    /// inside GPU `DEVICE_LOCAL` VRAM within a single `VkCommandBuffer` submission (`0` CPU copies
    /// between internal tree layers!).
    pub fn build_merkle_tree_poseidon2(
        &self,
        leaves: &[[u64; 4]],
        pk_seed: &[u64; 4],
        base_layer: u32,
    ) -> Result<[u64; 4], VulkanError> {
        check_ntt_log2("Merkle tree leaves", leaves.len())?;
        // Level `l` is tweaked with `base_layer + l`; a wrapped tweak would alias another layer.
        if base_layer
            .checked_add(leaves.len().trailing_zeros())
            .is_none()
        {
            return Err(AccelError::LengthOverflow.into());
        }
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let root = guard.exec_merkle_full_tree(leaves, pk_seed, base_layer)?;
            if leaves.len() > 1 {
                self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            }
            Ok(root)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (pk_seed, base_layer);
            match self._uninhabited {}
        }
    }
}

impl AcceleratorBackend for VulkanSpirvBackend {
    fn target_arch(&self) -> KernelTargetArch {
        KernelTargetArch::SpirV16
    }

    fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.pins[slot as usize]
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = slot;
            match self._uninhabited {}
        }
    }

    fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]) {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            if self.try_batch_keccak_f1600(states).is_err() {
                CpuReferenceBackend.batch_keccak_f1600(states);
            }
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    fn try_batch_keccak_f1600_pinned(
        &self,
        states: &mut [[u64; 25]],
    ) -> Result<CertifiedKernelPin, AccelError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.try_batch_keccak_f1600(states).map_err(accel_error)?;
            Ok(self.pins[KernelSlot::BatchKeccakF1600 as usize])
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    fn batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]) {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            if self.try_batch_poseidon2_perm12(states).is_err() {
                CpuReferenceBackend.batch_poseidon2_perm12(states);
            }
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    fn try_batch_poseidon2_perm12_pinned(
        &self,
        states: &mut [[u64; 12]],
    ) -> Result<CertifiedKernelPin, AccelError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.try_batch_poseidon2_perm12(states)
                .map_err(accel_error)?;
            Ok(self.pins[KernelSlot::BatchPoseidon2Perm12 as usize])
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    fn goldilocks_ntt_inplace(
        &self,
        buf: &mut [u64],
        twiddles: &[u64],
        inverse: bool,
    ) -> Result<(), AccelError> {
        let n = buf.len();
        // The kernels read only `twiddles[n >> s]` and take powers of those stage roots, so a
        // table that is not a primitive-root power table is refused instead of transformed
        // differently from the CPU reference (and then bound into a receipt).
        check_goldilocks_twiddles(n, twiddles)?;
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_goldilocks_ntt(buf, twiddles, inverse)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (twiddles, inverse);
            match self._uninhabited {}
        }
    }

    fn coset_lde_ext2(
        &self,
        evals: &[[u64; 2]],
        blowup: usize,
        shift: u64,
        out: &mut [[u64; 2]],
    ) -> Result<(), AccelError> {
        let n = evals.len();
        check_ntt_log2("LDE evaluation domain", n)?;
        if !blowup.is_power_of_two() {
            return Err(AccelError::NotPowerOfTwo {
                what: "LDE blowup",
                len: blowup,
            });
        }
        let m = n.checked_mul(blowup).ok_or(AccelError::LengthOverflow)?;
        check_ntt_log2("LDE codeword domain", m)?;
        if out.len() != m {
            return Err(AccelError::LengthMismatch {
                what: "LDE output",
                expected: m,
                actual: out.len(),
            });
        }
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_coset_lde_ext2(evals, blowup, shift, out)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = shift;
            match self._uninhabited {}
        }
    }

    fn try_merkle_layer_poseidon2_at(
        &self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        let expected_children = out_parents
            .len()
            .checked_mul(2)
            .ok_or(AccelError::LengthOverflow)?;
        if children.len() != expected_children {
            return Err(AccelError::LengthMismatch {
                what: "Merkle layer children",
                expected: expected_children,
                actual: children.len(),
            });
        }
        let max_parent_idx = if out_parents.is_empty() {
            start_parent_idx
        } else {
            start_parent_idx
                .checked_add((out_parents.len() - 1) as u64)
                .ok_or(AccelError::LengthOverflow)?
        };
        if max_parent_idx > u32::MAX as u64 {
            return Err(AccelError::LengthOverflow);
        }
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            if out_parents.is_empty() {
                return Ok(());
            }
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_merkle_layer(children, pk_seed, layer, start_parent_idx, out_parents)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (pk_seed, layer, start_parent_idx);
            match self._uninhabited {}
        }
    }

    fn bdoz_gf2_128_batch_dot(
        &self,
        shares: &[(u128, u128)],
        weights: &[(u128, u128)],
    ) -> Result<(u128, u128), AccelError> {
        if shares.len() != weights.len() {
            return Err(AccelError::LengthMismatch {
                what: "BDOZ batch dot weights",
                expected: shares.len(),
                actual: weights.len(),
            });
        }
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            if shares.is_empty() {
                return Ok((0, 0));
            }
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            let res = guard
                .exec_bdoz_gf2_128_dot(shares, weights)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(res)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (shares, weights);
            match self._uninhabited {}
        }
    }
}

// ============================================================================
// Keyed `ExecutionReceipt` Helpers Across All 6 Certified `KernelSlot`s
// ============================================================================

fn hash_u64_rows<const W: usize>(cust: &[u8], rows: &[[u64; W]]) -> [u8; 32] {
    let mut sp = init_cshake256(b"", cust);
    sp.absorb(&(rows.len() as u64).to_le_bytes());
    for row in rows {
        for &limb in row {
            sp.absorb(&limb.to_le_bytes());
        }
    }
    finalize_cshake256(&mut sp, true);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// Versioned input digest for authenticated Goldilocks NTT receipts, binding **both** `buf` and
/// `twiddles` (`QSAG.ACCEL.NTT_IN.V2 || len(buf) || buf || len(twiddles) || twiddles`).
pub fn goldilocks_ntt_input_digest(buf: &[u64], twiddles: &[u64]) -> [u8; 32] {
    let mut sp = init_cshake256(b"", b"QSAG.ACCEL.NTT_IN.V2");
    sp.absorb(&(buf.len() as u64).to_le_bytes());
    for &w in buf {
        sp.absorb(&w.to_le_bytes());
    }
    sp.absorb(&(twiddles.len() as u64).to_le_bytes());
    for &tw in twiddles {
        sp.absorb(&tw.to_le_bytes());
    }
    finalize_cshake256(&mut sp, true);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// Output digest for authenticated Goldilocks NTT receipts (`QSAG.ACCEL.NTT_OUT.V1 || len || buf`).
pub fn goldilocks_ntt_output_digest(buf: &[u64]) -> [u8; 32] {
    let mut sp = init_cshake256(b"", b"QSAG.ACCEL.NTT_OUT.V1");
    sp.absorb(&(buf.len() as u64).to_le_bytes());
    for &w in buf {
        sp.absorb(&w.to_le_bytes());
    }
    finalize_cshake256(&mut sp, true);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

fn hash_bdoz_inputs(shares: &[(u128, u128)], weights: &[(u128, u128)]) -> [u8; 32] {
    let mut sp = init_cshake256(b"", b"QSAG.ACCEL.BDOZ_IN.V1");
    sp.absorb(&(shares.len() as u64).to_le_bytes());
    for (&(s0, s1), &(w0, w1)) in shares.iter().zip(weights) {
        sp.absorb(&s0.to_le_bytes());
        sp.absorb(&s1.to_le_bytes());
        sp.absorb(&w0.to_le_bytes());
        sp.absorb(&w1.to_le_bytes());
    }
    finalize_cshake256(&mut sp, true);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// Execute `batch_keccak_f1600` on `backend` via [`AcceleratorBackend::try_batch_keccak_f1600_pinned`]
/// (failing closed on hardware execution error rather than stamping a hardware pin onto a CPU
/// fallback) and issue a keyed [`ExecutionReceipt`].
pub fn batch_keccak_f1600_with_receipt<B: AcceleratorBackend>(
    backend: &B,
    key: &BackendAttestationKey,
    states: &mut [[u64; 25]],
    transcript_anchor: [u8; 32],
) -> Result<ExecutionReceipt, AccelError> {
    let input_digest = hash_u64_rows(b"QSAG.ACCEL.KECCAK_IN.V1", states);
    let pin = backend.try_batch_keccak_f1600_pinned(states)?;
    let output_digest = hash_u64_rows(b"QSAG.ACCEL.KECCAK_OUT.V1", states);
    let desc = BatchJobDescriptor::KeccakF1600 {
        num_states: states.len(),
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

/// Execute `batch_poseidon2_perm12` on `backend` via
/// [`AcceleratorBackend::try_batch_poseidon2_perm12_pinned`] (failing closed on hardware execution
/// error rather than stamping a hardware pin onto a CPU fallback) and issue a keyed
/// [`ExecutionReceipt`].
pub fn batch_poseidon2_perm12_with_receipt<B: AcceleratorBackend>(
    backend: &B,
    key: &BackendAttestationKey,
    states: &mut [[u64; 12]],
    transcript_anchor: [u8; 32],
) -> Result<ExecutionReceipt, AccelError> {
    let input_digest = hash_u64_rows(b"QSAG.ACCEL.P2_PERM_IN.V1", states);
    let pin = backend.try_batch_poseidon2_perm12_pinned(states)?;
    let output_digest = hash_u64_rows(b"QSAG.ACCEL.P2_PERM_OUT.V1", states);
    let desc = BatchJobDescriptor::Poseidon2Perm12 {
        num_states: states.len(),
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

/// Execute `goldilocks_ntt_inplace` on `backend` and issue a keyed [`ExecutionReceipt`] whose
/// `input_digest` commits to **both** `buf` and `twiddles` via [`goldilocks_ntt_input_digest`].
pub fn goldilocks_ntt_with_receipt<B: AcceleratorBackend>(
    backend: &B,
    key: &BackendAttestationKey,
    buf: &mut [u64],
    twiddles: &[u64],
    inverse: bool,
    transcript_anchor: [u8; 32],
) -> Result<ExecutionReceipt, AccelError> {
    let input_digest = goldilocks_ntt_input_digest(buf, twiddles);
    backend.goldilocks_ntt_inplace(buf, twiddles, inverse)?;
    let output_digest = goldilocks_ntt_output_digest(buf);
    let pin = backend.kernel_pin(KernelSlot::GoldilocksNtt);
    let desc = BatchJobDescriptor::GoldilocksNtt {
        length: buf.len(),
        inverse,
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

/// Execute `coset_lde_ext2` on `backend` and issue a keyed [`ExecutionReceipt`].
pub fn coset_lde_ext2_with_receipt<B: AcceleratorBackend>(
    backend: &B,
    key: &BackendAttestationKey,
    evals: &[[u64; 2]],
    blowup: usize,
    shift: u64,
    transcript_anchor: [u8; 32],
    out: &mut [[u64; 2]],
) -> Result<ExecutionReceipt, AccelError> {
    let input_digest = hash_u64_rows(b"QSAG.ACCEL.LDE_IN.V1", evals);
    backend.coset_lde_ext2(evals, blowup, shift, out)?;
    let output_digest = hash_u64_rows(b"QSAG.ACCEL.LDE_OUT.V1", out);
    let pin = backend.kernel_pin(KernelSlot::CosetLdeExt2);
    let desc = BatchJobDescriptor::CosetLdeExt2 {
        domain_len: evals.len(),
        blowup,
        shift,
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

/// Execute `try_merkle_layer_poseidon2` on `backend` and issue a keyed [`ExecutionReceipt`].
pub fn merkle_layer_poseidon2_with_receipt<B: AcceleratorBackend>(
    backend: &B,
    key: &BackendAttestationKey,
    children: &[[u64; 4]],
    pk_seed: &[u64; 4],
    layer: u32,
    transcript_anchor: [u8; 32],
    out_parents: &mut [[u64; 4]],
) -> Result<ExecutionReceipt, AccelError> {
    let input_digest = merkle_layer_input_digest(children);
    backend.try_merkle_layer_poseidon2(children, pk_seed, layer, out_parents)?;
    let output_digest = merkle_layer_output_digest(out_parents);
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

/// Execute `bdoz_gf2_128_batch_dot` on `backend` and issue a keyed [`ExecutionReceipt`].
pub fn bdoz_gf2_128_batch_dot_with_receipt<B: AcceleratorBackend>(
    backend: &B,
    key: &BackendAttestationKey,
    shares: &[(u128, u128)],
    weights: &[(u128, u128)],
    transcript_anchor: [u8; 32],
) -> Result<((u128, u128), ExecutionReceipt), AccelError> {
    let input_digest = hash_bdoz_inputs(shares, weights);
    let (lane0, lane1) = backend.bdoz_gf2_128_batch_dot(shares, weights)?;
    let output_digest = cshake256_framed_32(
        b"QSAG.ACCEL.BDOZ_OUT.V1",
        &[&lane0.to_le_bytes(), &lane1.to_le_bytes()],
    );
    let pin = backend.kernel_pin(KernelSlot::BdozGf2128BatchDot);
    let desc = BatchJobDescriptor::BdozGf2128BatchDot {
        num_elements: shares.len(),
    };
    let receipt = ExecutionReceipt::compute_keyed(
        key,
        &pin,
        desc,
        transcript_anchor,
        input_digest,
        output_digest,
    )?;
    Ok(((lane0, lane1), receipt))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CpuReferenceBackend, KernelRegistryError, VerifiedKernelDigestRegistry};

    #[test]
    fn spirv_kernel_pins_and_dual_registry_verify_in_no_std() {
        let reg = VerifiedKernelDigestRegistry::<4>::with_cpu_and_spirv_pins();
        let cpu_pins = KernelSlot::ALL.map(CpuReferenceBackend::canonical_pin);
        let spirv_pins = VulkanSpirvBackend::canonical_pins();
        assert_eq!(
            reg.verify_loaded_profile(KernelTargetArch::CpuReference, &cpu_pins),
            Ok(())
        );
        assert_eq!(
            reg.verify_loaded_profile(KernelTargetArch::SpirV16, &spirv_pins),
            Ok(())
        );

        for slot in KernelSlot::ALL {
            let spv_bytes = spirv_kernel_bytes(slot);
            assert!(spv_bytes.len() >= 1024 && spv_bytes.len().is_multiple_of(4));
            // Valid SPIR-V magic word 0x07230203 in little-endian.
            assert_eq!(&spv_bytes[0..4], &0x0723_0203u32.to_le_bytes());

            let pin = VulkanSpirvBackend::canonical_pin(slot);
            assert_eq!(pin.slot, slot);
            assert_eq!(pin.target_arch, KernelTargetArch::SpirV16);

            let mut tampered = spirv_pins;
            tampered[slot as usize].poseidon2_digest[0] ^= 1;
            assert_eq!(
                reg.verify_loaded_profile(KernelTargetArch::SpirV16, &tampered),
                Err(KernelRegistryError::PinMismatch { slot })
            );
        }
    }

    #[test]
    fn ntt_receipt_binds_twiddle_table_and_separates_primitive_roots() {
        use crate::goldilocks::{GOLDILOCKS_PRIME, gl_inv_or_zero};

        let key = BackendAttestationKey::derive(&[0x5Au8; 32], b"cpu-ntt-test");
        let anchor = [0xA5u8; 32];
        let omega: u64 = 281_474_976_710_656; // 2^48, primitive 4th root of unity mod p
        let omega_inv = gl_inv_or_zero(omega);
        let tw1 = [1u64, omega];
        let tw2 = [1u64, omega_inv];
        let orig = [0u64, 1, 0, 0];

        let mut buf1 = orig;
        let mut buf2 = orig;
        let rec1 =
            goldilocks_ntt_with_receipt(&CpuReferenceBackend, &key, &mut buf1, &tw1, false, anchor)
                .expect("ntt receipt 1");
        let rec2 =
            goldilocks_ntt_with_receipt(&CpuReferenceBackend, &key, &mut buf2, &tw2, false, anchor)
                .expect("ntt receipt 2");

        assert_eq!(buf1, [1, omega, GOLDILOCKS_PRIME - 1, omega_inv]);
        assert_eq!(buf2, [1, omega_inv, GOLDILOCKS_PRIME - 1, omega]);
        assert_ne!(rec1.input_digest, rec2.input_digest);
        assert_ne!(
            goldilocks_ntt_input_digest(&orig, &tw1),
            goldilocks_ntt_input_digest(&orig, &tw2)
        );
        // Cross-verifying rec2 against tw1's input digest must fail.
        assert_eq!(rec2.input_digest, goldilocks_ntt_input_digest(&orig, &tw2));
        assert_ne!(rec2.input_digest, goldilocks_ntt_input_digest(&orig, &tw1));
    }

    #[test]
    fn twiddle_check_accepts_exactly_primitive_root_power_tables() {
        use crate::goldilocks::{
            check_goldilocks_twiddles, gl_mul, goldilocks_primitive_root,
            precompute_goldilocks_twiddles,
        };

        for log2_n in 0..=11u32 {
            let n = 1usize << log2_n;
            let table = precompute_goldilocks_twiddles(n).expect("twiddles");
            assert_eq!(check_goldilocks_twiddles(n, &table), Ok(()));
            // The inverse-root table is an equally valid primitive-root power table.
            if n >= 4 {
                let inv: std::vec::Vec<u64> = core::iter::once(1)
                    .chain(table[1..].iter().rev().map(|&w| crate::goldilocks::gl_neg(w)))
                    .collect();
                assert_eq!(check_goldilocks_twiddles(n, &inv), Ok(()));
            }
            // Any single perturbed entry is refused.
            for idx in 0..table.len() {
                let mut bad = table.clone();
                bad[idx] = gl_mul(bad[idx], 7);
                assert_eq!(
                    check_goldilocks_twiddles(n, &bad),
                    Err(AccelError::InvalidTwiddles),
                    "n={n}, idx={idx}"
                );
            }
        }

        // Geometric tables whose ratio is not a primitive n-th root are refused: ratio 1, and a
        // root of half the order.
        assert_eq!(
            check_goldilocks_twiddles(8, &[1, 1, 1, 1]),
            Err(AccelError::InvalidTwiddles)
        );
        let w4 = goldilocks_primitive_root(2).expect("4th root");
        let half_order = [1, w4, gl_mul(w4, w4), gl_mul(gl_mul(w4, w4), w4)];
        assert_eq!(
            check_goldilocks_twiddles(8, &half_order),
            Err(AccelError::InvalidTwiddles)
        );
        assert_eq!(
            check_goldilocks_twiddles(8, &[1, w4]),
            Err(AccelError::LengthMismatch {
                what: "NTT twiddles",
                expected: 4,
                actual: 2
            })
        );
    }

    #[test]
    fn audit_evidence_digest_separates_driver_and_telemetry_states() {
        let base = VulkanDeviceInfo {
            name_bytes: [0; 256],
            name_len: 0,
            max_compute_shared_memory_size: 65536,
            wave32_required: true,
            pipelines: [PipelineTelemetry {
                subgroup_size: Some(32),
                scratch_bytes: Some(0),
                ..PipelineTelemetry::default()
            }; KernelSlot::COUNT],
            vendor_id: 0x1002,
            device_id: 0x73df,
            driver_version: 1,
            api_version: 1,
            device_type: 2,
            max_push_constants_size: 128,
            max_storage_buffer_range: u32::MAX,
            max_compute_work_group_invocations: 1024,
        };
        let reference = base.audit_evidence_digest();
        assert_eq!(reference, base.audit_evidence_digest());

        let mut variants = std::vec::Vec::new();
        let mut v = base;
        v.wave32_required = false;
        variants.push(v);
        let mut v = base;
        v.driver_version = 2;
        variants.push(v);
        let mut v = base;
        v.name_bytes[0] = b'R';
        v.name_len = 1;
        variants.push(v);
        for slot in 0..KernelSlot::COUNT {
            let mut v = base;
            v.pipelines[slot].subgroup_size = Some(64);
            variants.push(v);
            let mut v = base;
            v.pipelines[slot].scratch_bytes = None;
            variants.push(v);
            let mut v = base;
            v.pipelines[slot].scratch_bytes = Some(8);
            variants.push(v);
            let mut v = base;
            v.pipelines[slot].spilled_vgprs = Some(0);
            variants.push(v);
        }
        let mut digests: std::vec::Vec<[u8; 32]> =
            variants.iter().map(VulkanDeviceInfo::audit_evidence_digest).collect();
        digests.push(reference);
        let total = digests.len();
        digests.sort_unstable();
        digests.dedup();
        assert_eq!(digests.len(), total);
    }

    #[test]
    fn merkle_position_framing_rejects_out_of_range_u64_indices() {
        let seed = [1u64, 2, 3, 4];
        let children = [[7u64; 4]; 2];
        let mut out = [[0u64; 4]; 1];

        // Exact colliding indices modulo p above 2^32 must be rejected cleanly.
        for bad_idx in [
            0xb3ad_a0b1_b0bb_bacfu64,
            0xb3ad_a0b0_b0bb_bad0u64,
            (u32::MAX as u64) + 1,
            u64::MAX,
        ] {
            assert_eq!(
                CpuReferenceBackend
                    .try_merkle_layer_poseidon2_at(&children, &seed, 0, bad_idx, &mut out),
                Err(AccelError::LengthOverflow)
            );
        }
        // Boundary `u32::MAX` for 1 parent succeeds, while 2 parents starting at `u32::MAX` overflows `u32`.
        assert_eq!(
            CpuReferenceBackend.try_merkle_layer_poseidon2_at(
                &children,
                &seed,
                0,
                u32::MAX as u64,
                &mut out
            ),
            Ok(())
        );
        let children4 = [[7u64; 4]; 4];
        let mut out2 = [[0u64; 4]; 2];
        assert_eq!(
            CpuReferenceBackend.try_merkle_layer_poseidon2_at(
                &children4,
                &seed,
                0,
                u32::MAX as u64,
                &mut out2
            ),
            Err(AccelError::LengthOverflow)
        );
    }

    #[test]
    fn failed_hardware_dispatch_never_stamps_spirv_pin_on_cpu_fallback() {
        struct FailingGpuMock;
        impl AcceleratorBackend for FailingGpuMock {
            fn target_arch(&self) -> KernelTargetArch {
                KernelTargetArch::SpirV16
            }
            fn kernel_pin(&self, slot: KernelSlot) -> CertifiedKernelPin {
                VulkanSpirvBackend::canonical_pin(slot)
            }
            fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]) {
                CpuReferenceBackend.batch_keccak_f1600(states);
            }
            fn try_batch_keccak_f1600_pinned(
                &self,
                _states: &mut [[u64; 25]],
            ) -> Result<CertifiedKernelPin, AccelError> {
                Err(AccelError::LengthOverflow)
            }
            fn batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]) {
                CpuReferenceBackend.batch_poseidon2_perm12(states);
            }
            fn try_batch_poseidon2_perm12_pinned(
                &self,
                _states: &mut [[u64; 12]],
            ) -> Result<CertifiedKernelPin, AccelError> {
                Err(AccelError::LengthOverflow)
            }
            fn goldilocks_ntt_inplace(
                &self,
                _buf: &mut [u64],
                _twiddles: &[u64],
                _inverse: bool,
            ) -> Result<(), AccelError> {
                Err(AccelError::LengthOverflow)
            }
            fn coset_lde_ext2(
                &self,
                _evals: &[[u64; 2]],
                _blowup: usize,
                _shift: u64,
                _out: &mut [[u64; 2]],
            ) -> Result<(), AccelError> {
                Err(AccelError::LengthOverflow)
            }
            fn try_merkle_layer_poseidon2_at(
                &self,
                _children: &[[u64; 4]],
                _pk_seed: &[u64; 4],
                _layer: u32,
                _start_parent_idx: u64,
                _out_parents: &mut [[u64; 4]],
            ) -> Result<(), AccelError> {
                Err(AccelError::LengthOverflow)
            }
            fn bdoz_gf2_128_batch_dot(
                &self,
                _shares: &[(u128, u128)],
                _weights: &[(u128, u128)],
            ) -> Result<(u128, u128), AccelError> {
                Err(AccelError::LengthOverflow)
            }
        }

        let key = BackendAttestationKey::derive(&[0x33u8; 32], b"mock-gpu-test");
        let mut k_states = [[0u64; 25]; 2];
        let mut p_states = [[0u64; 12]; 2];
        assert_eq!(
            batch_keccak_f1600_with_receipt(&FailingGpuMock, &key, &mut k_states, [0u8; 32]),
            Err(AccelError::LengthOverflow)
        );
        assert_eq!(
            batch_poseidon2_perm12_with_receipt(&FailingGpuMock, &key, &mut p_states, [0u8; 32]),
            Err(AccelError::LengthOverflow)
        );
    }

    #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
    #[test]
    fn non_linux_std_try_new_returns_unsupported_platform() {
        assert!(matches!(
            VulkanRdna2Backend::try_new(),
            Err(VulkanError::UnsupportedPlatform)
        ));
    }
}
