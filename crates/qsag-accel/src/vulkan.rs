//! Certified zero-dependency Vulkan / SPIR-V discrete GPU backend (`VulkanSpirvBackend`,
//! aliased as `VulkanRdna2Backend`) implementing [`AcceleratorBackend`] (`KernelTargetArch::SpirV15`).
//!
//! On 64-bit Linux with `feature = "std"`, `VulkanSpirvBackend::try_new()` dynamically loads
//! `libvulkan.so.1`, selects a discrete GPU (`VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU`) supporting
//! native 64-bit integer shaders (`shaderInt64`), allocates `DEVICE_LOCAL` VRAM storage buffers,
//! compiles all 6 deterministic SPIR-V compute kernels, and pins their SHA-256 and Width-12
//! Goldilocks Poseidon2 digests.
//!
//! On non-Linux targets, 32-bit targets, or `#![no_std]` builds without `std`, `try_new()` cleanly
//! returns `Err(VulkanError::UnsupportedPlatform)` with zero external crate dependencies.
//!
//! # Secret inputs
//!
//! * Every kernel requires the evidence in [`VulkanDeviceInfo::secret_slot_audit`].
//!   Both constructors reject missing Wave32, scratch, or spill telemetry; dispatch gates
//!   reject an unaudited slot before any input reaches the device.
//! * The infallible `batch_keccak_f1600` / `batch_poseidon2_perm12` answer from the CPU
//!   reference when the device fails. Each such call increments
//!   [`VulkanSpirvBackend::cpu_fallback_count`].
//! * A job's inputs are wiped from host staging memory on every exit once the device is known
//!   idle. After `VK_ERROR_DEVICE_LOST` that cannot be known: the backend refuses all further
//!   jobs and the failed job's inputs stay in staging memory and VRAM until the process exits.

#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use crate::goldilocks::{GOLDILOCKS_TWO_ADICITY, check_goldilocks_twiddles};
use crate::keccak::{cshake256_framed_32, finalize_cshake256, init_cshake256};
use crate::spirv_kernels::{
    canonical_prover_spirv_pin, canonical_prover_spirv_pins, canonical_spirv_pin,
    canonical_spirv_pins, prover_spirv_kernel_bytes, spirv_kernel_bytes,
};
use crate::{
    AccelError, AcceleratorBackend, BackendAttestationKey, BatchJobDescriptor, CertifiedKernelPin,
    CertifiedProverKernelPin, ExecutionReceipt, KernelSlot, KernelTargetArch, ProverKernelSlot,
    merkle_layer_input_digest, merkle_layer_output_digest,
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
    /// Prover pipeline executable properties disagree with the required subgroup size.
    UnexpectedProverSubgroupSize {
        slot: ProverKernelSlot,
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
            Self::UnexpectedProverSubgroupSize {
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
    pub prover_pipelines: [PipelineTelemetry; ProverKernelSlot::COUNT],
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

    /// The evidence a secret-bearing kernel slot requires: the driver was made to compile every
    /// pipeline at subgroup size 32 and reported, for each one, subgroup size 32, zero scratch
    /// bytes and no spilled registers. A statistic the driver did not report counts as missing
    /// evidence, except the two spill counters, which only some compilers emit.
    ///
    /// These are compiler reports, not a constant-time or physical side-channel proof.
    pub fn secret_slot_audit(&self) -> Result<(), VulkanError> {
        if !self.wave32_required {
            return Err(VulkanError::PipelineAuditFailed(
                "subgroup size 32 was not required at pipeline creation",
            ));
        }
        for stats in self.pipelines.iter().chain(self.prover_pipelines.iter()) {
            if stats.subgroup_size != Some(32) {
                return Err(VulkanError::PipelineAuditFailed(
                    "a pipeline did not report subgroup size 32",
                ));
            }
            if stats.scratch_bytes != Some(0) {
                return Err(VulkanError::PipelineAuditFailed(
                    "a pipeline did not report zero scratch bytes",
                ));
            }
            if stats.spilled_vgprs != Some(0) || stats.spilled_sgprs != Some(0) {
                return Err(VulkanError::PipelineAuditFailed(
                    "a pipeline reported spilled registers",
                ));
            }
        }
        Ok(())
    }

    /// Digest of the driver identity and per-pipeline executable telemetry this backend was
    /// built on. A host that folds it into a receipt's `transcript_anchor` makes the receipt
    /// name the driver state (Wave32, scratch, spill, LDS figures) it reports having run on.
    /// Like the receipt itself this is a report by the key holder, not a proof.
    pub fn audit_evidence_digest(&self) -> [u8; 32] {
        const PER_PIPELINE: usize = 7 * 9;
        const TOTAL_PIPELINES: usize = KernelSlot::COUNT + ProverKernelSlot::COUNT;
        let mut body = [0u8; 17 + TOTAL_PIPELINES * PER_PIPELINE];
        body[0..4].copy_from_slice(&self.vendor_id.to_le_bytes());
        body[4..8].copy_from_slice(&self.device_id.to_le_bytes());
        body[8..12].copy_from_slice(&self.driver_version.to_le_bytes());
        body[12..16].copy_from_slice(&self.api_version.to_le_bytes());
        body[16] = self.wave32_required as u8;
        for (chunk, stats) in body[17..]
            .as_chunks_mut::<PER_PIPELINE>()
            .0
            .iter_mut()
            .zip(self.pipelines.iter().chain(self.prover_pipelines.iter()))
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
            for (slot, field) in chunk.as_chunks_mut::<9>().0.iter_mut().zip(fields) {
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
/// GDDR6 / Infinity Cache VRAM (`KernelTargetArch::SpirV15`).
pub struct VulkanSpirvBackend {
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    info: VulkanDeviceInfo,
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    pins: [CertifiedKernelPin; KernelSlot::COUNT],
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    prover_pins: [CertifiedProverKernelPin; ProverKernelSlot::COUNT],
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    engine: std::sync::Mutex<RawVulkanEngine>,
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    gpu_submissions: AtomicU64,
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    cpu_fallbacks: AtomicU64,
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    prover_session_in_use: AtomicBool,
    /// `info.secret_slot_audit().is_ok()`, fixed at construction.
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    secret_slots_audited: bool,
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
                .field("cpu_fallbacks", &self.cpu_fallbacks.load(Ordering::Relaxed))
                .field("secret_slots_audited", &self.secret_slots_audited)
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

/// Refuse a secret-bearing slot on a backend without pipeline audit evidence.
#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
const fn secret_slot_gate(audited: bool, slot: KernelSlot) -> Result<(), AccelError> {
    if audited {
        Ok(())
    } else {
        Err(AccelError::SecretSlotUnaudited { slot })
    }
}

/// Run `gpu` on `states`; if it fails, count the fallback and run `cpu` instead.
/// A failed GPU job has not written `states` (results are copied back only on success).
#[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
fn gpu_or_counted_cpu_fallback<S: ?Sized>(
    fallbacks: &AtomicU64,
    states: &mut S,
    gpu: impl FnOnce(&mut S) -> Result<(), VulkanError>,
    cpu: impl FnOnce(&mut S),
) {
    if gpu(states).is_err() {
        fallbacks.fetch_add(1, Ordering::Relaxed);
        cpu(states);
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
    ///
    /// Requires audited Wave32 and explicit zero scratch and spill statistics for all slots.
    pub fn try_new() -> Result<Self, VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            let (engine, info) = RawVulkanEngine::try_new()?;
            info.secret_slot_audit()?;
            let pins = canonical_spirv_pins();
            let prover_pins = canonical_prover_spirv_pins();
            Ok(Self {
                info,
                pins,
                prover_pins,
                engine: std::sync::Mutex::new(engine),
                gpu_submissions: AtomicU64::new(0),
                cpu_fallbacks: AtomicU64::new(0),
                prover_session_in_use: AtomicBool::new(false),
                secret_slots_audited: info.secret_slot_audit().is_ok(),
            })
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            Err(VulkanError::UnsupportedPlatform)
        }
    }

    /// Require driver-confirmed Wave32 and zero scratch for every executable
    /// ([`VulkanDeviceInfo::secret_slot_audit`]). As with `try_new`, unavailable telemetry is an
    /// error. This checks compiler reports, not a formal constant-time or physical
    /// side-channel proof.
    pub fn try_new_audited() -> Result<Self, VulkanError> {
        let backend = Self::try_new()?;
        backend.device_info().secret_slot_audit()?;
        Ok(backend)
    }

    /// Whether this backend holds the evidence of [`VulkanDeviceInfo::secret_slot_audit`].
    /// Always true for either successful constructor. Unaudited dispatch returns
    /// [`AccelError::SecretSlotUnaudited`].
    pub fn secret_slots_audited(&self) -> bool {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.secret_slots_audited
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            match self._uninhabited {}
        }
    }

    /// Number of infallible `batch_keccak_f1600` / `batch_poseidon2_perm12` calls that the
    /// device failed and the CPU reference answered instead.
    pub fn cpu_fallback_count(&self) -> u64 {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.cpu_fallbacks.load(Ordering::Relaxed)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            match self._uninhabited {}
        }
    }

    /// Canonical `KernelTargetArch::SpirV15` pin for `slot` computed from its embedded SPIR-V binary.
    pub fn canonical_pin(slot: KernelSlot) -> CertifiedKernelPin {
        canonical_spirv_pin(slot)
    }

    /// Canonical `KernelTargetArch::SpirV15` pins for all 6 [`KernelSlot`]s.
    pub fn canonical_pins() -> [CertifiedKernelPin; KernelSlot::COUNT] {
        canonical_spirv_pins()
    }

    /// Independently measure all 6 embedded SPIR-V binaries for `CertifiedBackend::try_new_measured`.
    pub fn measure_embedded_spirv_pins() -> [CertifiedKernelPin; KernelSlot::COUNT] {
        KernelSlot::ALL.map(|slot| {
            CertifiedKernelPin::from_kernel_artifact(
                slot,
                KernelTargetArch::SpirV15,
                spirv_kernel_bytes(slot),
            )
        })
    }

    /// Canonical `KernelTargetArch::SpirV15` pin for a VRAM-resident [`ProverKernelSlot`].
    pub fn canonical_prover_pin(slot: ProverKernelSlot) -> CertifiedProverKernelPin {
        canonical_prover_spirv_pin(slot)
    }

    /// Canonical `KernelTargetArch::SpirV15` pins for all 4 [`ProverKernelSlot`]s.
    pub fn canonical_prover_pins() -> [CertifiedProverKernelPin; ProverKernelSlot::COUNT] {
        canonical_prover_spirv_pins()
    }

    /// Independently measure all 4 embedded VRAM-resident prover SPIR-V binaries.
    pub fn measure_embedded_prover_spirv_pins()
    -> [CertifiedProverKernelPin; ProverKernelSlot::COUNT] {
        ProverKernelSlot::ALL.map(|slot| {
            CertifiedProverKernelPin::from_kernel_artifact(
                slot,
                KernelTargetArch::SpirV15,
                prover_spirv_kernel_bytes(slot),
            )
        })
    }

    /// Certified pin for a bound VRAM-resident [`ProverKernelSlot`].
    pub fn prover_kernel_pin(&self, slot: ProverKernelSlot) -> CertifiedProverKernelPin {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.prover_pins[slot as usize]
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = slot;
            match self._uninhabited {}
        }
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
            secret_slot_gate(self.secret_slots_audited, KernelSlot::BatchKeccakF1600)
                .map_err(VulkanError::from)?;
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
            secret_slot_gate(self.secret_slots_audited, KernelSlot::BatchPoseidon2Perm12)
                .map_err(VulkanError::from)?;
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
            secret_slot_gate(self.secret_slots_audited, KernelSlot::MerkleLayerPoseidon2)
                .map_err(VulkanError::from)?;
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

    /// Acquire exclusive ownership of the persistent VRAM prover arena for one proving session.
    pub fn try_acquire_prover_session(&self) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            if !self.secret_slots_audited {
                return Err(VulkanError::PipelineAuditFailed(
                    "prover session requires audited Wave32 pipelines",
                ));
            }
            if self
                .prover_session_in_use
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
            {
                return Err(VulkanError::WorkspacePoisoned);
            }
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            match self._uninhabited {}
        }
    }

    /// Scrub all prover session VRAM buffers (`vkCmdFillBuffer`) and release session ownership.
    pub fn release_prover_session(&self) {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            if let Ok(mut guard) = self.engine.lock() {
                let _ = guard.scrub_prover_session();
            }
            self.prover_session_in_use.store(false, Ordering::Release);
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            match self._uninhabited {}
        }
    }

    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    fn check_prover_session_active(&self) -> Result<(), VulkanError> {
        if !self.secret_slots_audited {
            return Err(VulkanError::PipelineAuditFailed(
                "prover session requires audited Wave32 pipelines",
            ));
        }
        if !self.prover_session_in_use.load(Ordering::Acquire) {
            return Err(VulkanError::WorkspacePoisoned);
        }
        Ok(())
    }

    /// Upload Round-0 witness polynomials, convert in-place to monomial basis, run 4-coset
    /// Goldilocks Reed-Solomon LDE + salted Canopy leaf hashing + internal Merkle tree layers
    /// inside VRAM, and return `top_node` (`nodes[1]`).
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::too_many_arguments)]
    pub fn prover_whir_commit_round0_with<F>(
        &self,
        num_polys: usize,
        salt_seed: &[u8; 32],
        num_vars: usize,
        blowup: usize,
        group_arity: usize,
        max_stage1_domain_ext4: usize,
        max_stage1_groups: usize,
        extra_witness_words: usize,
        fill_chunk: F,
    ) -> Result<[u8; 32], VulkanError>
    where
        F: FnMut(usize, usize, &mut [u64]),
    {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let (top_node, subs) = guard.exec_prover_whir_commit_round0_with(
                num_polys,
                salt_seed,
                num_vars,
                blowup,
                group_arity,
                max_stage1_domain_ext4,
                max_stage1_groups,
                extra_witness_words,
                fill_chunk,
            )?;
            self.gpu_submissions.fetch_add(subs, Ordering::Relaxed);
            Ok(top_node)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (
                num_polys,
                salt_seed,
                num_vars,
                blowup,
                group_arity,
                max_stage1_domain_ext4,
                max_stage1_groups,
                extra_witness_words,
                fill_chunk,
            );
            match self._uninhabited {}
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn prover_whir_commit_round0(
        &self,
        polys: &[&[u64]],
        salt_seed: &[u8; 32],
        num_vars: usize,
        blowup: usize,
        group_arity: usize,
        max_stage1_domain_ext4: usize,
        max_stage1_groups: usize,
        extra_witness_words: usize,
    ) -> Result<[u8; 32], VulkanError> {
        let c_len = 1usize.checked_shl(num_vars as u32).unwrap_or(0);
        if polys.is_empty() || polys.iter().any(|p| p.len() != c_len) {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        self.prover_whir_commit_round0_with(
            polys.len(),
            salt_seed,
            num_vars,
            blowup,
            group_arity,
            max_stage1_domain_ext4,
            max_stage1_groups,
            extra_witness_words,
            |poly_idx, pos, dst| {
                dst.copy_from_slice(&polys[poly_idx][pos..pos + dst.len()]);
            },
        )
    }

    /// Expand `eq_table` Kronecker byte tables (`768 * num_polys` `Ext4`s) into `vram_work_a`
    /// and upload `lambda_pows` (`num_polys` `Ext4`s) for multi-polynomial batch sumcheck.
    pub fn prover_whir_batch_sumcheck_init(
        &self,
        eq_kronecker_768: &[[u64; 4]],
        lambda_pows: &[[u64; 4]],
        num_vars: usize,
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_batch_sumcheck_init(eq_kronecker_768, lambda_pows, num_vars)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (eq_kronecker_768, lambda_pows, num_vars);
            match self._uninhabited {}
        }
    }

    /// Evaluate `(ev0, ev2)` for one round of multi-polynomial batch point-reduction sumcheck.
    pub fn prover_whir_batch_sumcheck_eval(
        &self,
        round: usize,
        cur_len: usize,
        num_polys: usize,
        src_base: u32,
    ) -> Result<([u64; 4], [u64; 4]), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let out =
                guard.exec_prover_whir_batch_sumcheck_eval(round, cur_len, num_polys, src_base)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(out)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (round, cur_len, num_polys, src_base);
            match self._uninhabited {}
        }
    }

    /// Fold all `tables` and `kernels` in VRAM for one round of batch point-reduction sumcheck.
    pub fn prover_whir_batch_sumcheck_fold(
        &self,
        round: usize,
        cur_len: usize,
        num_polys: usize,
        src_base: u32,
        dst_base: u32,
        chal: [u64; 4],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_batch_sumcheck_fold(
                round, cur_len, num_polys, src_base, dst_base, chal,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (round, cur_len, num_polys, src_base, dst_base, chal);
            match self._uninhabited {}
        }
    }

    /// Read back small folded `tables` and `kernels` (`cur_len * num_polys` `Ext4`s) to finish
    /// the tiny L1 tail of batch point-reduction sumcheck on CPU.
    pub fn prover_whir_batch_sumcheck_read_tail(
        &self,
        cur_len: usize,
        num_polys: usize,
        src_base: u32,
        out_tables: &mut [[u64; 4]],
        out_kernels: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_batch_sumcheck_read_tail(
                cur_len,
                num_polys,
                src_base,
                out_tables,
                out_kernels,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (cur_len, num_polys, src_base, out_tables, out_kernels);
            match self._uninhabited {}
        }
    }

    /// Expand a 768-entry Kronecker monomial table into `cur_k` (`vram_work_a[0..(1<<num_vars)+2]`),
    /// and optionally compute `dot_base_ext4` against `vram_mono` for `out_dots.len()` polynomials.
    pub fn prover_whir_expand_monomial_and_dot(
        &self,
        mono_kronecker_768: &[[u64; 4]; 768],
        num_vars: usize,
        dot_k_offset: u32,
        out_dots: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_expand_monomial_and_dot(
                mono_kronecker_768,
                num_vars,
                dot_k_offset,
                out_dots,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (mono_kronecker_768, num_vars, dot_k_offset, out_dots);
            match self._uninhabited {}
        }
    }

    /// Construct `cur_coeffs[0..(1<<num_vars)+2]` in `vram_work_b` from `vram_mono` + `weights`
    /// and evaluate `stage0_ood_evals` at two OOD challenges in a single command buffer.
    pub fn prover_whir_open_init(
        &self,
        num_vars: usize,
        is_single: bool,
        weights: &[[[u64; 4]; 2]],
        z_ood_kronecker_2x768: &[[u64; 4]; 1536],
    ) -> Result<[[u64; 4]; 2], VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let evals = guard.exec_prover_whir_open_init(
                num_vars,
                is_single,
                weights,
                z_ood_kronecker_2x768,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(evals)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (num_vars, is_single, weights, z_ood_kronecker_2x768);
            match self._uninhabited {}
        }
    }

    /// Accumulate two scaled geometric OOD claims (`xi_0 * z_0^i`, `xi_1 * z_1^i`) into `cur_k`.
    pub fn prover_whir_add_ood_claims(
        &self,
        k_len: usize,
        k_base: u32,
        xi_z_kronecker_2x768: &[[u64; 4]; 1536],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_add_ood_claims(k_len, k_base, xi_z_kronecker_2x768)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (k_len, k_base, xi_z_kronecker_2x768);
            match self._uninhabited {}
        }
    }

    /// `prove_fold_in_place` Pass A: reduce `wire[0..3]` over `pairs_ck` pairs.
    pub fn prover_whir_fold_pass_a(
        &self,
        pairs_ck: usize,
        c_base: u32,
        k_base: u32,
    ) -> Result<[[u64; 4]; 3], VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let wires = guard.exec_prover_whir_fold_pass_a(pairs_ck, c_base, k_base)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(wires)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (pairs_ck, c_base, k_base);
            match self._uninhabited {}
        }
    }

    /// `prove_fold_in_place` Pass B: write folded `k_next` into `k_dst` and reduce `wire[3..5]`.
    pub fn prover_whir_fold_pass_b(
        &self,
        pairs_c: usize,
        c_base: u32,
        k_src: u32,
        k_half: u32,
        k_dst: u32,
        phi: [u64; 4],
    ) -> Result<[[u64; 4]; 2], VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let wires =
                guard.exec_prover_whir_fold_pass_b(pairs_c, c_base, k_src, k_half, k_dst, phi)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(wires)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (pairs_c, c_base, k_src, k_half, k_dst, phi);
            match self._uninhabited {}
        }
    }

    /// `prove_fold_in_place` Pass C: fold `cur_coeffs` (`c_src -> c_dst`), optionally normalizing
    /// both `cur_coeffs` and `cur_k` back to offset `0` at the end of a stage.
    #[allow(clippy::too_many_arguments)]
    pub fn prover_whir_fold_pass_c(
        &self,
        m: usize,
        c_src: u32,
        c_dst: u32,
        theta: [u64; 4],
        alpha: [u64; 4],
        beta: [u64; 4],
        normalize_to_zero: bool,
        norm_len: usize,
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_fold_pass_c(
                m,
                c_src,
                c_dst,
                theta,
                alpha,
                beta,
                normalize_to_zero,
                norm_len,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (
                m,
                c_src,
                c_dst,
                theta,
                alpha,
                beta,
                normalize_to_zero,
                norm_len,
            );
            match self._uninhabited {}
        }
    }

    /// Commit intermediate stage `stage_idx >= 1` (`cur_coeffs[0..coeff_len]` -> `Ext4` LDE +
    /// Canopy leaf + internal Merkle tree in ping-pong slot `stage_idx & 1`) and return `top_node`.
    pub fn prover_whir_commit_stage(
        &self,
        stage_idx: usize,
        coeff_len: usize,
        domain_len: usize,
        group_arity: usize,
    ) -> Result<[u8; 32], VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let top_node = guard.exec_prover_whir_commit_stage(
                stage_idx,
                coeff_len,
                domain_len,
                group_arity,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(top_node)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (stage_idx, coeff_len, domain_len, group_arity);
            match self._uninhabited {}
        }
    }

    /// Evaluate `cur_coeffs[c_base..c_base+coeff_len]` at two OOD challenges in VRAM.
    pub fn prover_whir_eval_univariate_2(
        &self,
        coeff_len: usize,
        c_base: u32,
        z_ood_kronecker_2x768: &[[u64; 4]; 1536],
    ) -> Result<[[u64; 4]; 2], VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let evals = guard.exec_prover_whir_eval_univariate_2(
                coeff_len,
                c_base,
                z_ood_kronecker_2x768,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(evals)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (coeff_len, c_base, z_ood_kronecker_2x768);
            match self._uninhabited {}
        }
    }

    /// Gather queried fibers, Round-0 salts (if `stage_idx == 0`), and Steiner Merkle siblings.
    #[allow(clippy::too_many_arguments)]
    pub fn prover_whir_gather_queries(
        &self,
        stage_idx: usize,
        group_arity: usize,
        num_polys: usize,
        num_groups: usize,
        q_indices: &[u64],
        sib_indices: &[u64],
        out_words: &mut [u64],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_gather_queries(
                stage_idx,
                group_arity,
                num_polys,
                num_groups,
                q_indices,
                sib_indices,
                out_words,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (
                stage_idx,
                group_arity,
                num_polys,
                num_groups,
                q_indices,
                sib_indices,
                out_words,
            );
            match self._uninhabited {}
        }
    }

    /// Accumulate batched query shift claims into `cur_k[k_base..k_base+k_len]`.
    pub fn prover_whir_accumulate_shift_claims(
        &self,
        k_len: usize,
        k_base: u32,
        z_pow_256: &[u64],
        claims_meta: &[[u64; 8]],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_accumulate_shift_claims(
                k_len,
                k_base,
                z_pow_256,
                claims_meta,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (k_len, k_base, z_pow_256, claims_meta);
            match self._uninhabited {}
        }
    }

    /// Read back final early-stop univariate coefficients `cur_coeffs[c_base..c_base+out.len()]`.
    pub fn prover_whir_read_final_coeffs(
        &self,
        c_base: u32,
        out_coeffs: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_whir_read_final_coeffs(c_base, out_coeffs)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (c_base, out_coeffs);
            match self._uninhabited {}
        }
    }

    /// Initialize VRAM AIR row sumcheck for one shard: upload `(eq_tau, eq_not_last, shift_tau)`
    /// and static `gammas`, and transpose row-major shard witness into column-major `cols_base`.
    pub fn prover_air_init_shard(
        &self,
        witness_word_offset: u32,
        cols_base_word_offset: u32,
        total_rows: usize,
        shift_tables_3m: &[[u64; 4]],
        static_gammas_ext4: &[[u64; 4]],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_air_init_shard(
                witness_word_offset,
                cols_base_word_offset,
                total_rows,
                shift_tables_3m,
                static_gammas_ext4,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (
                witness_word_offset,
                cols_base_word_offset,
                total_rows,
                shift_tables_3m,
                static_gammas_ext4,
            );
            match self._uninhabited {}
        }
    }

    /// Evaluate degree-8 AIR row-constraint univariate evaluations `[ev_0, ev_2..=ev_8]` for one
    /// sumcheck round by chaining `AirRowGroupA` and `AirRowGroupB` in a single command buffer.
    #[allow(clippy::too_many_arguments)]
    pub fn prover_air_eval_round(
        &self,
        is_round0_base: bool,
        cur_m: usize,
        cur_r: usize,
        cur_s: usize,
        folding_signer: bool,
        col_src: u32,
        sh_src: u32,
        dyn_ext4_off: u32,
        dyn_words: &[u64],
        signers_off: u32,
        steps_off: u32,
        op_hdr_off: u32,
        op_ent_off: u32,
        sorted_u64_off: u32,
    ) -> Result<[[u64; 4]; 8], VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let evals = guard.exec_prover_air_eval_round(
                is_round0_base,
                cur_m,
                cur_r,
                cur_s,
                folding_signer,
                col_src,
                sh_src,
                dyn_ext4_off,
                dyn_words,
                signers_off,
                steps_off,
                op_hdr_off,
                op_ent_off,
                sorted_u64_off,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(evals)
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (
                is_round0_base,
                cur_m,
                cur_r,
                cur_s,
                folding_signer,
                col_src,
                sh_src,
                dyn_ext4_off,
                dyn_words,
                signers_off,
                steps_off,
                op_hdr_off,
                op_ent_off,
                sorted_u64_off,
            );
            match self._uninhabited {}
        }
    }

    /// Fold all 256 AIR trace columns and 3 shift tables in VRAM after squeezing round challenge.
    #[allow(clippy::too_many_arguments)]
    pub fn prover_air_fold_round(
        &self,
        is_round0_base: bool,
        cur_m: usize,
        col_src: u32,
        col_dst: u32,
        sh_src: u32,
        sh_dst: u32,
        chal: [u64; 4],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_air_fold_round(
                is_round0_base,
                cur_m,
                col_src,
                col_dst,
                sh_src,
                sh_dst,
                chal,
            )?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (
                is_round0_base,
                cur_m,
                col_src,
                col_dst,
                sh_src,
                sh_dst,
                chal,
            );
            match self._uninhabited {}
        }
    }

    /// Execute an in-place Goldilocks NTT using the canonical `GOLDILOCKS_ROOT_2_32` subgroup
    /// generator without allocating or scanning a host twiddle table (`O(log N)` stage roots).
    pub fn goldilocks_ntt_canonical_inplace(
        &self,
        buf: &mut [u64],
        inverse: bool,
    ) -> Result<(), AccelError> {
        check_ntt_log2("NTT input", buf.len())?;
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            secret_slot_gate(self.secret_slots_audited, KernelSlot::GoldilocksNtt)?;
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_goldilocks_ntt_canonical(buf, inverse)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = inverse;
            match self._uninhabited {}
        }
    }

    /// Read back folded `Ext4` columns (`out_cols.len() == 256 * cur_m`) from `vram_work_a`.
    pub fn prover_air_read_folded_cols(
        &self,
        col_src_ext4: u32,
        out_cols: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.prover_air_read_tail(col_src_ext4, 0, out_cols, &mut [])
    }

    /// Read back folded `Ext4` columns (`256 * cur_m`) and shift tables (`3 * cur_m`) in one DMA
    /// to complete the L2/L3-cache-resident merged-opcode tail of AIR row sumcheck on CPU.
    pub fn prover_air_read_tail(
        &self,
        col_src_ext4: u32,
        sh_src_ext4: u32,
        out_cols: &mut [[u64; 4]],
        out_shifts: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
        {
            self.check_prover_session_active()?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            guard.exec_prover_air_read_tail(col_src_ext4, sh_src_ext4, out_cols, out_shifts)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(feature = "std", target_os = "linux", target_pointer_width = "64")))]
        {
            let _ = (col_src_ext4, sh_src_ext4, out_cols, out_shifts);
            match self._uninhabited {}
        }
    }
}

impl AcceleratorBackend for VulkanSpirvBackend {
    fn hardware_audit_digest(&self) -> [u8; 32] {
        self.device_info().audit_evidence_digest()
    }

    fn target_arch(&self) -> KernelTargetArch {
        KernelTargetArch::SpirV15
    }

    fn cpu_fallback_count(&self) -> u64 {
        VulkanSpirvBackend::cpu_fallback_count(self)
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
            gpu_or_counted_cpu_fallback(
                &self.cpu_fallbacks,
                states,
                |s| self.try_batch_keccak_f1600(s),
                |s| CpuReferenceBackend.batch_keccak_f1600(s),
            );
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
            gpu_or_counted_cpu_fallback(
                &self.cpu_fallbacks,
                states,
                |s| self.try_batch_poseidon2_perm12(s),
                |s| CpuReferenceBackend.batch_poseidon2_perm12(s),
            );
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
            secret_slot_gate(self.secret_slots_audited, KernelSlot::GoldilocksNtt)?;
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
            secret_slot_gate(self.secret_slots_audited, KernelSlot::CosetLdeExt2)?;
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
            secret_slot_gate(self.secret_slots_audited, KernelSlot::MerkleLayerPoseidon2)?;
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
            // Shares are MAC key material: no unaudited pipeline sees them, and there is no
            // CPU fallback behind the caller's back.
            secret_slot_gate(self.secret_slots_audited, KernelSlot::BdozGf2128BatchDot)?;
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
    ExecutionReceipt::compute_audited(
        key,
        &pin,
        desc,
        transcript_anchor,
        input_digest,
        output_digest,
        backend.hardware_audit_digest(),
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
    ExecutionReceipt::compute_audited(
        key,
        &pin,
        desc,
        transcript_anchor,
        input_digest,
        output_digest,
        backend.hardware_audit_digest(),
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
    #[cfg(feature = "std")]
    let start = std::time::Instant::now();
    let input_digest = goldilocks_ntt_input_digest(buf, twiddles);
    #[cfg(feature = "std")]
    let input_elapsed = start.elapsed();
    backend.goldilocks_ntt_inplace(buf, twiddles, inverse)?;
    #[cfg(feature = "std")]
    let kernel_elapsed = start.elapsed() - input_elapsed;
    let output_digest = goldilocks_ntt_output_digest(buf);
    #[cfg(feature = "std")]
    if std::env::var_os("QSAG_PROFILE").is_some() {
        std::eprintln!(
            "qsag_ntt n={} input_digest={:.3} kernel={:.3} output_digest={:.3} ms",
            buf.len(),
            input_elapsed.as_secs_f64() * 1000.0,
            kernel_elapsed.as_secs_f64() * 1000.0,
            (start.elapsed() - input_elapsed - kernel_elapsed).as_secs_f64() * 1000.0
        );
    }
    let pin = backend.kernel_pin(KernelSlot::GoldilocksNtt);
    let desc = BatchJobDescriptor::GoldilocksNtt {
        length: buf.len(),
        inverse,
    };
    ExecutionReceipt::compute_audited(
        key,
        &pin,
        desc,
        transcript_anchor,
        input_digest,
        output_digest,
        backend.hardware_audit_digest(),
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
    ExecutionReceipt::compute_audited(
        key,
        &pin,
        desc,
        transcript_anchor,
        input_digest,
        output_digest,
        backend.hardware_audit_digest(),
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
    ExecutionReceipt::compute_audited(
        key,
        &pin,
        desc,
        transcript_anchor,
        input_digest,
        output_digest,
        backend.hardware_audit_digest(),
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
    let receipt = ExecutionReceipt::compute_audited(
        key,
        &pin,
        desc,
        transcript_anchor,
        input_digest,
        output_digest,
        backend.hardware_audit_digest(),
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
            reg.verify_loaded_profile(KernelTargetArch::SpirV15, &spirv_pins),
            Ok(())
        );

        for slot in KernelSlot::ALL {
            let spv_bytes = spirv_kernel_bytes(slot);
            assert!(spv_bytes.len() >= 1024 && spv_bytes.len().is_multiple_of(4));
            // Valid SPIR-V magic word 0x07230203 in little-endian.
            assert_eq!(&spv_bytes[0..4], &0x0723_0203u32.to_le_bytes());

            let pin = VulkanSpirvBackend::canonical_pin(slot);
            assert_eq!(pin.slot, slot);
            assert_eq!(pin.target_arch, KernelTargetArch::SpirV15);

            let mut tampered = spirv_pins;
            tampered[slot as usize].poseidon2_digest[0] ^= 1;
            assert_eq!(
                reg.verify_loaded_profile(KernelTargetArch::SpirV15, &tampered),
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
                    .chain(
                        table[1..]
                            .iter()
                            .rev()
                            .map(|&w| crate::goldilocks::gl_neg(w)),
                    )
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
        let fourth_power = goldilocks_primitive_root(2).expect("4th root");
        let half_order = [
            1,
            fourth_power,
            gl_mul(fourth_power, fourth_power),
            gl_mul(gl_mul(fourth_power, fourth_power), fourth_power),
        ];
        assert_eq!(
            check_goldilocks_twiddles(8, &half_order),
            Err(AccelError::InvalidTwiddles)
        );
        assert_eq!(
            check_goldilocks_twiddles(8, &[1, fourth_power]),
            Err(AccelError::LengthMismatch {
                what: "NTT twiddles",
                expected: 4,
                actual: 2
            })
        );
    }

    #[test]
    fn audit_evidence_digest_separates_driver_and_telemetry_states() {
        let base = audited_device_info();
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
            v.pipelines[slot].spilled_vgprs = None;
            variants.push(v);
        }
        for slot in 0..ProverKernelSlot::COUNT {
            let mut v = base;
            v.prover_pipelines[slot].subgroup_size = Some(64);
            variants.push(v);
            let mut v = base;
            v.prover_pipelines[slot].scratch_bytes = None;
            variants.push(v);
            let mut v = base;
            v.prover_pipelines[slot].scratch_bytes = Some(8);
            variants.push(v);
            let mut v = base;
            v.prover_pipelines[slot].spilled_vgprs = None;
            variants.push(v);
        }
        let mut digests: std::vec::Vec<[u8; 32]> = variants
            .iter()
            .map(VulkanDeviceInfo::audit_evidence_digest)
            .collect();
        digests.push(reference);
        let total = digests.len();
        digests.sort_unstable();
        digests.dedup();
        assert_eq!(digests.len(), total);
    }

    fn audited_device_info() -> VulkanDeviceInfo {
        VulkanDeviceInfo {
            name_bytes: [0; 256],
            name_len: 0,
            max_compute_shared_memory_size: 65536,
            wave32_required: true,
            pipelines: [PipelineTelemetry {
                subgroup_size: Some(32),
                scratch_bytes: Some(0),
                spilled_vgprs: Some(0),
                spilled_sgprs: Some(0),
                ..PipelineTelemetry::default()
            }; KernelSlot::COUNT],
            prover_pipelines: [PipelineTelemetry {
                subgroup_size: Some(32),
                scratch_bytes: Some(0),
                spilled_vgprs: Some(0),
                spilled_sgprs: Some(0),
                ..PipelineTelemetry::default()
            }; ProverKernelSlot::COUNT],
            vendor_id: 0x1002,
            device_id: 0x73df,
            driver_version: 1,
            api_version: 1,
            device_type: 2,
            max_push_constants_size: 128,
            max_storage_buffer_range: u32::MAX,
            max_compute_work_group_invocations: 1024,
        }
    }

    #[test]
    fn secret_slot_audit_requires_wave32_zero_scratch_and_no_spills_on_every_pipeline() {
        let good = audited_device_info();
        assert_eq!(good.secret_slot_audit(), Ok(()));

        // Both spill counters must explicitly report zero.
        let mut reported_zero_spills = good;
        for stats in &mut reported_zero_spills.pipelines {
            stats.spilled_vgprs = Some(0);
            stats.spilled_sgprs = Some(0);
        }
        assert_eq!(reported_zero_spills.secret_slot_audit(), Ok(()));

        let mut not_required = good;
        not_required.wave32_required = false;
        assert!(matches!(
            not_required.secret_slot_audit(),
            Err(VulkanError::PipelineAuditFailed(_))
        ));

        // What `try_new` yields on a driver without executable statistics: nothing reported.
        let mut no_telemetry = good;
        no_telemetry.pipelines = [PipelineTelemetry::default(); KernelSlot::COUNT];
        assert!(no_telemetry.secret_slot_audit().is_err());

        let defects: [fn(&mut PipelineTelemetry); 8] = [
            |t| t.subgroup_size = None,
            |t| t.subgroup_size = Some(64),
            |t| t.scratch_bytes = None,
            |t| t.scratch_bytes = Some(8),
            |t| t.spilled_vgprs = None,
            |t| t.spilled_sgprs = None,
            |t| t.spilled_vgprs = Some(1),
            |t| t.spilled_sgprs = Some(1),
        ];
        for slot in 0..KernelSlot::COUNT {
            for (case, defect) in defects.iter().enumerate() {
                let mut bad = good;
                defect(&mut bad.pipelines[slot]);
                assert!(
                    matches!(
                        bad.secret_slot_audit(),
                        Err(VulkanError::PipelineAuditFailed(_))
                    ),
                    "slot {slot}, defect {case} passed the audit"
                );
            }
        }
        for slot in 0..ProverKernelSlot::COUNT {
            for (case, defect) in defects.iter().enumerate() {
                let mut bad = good;
                defect(&mut bad.prover_pipelines[slot]);
                assert!(
                    matches!(
                        bad.secret_slot_audit(),
                        Err(VulkanError::PipelineAuditFailed(_))
                    ),
                    "prover slot {slot}, defect {case} passed the audit"
                );
            }
        }
    }

    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    #[test]
    fn secret_slot_gate_refuses_exactly_the_unaudited_backend() {
        for slot in KernelSlot::ALL {
            assert_eq!(secret_slot_gate(true, slot), Ok(()));
            assert_eq!(
                secret_slot_gate(false, slot),
                Err(AccelError::SecretSlotUnaudited { slot })
            );
        }
    }

    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    #[test]
    fn device_failure_on_the_infallible_path_is_counted_and_answered_by_the_cpu() {
        let fallbacks = AtomicU64::new(0);
        let input = [[0x0123_4567_89AB_CDEFu64; 25]; 3];
        let mut expected = input;
        CpuReferenceBackend.batch_keccak_f1600(&mut expected);

        // Device succeeds: the CPU closure never runs and nothing is counted.
        let mut states = input;
        gpu_or_counted_cpu_fallback(
            &fallbacks,
            &mut states[..],
            |s| {
                CpuReferenceBackend.batch_keccak_f1600(s);
                Ok(())
            },
            |_| panic!("fallback ran after a successful device job"),
        );
        assert_eq!(states, expected);
        assert_eq!(fallbacks.load(Ordering::Relaxed), 0);

        // Device fails: one count per call, CPU result returned.
        for calls in 1..=3u64 {
            let mut states = input;
            gpu_or_counted_cpu_fallback(
                &fallbacks,
                &mut states[..],
                |_| Err(VulkanError::WorkspacePoisoned),
                |s| CpuReferenceBackend.batch_keccak_f1600(s),
            );
            assert_eq!(states, expected);
            assert_eq!(fallbacks.load(Ordering::Relaxed), calls);
        }
    }

    /// Needs a discrete GPU; returns early without one.
    #[cfg(all(feature = "std", target_os = "linux", target_pointer_width = "64"))]
    #[test]
    fn live_backend_refuses_bdoz_without_audit_evidence_and_counts_fallbacks() {
        let mut gpu = match VulkanSpirvBackend::try_new() {
            Ok(gpu) => gpu,
            Err(VulkanError::LibraryLoadFailed | VulkanError::NoDiscreteGpuFound) => return,
            Err(other) => panic!("unexpected Vulkan initialization error: {other}"),
        };
        assert_eq!(
            gpu.secret_slots_audited(),
            gpu.device_info().secret_slot_audit().is_ok()
        );
        let shares = [(0xAAu128, 0xBBu128); 4];
        let weights = [(3u128, 5u128); 4];
        let slot = KernelSlot::BdozGf2128BatchDot;

        // Inject missing audit status to exercise dispatch gates independently of construction.
        gpu.secret_slots_audited = false;
        assert_eq!(
            gpu.bdoz_gf2_128_batch_dot(&shares, &weights),
            Err(AccelError::SecretSlotUnaudited { slot })
        );
        let key = BackendAttestationKey::derive(&[0x44u8; 32], b"unaudited-gpu");
        assert_eq!(
            bdoz_gf2_128_batch_dot_with_receipt(&gpu, &key, &shares, &weights, [0u8; 32])
                .map(|_| ()),
            Err(AccelError::SecretSlotUnaudited { slot })
        );
        assert_eq!(
            gpu.gpu_submission_count(),
            0,
            "refused shares reached the GPU"
        );
        // Shape errors still come first, as on every backend.
        assert!(matches!(
            gpu.bdoz_gf2_128_batch_dot(&shares, &weights[..1]),
            Err(AccelError::LengthMismatch { .. })
        ));

        // A device failure on the infallible path is visible through the trait.
        assert_eq!(AcceleratorBackend::cpu_fallback_count(&gpu), 0);
        let mut states = [[9u64; 25]; 2];
        let mut expected = states;
        CpuReferenceBackend.batch_keccak_f1600(&mut expected);
        gpu.batch_keccak_f1600(&mut states);
        assert_eq!(states, expected);
        assert_eq!(gpu.cpu_fallback_count(), 1);
        assert_eq!(gpu.gpu_submission_count(), 0);
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
                KernelTargetArch::SpirV15
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
