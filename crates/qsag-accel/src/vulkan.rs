//! Certified zero-dependency Vulkan / SPIR-V GPU backend (`VulkanSpirvBackend`,
//! aliased as `VulkanSpirvBackend`) implementing [`AcceleratorBackend`] (`KernelTargetArch::SpirV15`).
//!
//! On 64-bit Linux (`libvulkan.so.1` / Mesa RADV) and 64-bit macOS Apple Silicon (`libvulkan.1.dylib`
//! / `libMoltenVK.dylib` via `VK_KHR_portability_enumeration` + `VK_KHR_portability_subset`) with
//! `feature = "std"`, `VulkanSpirvBackend` dynamically loads the runtime Vulkan library, selects a
//! hardware GPU supporting native 64-bit integer shaders (`shaderInt64`), allocates `DEVICE_LOCAL`
//! VRAM storage buffers, compiles all 6 deterministic SPIR-V compute kernels,
//! and pins their SHA-256 and Width-12 Goldilocks Poseidon2 digests.
//!
//! On other targets, 32-bit targets, or `#![no_std]` builds without `std`, `try_new()` cleanly
//! returns `Err(VulkanError::UnsupportedPlatform)` with zero external crate dependencies.
//!
//! # Secret inputs
//!
//! * Secret-bearing slots (`BdozGf2128BatchDot`) and audited `try_new()` / `try_new_audited()`
//!   constructors require the full evidence in [`VulkanDeviceInfo::secret_slot_audit`].
//!   [`VulkanSpirvBackend::try_new_portability`] enables public-data kernels on Wave32 portability
//!   drivers (such as Apple Silicon `libMoltenVK.dylib`) while keeping `BdozGf2128BatchDot` and
//!   audited V5 receipts gated behind `secret_slots_audited`.
//! * GPU execution is strict by default: fallible/pinned methods return errors and legacy
//!   infallible batch methods panic on failure. Only explicitly named `*_with_cpu_fallback`
//!   methods permit CPU execution; they return the failure reason and record telemetry.
//! * A job's inputs are wiped from host staging memory on every exit once the device is known
//!   idle. After `VK_ERROR_DEVICE_LOST` that cannot be known: the backend refuses all further
//!   jobs and the failed job's inputs stay in staging memory and VRAM until the process exits.

#[cfg(all(
    feature = "std",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
use core::sync::atomic::{AtomicU64, Ordering};

use crate::goldilocks::{check_goldilocks_twiddles, coset_lde_shape, ntt_log2_len};
use crate::keccak::{cshake256_framed_32, finalize_cshake256, init_cshake256};
use crate::poseidon2::{Poseidon2Merkle2BlockAddr, merkle_layer_2block_shape, merkle_layer_shape};
use crate::spirv_kernels::{canonical_spirv_pin, canonical_spirv_pins};
use crate::{
    AccelError, AcceleratorBackend, BackendAttestationKey, BatchJobDescriptor, CertifiedKernelPin,
    ExecutionReceipt, KernelSlot, KernelTargetArch, hash_counted_u64s, hash_u64_rows,
    merkle_layer_input_digest, merkle_layer_output_digest,
};

#[cfg(all(
    feature = "std",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
use crate::CpuReferenceBackend;
#[cfg(all(
    feature = "std",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
use crate::poseidon2::{poseidon2_canopy_root_cpu, poseidon2_canopy_tree_key_cpu};
#[cfg(all(
    feature = "std",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
use crate::vulkan_ffi::RawVulkanEngine;

/// Errors returned during Vulkan device discovery, pipeline creation, or GPU kernel execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VulkanError {
    /// Target OS, pointer width, or crate feature configuration does not enable the Vulkan loader.
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
    /// Dynamic `dlopen` of the platform Vulkan / MoltenVK library failed.
    LibraryLoadFailed,
    /// A required core Vulkan entry point was not exported by the loader or ICD.
    SymbolMissing(&'static str),
    /// A Vulkan API call returned a non-`VK_SUCCESS` status code.
    VkResult { op: &'static str, code: i32 },
    /// No compatible hardware GPU physical device was reported by the Vulkan instance.
    NoDiscreteGpuFound,
    /// Hardware GPU does not advertise `VkPhysicalDeviceFeatures::shaderInt64`.
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
            Self::UnsupportedPlatform => f.write_str(
                "Vulkan SPIR-V backend requires 64-bit Linux or macOS with feature `std`",
            ),
            Self::LibraryLoadFailed => {
                f.write_str("failed to dlopen Vulkan / MoltenVK runtime library")
            }
            Self::SymbolMissing(sym) => write!(f, "missing Vulkan entry point `{sym}`"),
            Self::VkResult { op, code } => write!(f, "{op} failed with VkResult {code}"),
            Self::NoDiscreteGpuFound => {
                f.write_str("no compatible hardware Vulkan GPU physical device found")
            }
            Self::MissingShaderInt64 => {
                f.write_str("hardware Vulkan GPU does not support `shaderInt64`")
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
    /// Spilled registers. RADV reports both counters for every pipeline (observed as zero for
    /// all six kernels on the RX 6750 XT); a driver that omits them fails [`Self::audit`].
    pub spilled_vgprs: Option<u64>,
    pub spilled_sgprs: Option<u64>,
}

impl PipelineTelemetry {
    /// The pipeline gate every kernel passes before the engine exists: the driver must
    /// report zero private scratch memory and zero spilled registers. A statistic the driver
    /// did not report (`None`) is a failure, never an implicit zero, so a driver without
    /// `VK_KHR_pipeline_executable_properties` (every field `None`) cannot pass.
    pub fn audit(&self) -> Result<(), VulkanError> {
        if self.scratch_bytes.is_none()
            || self.spilled_vgprs.is_none()
            || self.spilled_sgprs.is_none()
        {
            return Err(VulkanError::PipelineAuditFailed(
                "scratch or spill statistic not reported",
            ));
        }
        if self.scratch_bytes != Some(0) {
            return Err(VulkanError::PipelineAuditFailed(
                "nonzero private scratch memory",
            ));
        }
        if self.spilled_vgprs != Some(0) || self.spilled_sgprs != Some(0) {
            return Err(VulkanError::PipelineAuditFailed("spilled registers"));
        }
        Ok(())
    }
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
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
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

    /// True iff every compute pipeline reports `subgroup_size == Some(32)` (Wave32 /
    /// Apple GPU 32-lane SIMD-group width), which our subgroup-shuffle shaders assume.
    pub fn wave32_subgroup_confirmed(&self) -> bool {
        self.pipelines
            .iter()
            .all(|stats| stats.subgroup_size == Some(32))
    }

    /// The evidence a secret-bearing kernel slot requires: the driver was made to compile every
    /// pipeline at subgroup size 32 and reported, for each one, subgroup size 32, zero scratch
    /// bytes and no spilled registers ([`PipelineTelemetry::audit`]). A statistic the driver did
    /// not report counts as missing evidence.
    ///
    /// These are compiler reports, not a constant-time or physical side-channel proof.
    pub fn secret_slot_audit(&self) -> Result<(), VulkanError> {
        if !self.wave32_required {
            return Err(VulkanError::PipelineAuditFailed(
                "subgroup size 32 was not required at pipeline creation",
            ));
        }
        for stats in &self.pipelines {
            if stats.subgroup_size != Some(32) {
                return Err(VulkanError::PipelineAuditFailed(
                    "a pipeline did not report subgroup size 32",
                ));
            }
            stats.audit()?;
        }
        Ok(())
    }

    /// Digest of the driver identity and per-pipeline executable telemetry this backend was
    /// built on. A host that folds it into a receipt's `transcript_anchor` makes the receipt
    /// name the driver state (Wave32, scratch, spill, LDS figures) it reports having run on.
    /// Like the receipt itself this is a report by the key holder, not a proof.
    pub fn audit_evidence_digest(&self) -> [u8; 32] {
        const PER_PIPELINE: usize = 7 * 9;
        const TOTAL_PIPELINES: usize = KernelSlot::COUNT;
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
            .zip(self.pipelines.iter())
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

/// Execution location of an explicitly fallback-enabled batch. CPU results carry the original
/// GPU failure and must never be attributed to a SPIR-V kernel pin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[must_use = "inspect whether execution used the GPU or the CPU fallback"]
pub enum BatchExecution {
    Gpu,
    CpuFallback { error: VulkanError },
}

/// Most recent explicit CPU fallback. The count is cumulative across both batch slots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuFallbackEvent {
    pub count: u64,
    pub slot: KernelSlot,
    pub error: VulkanError,
}

/// Hardware GPU compute backend executing certified 64-bit SPIR-V shaders in `DEVICE_LOCAL`
/// VRAM / unified memory (`KernelTargetArch::SpirV15`).
pub struct VulkanSpirvBackend {
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    info: VulkanDeviceInfo,
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    pins: [CertifiedKernelPin; KernelSlot::COUNT],
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    engine: std::sync::Mutex<RawVulkanEngine>,
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    gpu_submissions: AtomicU64,
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    cpu_fallbacks: AtomicU64,
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    last_cpu_fallback: std::sync::Mutex<Option<CpuFallbackEvent>>,
    /// `info.secret_slot_audit().is_ok()`, fixed at construction.
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    secret_slots_audited: bool,
    /// Set only by [`Self::try_new_portability`] when Wave32 subgroup width is confirmed on a
    /// portability driver (e.g. macOS Apple Silicon `libMoltenVK.dylib`). Never unlocks
    /// `BdozGf2128BatchDot` or audited V5 prover receipts.
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    portability_public_enabled: bool,
    #[cfg(not(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    )))]
    _uninhabited: core::convert::Infallible,
}

impl core::fmt::Debug for VulkanSpirvBackend {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            f.debug_struct("VulkanSpirvBackend")
                .field("info", &self.info)
                .field(
                    "gpu_submissions",
                    &self.gpu_submissions.load(Ordering::Relaxed),
                )
                .field("cpu_fallbacks", &self.cpu_fallbacks.load(Ordering::Relaxed))
                .field("secret_slots_audited", &self.secret_slots_audited)
                .field(
                    "portability_public_enabled",
                    &self.portability_public_enabled,
                )
                .finish()
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = f;
            match self._uninhabited {}
        }
    }
}

/// Shape errors pass through; every device, driver, or lock failure is a backend failure.
#[cfg(all(
    feature = "std",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
fn accel_error(err: VulkanError) -> AccelError {
    match err {
        VulkanError::Accel(shape) => shape,
        _ => AccelError::BackendFailure,
    }
}

/// Refuse a secret-bearing slot on a backend without pipeline audit evidence.
#[cfg(all(
    feature = "std",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
const fn secret_slot_gate(audited: bool, slot: KernelSlot) -> Result<(), AccelError> {
    if audited {
        Ok(())
    } else {
        Err(AccelError::SecretSlotUnaudited { slot })
    }
}

/// Gate for public-data slots: requires either full `secret_slots_audited` or explicit
/// Wave32-confirmed `portability_public_enabled` (`try_new_portability`).
#[cfg(all(
    feature = "std",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
const fn public_slot_gate(
    audited: bool,
    portability_public_enabled: bool,
    slot: KernelSlot,
) -> Result<(), AccelError> {
    if audited || portability_public_enabled {
        Ok(())
    } else {
        Err(AccelError::SecretSlotUnaudited { slot })
    }
}

/// A failed GPU job has not written `states`: FFI copies back only after successful submission.
/// No callback runs under the telemetry lock, so panic in a caller cannot poison it.
#[cfg(all(
    feature = "std",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
fn gpu_or_explicit_cpu_fallback<S: ?Sized>(
    fallbacks: &AtomicU64,
    last: &std::sync::Mutex<Option<CpuFallbackEvent>>,
    slot: KernelSlot,
    states: &mut S,
    gpu: impl FnOnce(&mut S) -> Result<(), VulkanError>,
    cpu: impl FnOnce(&mut S),
) -> BatchExecution {
    match gpu(states) {
        Ok(()) => BatchExecution::Gpu,
        Err(error) => {
            cpu(states);
            let mut event = last
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let count = fallbacks.fetch_add(1, Ordering::Relaxed) + 1;
            *event = Some(CpuFallbackEvent { count, slot, error });
            BatchExecution::CpuFallback { error }
        }
    }
}

impl VulkanSpirvBackend {
    /// Runtime library search paths probed on macOS (`libvulkan.1.dylib` loader and `libMoltenVK.dylib`).
    pub const fn macos_library_search_paths() -> [&'static str; 2] {
        [
            "/opt/homebrew/lib/libvulkan.1.dylib",
            "/opt/homebrew/lib/libMoltenVK.dylib",
        ]
    }

    /// Discover a hardware Vulkan GPU with `shaderInt64`, compile all embedded SPIR-V compute
    /// pipelines, and allocate persistent host-cached staging + `DEVICE_LOCAL` VRAM buffers.
    ///
    /// Requires audited Wave32 and explicit zero scratch and spill statistics for all slots.
    pub fn try_new() -> Result<Self, VulkanError> {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            let (engine, info) = RawVulkanEngine::try_new()?;
            info.secret_slot_audit()?;
            let pins = canonical_spirv_pins();
            Ok(Self {
                info,
                pins,
                engine: std::sync::Mutex::new(engine),
                gpu_submissions: AtomicU64::new(0),
                cpu_fallbacks: AtomicU64::new(0),
                last_cpu_fallback: std::sync::Mutex::new(None),
                secret_slots_audited: info.secret_slot_audit().is_ok(),
                portability_public_enabled: false,
            })
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            Err(VulkanError::UnsupportedPlatform)
        }
    }

    /// Discover a hardware Vulkan or `VK_KHR_portability_subset` GPU (such as Apple Silicon
    /// unified-memory GPUs via `libMoltenVK.dylib`) with `shaderInt64` and confirmed 32-lane
    /// subgroup width (`subgroupSize == 32`).
    ///
    /// If the driver also reports full zero-scratch / zero-spill `VK_KHR_pipeline_executable_properties`
    /// telemetry (e.g. Linux Mesa RADV), `secret_slots_audited()` is `true` and all kernels and
    /// audited V5 receipts are enabled. On portability drivers without executable statistics
    /// (such as `libMoltenVK`), public-data kernels execute natively on GPU while secret-bearing
    /// `BdozGf2128BatchDot` and audited V5 receipts remain strictly gated closed.
    pub fn try_new_portability() -> Result<Self, VulkanError> {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            let (engine, info) = RawVulkanEngine::try_new_portability()?;
            if !info.wave32_subgroup_confirmed() {
                return Err(VulkanError::PipelineAuditFailed(
                    "portability backend requires confirmed subgroup size 32",
                ));
            }
            let secret_slots_audited = info.secret_slot_audit().is_ok();
            let pins = canonical_spirv_pins();
            Ok(Self {
                info,
                pins,
                engine: std::sync::Mutex::new(engine),
                gpu_submissions: AtomicU64::new(0),
                cpu_fallbacks: AtomicU64::new(0),
                last_cpu_fallback: std::sync::Mutex::new(None),
                secret_slots_audited,
                portability_public_enabled: true,
            })
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            Err(VulkanError::UnsupportedPlatform)
        }
    }

    /// Require driver-confirmed Wave32 and zero scratch for every executable
    /// ([`VulkanDeviceInfo::secret_slot_audit`]). As with `try_new`, unavailable telemetry is an
    /// error. This checks compiler reports, not a formal constant-time or physical
    /// side-channel proof.
    #[cfg(all(
        feature = "fault-injection-audit",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    #[doc(hidden)]
    pub fn audit_replace_kernel_spirv(&self, slot: KernelSlot, spv: &[u32]) -> Result<(), VulkanError> {
        let mut eng = self.engine.lock().map_err(|_| VulkanError::WorkspacePoisoned)?;
        eng.replace_kernel_pipeline_for_audit(slot, spv)
    }

    pub fn try_new_audited() -> Result<Self, VulkanError> {
        let backend = Self::try_new()?;
        backend.device_info().secret_slot_audit()?;
        Ok(backend)
    }

    /// Whether this backend holds the evidence of [`VulkanDeviceInfo::secret_slot_audit`].
    /// Always true for `try_new` / `try_new_audited`. Unaudited secret-slot dispatch returns
    /// [`AccelError::SecretSlotUnaudited`].
    pub fn secret_slots_audited(&self) -> bool {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            self.secret_slots_audited
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            match self._uninhabited {}
        }
    }

    /// Number of explicitly fallback-enabled calls answered by the CPU after GPU failure.
    pub fn cpu_fallback_count(&self) -> u64 {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            self.cpu_fallbacks.load(Ordering::Relaxed)
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            match self._uninhabited {}
        }
    }

    /// Latest explicit fallback, including the affected kernel and original GPU error.
    pub fn last_cpu_fallback(&self) -> Option<CpuFallbackEvent> {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            *self
                .last_cpu_fallback
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            match self._uninhabited {}
        }
    }

    /// Explicitly allow CPU Keccak execution if the GPU fails. Inspect the returned location
    /// and error; use the pinned method instead when GPU execution is required.
    pub fn batch_keccak_f1600_with_cpu_fallback(&self, states: &mut [[u64; 25]]) -> BatchExecution {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            gpu_or_explicit_cpu_fallback(
                &self.cpu_fallbacks,
                &self.last_cpu_fallback,
                KernelSlot::BatchKeccakF1600,
                states,
                |s| self.try_batch_keccak_f1600(s),
                |s| CpuReferenceBackend.batch_keccak_f1600(s),
            )
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    /// Explicitly allow CPU Poseidon2 execution if the GPU fails. The returned error and
    /// [`Self::last_cpu_fallback`] identify the fallback; this method issues no GPU receipt.
    pub fn batch_poseidon2_perm12_with_cpu_fallback(
        &self,
        states: &mut [[u64; 12]],
    ) -> BatchExecution {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            gpu_or_explicit_cpu_fallback(
                &self.cpu_fallbacks,
                &self.last_cpu_fallback,
                KernelSlot::BatchPoseidon2Perm12,
                states,
                |s| self.try_batch_poseidon2_perm12(s),
                |s| CpuReferenceBackend.batch_poseidon2_perm12(s),
            )
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = states;
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

    /// Pins of the 6 embedded SPIR-V binaries the engine loads, for
    /// `CertifiedBackend::try_new_measured`. The modules are compiled in, so these equal
    /// [`Self::canonical_pins`].
    pub fn measure_embedded_spirv_pins() -> [CertifiedKernelPin; KernelSlot::COUNT] {
        canonical_spirv_pins()
    }

    /// Hardware properties of the bound Vulkan GPU.
    pub fn device_info(&self) -> &VulkanDeviceInfo {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            &self.info
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            match self._uninhabited {}
        }
    }

    /// Physical device name reported by the Vulkan driver.
    pub fn device_name(&self) -> &str {
        self.device_info().device_name()
    }

    /// PCI vendor ID reported by the Vulkan driver (`0x1002` for AMD, `0x106B` for Apple).
    pub fn vendor_id(&self) -> u32 {
        self.device_info().vendor_id
    }

    /// Driver version word reported by the Vulkan driver.
    pub fn driver_version(&self) -> u32 {
        self.device_info().driver_version
    }

    /// Total number of `VkCommandBuffer` submissions executed on the physical GPU by this instance.
    pub fn gpu_submission_count(&self) -> u64 {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            self.gpu_submissions.load(Ordering::Relaxed)
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            match self._uninhabited {}
        }
    }

    /// Fallible GPU batch `Keccak-f[1600]` dispatch.
    pub fn try_batch_keccak_f1600(&self, states: &mut [[u64; 25]]) -> Result<(), VulkanError> {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::BatchKeccakF1600,
            )
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
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    /// Fallible GPU batch Width-12 Goldilocks `Poseidon2` dispatch.
    pub fn try_batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]) -> Result<(), VulkanError> {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::BatchPoseidon2Perm12,
            )
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
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
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
        ntt_log2_len("Merkle tree leaves", leaves.len())?;
        // Level `l` is tweaked with `base_layer + l`; a wrapped tweak would alias another layer.
        if base_layer
            .checked_add(leaves.len().trailing_zeros().saturating_sub(1))
            .is_none()
        {
            return Err(AccelError::LengthOverflow.into());
        }
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::MerkleLayerPoseidon2,
            )
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
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (pk_seed, base_layer);
            match self._uninhabited {}
        }
    }

    /// Build a complete 2-block full-`pk_seed` Poseidon2 Merkle tree (`qsag_agg::sig::merkle_node_hash`,
    /// `paper/qsag.typ:220`) of `leaves.len() = 2^H` leaves completely inside GPU `DEVICE_LOCAL`
    /// VRAM within a single `VkCommandBuffer` submission (`0` CPU copies between tree layers).
    pub fn build_merkle_tree_poseidon2_2block(
        &self,
        leaves: &[[u64; 4]],
        domain_tag: u64,
        pk_seed: &[u64; 4],
        layer: u32,
        tree_idx: u64,
        base_level: u32,
    ) -> Result<[u64; 4], VulkanError> {
        ntt_log2_len("Merkle tree leaves", leaves.len())?;
        if layer > 0xFFFE {
            return Err(AccelError::LengthOverflow.into());
        }
        let h = leaves.len().trailing_zeros();
        let max_lvl = if h == 0 {
            Some(base_level)
        } else {
            base_level.checked_add(h - 1)
        };
        if max_lvl.is_none_or(|l| l > 0xFFFF) {
            return Err(AccelError::LengthOverflow.into());
        }
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::MerkleLayerPoseidon2,
            )
            .map_err(VulkanError::from)?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let root = guard.exec_merkle_full_tree_2block(
                leaves, domain_tag, pk_seed, layer, tree_idx, base_level,
            )?;
            if leaves.len() > 1 {
                self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            }
            Ok(root)
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (domain_tag, pk_seed, layer, tree_idx, base_level);
            match self._uninhabited {}
        }
    }

    /// Build a complete 1-indexed Poseidon2 WHIR Canopy Merkle tree (`out_nodes.len() == 2 * leaves.len()`,
    /// matching `qsag_agg::pcs::MerkleCanopyTree::build_poseidon2` in WHIR regimes 7 & 8) completely
    /// inside GPU VRAM within a single `VkCommandBuffer` submission, returning the domain-separated
    /// Canopy commitment root `poseidon2_canopy_root_cpu(stage_idx, log_leaves, tree_salt, out_nodes[1])`.
    pub fn build_canopy_tree_poseidon2(
        &self,
        leaves: &[[u64; 4]],
        stage_idx: u8,
        tree_salt: [u64; 4],
        out_nodes: &mut [[u64; 4]],
    ) -> Result<[u64; 4], VulkanError> {
        let log_leaves = ntt_log2_len("Canopy tree leaves", leaves.len())? as u8;
        let total_nodes = leaves
            .len()
            .checked_mul(2)
            .ok_or(AccelError::LengthOverflow)?;
        if out_nodes.len() != total_nodes {
            return Err(AccelError::LengthMismatch {
                what: "Canopy tree nodes",
                expected: total_nodes,
                actual: out_nodes.len(),
            }
            .into());
        }
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::MerkleLayerPoseidon2,
            )
            .map_err(VulkanError::from)?;
            let tree_key = poseidon2_canopy_tree_key_cpu(stage_idx, log_leaves, tree_salt);
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let top_node =
                guard.exec_canopy_tree_poseidon2(leaves, &tree_key, 0, 0, 0, 2, out_nodes)?;
            if leaves.len() > 1 {
                self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            }
            Ok(poseidon2_canopy_root_cpu(
                stage_idx, log_leaves, tree_salt, top_node,
            ))
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (stage_idx, log_leaves, tree_salt);
            match self._uninhabited {}
        }
    }

    /// Build a complete 1-indexed 2-block Poseidon2 Canopy Merkle tree (`out_nodes.len() == 2 * leaves.len()`)
    /// completely inside GPU VRAM within a single `VkCommandBuffer` submission, returning `out_nodes[1]`.
    pub fn build_canopy_tree_poseidon2_2block(
        &self,
        leaves: &[[u64; 4]],
        domain_tag: u64,
        pk_seed: &[u64; 4],
        layer: u32,
        tree_idx: u64,
        out_nodes: &mut [[u64; 4]],
    ) -> Result<[u64; 4], VulkanError> {
        ntt_log2_len("Canopy tree leaves", leaves.len())?;
        let total_nodes = leaves
            .len()
            .checked_mul(2)
            .ok_or(AccelError::LengthOverflow)?;
        if out_nodes.len() != total_nodes {
            return Err(AccelError::LengthMismatch {
                what: "Canopy tree nodes",
                expected: total_nodes,
                actual: out_nodes.len(),
            }
            .into());
        }
        if layer > 0xFFFE || leaves.len().trailing_zeros() > 0x10000 {
            return Err(AccelError::LengthOverflow.into());
        }
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::MerkleLayerPoseidon2,
            )
            .map_err(VulkanError::from)?;
            let mut guard = self
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let top_node = guard.exec_canopy_tree_poseidon2(
                leaves, pk_seed, layer, domain_tag, tree_idx, 1, out_nodes,
            )?;
            if leaves.len() > 1 {
                self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            }
            Ok(top_node)
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (domain_tag, pk_seed, layer, tree_idx);
            match self._uninhabited {}
        }
    }

    /// Whether all compute pipelines passed zero-scratch / zero-spill driver telemetry.
    pub fn is_secret_slots_audited(&self) -> bool {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            self.secret_slots_audited
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
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
        ntt_log2_len("NTT input", buf.len())?;
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::GoldilocksNtt,
            )?;
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_goldilocks_ntt_canonical(buf, inverse)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = inverse;
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
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            self.pins[slot as usize]
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = slot;
            match self._uninhabited {}
        }
    }

    fn batch_keccak_f1600(&self, states: &mut [[u64; 25]]) {
        self.try_batch_keccak_f1600(states).expect(
            "strict Vulkan batch execution failed; use try_batch_keccak_f1600 to handle errors",
        );
    }

    fn try_batch_keccak_f1600_pinned(
        &self,
        states: &mut [[u64; 25]],
    ) -> Result<CertifiedKernelPin, AccelError> {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            self.try_batch_keccak_f1600(states).map_err(accel_error)?;
            Ok(self.pins[KernelSlot::BatchKeccakF1600 as usize])
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = states;
            match self._uninhabited {}
        }
    }

    fn batch_poseidon2_perm12(&self, states: &mut [[u64; 12]]) {
        self.try_batch_poseidon2_perm12(states).expect(
            "strict Vulkan batch execution failed; use try_batch_poseidon2_perm12 to handle errors",
        );
    }

    fn try_batch_poseidon2_perm12_pinned(
        &self,
        states: &mut [[u64; 12]],
    ) -> Result<CertifiedKernelPin, AccelError> {
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            self.try_batch_poseidon2_perm12(states)
                .map_err(accel_error)?;
            Ok(self.pins[KernelSlot::BatchPoseidon2Perm12 as usize])
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
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
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::GoldilocksNtt,
            )?;
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_goldilocks_ntt(buf, twiddles, inverse)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
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
        coset_lde_shape(evals.len(), blowup, out.len())?;
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::CosetLdeExt2,
            )?;
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_coset_lde_ext2(evals, blowup, shift, out)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
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
        merkle_layer_shape(children.len(), out_parents.len(), start_parent_idx)?;
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::MerkleLayerPoseidon2,
            )?;
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
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (pk_seed, layer, start_parent_idx);
            match self._uninhabited {}
        }
    }

    fn try_merkle_layer_poseidon2_2block_at(
        &self,
        children: &[[u64; 4]],
        domain_tag: u64,
        pk_seed: &[u64; 4],
        addr: Poseidon2Merkle2BlockAddr,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        merkle_layer_2block_shape(children.len(), out_parents.len(), addr)?;
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::MerkleLayerPoseidon2,
            )?;
            if out_parents.is_empty() {
                return Ok(());
            }
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_merkle_layer_mode(
                    children,
                    pk_seed,
                    addr.layer,
                    addr.level,
                    domain_tag,
                    addr.tree_idx,
                    1,
                    addr.start_node_idx,
                    out_parents,
                )
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (domain_tag, pk_seed, addr);
            match self._uninhabited {}
        }
    }

    fn try_merkle_layer_poseidon2_canopy_at(
        &self,
        children: &[[u64; 4]],
        tree_key: &[u64; 4],
        start_node_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        merkle_layer_shape(children.len(), out_parents.len(), start_node_idx)?;
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::MerkleLayerPoseidon2,
            )?;
            if out_parents.is_empty() {
                return Ok(());
            }
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_merkle_layer_mode(
                    children,
                    tree_key,
                    0,
                    0,
                    0,
                    0,
                    2,
                    start_node_idx,
                    out_parents,
                )
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (tree_key, start_node_idx);
            match self._uninhabited {}
        }
    }

    fn try_merkle_layer_poseidon2_fixed_tweak(
        &self,
        children: &[[u64; 4]],
        tweak: &[u64; 4],
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), AccelError> {
        merkle_layer_shape(children.len(), out_parents.len(), 0)?;
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            public_slot_gate(
                self.secret_slots_audited,
                self.portability_public_enabled,
                KernelSlot::MerkleLayerPoseidon2,
            )?;
            if out_parents.is_empty() {
                return Ok(());
            }
            let mut guard = self.engine.lock().map_err(|_| AccelError::BackendFailure)?;
            guard
                .exec_merkle_layer_mode(children, tweak, 0, 0, 0, 0, 3, 0, out_parents)
                .map_err(accel_error)?;
            self.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = tweak;
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
        #[cfg(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
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
        #[cfg(not(all(
            feature = "std",
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (shares, weights);
            match self._uninhabited {}
        }
    }
}

// ============================================================================
// Keyed `ExecutionReceipt` Helpers Across All 6 Certified `KernelSlot`s
// ============================================================================

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
    hash_counted_u64s(b"QSAG.ACCEL.NTT_OUT.V1", buf.len(), buf)
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
    #[cfg(all(test, feature = "std"))]
    let start = std::time::Instant::now();
    let input_digest = goldilocks_ntt_input_digest(buf, twiddles);
    #[cfg(all(test, feature = "std"))]
    let input_elapsed = start.elapsed();
    backend.goldilocks_ntt_inplace(buf, twiddles, inverse)?;
    #[cfg(all(test, feature = "std"))]
    let kernel_elapsed = start.elapsed() - input_elapsed;
    let output_digest = goldilocks_ntt_output_digest(buf);
    #[cfg(all(test, feature = "std"))]
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
mod telemetry_audit_tests {
    use super::{PipelineTelemetry, VulkanError};

    const CLEAN: PipelineTelemetry = PipelineTelemetry {
        subgroup_size: Some(32),
        scratch_bytes: Some(0),
        vgprs: None,
        sgprs: None,
        lds_bytes: None,
        spilled_vgprs: Some(0),
        spilled_sgprs: Some(0),
    };

    #[test]
    fn missing_or_nonzero_scratch_and_spill_statistics_fail_closed() {
        assert_eq!(CLEAN.audit(), Ok(()));
        // A driver without the executable-statistics extension reports nothing at all.
        let cases: [fn(&mut PipelineTelemetry); 7] = [
            |t| *t = PipelineTelemetry::default(),
            |t| t.scratch_bytes = None,
            |t| t.spilled_vgprs = None,
            |t| t.spilled_sgprs = None,
            |t| t.scratch_bytes = Some(8),
            |t| t.spilled_vgprs = Some(1),
            |t| t.spilled_sgprs = Some(1),
        ];
        for change in cases {
            let mut tel = CLEAN;
            change(&mut tel);
            assert!(
                matches!(tel.audit(), Err(VulkanError::PipelineAuditFailed(_))),
                "{tel:?}"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spirv_kernels::spirv_kernel_bytes;
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
        use crate::goldilocks::{check_goldilocks_twiddles, gl_mul, goldilocks_primitive_root};

        for log2_n in 0..=11u32 {
            let n = 1usize << log2_n;
            let mut table = std::vec![1; n / 2];
            let root = goldilocks_primitive_root(log2_n).expect("root");
            for i in 1..table.len() {
                table[i] = gl_mul(table[i - 1], root);
            }
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
    }

    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    #[test]
    fn secret_slot_gate_refuses_exactly_the_unaudited_backend() {
        for slot in KernelSlot::ALL {
            assert_eq!(secret_slot_gate(true, slot), Ok(()));
            assert_eq!(
                secret_slot_gate(false, slot),
                Err(AccelError::SecretSlotUnaudited { slot })
            );
            assert_eq!(public_slot_gate(true, false, slot), Ok(()));
            assert_eq!(public_slot_gate(false, true, slot), Ok(()));
            assert_eq!(
                public_slot_gate(false, false, slot),
                Err(AccelError::SecretSlotUnaudited { slot })
            );
        }
    }

    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    #[test]
    fn explicit_cpu_fallback_reports_success_and_original_error() {
        let fallbacks = AtomicU64::new(0);
        let last = std::sync::Mutex::new(None);
        let slot = KernelSlot::BatchKeccakF1600;
        let input = [[0x0123_4567_89AB_CDEFu64; 25]; 3];
        let mut expected = input;
        CpuReferenceBackend.batch_keccak_f1600(&mut expected);

        // Device succeeds: the CPU closure never runs and nothing is counted.
        let mut states = input;
        let outcome = gpu_or_explicit_cpu_fallback(
            &fallbacks,
            &last,
            slot,
            &mut states[..],
            |s| {
                CpuReferenceBackend.batch_keccak_f1600(s);
                Ok(())
            },
            |_| panic!("fallback ran after a successful device job"),
        );
        assert_eq!(states, expected);
        assert_eq!(fallbacks.load(Ordering::Relaxed), 0);
        assert_eq!(outcome, BatchExecution::Gpu);
        assert_eq!(*last.lock().unwrap(), None);

        // Device fails: one count per call, CPU result returned.
        for calls in 1..=3u64 {
            let mut states = input;
            let outcome = gpu_or_explicit_cpu_fallback(
                &fallbacks,
                &last,
                slot,
                &mut states[..],
                |_| Err(VulkanError::WorkspacePoisoned),
                |s| CpuReferenceBackend.batch_keccak_f1600(s),
            );
            assert_eq!(states, expected);
            assert_eq!(fallbacks.load(Ordering::Relaxed), calls);
            assert_eq!(
                outcome,
                BatchExecution::CpuFallback {
                    error: VulkanError::WorkspacePoisoned
                }
            );
            assert_eq!(
                *last.lock().unwrap(),
                Some(CpuFallbackEvent {
                    count: calls,
                    slot,
                    error: VulkanError::WorkspacePoisoned,
                })
            );
        }
    }

    /// Needs a hardware GPU; returns early without one.
    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
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

        // Strict paths fail closed without changing inputs or counting a CPU fallback.
        assert_eq!(AcceleratorBackend::cpu_fallback_count(&gpu), 0);
        let mut states = [[9u64; 25]; 2];
        let mut expected = states;
        CpuReferenceBackend.batch_keccak_f1600(&mut expected);
        let original = states;
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                gpu.batch_keccak_f1600(&mut states);
            }))
            .is_err()
        );
        assert_eq!(states, original);
        assert!(gpu.try_batch_keccak_f1600_pinned(&mut states).is_err());
        assert_eq!(gpu.cpu_fallback_count(), 0);
        let outcome = gpu.batch_keccak_f1600_with_cpu_fallback(&mut states);
        assert!(matches!(outcome, BatchExecution::CpuFallback { .. }));
        assert_eq!(states, expected);
        assert_eq!(gpu.cpu_fallback_count(), 1);
        assert_eq!(gpu.gpu_submission_count(), 0);

        let mut poseidon = [[u64::MAX; 12]; 3];
        let original = poseidon;
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                gpu.batch_poseidon2_perm12(&mut poseidon);
            }))
            .is_err()
        );
        assert!(
            gpu.try_batch_poseidon2_perm12_pinned(&mut poseidon)
                .is_err()
        );
        assert_eq!(poseidon, original);
        assert_eq!(gpu.cpu_fallback_count(), 1);
        let mut expected = original;
        CpuReferenceBackend.batch_poseidon2_perm12(&mut expected);
        let error = VulkanError::Accel(AccelError::SecretSlotUnaudited {
            slot: KernelSlot::BatchPoseidon2Perm12,
        });
        assert_eq!(
            gpu.batch_poseidon2_perm12_with_cpu_fallback(&mut poseidon),
            BatchExecution::CpuFallback { error }
        );
        assert_eq!(poseidon, expected);
        assert_eq!(
            gpu.last_cpu_fallback(),
            Some(CpuFallbackEvent {
                count: 2,
                slot: KernelSlot::BatchPoseidon2Perm12,
                error,
            })
        );
        assert_eq!(gpu.gpu_submission_count(), 0);
    }

    #[test]
    fn macos_moltenvk_search_paths_and_wave32_portability_gate() {
        let paths = VulkanSpirvBackend::macos_library_search_paths();
        assert_eq!(
            paths,
            [
                "/opt/homebrew/lib/libvulkan.1.dylib",
                "/opt/homebrew/lib/libMoltenVK.dylib"
            ]
        );
        assert!(paths.iter().all(|p| p.starts_with('/')));

        let mut portability_info = audited_device_info();
        portability_info.wave32_required = false;
        for stats in &mut portability_info.pipelines {
            stats.scratch_bytes = None;
            stats.spilled_vgprs = None;
            stats.spilled_sgprs = None;
        }
        assert!(portability_info.wave32_subgroup_confirmed());
        assert!(portability_info.secret_slot_audit().is_err());

        let mut wave64_info = portability_info;
        wave64_info.pipelines[0].subgroup_size = Some(64);
        assert!(!wave64_info.wave32_subgroup_confirmed());
    }

    #[cfg(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    #[test]
    fn portability_public_enablement_cannot_unlock_secrets() {
        let mut gpu = match VulkanSpirvBackend::try_new_portability() {
            Ok(gpu) => gpu,
            Err(VulkanError::LibraryLoadFailed | VulkanError::NoDiscreteGpuFound) => {
                assert!(std::env::var_os("QSAG_REQUIRE_GPU_AUDIT").is_none());
                return;
            }
            Err(e) => panic!("portability init: {e}"),
        };
        // Exercise the MoltenVK policy on the live device without fabricating telemetry.
        gpu.secret_slots_audited = false;
        gpu.portability_public_enabled = true;
        let key = BackendAttestationKey::derive(&[7; 32], b"portability-gate-test");
        assert!(matches!(
            gpu.bdoz_gf2_128_batch_dot(&[(1, 2)], &[(3, 4)]),
            Err(AccelError::SecretSlotUnaudited { .. })
        ));
        assert!(matches!(
            bdoz_gf2_128_batch_dot_with_receipt(&gpu, &key, &[(1, 2)], &[(3, 4)], [0u8; 32]),
            Err(AccelError::SecretSlotUnaudited { .. })
        ));
        assert_eq!(gpu.gpu_submission_count(), 0);
        let mut states = [[1; 12]; 1];
        let mut expected = states;
        CpuReferenceBackend.batch_poseidon2_perm12(&mut expected);
        gpu.try_batch_poseidon2_perm12_pinned(&mut states).unwrap();
        assert_eq!(states, expected);
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

    #[cfg(not(all(
        feature = "std",
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    )))]
    #[test]
    fn non_linux_macos_std_try_new_returns_unsupported_platform() {
        assert!(matches!(
            VulkanSpirvBackend::try_new(),
            Err(VulkanError::UnsupportedPlatform)
        ));
        assert!(matches!(
            VulkanSpirvBackend::try_new_portability(),
            Err(VulkanError::UnsupportedPlatform)
        ));
    }
}
