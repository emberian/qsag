//! Minimal zero-dependency Linux/macOS 64-bit Vulkan 1.2+ dynamic loader (`dlopen`)
//! and RAII compute engine targeting discrete RDNA2/SPIR-V and Wave32 portability GPUs with `shaderInt64`.
//!
//! All `unsafe` FFI calls in `qsag-accel` are strictly isolated inside this single module.
//!
//! # Job data residue and the host wipe
//!
//! Every job writes its inputs to the host-mapped staging buffer, and its command buffer copies
//! them to VRAM, computes, copies the result back to staging and zero-fills the VRAM it used.
//! Inputs and outputs may be secret. Each `exec_*` entry point runs under `RawVulkanEngine::run_job`,
//! which settles the staging buffer on every exit (success, `?` return, or unwind):
//!
//! * The host wipes staging only while the engine is `Ready`, meaning every submission it ever
//!   made has been proven complete by its fence or by a `vkDeviceWaitIdle` that returned
//!   `VK_SUCCESS`. The device reads and writes staging by DMA while a submission is live, so a
//!   wipe issued earlier could run before the job's copy-back and leave the output behind.
//! * A job that fails before `vkQueueSubmit` never reached the device and is wiped at once.
//! * A job whose submit or fence wait fails without device loss leaves the engine
//!   `InFlightQuarantined`. One `vkDeviceWaitIdle` is attempted on the way out; if it succeeds the
//!   residue is wiped, otherwise the byte count is kept and the wipe happens at the next
//!   successful idle (the next job's `ensure_ready`, or teardown). No job runs in between.
//!
//! Limit: after `VK_ERROR_DEVICE_LOST` nothing in Vulkan proves that the device has stopped
//! touching the buffers, and the VRAM zero-fill is part of the lost command buffer. The engine
//! then refuses every later job and does not wipe while it is live. Teardown wipes and frees only
//! if `vkDeviceWaitIdle` returns `VK_SUCCESS`; otherwise it detaches every handle, and the
//! staging mapping and the VRAM allocations keep the failed job's data until the process exits
//! and the driver reclaims them. A host that sends secrets to this backend must treat a
//! device-lost error as a reason to end the process.
//!
//! A buffer that a job displaces is cleared before it is freed: a host mapping by a volatile
//! zero fill of its whole capacity (`destroy_gpu_buffer`), a device-local prover buffer by a
//! `vkCmdFillBuffer` submission over the extent the session used (`ensure_one_prover_buf`).
//! No buffer is allocated, replaced or freed, no descriptor set is written and no command pool
//! is reset unless the engine is `Ready`; `run_job` and `run_prover_job` establish that first.
//!
//! # Prover session bounds
//!
//! The prover entry points take offsets and lengths from safe callers and hand them to
//! `vkCmdCopyBuffer` and to shaders that index storage buffers without bounds checks, so every
//! range is validated on the host before a command is recorded:
//!
//! * `job_prover_whir_commit_round0` establishes the arena (`ProverArena::session`). Every
//!   other prover job fails without it, and a scrub of the session removes it.
//! * `GpuBuffer::used` is the extent the session has reserved or written. A range the device
//!   reads must lie inside `used` (`GpuBuffer::check_read`); a range it writes must lie inside
//!   `capacity` and extends `used` (`GpuBuffer::reserve_write`). New prover buffers start
//!   zero-filled, so a read inside `used` returns session data or zeros.
//! * Lengths are combined with checked `u64` arithmetic and narrowed with `to_u32`.
//! * Tables the AIR shaders index through (sorted rows, opcode headers and entries) and the
//!   query and sibling lists of the gather kernel are validated value by value
//!   (`AirTables::validate_op_tables`, `exec_prover_whir_gather_queries`).
//!
//! A prover job that fails, including one rejected here, scrubs and ends its session.
//!
//! Shader index bounds: the device's `maxStorageBufferRange` is a `u32` byte count.
//! Every checked buffer extent is at most that limit, so its `u64` word offsets are
//! below 2^29 and its Ext4 offsets below 2^27. Thus the shaders' `idx * 4`, polynomial
//! strides, and heap offsets fit `uint`; byte offsets stay in checked host `u64`.
//! At nv=26 the fold arenas reserve 3 * 2^25 + 4 Ext4s (3 GiB + 128 bytes), including
//! both trailing-zero pairs. Dispatch padding is at most 255 lanes, still far below
//! 2^32 for these arenas. Same-buffer parallel reads and writes must also be disjoint.

use core::ffi::{c_char, c_void};
use core::mem::{MaybeUninit, size_of};
use core::ptr::{null, null_mut};

use crate::goldilocks::{
    gl_inv_or_zero, gl_mul, gl_neg, gl_pow_pub, gl_reduce_u64, goldilocks_primitive_root,
};
use crate::spirv_kernels::{prover_spirv_kernel_words, spirv_kernel_words};
use crate::vulkan::{VulkanDeviceInfo, VulkanError};
use crate::{KernelSlot, ProverKernelSlot};

const RTLD_NOW: i32 = 2;
const RTLD_LOCAL: i32 = 0;

#[cfg_attr(target_os = "linux", link(name = "dl"))]
unsafe extern "C" {
    fn dlopen(filename: *const c_char, flags: i32) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlclose(handle: *mut c_void) -> i32;
}

const VK_SUCCESS: i32 = 0;
const VK_TRUE: u32 = 1;
const VK_WHOLE_SIZE: u64 = u64::MAX;

const fn vk_make_api_version(variant: u32, major: u32, minor: u32, patch: u32) -> u32 {
    (variant << 29) | (major << 22) | (minor << 12) | patch
}

const VK_API_VERSION_1_2: u32 = vk_make_api_version(0, 1, 2, 0);
const VK_API_VERSION_1_3: u32 = vk_make_api_version(0, 1, 3, 0);

const VK_STRUCTURE_TYPE_APPLICATION_INFO: u32 = 0;
const VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO: u32 = 1;
const VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO: u32 = 2;
const VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO: u32 = 3;
const VK_STRUCTURE_TYPE_SUBMIT_INFO: u32 = 4;
const VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO: u32 = 5;
const VK_STRUCTURE_TYPE_FENCE_CREATE_INFO: u32 = 8;
const VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO: u32 = 12;
const VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO: u32 = 16;
const VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO: u32 = 18;
const VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO: u32 = 29;
const VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO: u32 = 30;
const VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO: u32 = 32;
const VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO: u32 = 33;
const VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO: u32 = 34;
const VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET: u32 = 35;
const VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO: u32 = 39;
const VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO: u32 = 40;
const VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO: u32 = 42;
const VK_STRUCTURE_TYPE_MEMORY_BARRIER: u32 = 46;

const VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU: u32 = 1;
const VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU: u32 = 2;
const VK_PHYSICAL_DEVICE_TYPE_VIRTUAL_GPU: u32 = 3;

const VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR: u32 = 0x0000_0001;
const VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_SUBGROUP_PROPERTIES: u32 = 1_000_094_000;

/// Canonical runtime search order for the Vulkan loader / MoltenVK ICD on macOS Apple Silicon.
#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
pub(crate) const MACOS_VULKAN_LIB_CANDIDATES: [&core::ffi::CStr; 2] = [
    c"/opt/homebrew/lib/libvulkan.1.dylib",
    c"/opt/homebrew/lib/libMoltenVK.dylib",
];

const VK_QUEUE_GRAPHICS_BIT: u32 = 1;
const VK_QUEUE_COMPUTE_BIT: u32 = 2;
const VK_QUEUE_TRANSFER_BIT: u32 = 4;

const VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT: u32 = 1;
const VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT: u32 = 2;
const VK_MEMORY_PROPERTY_HOST_COHERENT_BIT: u32 = 4;
const VK_MEMORY_PROPERTY_HOST_CACHED_BIT: u32 = 8;
const VK_MEMORY_PROPERTY_DEVICE_UNCACHED_BIT_AMD: u32 = 128;

const VK_BUFFER_USAGE_TRANSFER_SRC_BIT: u32 = 1;
const VK_BUFFER_USAGE_TRANSFER_DST_BIT: u32 = 2;
const VK_BUFFER_USAGE_STORAGE_BUFFER_BIT: u32 = 32;
const VK_SHARING_MODE_EXCLUSIVE: u32 = 0;

const VK_SHADER_STAGE_COMPUTE_BIT: u32 = 32;
const VK_DESCRIPTOR_TYPE_STORAGE_BUFFER: u32 = 7;
const VK_PIPELINE_BIND_POINT_COMPUTE: u32 = 1;

const VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT: u32 = 2;
const VK_COMMAND_BUFFER_LEVEL_PRIMARY: u32 = 0;
const VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT: u32 = 1;

const VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT: u32 = 2048;
const VK_PIPELINE_STAGE_TRANSFER_BIT: u32 = 4096;
const VK_PIPELINE_STAGE_HOST_BIT: u32 = 16384;

const VK_ACCESS_SHADER_READ_BIT: u32 = 32;
const VK_ACCESS_SHADER_WRITE_BIT: u32 = 64;
const VK_ACCESS_TRANSFER_READ_BIT: u32 = 2048;
const VK_ACCESS_TRANSFER_WRITE_BIT: u32 = 4096;
const VK_ACCESS_HOST_READ_BIT: u32 = 8192;

const FEATURE_SHADER_INT64_INDEX: usize = 40;
const MIN_BUFFER_ALLOC_BYTES: u64 = 4096;

type VkInstance = *mut c_void;
type VkPhysicalDevice = *mut c_void;
type VkDevice = *mut c_void;
type VkQueue = *mut c_void;
type VkCommandBuffer = *mut c_void;

type VkBuffer = u64;
type VkDeviceMemory = u64;
type VkShaderModule = u64;
type VkDescriptorSetLayout = u64;
type VkPipelineLayout = u64;
type VkPipeline = u64;
type VkDescriptorPool = u64;
type VkDescriptorSet = u64;
type VkCommandPool = u64;
type VkFence = u64;

#[repr(C)]
struct VkApplicationInfo {
    s_type: u32,
    p_next: *const c_void,
    p_application_name: *const c_char,
    application_version: u32,
    p_engine_name: *const c_char,
    engine_version: u32,
    api_version: u32,
}
const _: () = assert!(size_of::<VkApplicationInfo>() == 48);

#[repr(C)]
struct VkInstanceCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    p_application_info: *const VkApplicationInfo,
    enabled_layer_count: u32,
    pp_enabled_layer_names: *const *const c_char,
    enabled_extension_count: u32,
    pp_enabled_extension_names: *const *const c_char,
}
const _: () = assert!(size_of::<VkInstanceCreateInfo>() == 64);

#[repr(C, align(8))]
struct VkPhysicalDevicePropertiesRaw {
    api_version: u32,
    driver_version: u32,
    vendor_id: u32,
    device_id: u32,
    device_type: u32,
    device_name: [u8; 256],
    pipeline_cache_uuid: [u8; 16],
    _pad_limits: u32,
    limits_and_sparse: [u8; 528],
}
const _: () = assert!(size_of::<VkPhysicalDevicePropertiesRaw>() == 824);

impl VkPhysicalDevicePropertiesRaw {
    fn read_limits_u32(&self, rel_offset: usize) -> u32 {
        let mut b = [0u8; 4];
        b.copy_from_slice(&self.limits_and_sparse[rel_offset..rel_offset + 4]);
        u32::from_ne_bytes(b)
    }

    fn max_storage_buffer_range(&self) -> u32 {
        self.read_limits_u32(324 - 296)
    }

    fn max_push_constants_size(&self) -> u32 {
        self.read_limits_u32(328 - 296)
    }

    fn max_compute_work_group_count_x(&self) -> u32 {
        self.read_limits_u32(516 - 296)
    }

    fn max_compute_work_group_invocations(&self) -> u32 {
        self.read_limits_u32(528 - 296)
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
struct VkPhysicalDeviceFeatures {
    flags: [u32; 55],
}
const _: () = assert!(size_of::<VkPhysicalDeviceFeatures>() == 220);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkMemoryType {
    property_flags: u32,
    heap_index: u32,
}
const _: () = assert!(size_of::<VkMemoryType>() == 8);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkMemoryHeap {
    size: u64,
    flags: u32,
    _pad: u32,
}
const _: () = assert!(size_of::<VkMemoryHeap>() == 16);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkPhysicalDeviceMemoryProperties {
    memory_type_count: u32,
    memory_types: [VkMemoryType; 32],
    memory_heap_count: u32,
    memory_heaps: [VkMemoryHeap; 16],
}
const _: () = assert!(size_of::<VkPhysicalDeviceMemoryProperties>() == 520);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkQueueFamilyProperties {
    queue_flags: u32,
    queue_count: u32,
    timestamp_valid_bits: u32,
    min_image_transfer_granularity: [u32; 3],
}
const _: () = assert!(size_of::<VkQueueFamilyProperties>() == 24);

#[repr(C)]
struct VkDeviceQueueCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    queue_family_index: u32,
    queue_count: u32,
    p_queue_priorities: *const f32,
}
const _: () = assert!(size_of::<VkDeviceQueueCreateInfo>() == 40);

#[repr(C)]
struct VkDeviceCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    queue_create_info_count: u32,
    p_queue_create_infos: *const VkDeviceQueueCreateInfo,
    enabled_layer_count: u32,
    pp_enabled_layer_names: *const *const c_char,
    enabled_extension_count: u32,
    pp_enabled_extension_names: *const *const c_char,
    p_enabled_features: *const VkPhysicalDeviceFeatures,
}
const _: () = assert!(size_of::<VkDeviceCreateInfo>() == 72);

#[repr(C)]
struct VkBufferCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    size: u64,
    usage: u32,
    sharing_mode: u32,
    queue_family_index_count: u32,
    p_queue_family_indices: *const u32,
}
const _: () = assert!(size_of::<VkBufferCreateInfo>() == 56);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkMemoryRequirements {
    size: u64,
    alignment: u64,
    memory_type_bits: u32,
    _pad: u32,
}
const _: () = assert!(size_of::<VkMemoryRequirements>() == 24);

#[repr(C)]
struct VkMemoryAllocateInfo {
    s_type: u32,
    p_next: *const c_void,
    allocation_size: u64,
    memory_type_index: u32,
}
const _: () = assert!(size_of::<VkMemoryAllocateInfo>() == 32);

#[repr(C)]
struct VkShaderModuleCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    code_size: usize,
    p_code: *const u32,
}
const _: () = assert!(size_of::<VkShaderModuleCreateInfo>() == 40);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkDescriptorSetLayoutBinding {
    binding: u32,
    descriptor_type: u32,
    descriptor_count: u32,
    stage_flags: u32,
    p_immutable_samplers: *const c_void,
}
const _: () = assert!(size_of::<VkDescriptorSetLayoutBinding>() == 24);

#[repr(C)]
struct VkDescriptorSetLayoutCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    binding_count: u32,
    p_bindings: *const VkDescriptorSetLayoutBinding,
}
const _: () = assert!(size_of::<VkDescriptorSetLayoutCreateInfo>() == 32);

#[repr(C)]
struct VkPushConstantRange {
    stage_flags: u32,
    offset: u32,
    size: u32,
}
const _: () = assert!(size_of::<VkPushConstantRange>() == 12);

#[repr(C)]
struct VkPipelineLayoutCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    set_layout_count: u32,
    p_set_layouts: *const VkDescriptorSetLayout,
    push_constant_range_count: u32,
    p_push_constant_ranges: *const VkPushConstantRange,
}
const _: () = assert!(size_of::<VkPipelineLayoutCreateInfo>() == 48);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkPipelineShaderStageCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    stage: u32,
    module: VkShaderModule,
    p_name: *const c_char,
    p_specialization_info: *const c_void,
}
const _: () = assert!(size_of::<VkPipelineShaderStageCreateInfo>() == 48);

#[repr(C)]
struct VkComputePipelineCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    stage: VkPipelineShaderStageCreateInfo,
    layout: VkPipelineLayout,
    base_pipeline_handle: VkPipeline,
    base_pipeline_index: i32,
}
const _: () = assert!(size_of::<VkComputePipelineCreateInfo>() == 96);

#[repr(C)]
struct VkDescriptorPoolSize {
    ty: u32,
    descriptor_count: u32,
}
const _: () = assert!(size_of::<VkDescriptorPoolSize>() == 8);

#[repr(C)]
struct VkDescriptorPoolCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    max_sets: u32,
    pool_size_count: u32,
    p_pool_sizes: *const VkDescriptorPoolSize,
}
const _: () = assert!(size_of::<VkDescriptorPoolCreateInfo>() == 40);

#[repr(C)]
struct VkDescriptorSetAllocateInfo {
    s_type: u32,
    p_next: *const c_void,
    descriptor_pool: VkDescriptorPool,
    descriptor_set_count: u32,
    p_set_layouts: *const VkDescriptorSetLayout,
}
const _: () = assert!(size_of::<VkDescriptorSetAllocateInfo>() == 40);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkDescriptorBufferInfo {
    buffer: VkBuffer,
    offset: u64,
    range: u64,
}
const _: () = assert!(size_of::<VkDescriptorBufferInfo>() == 24);

#[repr(C)]
#[derive(Clone, Copy)]
struct VkWriteDescriptorSet {
    s_type: u32,
    p_next: *const c_void,
    dst_set: VkDescriptorSet,
    dst_binding: u32,
    dst_array_element: u32,
    descriptor_count: u32,
    descriptor_type: u32,
    p_image_info: *const c_void,
    p_buffer_info: *const VkDescriptorBufferInfo,
    p_texel_buffer_view: *const c_void,
}
const _: () = assert!(size_of::<VkWriteDescriptorSet>() == 64);

#[repr(C)]
struct VkCommandPoolCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    queue_family_index: u32,
}
const _: () = assert!(size_of::<VkCommandPoolCreateInfo>() == 24);

#[repr(C)]
struct VkCommandBufferAllocateInfo {
    s_type: u32,
    p_next: *const c_void,
    command_pool: VkCommandPool,
    level: u32,
    command_buffer_count: u32,
}
const _: () = assert!(size_of::<VkCommandBufferAllocateInfo>() == 32);

#[repr(C)]
struct VkCommandBufferBeginInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
    p_inheritance_info: *const c_void,
}
const _: () = assert!(size_of::<VkCommandBufferBeginInfo>() == 32);

#[repr(C)]
struct VkBufferCopy {
    src_offset: u64,
    dst_offset: u64,
    size: u64,
}
const _: () = assert!(size_of::<VkBufferCopy>() == 24);

#[repr(C)]
struct VkMemoryBarrier {
    s_type: u32,
    p_next: *const c_void,
    src_access_mask: u32,
    dst_access_mask: u32,
}
const _: () = assert!(size_of::<VkMemoryBarrier>() == 24);

#[repr(C)]
struct VkFenceCreateInfo {
    s_type: u32,
    p_next: *const c_void,
    flags: u32,
}
const _: () = assert!(size_of::<VkFenceCreateInfo>() == 24);

#[repr(C)]
struct VkSubmitInfo {
    s_type: u32,
    p_next: *const c_void,
    wait_semaphore_count: u32,
    p_wait_semaphores: *const u64,
    p_wait_dst_stage_mask: *const u32,
    command_buffer_count: u32,
    p_command_buffers: *const VkCommandBuffer,
    signal_semaphore_count: u32,
    p_signal_semaphores: *const u64,
}
const _: () = assert!(size_of::<VkSubmitInfo>() == 72);

// Push constant layouts matching `shaders/*.comp` byte-for-byte.
#[repr(C)]
struct BatchStatesPushConsts {
    num_states: u32,
    base_state: u32,
    _pad0: u32,
    _pad1: u32,
}
const _: () = assert!(size_of::<BatchStatesPushConsts>() == 16);

#[repr(C)]
struct NttPushConsts {
    w_step: u64,
    n: u32,
    log2_n: u32,
    stage: u32,
    mode: u32,
    base_wg: u32,
    _pad: u32,
}
const _: () = assert!(size_of::<NttPushConsts>() == 32);

#[repr(C)]
struct CosetLdePushConsts {
    w_step: u64,
    shift_c: u64,
    len: u32,
    aux_n: u32,
    log2_len: u32,
    stage: u32,
    mode: u32,
    base_wg: u32,
}
const _: () = assert!(size_of::<CosetLdePushConsts>() == 40);

#[repr(C)]
struct MerklePushConsts {
    s0: u64,
    s1: u64,
    s2: u64,
    s3: u64,
    start_parent_idx: u64,
    num_parents: u64,
    in_offset_u64: u64,
    out_offset_u64: u64,
    domain_tag: u64,
    tree_idx: u64,
    layer: u32,
    base_parent: u32,
    level: u32,
    mode: u32,
}
const _: () = assert!(size_of::<MerklePushConsts>() == 96);

#[repr(C)]
struct BdozDotPushConsts {
    num_elements: u32,
    num_groups: u32,
    mode: u32,
    _pad: u32,
}
const _: () = assert!(size_of::<BdozDotPushConsts>() == 16);

#[repr(C)]
#[derive(Clone, Copy)]
struct WhirLdePushConsts {
    scalar0: u64,
    scalar1: u64,
    scalar2: u64,
    scalar3: u64,
    mode: u32,
    len: u32,
    aux0: u32,
    aux1: u32,
    aux2: u32,
    aux3: u32,
    aux4: u32,
    aux5: u32,
}
const _: () = assert!(size_of::<WhirLdePushConsts>() == 64);

#[repr(C)]
#[derive(Clone, Copy)]
struct WhirFoldPushConsts {
    c0: [u64; 4],
    c1: [u64; 4],
    c2: [u64; 4],
    mode: u32,
    len: u32,
    aux0: u32,
    aux1: u32,
    aux2: u32,
    aux3: u32,
    aux4: u32,
    aux5: u32,
}
const _: () = assert!(size_of::<WhirFoldPushConsts>() == 128);

#[repr(C)]
#[derive(Clone, Copy)]
struct AirGroupAPushConsts {
    chal: [u64; 4],
    mode: u32,
    cur_m: u32,
    cur_r: u32,
    flags: u32,
    col_src: u32,
    col_dst: u32,
    sh_src: u32,
    steps_off: u32,
    out_off: u32,
    base_x: u32,
    aux0: u32,
    aux1: u32,
    _pad_align: [u32; 4],
}
const _: () = assert!(size_of::<AirGroupAPushConsts>() == 96);

#[repr(C)]
#[derive(Clone, Copy)]
struct AirGroupBPushConsts {
    is_base: u32,
    cur_m: u32,
    cur_r: u32,
    cur_s: u32,
    flags: u32,
    col_src: u32,
    sh_src: u32,
    signers_off: u32,
    steps_off: u32,
    op_hdr_off: u32,
    op_ent_off: u32,
    sorted_u64_off: u32,
    out_off: u32,
    base_x: u32,
    _pad0: u32,
    _pad1: u32,
}
const _: () = assert!(size_of::<AirGroupBPushConsts>() == 64);

#[cfg(not(target_os = "macos"))]
type PfnVkIcdNegotiateVersion = unsafe extern "C" fn(*mut u32) -> i32;

type PfnVoid = Option<unsafe extern "C" fn()>;
type PfnVkGetInstanceProcAddr = unsafe extern "C" fn(VkInstance, *const c_char) -> PfnVoid;
type PfnVkEnumerateInstanceVersion = unsafe extern "C" fn(*mut u32) -> i32;
type PfnVkCreateInstance =
    unsafe extern "C" fn(*const VkInstanceCreateInfo, *const c_void, *mut VkInstance) -> i32;
type PfnVkDestroyInstance = unsafe extern "C" fn(VkInstance, *const c_void);
type PfnVkEnumeratePhysicalDevices =
    unsafe extern "C" fn(VkInstance, *mut u32, *mut VkPhysicalDevice) -> i32;
type PfnVkGetPhysicalDeviceProperties =
    unsafe extern "C" fn(VkPhysicalDevice, *mut VkPhysicalDevicePropertiesRaw);
type PfnVkGetPhysicalDeviceFeatures =
    unsafe extern "C" fn(VkPhysicalDevice, *mut VkPhysicalDeviceFeatures);
type PfnVkGetPhysicalDeviceMemoryProperties =
    unsafe extern "C" fn(VkPhysicalDevice, *mut VkPhysicalDeviceMemoryProperties);
type PfnVkGetPhysicalDeviceQueueFamilyProperties =
    unsafe extern "C" fn(VkPhysicalDevice, *mut u32, *mut VkQueueFamilyProperties);
type PfnVkCreateDevice = unsafe extern "C" fn(
    VkPhysicalDevice,
    *const VkDeviceCreateInfo,
    *const c_void,
    *mut VkDevice,
) -> i32;
type PfnVkGetDeviceProcAddr = unsafe extern "C" fn(VkDevice, *const c_char) -> PfnVoid;

// Extension ABI mirrors vulkan_core.h. All output buffers are initialized, bounded,
// and remain alive through their synchronous Vulkan calls.
#[repr(C)]
#[derive(Clone, Copy)]
struct ExtensionProperties {
    name: [u8; 256],
    version: u32,
}
#[repr(C)]
struct FeatureChain {
    s_type: u32,
    p_next: *mut c_void,
    enabled: u32,
    extra: u32,
}
#[repr(C)]
struct Features2 {
    s_type: u32,
    p_next: *mut c_void,
    features: VkPhysicalDeviceFeatures,
}
#[repr(C)]
struct Properties2 {
    s_type: u32,
    p_next: *mut c_void,
    properties: VkPhysicalDevicePropertiesRaw,
}
#[repr(C)]
struct SubgroupProperties {
    s_type: u32,
    p_next: *mut c_void,
    min: u32,
    max: u32,
    max_compute_subgroups: u32,
    required_stages: u32,
}
#[repr(C)]
struct CoreSubgroupProperties {
    s_type: u32,
    p_next: *mut c_void,
    subgroup_size: u32,
    supported_stages: u32,
    supported_operations: u32,
    quad_operations_in_all_stages: u32,
}
const _: () = assert!(size_of::<CoreSubgroupProperties>() == 32);
#[repr(C)]
struct RequiredSubgroup {
    s_type: u32,
    p_next: *const c_void,
    size: u32,
}
#[repr(C)]
struct PipelineInfo {
    s_type: u32,
    p_next: *const c_void,
    pipeline: VkPipeline,
}
#[repr(C)]
struct ExecutableInfo {
    s_type: u32,
    p_next: *const c_void,
    pipeline: VkPipeline,
    index: u32,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct ExecutableProperties {
    s_type: u32,
    p_next: *mut c_void,
    stages: u32,
    name: [u8; 256],
    description: [u8; 256],
    subgroup_size: u32,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct ExecutableStatistic {
    s_type: u32,
    p_next: *mut c_void,
    name: [u8; 256],
    description: [u8; 256],
    format: u32,
    value: u64,
}
const _: () = assert!(size_of::<ExecutableProperties>() == 536);
const _: () = assert!(size_of::<ExecutableStatistic>() == 544);
type GetExecutables =
    unsafe extern "C" fn(VkDevice, *const PipelineInfo, *mut u32, *mut ExecutableProperties) -> i32;
type GetStatistics = unsafe extern "C" fn(
    VkDevice,
    *const ExecutableInfo,
    *mut u32,
    *mut ExecutableStatistic,
) -> i32;

struct DeviceFns {
    destroy_device: unsafe extern "C" fn(VkDevice, *const c_void),
    get_device_queue: unsafe extern "C" fn(VkDevice, u32, u32, *mut VkQueue),
    create_buffer: unsafe extern "C" fn(
        VkDevice,
        *const VkBufferCreateInfo,
        *const c_void,
        *mut VkBuffer,
    ) -> i32,
    destroy_buffer: unsafe extern "C" fn(VkDevice, VkBuffer, *const c_void),
    get_buffer_memory_requirements:
        unsafe extern "C" fn(VkDevice, VkBuffer, *mut VkMemoryRequirements),
    allocate_memory: unsafe extern "C" fn(
        VkDevice,
        *const VkMemoryAllocateInfo,
        *const c_void,
        *mut VkDeviceMemory,
    ) -> i32,
    free_memory: unsafe extern "C" fn(VkDevice, VkDeviceMemory, *const c_void),
    map_memory:
        unsafe extern "C" fn(VkDevice, VkDeviceMemory, u64, u64, u32, *mut *mut c_void) -> i32,
    unmap_memory: unsafe extern "C" fn(VkDevice, VkDeviceMemory),
    bind_buffer_memory: unsafe extern "C" fn(VkDevice, VkBuffer, VkDeviceMemory, u64) -> i32,
    create_shader_module: unsafe extern "C" fn(
        VkDevice,
        *const VkShaderModuleCreateInfo,
        *const c_void,
        *mut VkShaderModule,
    ) -> i32,
    destroy_shader_module: unsafe extern "C" fn(VkDevice, VkShaderModule, *const c_void),
    create_descriptor_set_layout: unsafe extern "C" fn(
        VkDevice,
        *const VkDescriptorSetLayoutCreateInfo,
        *const c_void,
        *mut VkDescriptorSetLayout,
    ) -> i32,
    destroy_descriptor_set_layout:
        unsafe extern "C" fn(VkDevice, VkDescriptorSetLayout, *const c_void),
    create_pipeline_layout: unsafe extern "C" fn(
        VkDevice,
        *const VkPipelineLayoutCreateInfo,
        *const c_void,
        *mut VkPipelineLayout,
    ) -> i32,
    destroy_pipeline_layout: unsafe extern "C" fn(VkDevice, VkPipelineLayout, *const c_void),
    create_compute_pipelines: unsafe extern "C" fn(
        VkDevice,
        u64,
        u32,
        *const VkComputePipelineCreateInfo,
        *const c_void,
        *mut VkPipeline,
    ) -> i32,
    destroy_pipeline: unsafe extern "C" fn(VkDevice, VkPipeline, *const c_void),
    create_descriptor_pool: unsafe extern "C" fn(
        VkDevice,
        *const VkDescriptorPoolCreateInfo,
        *const c_void,
        *mut VkDescriptorPool,
    ) -> i32,
    destroy_descriptor_pool: unsafe extern "C" fn(VkDevice, VkDescriptorPool, *const c_void),
    allocate_descriptor_sets: unsafe extern "C" fn(
        VkDevice,
        *const VkDescriptorSetAllocateInfo,
        *mut VkDescriptorSet,
    ) -> i32,
    update_descriptor_sets:
        unsafe extern "C" fn(VkDevice, u32, *const VkWriteDescriptorSet, u32, *const c_void),
    create_command_pool: unsafe extern "C" fn(
        VkDevice,
        *const VkCommandPoolCreateInfo,
        *const c_void,
        *mut VkCommandPool,
    ) -> i32,
    destroy_command_pool: unsafe extern "C" fn(VkDevice, VkCommandPool, *const c_void),
    reset_command_pool: unsafe extern "C" fn(VkDevice, VkCommandPool, u32) -> i32,
    allocate_command_buffers: unsafe extern "C" fn(
        VkDevice,
        *const VkCommandBufferAllocateInfo,
        *mut VkCommandBuffer,
    ) -> i32,
    begin_command_buffer:
        unsafe extern "C" fn(VkCommandBuffer, *const VkCommandBufferBeginInfo) -> i32,
    end_command_buffer: unsafe extern "C" fn(VkCommandBuffer) -> i32,
    cmd_copy_buffer:
        unsafe extern "C" fn(VkCommandBuffer, VkBuffer, VkBuffer, u32, *const VkBufferCopy),
    cmd_fill_buffer: unsafe extern "C" fn(VkCommandBuffer, VkBuffer, u64, u64, u32),
    cmd_bind_pipeline: unsafe extern "C" fn(VkCommandBuffer, u32, VkPipeline),
    cmd_bind_descriptor_sets: unsafe extern "C" fn(
        VkCommandBuffer,
        u32,
        VkPipelineLayout,
        u32,
        u32,
        *const VkDescriptorSet,
        u32,
        *const u32,
    ),
    cmd_push_constants:
        unsafe extern "C" fn(VkCommandBuffer, VkPipelineLayout, u32, u32, u32, *const c_void),
    cmd_dispatch: unsafe extern "C" fn(VkCommandBuffer, u32, u32, u32),
    cmd_pipeline_barrier: unsafe extern "C" fn(
        VkCommandBuffer,
        u32,
        u32,
        u32,
        u32,
        *const VkMemoryBarrier,
        u32,
        *const c_void,
        u32,
        *const c_void,
    ),
    create_fence: unsafe extern "C" fn(
        VkDevice,
        *const VkFenceCreateInfo,
        *const c_void,
        *mut VkFence,
    ) -> i32,
    destroy_fence: unsafe extern "C" fn(VkDevice, VkFence, *const c_void),
    reset_fences: unsafe extern "C" fn(VkDevice, u32, *const VkFence) -> i32,
    wait_for_fences: unsafe extern "C" fn(VkDevice, u32, *const VkFence, u32, u64) -> i32,
    queue_submit: unsafe extern "C" fn(VkQueue, u32, *const VkSubmitInfo, VkFence) -> i32,
    device_wait_idle: unsafe extern "C" fn(VkDevice) -> i32,
}

#[derive(Clone, Copy)]
struct KernelPipeline {
    shader_module: VkShaderModule,
    pipeline_layout: VkPipelineLayout,
    pipeline: VkPipeline,
}

struct GpuBuffer {
    buffer: VkBuffer,
    memory: VkDeviceMemory,
    capacity: u64,
    used: u64,
    mapped: *mut u8,
}

impl Default for GpuBuffer {
    fn default() -> Self {
        Self {
            buffer: 0,
            memory: 0,
            capacity: 0,
            used: 0,
            mapped: null_mut(),
        }
    }
}

/// Bytes of one `Ext4` element and of one base-field word in a storage buffer.
const EXT4_BYTES: u64 = 32;
const WORD_BYTES: u64 = 8;

fn length_overflow() -> VulkanError {
    VulkanError::Accel(crate::AccelError::LengthOverflow)
}

fn out_of_range(what: &'static str, available: u64, requested: u64) -> VulkanError {
    let clamp = |v: u64| usize::try_from(v).unwrap_or(usize::MAX);
    VulkanError::Accel(crate::AccelError::LengthMismatch {
        what,
        expected: clamp(available),
        actual: clamp(requested),
    })
}

fn cmul(a: u64, b: u64) -> Result<u64, VulkanError> {
    a.checked_mul(b).ok_or_else(length_overflow)
}

fn cadd(a: u64, b: u64) -> Result<u64, VulkanError> {
    a.checked_add(b).ok_or_else(length_overflow)
}

/// `base + count * stride` elements, in bytes of `elem_bytes` each: the exclusive end of the
/// range a shader or copy reaches when it indexes `base + i * stride` for `i < count`.
fn span_end(base: u64, count: u64, stride: u64, elem_bytes: u64) -> Result<u64, VulkanError> {
    cmul(cadd(base, cmul(count, stride)?)?, elem_bytes)
}

/// Parallel folds and transposes cannot overwrite another invocation's unread input.
/// All coordinates use the same element unit; touching endpoints are allowed.
fn check_disjoint(src: u64, src_len: u64, dst: u64, dst_len: u64) -> Result<(), VulkanError> {
    let src_end = cadd(src, src_len)?;
    let dst_end = cadd(dst, dst_len)?;
    if src_len != 0 && dst_len != 0 && src < dst_end && dst < src_end {
        return Err(length_overflow());
    }
    Ok(())
}

fn to_u32<T: TryInto<u32>>(value: T) -> Result<u32, VulkanError> {
    value.try_into().map_err(|_| length_overflow())
}

fn to_u64(value: usize) -> u64 {
    value as u64
}

/// `1 << num_vars` for `num_vars <= max_vars`.
fn pow2_len(num_vars: usize, max_vars: usize) -> Result<usize, VulkanError> {
    if num_vars > max_vars || num_vars >= usize::BITS as usize {
        return Err(length_overflow());
    }
    Ok(1usize << num_vars)
}

impl GpuBuffer {
    /// A range the device will read (copy source or shader input) must lie inside what the
    /// current session reserved in this buffer.
    fn check_read(&self, what: &'static str, end_bytes: u64) -> Result<(), VulkanError> {
        if self.buffer == 0 || end_bytes > self.used || end_bytes > self.capacity {
            return Err(out_of_range(what, self.used.min(self.capacity), end_bytes));
        }
        Ok(())
    }

    /// A range the device will write (copy destination or shader output) must lie inside the
    /// allocation; it becomes part of what the session holds and what its scrub clears.
    fn reserve_write(&mut self, what: &'static str, end_bytes: u64) -> Result<(), VulkanError> {
        if self.buffer == 0 || end_bytes > self.capacity {
            return Err(out_of_range(what, self.capacity, end_bytes));
        }
        let aligned = end_bytes.saturating_add(7) & !7;
        self.used = self.used.max(aligned).min(self.capacity);
        Ok(())
    }
}

/// One `vkCmdCopyBuffer` region whose source range was checked against `src` (a read) and whose
/// destination range fits `dst_capacity`. `size > 0` and nonzero handles are valid-usage rules.
fn checked_copy(
    what: &'static str,
    src: &GpuBuffer,
    src_offset: u64,
    dst_capacity: u64,
    dst_offset: u64,
    size: u64,
) -> Result<VkBufferCopy, VulkanError> {
    let src_end = cadd(src_offset, size)?;
    let dst_end = cadd(dst_offset, size)?;
    if size == 0 {
        return Err(out_of_range(what, 1, 0));
    }
    src.check_read(what, src_end)?;
    if dst_end > dst_capacity {
        return Err(out_of_range(what, dst_capacity, dst_end));
    }
    Ok(VkBufferCopy {
        src_offset,
        dst_offset,
        size,
    })
}

/// Driver calls whose result code a test can replace (see `RawVulkanEngine::injected_rc`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FaultPoint {
    /// `begin_cmd` fails before any command is recorded.
    BeginCmd = 0,
    /// `vkQueueSubmit` is not called; the injected code is reported instead.
    QueueSubmit = 1,
    /// The submission is real; the injected code is reported instead of waiting on its fence.
    FenceWait = 2,
    /// `vkDeviceWaitIdle` is not called; the injected code is reported instead.
    DeviceWaitIdle = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EngineExecState {
    Ready,
    /// A queue submission was issued (or returned an indeterminate error / failed fence wait)
    /// and full device completion has not yet been established.
    InFlightQuarantined,
    /// Unrecoverable `VK_ERROR_DEVICE_LOST` (`-4`).
    DeviceLostQuarantined,
}

/// Upper bound on the selector entries of one row's opcode list.
const AIR_MAX_OPS_PER_ROW: u64 = 4096;

/// Host view of `vram_aux_in` during an AIR round: the static tables uploaded by
/// `exec_prover_air_init_shard` followed (without overlap) by this round's dynamic words.
struct AirTables<'a> {
    static_words: &'a [u64],
    dyn_words: &'a [u64],
    dyn_word0: u64,
}

impl AirTables<'_> {
    fn word(&self, idx: u64) -> Result<u64, VulkanError> {
        let static_len = to_u64(self.static_words.len());
        if idx < static_len {
            return Ok(self.static_words[idx as usize]);
        }
        match idx.checked_sub(self.dyn_word0) {
            Some(rel) if rel < to_u64(self.dyn_words.len()) => Ok(self.dyn_words[rel as usize]),
            _ => Err(out_of_range(
                "AIR table index (outside the uploaded tables)",
                static_len.max(self.dyn_word0.saturating_add(to_u64(self.dyn_words.len()))),
                idx,
            )),
        }
    }

    /// Everything `air_row_group_b.comp` reaches through uploaded indices: the sorted row
    /// list, each reachable row's opcode header, and each opcode entry it names.
    fn validate_op_tables(
        &self,
        half_m: u64,
        key_mask: Option<u64>,
        key_count: u64,
        sorted_u64_off: u64,
        op_hdr_off: u64,
        op_ent_off: u64,
    ) -> Result<(), VulkanError> {
        let static_gamma_end_ext4 = to_u64(self.static_words.len()) / 4;
        let mut seen = std::vec![false; usize::try_from(key_count).map_err(|_| length_overflow())?];
        for tid in 0..half_m {
            let idx = self.word(cadd(sorted_u64_off, tid)?)?;
            if idx >= half_m {
                return Err(out_of_range("AIR sorted row index", half_m, idx));
            }
            let key = key_mask.map_or(idx, |mask| idx & mask);
            let slot = seen
                .get_mut(key as usize)
                .ok_or_else(|| out_of_range("AIR opcode header index", key_count, key))?;
            if core::mem::replace(slot, true) {
                continue;
            }
            let hdr = cmul(cadd(op_hdr_off, key)?, 4)?;
            let e_start = self.word(hdr)?;
            let e_count = self.word(cadd(hdr, 1)?)?;
            if e_count > AIR_MAX_OPS_PER_ROW || e_start > u64::from(u32::MAX) {
                return Err(out_of_range(
                    "AIR opcode list length",
                    AIR_MAX_OPS_PER_ROW,
                    e_count.max(e_start),
                ));
            }
            for e in 0..e_count {
                let ent = cmul(cadd(op_ent_off, cmul(cadd(e_start, e)?, 3)?)?, 4)?;
                let kind_id = self.word(ent)?;
                let kind_arg = self.word(cadd(ent, 1)?)?;
                let gamma_base = self.word(cadd(ent, 2)?)?;
                // The entry's two selector values end eleven words after its first.
                self.word(cadd(ent, 11)?)?;
                // An opcode reads exactly `terms` consecutive gammas starting at `gamma_base`.
                // They must lie in the static table `exec_prover_air_init_shard` uploaded,
                // after the Group A gammas. This keeps every read inside the session's
                // buffer and off the per-round tables. The host does not know where the
                // caller's opcode blocks end inside the static table, so a base that names
                // another opcode's block, or the row list behind them, is not detected here:
                // it yields a proof the verifier rejects, never an out-of-buffer read.
                let Some(terms) = crate::vulkan::air_op_term_count(kind_id, kind_arg) else {
                    return Err(out_of_range("AIR opcode kind or argument", 23, kind_id));
                };
                if gamma_base < crate::vulkan::AIR_OP_GAMMA_BASE_EXT4
                    || cadd(gamma_base, terms)? > static_gamma_end_ext4
                {
                    return Err(out_of_range(
                        "AIR opcode gamma block (outside the static gamma table)",
                        static_gamma_end_ext4,
                        gamma_base,
                    ));
                }
            }
        }
        Ok(())
    }
}

/// What `job_prover_whir_commit_round0` established for the current prover session.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProverSessionDims {
    num_polys: usize,
    num_vars: usize,
    turboshake_canopy: bool,
}

/// Host copy of the static tables `exec_prover_air_init_shard` uploaded to the start of
/// `vram_aux_in` (public gamma weights and row indices), so the tables the AIR shaders index
/// through can be validated before dispatch. Dropped by any job that rewrites that buffer.
struct AirShardState {
    total_rows: u64,
    static_words: std::vec::Vec<u64>,
}

/// Identity of a committed Merkle tree resident in VRAM. A gather must name exactly the
/// tree that occupies its slot.
#[derive(Clone, Copy, PartialEq, Eq)]
struct CommittedTree {
    stage_idx: usize,
    group_arity: usize,
    num_groups: usize,
}

#[derive(Default)]
struct ProverArena {
    /// `Some` between a successful round-0 commit and the next scrub of the session. Every
    /// other prover entry point refuses to run without it.
    session: Option<ProverSessionDims>,
    /// The round-0 tree, then the folded-stage tree in each parity slot (`stage_idx & 1`).
    committed_trees: [Option<CommittedTree>; 3],
    /// Session data may remain in VRAM: set when a session is invalidated, cleared only by
    /// a completed scrub. The next prover job scrubs before it touches the arena.
    scrub_pending: bool,
    /// A buffer was replaced and the descriptor sets still name the old one.
    descriptors_dirty: bool,
    /// `Some` between `exec_prover_air_init_shard` and the next job that rewrites `vram_aux_in`.
    air: Option<AirShardState>,
    /// Buffers whose scrub submission failed: they may still be referenced by the device, so
    /// they are neither reused nor freed until teardown has established idle.
    limbo: std::vec::Vec<GpuBuffer>,
    initialized: bool,
    twiddles_ready: bool,
    last_fold_k_dst: Option<u32>,
    salt_seed_words: [u64; 4],
    desc_pool: VkDescriptorPool,
    ds_lde_r0: VkDescriptorSet,
    ds_gather_r0: VkDescriptorSet,
    ds_lde_stage: [VkDescriptorSet; 2],
    ds_gather_stage: [VkDescriptorSet; 2],
    ds_fold_kronecker: VkDescriptorSet,
    ds_fold_mono: VkDescriptorSet,
    ds_fold_witness: VkDescriptorSet,
    ds_air: VkDescriptorSet,
    twiddles_24: GpuBuffer,
    vram_witness: GpuBuffer,
    vram_mono: GpuBuffer,
    vram_cw0: GpuBuffer,
    vram_tree0: GpuBuffer,
    vram_work_a: GpuBuffer,
    vram_work_b: GpuBuffer,
    vram_cw_stage: [GpuBuffer; 2],
    vram_tree_stage: [GpuBuffer; 2],
    vram_aux_in: GpuBuffer,
    vram_aux_b: GpuBuffer,
    vram_partials: GpuBuffer,
}

impl ProverArena {
    /// Every buffer that holds session data. `twiddles_24` is public and outlives sessions.
    fn session_buffers(&mut self) -> [&mut GpuBuffer; 13] {
        let [cw_stage_0, cw_stage_1] = &mut self.vram_cw_stage;
        let [tree_stage_0, tree_stage_1] = &mut self.vram_tree_stage;
        [
            &mut self.vram_witness,
            &mut self.vram_mono,
            &mut self.vram_cw0,
            &mut self.vram_tree0,
            &mut self.vram_work_a,
            &mut self.vram_work_b,
            cw_stage_0,
            cw_stage_1,
            tree_stage_0,
            tree_stage_1,
            &mut self.vram_aux_in,
            &mut self.vram_aux_b,
            &mut self.vram_partials,
        ]
    }

    /// End the session: nothing may read its buffers again, and they are owed a scrub.
    fn invalidate_session(&mut self) {
        self.session = None;
        self.committed_trees = [None; 3];
        self.air = None;
        self.last_fold_k_dst = None;
        self.scrub_pending = true;
        crate::ct::ct_zeroize_u64s(&mut self.salt_seed_words);
    }
}

pub(crate) struct RawVulkanEngine {
    lib_handle: *mut c_void,
    radv_lib_handle: *mut c_void,
    destroy_instance: PfnVkDestroyInstance,
    instance: VkInstance,
    device: VkDevice,
    fns: DeviceFns,
    queue: VkQueue,
    mem_props: VkPhysicalDeviceMemoryProperties,
    wave32: bool,
    core_subgroup_size: Option<u32>,
    require_exec_telemetry: bool,
    executable_fns: Option<(GetExecutables, GetStatistics)>,
    telemetry: [crate::vulkan::PipelineTelemetry; KernelSlot::COUNT],
    prover_telemetry: [crate::vulkan::PipelineTelemetry; ProverKernelSlot::COUNT],
    max_wg_x: u32,
    max_storage_range: u64,
    exec_state: EngineExecState,
    /// Leading bytes of the staging mapping that may hold job data and have not been wiped.
    /// Nonzero while a job runs, and afterwards only while idle could not be established.
    staging_residue_bytes: u64,
    #[cfg(test)]
    fail_alloc_countdown: core::cell::Cell<Option<u32>>,
    #[cfg(test)]
    injected_rcs: core::cell::Cell<[Option<i32>; 4]>,
    /// Test observation: `(alloc_gpu_buffer calls, prover descriptor refreshes)`.
    #[cfg(test)]
    mutation_counters: core::cell::Cell<(u64, u64)>,
    /// Test observation of the last host mapping released: `(bytes, all bytes were zero)`.
    #[cfg(test)]
    last_unmapped: core::cell::Cell<Option<(u64, bool)>>,
    dsl_1buf: VkDescriptorSetLayout,
    dsl_2buf: VkDescriptorSetLayout,
    dsl_3buf: VkDescriptorSetLayout,
    dsl_6buf: VkDescriptorSetLayout,
    pipelines: [KernelPipeline; KernelSlot::COUNT],
    prover_pipelines: [KernelPipeline; ProverKernelSlot::COUNT],
    desc_pool: VkDescriptorPool,
    ds_1buf_a: VkDescriptorSet,
    ds_2buf_ab: VkDescriptorSet,
    ds_2buf_ba: VkDescriptorSet,
    ds_2buf_aa: VkDescriptorSet,
    ds_3buf_abc: VkDescriptorSet,
    cmd_pool: VkCommandPool,
    cmd_buf: VkCommandBuffer,
    upload_cmd_buf: VkCommandBuffer,
    fence: VkFence,
    upload_fence: VkFence,
    staging: GpuBuffer,
    vram_a: GpuBuffer,
    vram_b: GpuBuffer,
    vram_c: GpuBuffer,
    prover: ProverArena,
}

// SAFETY: Every `RawVulkanEngine` instance owns an independent `VkDevice` / `VkCommandPool` /
// `VkQueue` synchronization scope and is exclusively accessed behind a `std::sync::Mutex`.
unsafe impl Send for RawVulkanEngine {}

fn check_vk(op: &'static str, code: i32) -> Result<(), VulkanError> {
    if code == VK_SUCCESS {
        Ok(())
    } else {
        Err(VulkanError::VkResult { op, code })
    }
}

unsafe fn load_inst_fn<F: Copy>(
    gipa: PfnVkGetInstanceProcAddr,
    instance: VkInstance,
    cname: &'static core::ffi::CStr,
    label: &'static str,
) -> Result<F, VulkanError> {
    let sym = unsafe { gipa(instance, cname.as_ptr()) };
    match sym {
        Some(ptr) => {
            assert_eq!(size_of::<F>(), size_of::<unsafe extern "C" fn()>());
            Ok(unsafe { core::mem::transmute_copy(&ptr) })
        }
        None => Err(VulkanError::SymbolMissing(label)),
    }
}

unsafe fn load_dev_fn<F: Copy>(
    gdpa: PfnVkGetDeviceProcAddr,
    device: VkDevice,
    cname: &'static core::ffi::CStr,
    label: &'static str,
) -> Result<F, VulkanError> {
    let sym = unsafe { gdpa(device, cname.as_ptr()) };
    match sym {
        Some(ptr) => {
            assert_eq!(size_of::<F>(), size_of::<unsafe extern "C" fn()>());
            Ok(unsafe { core::mem::transmute_copy(&ptr) })
        }
        None => Err(VulkanError::SymbolMissing(label)),
    }
}

fn find_memory_type(
    mem_props: &VkPhysicalDeviceMemoryProperties,
    type_bits: u32,
    required: u32,
    preferred: u32,
    forbidden: u32,
) -> Option<u32> {
    let count = (mem_props.memory_type_count as usize).min(mem_props.memory_types.len());
    for (idx, mt) in mem_props.memory_types.iter().enumerate().take(count) {
        let bit = 1u32 << idx;
        if (type_bits & bit) != 0
            && (mt.property_flags & required) == required
            && (mt.property_flags & preferred) == preferred
            && (mt.property_flags & forbidden) == 0
        {
            return Some(idx as u32);
        }
    }
    for (idx, mt) in mem_props.memory_types.iter().enumerate().take(count) {
        let bit = 1u32 << idx;
        if (type_bits & bit) != 0
            && (mt.property_flags & required) == required
            && (mt.property_flags & forbidden) == 0
        {
            return Some(idx as u32);
        }
    }
    for (idx, mt) in mem_props.memory_types.iter().enumerate().take(count) {
        let bit = 1u32 << idx;
        if (type_bits & bit) != 0
            && (mt.property_flags & required) == required
            && (mt.property_flags & VK_MEMORY_PROPERTY_DEVICE_UNCACHED_BIT_AMD) == 0
        {
            return Some(idx as u32);
        }
    }
    for (idx, mt) in mem_props.memory_types.iter().enumerate().take(count) {
        let bit = 1u32 << idx;
        if (type_bits & bit) != 0 && (mt.property_flags & required) == required {
            return Some(idx as u32);
        }
    }
    None
}

fn contains_ascii_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    let end = haystack
        .iter()
        .position(|&b| b == 0)
        .unwrap_or(haystack.len());
    haystack[..end].windows(needle.len()).any(|w| w == needle)
}

fn has_extension_named(exts: &[ExtensionProperties], target: &core::ffi::CStr) -> bool {
    exts.iter()
        .any(|e| e.name.starts_with(target.to_bytes_with_nul()))
}

pub(crate) const fn is_accepted_gpu_device_type(
    device_type: u32,
    allow_portability_virtual_gpu: bool,
) -> bool {
    device_type == VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU
        || device_type == VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU
        || (allow_portability_virtual_gpu && device_type == VK_PHYSICAL_DEVICE_TYPE_VIRTUAL_GPU)
}

unsafe fn loader_supports_portability_enumeration(gipa: PfnVkGetInstanceProcAddr) -> bool {
    type PfnEnumInstExts =
        unsafe extern "C" fn(*const c_char, *mut u32, *mut ExtensionProperties) -> i32;
    let Ok(enum_inst_exts) = (unsafe {
        load_inst_fn::<PfnEnumInstExts>(
            gipa,
            null_mut(),
            c"vkEnumerateInstanceExtensionProperties",
            "vkEnumerateInstanceExtensionProperties",
        )
    }) else {
        return false;
    };
    let mut count = 0u32;
    if unsafe { enum_inst_exts(null(), &mut count, null_mut()) } != VK_SUCCESS || count == 0 {
        return false;
    }
    let mut exts =
        std::vec![ExtensionProperties { name: [0; 256], version: 0 }; count.min(512) as usize];
    count = exts.len() as u32;
    let rc = unsafe { enum_inst_exts(null(), &mut count, exts.as_mut_ptr()) };
    if rc != VK_SUCCESS && rc != 5 {
        return false;
    }
    exts.truncate(count as usize);
    has_extension_named(&exts, c"VK_KHR_portability_enumeration")
}

impl RawVulkanEngine {
    pub(crate) fn try_new() -> Result<(Self, VulkanDeviceInfo), VulkanError> {
        Self::try_new_with_policy(true)
    }

    pub(crate) fn try_new_portability() -> Result<(Self, VulkanDeviceInfo), VulkanError> {
        Self::try_new_with_policy(false)
    }

    fn try_new_with_policy(
        require_exec_telemetry: bool,
    ) -> Result<(Self, VulkanDeviceInfo), VulkanError> {
        if cfg!(target_endian = "big") {
            return Err(VulkanError::UnsupportedPlatform);
        }

        #[cfg(target_os = "macos")]
        {
            // Homebrew prefixes are user-writable; loading code from them requires opt-in.
            if std::env::var_os("QSAG_ALLOW_USER_VULKAN_LOADER").is_none() {
                return Err(VulkanError::LibraryLoadFailed);
            }
            // A loader with no usable ICD falls through to the next candidate; the error
            // reported is that of the last library that loaded at all.
            let mut last_err = VulkanError::LibraryLoadFailed;
            for cand in MACOS_VULKAN_LIB_CANDIDATES {
                let lib_handle = unsafe { dlopen(cand.as_ptr(), RTLD_NOW | RTLD_LOCAL) };
                if lib_handle.is_null() {
                    continue;
                }
                match unsafe {
                    Self::try_open_with_loaded_lib(lib_handle, true, require_exec_telemetry)
                } {
                    Ok(ok) => return Ok(ok),
                    Err(e) => last_err = e,
                }
            }
            Err(last_err)
        }

        #[cfg(not(target_os = "macos"))]
        {
            // Determine whether an explicit Vulkan ICD environment override is active.
            // On dual-ICD Linux AMD hosts (`amdvlk64.so` + Mesa `libvulkan_radeon.so`), AMDVLK's
            // `/etc/vulkan/implicit_layer.d/amd_icd64.json` (`VK_LAYER_AMD_switchable_graphics_64`)
            // intercepts `libvulkan.so.1` and hides Mesa RADV Wave32 devices unless negotiated
            // directly via the Khronos ICD v5 ABI (`vk_icdNegotiateLoaderICDInterfaceVersion`).
            let icd_override = std::env::var_os("VK_ICD_FILENAMES")
                .or_else(|| std::env::var_os("VK_DRIVER_FILES"))
                .or_else(|| std::env::var_os("VK_ADD_DRIVER_FILES"));
            let allow_direct_radv = match &icd_override {
                None => true,
                Some(v) => v.to_string_lossy().contains("radeon_icd"),
            };
            let mut radv_err: Option<VulkanError> = None;
            if allow_direct_radv {
                match unsafe { Self::try_new_with_radv_icd(require_exec_telemetry) } {
                    Some(Ok((eng, info))) => return Ok((eng, info)),
                    Some(Err(VulkanError::NoDiscreteGpuFound)) | None => {}
                    Some(Err(e)) => radv_err = Some(e),
                }
            }

            let linux_loader_paths = [
                c"/usr/lib/x86_64-linux-gnu/libvulkan.so.1",
                c"/usr/lib/aarch64-linux-gnu/libvulkan.so.1",
                c"/usr/lib64/libvulkan.so.1",
                c"/usr/lib/libvulkan.so.1",
            ];
            let mut lib_handle: *mut c_void = null_mut();
            for cand in linux_loader_paths {
                let h = unsafe { dlopen(cand.as_ptr(), RTLD_NOW | RTLD_LOCAL) };
                if !h.is_null() {
                    lib_handle = h;
                    break;
                }
            }
            if lib_handle.is_null()
                && std::env::var_os("QSAG_ALLOW_RELATIVE_VULKAN_LOADER").is_some()
            {
                lib_handle = unsafe { dlopen(c"libvulkan.so.1".as_ptr(), RTLD_NOW | RTLD_LOCAL) };
            }
            if lib_handle.is_null() {
                if let Some(e) = radv_err {
                    return Err(e);
                }
                return Err(VulkanError::LibraryLoadFailed);
            }

            let default_res = unsafe {
                Self::try_open_with_loaded_lib(lib_handle, false, require_exec_telemetry)
            };
            if default_res.is_err()
                && let Some(e) = radv_err
            {
                return Err(e);
            }
            default_res
        }
    }

    /// Consumes `lib_handle` (storing it inside `RawVulkanEngine` on `Ok`, or `dlclose`ing on `Err`).
    unsafe fn try_open_with_loaded_lib(
        lib_handle: *mut c_void,
        enable_portability: bool,
        require_exec_telemetry: bool,
    ) -> Result<(Self, VulkanDeviceInfo), VulkanError> {
        let gipa_raw = unsafe { dlsym(lib_handle, c"vkGetInstanceProcAddr".as_ptr()) };
        if gipa_raw.is_null() {
            unsafe {
                let _ = dlclose(lib_handle);
            }
            return Err(VulkanError::SymbolMissing("vkGetInstanceProcAddr"));
        }
        let gipa: PfnVkGetInstanceProcAddr = unsafe { core::mem::transmute(gipa_raw) };

        let create_instance: PfnVkCreateInstance = match unsafe {
            load_inst_fn(gipa, null_mut(), c"vkCreateInstance", "vkCreateInstance")
        } {
            Ok(f) => f,
            Err(e) => {
                unsafe {
                    let _ = dlclose(lib_handle);
                }
                return Err(e);
            }
        };

        let mut loader_api = VK_API_VERSION_1_2;
        if let Ok(enum_ver) = unsafe {
            load_inst_fn::<PfnVkEnumerateInstanceVersion>(
                gipa,
                null_mut(),
                c"vkEnumerateInstanceVersion",
                "vkEnumerateInstanceVersion",
            )
        } {
            let mut v = 0u32;
            if unsafe { enum_ver(&mut v) } == VK_SUCCESS && v >= VK_API_VERSION_1_3 {
                loader_api = VK_API_VERSION_1_3;
            }
        }

        let use_portability_enum =
            enable_portability && unsafe { loader_supports_portability_enumeration(gipa) };
        let port_ext_name: *const c_char = c"VK_KHR_portability_enumeration".as_ptr();
        let app_info = VkApplicationInfo {
            s_type: VK_STRUCTURE_TYPE_APPLICATION_INFO,
            p_next: null(),
            p_application_name: c"qsag-accel".as_ptr(),
            application_version: 1,
            p_engine_name: c"qsag-spirv".as_ptr(),
            engine_version: 1,
            api_version: loader_api,
        };
        let inst_info = VkInstanceCreateInfo {
            s_type: VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO,
            p_next: null(),
            flags: if use_portability_enum {
                VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR
            } else {
                0
            },
            p_application_info: &app_info,
            enabled_layer_count: 0,
            pp_enabled_layer_names: null(),
            enabled_extension_count: u32::from(use_portability_enum),
            pp_enabled_extension_names: if use_portability_enum {
                &port_ext_name
            } else {
                null()
            },
        };
        let mut instance: VkInstance = null_mut();
        let rc = unsafe { create_instance(&inst_info, null(), &mut instance) };
        let default_res = if rc == VK_SUCCESS {
            // Without `vkDestroyInstance` the live instance cannot be destroyed, so the `?`
            // leaves its library loaded.
            let destroy_instance: PfnVkDestroyInstance =
                unsafe { load_inst_fn(gipa, instance, c"vkDestroyInstance", "vkDestroyInstance") }?;
            let mut lib_slot = null_mut();
            let mut radv_slot = null_mut();
            let res = unsafe {
                Self::init_with_instance(
                    &mut lib_slot,
                    &mut radv_slot,
                    gipa,
                    &mut instance,
                    destroy_instance,
                    require_exec_telemetry,
                )
            };
            if let Ok((mut eng, info)) = res {
                eng.lib_handle = lib_handle;
                return Ok((eng, info));
            }
            unsafe {
                if !instance.is_null() {
                    destroy_instance(instance, null());
                }
            }
            res
        } else if rc == -3 || rc == -9 {
            Err(VulkanError::NoDiscreteGpuFound)
        } else {
            Err(VulkanError::VkResult {
                op: "vkCreateInstance",
                code: rc,
            })
        };

        unsafe {
            let _ = dlclose(lib_handle);
        }
        default_res
    }

    #[cfg(not(target_os = "macos"))]
    unsafe fn try_new_with_radv_icd(
        require_exec_telemetry: bool,
    ) -> Option<Result<(Self, VulkanDeviceInfo), VulkanError>> {
        let radv_paths = [
            c"/usr/lib/x86_64-linux-gnu/libvulkan_radeon.so",
            c"/usr/lib/aarch64-linux-gnu/libvulkan_radeon.so",
            c"/usr/lib64/libvulkan_radeon.so",
            c"/usr/lib/libvulkan_radeon.so",
        ];
        let mut radv_lib: *mut c_void = null_mut();
        for path in radv_paths {
            let h = unsafe { dlopen(path.as_ptr(), RTLD_NOW | RTLD_LOCAL) };
            if !h.is_null() {
                radv_lib = h;
                break;
            }
        }
        if radv_lib.is_null() && std::env::var_os("QSAG_ALLOW_RELATIVE_VULKAN_LOADER").is_some() {
            radv_lib = unsafe { dlopen(c"libvulkan_radeon.so".as_ptr(), RTLD_NOW | RTLD_LOCAL) };
        }
        if radv_lib.is_null() {
            return None;
        }

        let negotiate_raw = unsafe {
            dlsym(
                radv_lib,
                c"vk_icdNegotiateLoaderICDInterfaceVersion".as_ptr(),
            )
        };
        let icd_gipa_raw = unsafe { dlsym(radv_lib, c"vk_icdGetInstanceProcAddr".as_ptr()) };
        if negotiate_raw.is_null() || icd_gipa_raw.is_null() {
            unsafe {
                let _ = dlclose(radv_lib);
            }
            return None;
        }
        let negotiate: PfnVkIcdNegotiateVersion = unsafe { core::mem::transmute(negotiate_raw) };
        let mut icd_ver = 5u32;
        if unsafe { negotiate(&mut icd_ver) } != VK_SUCCESS || icd_ver < 5 {
            unsafe {
                let _ = dlclose(radv_lib);
            }
            return None;
        }
        let icd_gipa: PfnVkGetInstanceProcAddr = unsafe { core::mem::transmute(icd_gipa_raw) };

        let Ok(create_instance) = (unsafe {
            load_inst_fn::<PfnVkCreateInstance>(
                icd_gipa,
                null_mut(),
                c"vkCreateInstance",
                "vkCreateInstance",
            )
        }) else {
            unsafe {
                let _ = dlclose(radv_lib);
            }
            return None;
        };

        let mut icd_api = VK_API_VERSION_1_2;
        if let Ok(enum_ver) = unsafe {
            load_inst_fn::<PfnVkEnumerateInstanceVersion>(
                icd_gipa,
                null_mut(),
                c"vkEnumerateInstanceVersion",
                "vkEnumerateInstanceVersion",
            )
        } {
            let mut v = 0u32;
            if unsafe { enum_ver(&mut v) } == VK_SUCCESS && v >= VK_API_VERSION_1_3 {
                icd_api = VK_API_VERSION_1_3;
            }
        }

        let app_info = VkApplicationInfo {
            s_type: VK_STRUCTURE_TYPE_APPLICATION_INFO,
            p_next: null(),
            p_application_name: c"qsag-accel".as_ptr(),
            application_version: 1,
            p_engine_name: c"qsag-spirv".as_ptr(),
            engine_version: 1,
            api_version: icd_api,
        };
        let inst_info = VkInstanceCreateInfo {
            s_type: VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO,
            p_next: null(),
            flags: 0,
            p_application_info: &app_info,
            enabled_layer_count: 0,
            pp_enabled_layer_names: null(),
            enabled_extension_count: 0,
            pp_enabled_extension_names: null(),
        };
        let mut instance: VkInstance = null_mut();
        if unsafe { create_instance(&inst_info, null(), &mut instance) } != VK_SUCCESS {
            unsafe {
                let _ = dlclose(radv_lib);
            }
            return None;
        }
        let Ok(destroy_instance) = (unsafe {
            load_inst_fn::<PfnVkDestroyInstance>(
                icd_gipa,
                instance,
                c"vkDestroyInstance",
                "vkDestroyInstance",
            )
        }) else {
            // The live instance cannot be destroyed, so its library stays loaded.
            return None;
        };

        let mut lib_slot: *mut c_void = null_mut();
        let mut radv_slot: *mut c_void = radv_lib;
        match unsafe {
            Self::init_with_instance(
                &mut lib_slot,
                &mut radv_slot,
                icd_gipa,
                &mut instance,
                destroy_instance,
                require_exec_telemetry,
            )
        } {
            Ok((mut eng, info)) => {
                eng.radv_lib_handle = radv_lib;
                Some(Ok((eng, info)))
            }
            Err(e) => {
                unsafe {
                    if !instance.is_null() {
                        destroy_instance(instance, null());
                    }
                    if !radv_slot.is_null() {
                        let _ = dlclose(radv_slot);
                    }
                }
                Some(Err(e))
            }
        }
    }

    unsafe fn init_with_instance(
        lib_handle: &mut *mut c_void,
        radv_lib_handle: &mut *mut c_void,
        gipa: PfnVkGetInstanceProcAddr,
        instance_slot: &mut VkInstance,
        destroy_instance: PfnVkDestroyInstance,
        require_exec_telemetry: bool,
    ) -> Result<(Self, VulkanDeviceInfo), VulkanError> {
        let instance = *instance_slot;
        let enum_devs: PfnVkEnumeratePhysicalDevices = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkEnumeratePhysicalDevices",
                "vkEnumeratePhysicalDevices",
            )?
        };
        let get_props: PfnVkGetPhysicalDeviceProperties = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetPhysicalDeviceProperties",
                "vkGetPhysicalDeviceProperties",
            )?
        };
        let get_feats: PfnVkGetPhysicalDeviceFeatures = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetPhysicalDeviceFeatures",
                "vkGetPhysicalDeviceFeatures",
            )?
        };
        let get_mem_props: PfnVkGetPhysicalDeviceMemoryProperties = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetPhysicalDeviceMemoryProperties",
                "vkGetPhysicalDeviceMemoryProperties",
            )?
        };
        let get_q_props: PfnVkGetPhysicalDeviceQueueFamilyProperties = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetPhysicalDeviceQueueFamilyProperties",
                "vkGetPhysicalDeviceQueueFamilyProperties",
            )?
        };
        let create_device: PfnVkCreateDevice =
            unsafe { load_inst_fn(gipa, instance, c"vkCreateDevice", "vkCreateDevice")? };
        let gdpa: PfnVkGetDeviceProcAddr = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetDeviceProcAddr",
                "vkGetDeviceProcAddr",
            )?
        };

        const VK_INCOMPLETE: i32 = 5;
        let mut phys_devs = std::vec::Vec::new();
        let mut enumerated = false;
        for _ in 0..4 {
            let mut dev_count = 0u32;
            let enum_rc = unsafe { enum_devs(instance, &mut dev_count, null_mut()) };
            if enum_rc == -3 || enum_rc == -9 {
                return Err(VulkanError::NoDiscreteGpuFound);
            }
            check_vk("vkEnumeratePhysicalDevices(count)", enum_rc)?;
            if dev_count == 0 {
                return Err(VulkanError::NoDiscreteGpuFound);
            }
            phys_devs.clear();
            phys_devs.resize(dev_count as usize, null_mut());
            let list_rc = unsafe { enum_devs(instance, &mut dev_count, phys_devs.as_mut_ptr()) };
            if list_rc == VK_INCOMPLETE {
                continue;
            }
            check_vk("vkEnumeratePhysicalDevices(list)", list_rc)?;
            phys_devs.truncate(dev_count as usize);
            enumerated = true;
            break;
        }
        if !enumerated || phys_devs.is_empty() {
            return Err(VulkanError::NoDiscreteGpuFound);
        }

        let enumerate_extensions: unsafe extern "C" fn(
            VkPhysicalDevice,
            *const c_char,
            *mut u32,
            *mut ExtensionProperties,
        ) -> i32 = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkEnumerateDeviceExtensionProperties",
                "vkEnumerateDeviceExtensionProperties",
            )?
        };
        let get_features2_opt: Option<unsafe extern "C" fn(VkPhysicalDevice, *mut Features2)> = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetPhysicalDeviceFeatures2",
                "vkGetPhysicalDeviceFeatures2",
            )
            .ok()
        };
        let get_properties2_opt: Option<unsafe extern "C" fn(VkPhysicalDevice, *mut Properties2)> = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetPhysicalDeviceProperties2",
                "vkGetPhysicalDeviceProperties2",
            )
            .ok()
        };

        // Select hardware GPU (`DISCRETE_GPU` preferred over `INTEGRATED_GPU`; software/CPU ICDs
        // such as `llvmpipe` are strictly rejected), preferring Wave32 + executable-telemetry
        // capable drivers (e.g. Mesa RADV over AMDVLK).
        type DevRank = (bool, bool, bool, bool, u32);
        let mut chosen: Option<(
            VkPhysicalDevice,
            VkPhysicalDevicePropertiesRaw,
            VkPhysicalDeviceFeatures,
            DevRank,
        )> = None;
        let mut saw_hw_gpu_without_int64 = false;
        for &pd in &phys_devs {
            if pd.is_null() {
                continue;
            }
            let mut props =
                unsafe { MaybeUninit::<VkPhysicalDevicePropertiesRaw>::zeroed().assume_init() };
            let mut feats =
                unsafe { MaybeUninit::<VkPhysicalDeviceFeatures>::zeroed().assume_init() };
            unsafe {
                get_props(pd, &mut props);
                get_feats(pd, &mut feats);
            }
            let is_hw_gpu =
                is_accepted_gpu_device_type(props.device_type, cfg!(target_os = "macos"));
            if is_hw_gpu {
                if feats.flags[FEATURE_SHADER_INT64_INDEX] == 0 {
                    saw_hw_gpu_without_int64 = true;
                    continue;
                }
                let mut can_audit = false;
                if let (Some(gf2), Some(gp2)) = (get_features2_opt, get_properties2_opt) {
                    let mut ec = 0u32;
                    if unsafe { enumerate_extensions(pd, null(), &mut ec, null_mut()) }
                        == VK_SUCCESS
                        && ec > 0
                    {
                        let mut dev_exts = std::vec![
                            ExtensionProperties { name: [0; 256], version: 0 };
                            ec as usize
                        ];
                        if unsafe {
                            enumerate_extensions(pd, null(), &mut ec, dev_exts.as_mut_ptr())
                        } == VK_SUCCESS
                        {
                            dev_exts.truncate(ec as usize);
                            let has_e = dev_exts.iter().any(|e| {
                                e.name.starts_with(
                                    c"VK_KHR_pipeline_executable_properties".to_bytes_with_nul(),
                                )
                            });
                            let has_s = dev_exts.iter().any(|e| {
                                e.name.starts_with(
                                    c"VK_EXT_subgroup_size_control".to_bytes_with_nul(),
                                )
                            });
                            if has_e && has_s {
                                let mut exec_f = FeatureChain {
                                    s_type: 1000269000,
                                    p_next: null_mut(),
                                    enabled: 0,
                                    extra: 0,
                                };
                                let mut sg_f = FeatureChain {
                                    s_type: 1000225002,
                                    p_next: (&mut exec_f as *mut FeatureChain).cast(),
                                    enabled: 0,
                                    extra: 0,
                                };
                                let mut f2 = Features2 {
                                    s_type: 1000059000,
                                    p_next: (&mut sg_f as *mut FeatureChain).cast(),
                                    features: VkPhysicalDeviceFeatures { flags: [0; 55] },
                                };
                                unsafe {
                                    gf2(pd, &mut f2);
                                }
                                let mut sgp = SubgroupProperties {
                                    s_type: 1000225000,
                                    p_next: null_mut(),
                                    min: 0,
                                    max: 0,
                                    max_compute_subgroups: 0,
                                    required_stages: 0,
                                };
                                let mut p2 = Properties2 {
                                    s_type: 1000059001,
                                    p_next: (&mut sgp as *mut SubgroupProperties).cast(),
                                    properties: unsafe { core::mem::zeroed() },
                                };
                                unsafe {
                                    gp2(pd, &mut p2);
                                }
                                can_audit = exec_f.enabled != 0
                                    && sg_f.enabled != 0
                                    && sgp.min <= 32
                                    && sgp.max >= 32
                                    && (sgp.required_stages & VK_SHADER_STAGE_COMPUTE_BIT) != 0
                                    && sgp.max_compute_subgroups >= 8;
                            }
                        }
                    }
                }
                let rank: DevRank = (
                    can_audit,
                    props.device_type == VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU,
                    props.vendor_id == 0x1002,
                    contains_ascii_subslice(&props.device_name, b"RADV"),
                    props.read_limits_u32(512 - 296),
                );
                let replace = match &chosen {
                    None => true,
                    Some((_, _, _, prev_rank)) => rank > *prev_rank,
                };
                if replace {
                    chosen = Some((pd, props, feats, rank));
                }
            }
        }

        let (phys_dev, props, _, _) = match chosen {
            Some(c) => c,
            None if saw_hw_gpu_without_int64 => return Err(VulkanError::MissingShaderInt64),
            None => return Err(VulkanError::NoDiscreteGpuFound),
        };

        // SPIR-V modules target Vulkan 1.2. Check all fixed shader resource limits
        // before creating any device objects (not merely before dispatch).
        if props.api_version < VK_API_VERSION_1_2
            || props.max_compute_work_group_invocations() < 256
            || props.read_limits_u32(532 - 296) < 256
            || props.max_push_constants_size() < 128
            || props.read_limits_u32(512 - 296) < 16384
            || props.max_compute_work_group_count_x() == 0
        {
            return Err(VulkanError::UnsupportedDeviceLimits);
        }
        let mut count = 0;
        check_vk("vkEnumerateDeviceExtensionProperties", unsafe {
            enumerate_extensions(phys_dev, null(), &mut count, null_mut())
        })?;
        let mut extensions =
            std::vec![ExtensionProperties { name: [0; 256], version: 0 }; count as usize];
        check_vk("vkEnumerateDeviceExtensionProperties", unsafe {
            enumerate_extensions(phys_dev, null(), &mut count, extensions.as_mut_ptr())
        })?;
        extensions.truncate(count as usize);
        let has = |name: &core::ffi::CStr| {
            extensions
                .iter()
                .any(|e| e.name.starts_with(name.to_bytes_with_nul()))
        };
        let has_exec = has(c"VK_KHR_pipeline_executable_properties");
        let has_subgroup = has(c"VK_EXT_subgroup_size_control");
        let has_portability_subset = has(c"VK_KHR_portability_subset");
        let mut executable = FeatureChain {
            s_type: 1000269000,
            p_next: null_mut(),
            enabled: 0,
            extra: 0,
        };
        let mut subgroup = FeatureChain {
            s_type: 1000225002,
            p_next: null_mut(),
            enabled: 0,
            extra: 0,
        };
        let mut features2 = Features2 {
            s_type: 1000059000,
            p_next: null_mut(),
            features: VkPhysicalDeviceFeatures { flags: [0; 55] },
        };
        if has_exec {
            features2.p_next = (&mut executable as *mut FeatureChain).cast();
        }
        if has_subgroup {
            subgroup.p_next = features2.p_next;
            features2.p_next = (&mut subgroup as *mut FeatureChain).cast();
        }
        let get_features2: unsafe extern "C" fn(VkPhysicalDevice, *mut Features2) = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetPhysicalDeviceFeatures2",
                "vkGetPhysicalDeviceFeatures2",
            )?
        };
        unsafe {
            get_features2(phys_dev, &mut features2);
        }
        let mut core_sg = CoreSubgroupProperties {
            s_type: VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_SUBGROUP_PROPERTIES,
            p_next: null_mut(),
            subgroup_size: 0,
            supported_stages: 0,
            supported_operations: 0,
            quad_operations_in_all_stages: 0,
        };
        let mut sg_props = SubgroupProperties {
            s_type: 1000225000,
            p_next: (&mut core_sg as *mut CoreSubgroupProperties).cast(),
            min: 0,
            max: 0,
            max_compute_subgroups: 0,
            required_stages: 0,
        };
        let get_properties2: unsafe extern "C" fn(VkPhysicalDevice, *mut Properties2) = unsafe {
            load_inst_fn(
                gipa,
                instance,
                c"vkGetPhysicalDeviceProperties2",
                "vkGetPhysicalDeviceProperties2",
            )?
        };
        {
            let mut p2 = Properties2 {
                s_type: 1000059001,
                p_next: if has_subgroup {
                    (&mut sg_props as *mut SubgroupProperties).cast()
                } else {
                    (&mut core_sg as *mut CoreSubgroupProperties).cast()
                },
                properties: unsafe { core::mem::zeroed() },
            };
            unsafe {
                get_properties2(phys_dev, &mut p2);
            }
        }
        let core_subgroup_size = (core_sg.subgroup_size > 0
            && (core_sg.supported_stages & VK_SHADER_STAGE_COMPUTE_BIT) != 0)
            .then_some(core_sg.subgroup_size);
        let wave32 = has_subgroup
            && subgroup.enabled != 0
            && sg_props.min <= 32
            && sg_props.max >= 32
            && sg_props.required_stages & VK_SHADER_STAGE_COMPUTE_BIT != 0
            && sg_props.max_compute_subgroups >= 8;
        let capture = has_exec && executable.enabled != 0;
        // Enable only queried features we actually use, preserving the pNext lifetimes.
        subgroup.enabled = u32::from(wave32);
        subgroup.extra = 0;
        subgroup.p_next = null_mut();
        executable.p_next = null_mut();
        let mut enabled_extensions = std::vec::Vec::new();
        let mut device_chain: *mut c_void = null_mut();
        if has_portability_subset {
            enabled_extensions.push(c"VK_KHR_portability_subset".as_ptr());
        }
        if capture {
            enabled_extensions.push(c"VK_KHR_pipeline_executable_properties".as_ptr());
            device_chain = (&mut executable as *mut FeatureChain).cast();
        }
        if wave32 {
            enabled_extensions.push(c"VK_EXT_subgroup_size_control".as_ptr());
            subgroup.p_next = device_chain;
            device_chain = (&mut subgroup as *mut FeatureChain).cast();
        }
        let mut mem_props =
            unsafe { MaybeUninit::<VkPhysicalDeviceMemoryProperties>::zeroed().assume_init() };
        unsafe {
            get_mem_props(phys_dev, &mut mem_props);
        }

        let mut qf_count = 0u32;
        unsafe {
            get_q_props(phys_dev, &mut qf_count, null_mut());
        }
        if qf_count == 0 {
            return Err(VulkanError::NoComputeQueueFamily);
        }
        let mut qf_props = std::vec![
            VkQueueFamilyProperties {
                queue_flags: 0,
                queue_count: 0,
                timestamp_valid_bits: 0,
                min_image_transfer_granularity: [0; 3],
            };
            qf_count as usize
        ];
        unsafe {
            get_q_props(phys_dev, &mut qf_count, qf_props.as_mut_ptr());
        }

        qf_props.truncate(qf_count as usize);

        // Prefer dedicated async compute + transfer queue family (`!GRAPHICS`), fallback to any compute queue.
        let mut queue_family_index: Option<u32> = None;
        for (idx, qf) in qf_props.iter().enumerate() {
            if qf.queue_count > 0
                && (qf.queue_flags & (VK_QUEUE_COMPUTE_BIT | VK_QUEUE_TRANSFER_BIT))
                    == (VK_QUEUE_COMPUTE_BIT | VK_QUEUE_TRANSFER_BIT)
                && (qf.queue_flags & VK_QUEUE_GRAPHICS_BIT) == 0
            {
                queue_family_index = Some(idx as u32);
                break;
            }
        }
        if queue_family_index.is_none() {
            for (idx, qf) in qf_props.iter().enumerate() {
                if qf.queue_count > 0 && (qf.queue_flags & VK_QUEUE_COMPUTE_BIT) != 0 {
                    queue_family_index = Some(idx as u32);
                    break;
                }
            }
        }
        let qf_idx = queue_family_index.ok_or(VulkanError::NoComputeQueueFamily)?;

        let priority: f32 = 1.0;
        let q_info = VkDeviceQueueCreateInfo {
            s_type: VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO,
            p_next: null(),
            flags: 0,
            queue_family_index: qf_idx,
            queue_count: 1,
            p_queue_priorities: &priority,
        };
        let mut enabled_features = VkPhysicalDeviceFeatures { flags: [0u32; 55] };
        enabled_features.flags[FEATURE_SHADER_INT64_INDEX] = VK_TRUE;

        let dev_info_create = VkDeviceCreateInfo {
            s_type: VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO,
            p_next: device_chain,
            flags: 0,
            queue_create_info_count: 1,
            p_queue_create_infos: &q_info,
            enabled_layer_count: 0,
            pp_enabled_layer_names: null(),
            enabled_extension_count: enabled_extensions.len() as u32,
            pp_enabled_extension_names: enabled_extensions.as_ptr(),
            p_enabled_features: &enabled_features,
        };
        let mut device: VkDevice = null_mut();
        check_vk("vkCreateDevice", unsafe {
            create_device(phys_dev, &dev_info_create, null(), &mut device)
        })?;

        let fns = match unsafe { Self::load_device_fns(gdpa, device) } {
            Ok(f) => f,
            Err(e) => {
                if let Ok(destroy_dev) = unsafe {
                    load_dev_fn::<unsafe extern "C" fn(VkDevice, *const c_void)>(
                        gdpa,
                        device,
                        c"vkDestroyDevice",
                        "vkDestroyDevice",
                    )
                } {
                    unsafe {
                        destroy_dev(device, null());
                    }
                }
                return Err(e);
            }
        };

        let mut queue: VkQueue = null_mut();
        unsafe {
            (fns.get_device_queue)(device, qf_idx, 0, &mut queue);
        }

        let name_len = props
            .device_name
            .iter()
            .position(|&b| b == 0)
            .unwrap_or(props.device_name.len());
        let (name_bytes, copy_len) =
            VulkanDeviceInfo::sanitize_device_name(&props.device_name[..name_len]);
        let mut dev_info = VulkanDeviceInfo {
            max_compute_shared_memory_size: props.read_limits_u32(512 - 296),
            wave32_required: wave32,
            pipelines: [crate::vulkan::PipelineTelemetry::default(); KernelSlot::COUNT],
            prover_pipelines: [crate::vulkan::PipelineTelemetry::default();
                ProverKernelSlot::COUNT],
            name_bytes,
            name_len: copy_len,
            vendor_id: props.vendor_id,
            device_id: props.device_id,
            driver_version: props.driver_version,
            api_version: props.api_version,
            device_type: props.device_type,
            max_push_constants_size: props.max_push_constants_size(),
            max_storage_buffer_range: props.max_storage_buffer_range(),
            max_compute_work_group_invocations: props.max_compute_work_group_invocations(),
        };

        let mut engine = Self {
            lib_handle: core::mem::replace(lib_handle, null_mut()),
            radv_lib_handle: core::mem::replace(radv_lib_handle, null_mut()),
            destroy_instance,
            instance: core::mem::replace(instance_slot, null_mut()),
            device,
            fns,
            queue,
            mem_props,
            wave32,
            core_subgroup_size,
            require_exec_telemetry,
            executable_fns: None,
            telemetry: [crate::vulkan::PipelineTelemetry::default(); KernelSlot::COUNT],
            prover_telemetry: [crate::vulkan::PipelineTelemetry::default();
                ProverKernelSlot::COUNT],
            max_wg_x: props.max_compute_work_group_count_x(),
            max_storage_range: props.max_storage_buffer_range() as u64,
            exec_state: EngineExecState::Ready,
            staging_residue_bytes: 0,
            #[cfg(test)]
            fail_alloc_countdown: core::cell::Cell::new(None),
            #[cfg(test)]
            injected_rcs: core::cell::Cell::new([None; 4]),
            #[cfg(test)]
            mutation_counters: core::cell::Cell::new((0, 0)),
            #[cfg(test)]
            last_unmapped: core::cell::Cell::new(None),
            dsl_1buf: 0,
            dsl_2buf: 0,
            dsl_3buf: 0,
            dsl_6buf: 0,
            pipelines: [KernelPipeline {
                shader_module: 0,
                pipeline_layout: 0,
                pipeline: 0,
            }; KernelSlot::COUNT],
            prover_pipelines: [KernelPipeline {
                shader_module: 0,
                pipeline_layout: 0,
                pipeline: 0,
            }; ProverKernelSlot::COUNT],
            desc_pool: 0,
            ds_1buf_a: 0,
            ds_2buf_ab: 0,
            ds_2buf_ba: 0,
            ds_2buf_aa: 0,
            ds_3buf_abc: 0,
            cmd_pool: 0,
            cmd_buf: null_mut(),
            upload_cmd_buf: null_mut(),
            fence: 0,
            upload_fence: 0,
            staging: GpuBuffer::default(),
            vram_a: GpuBuffer::default(),
            vram_b: GpuBuffer::default(),
            vram_c: GpuBuffer::default(),
            prover: ProverArena::default(),
        };

        unsafe {
            if capture {
                engine.executable_fns = Some((
                    load_dev_fn(
                        gdpa,
                        device,
                        c"vkGetPipelineExecutablePropertiesKHR",
                        "vkGetPipelineExecutablePropertiesKHR",
                    )?,
                    load_dev_fn(
                        gdpa,
                        device,
                        c"vkGetPipelineExecutableStatisticsKHR",
                        "vkGetPipelineExecutableStatisticsKHR",
                    )?,
                ));
            }
            engine.build_pipelines_and_pools(qf_idx)?;
        }

        dev_info.pipelines = engine.telemetry;
        dev_info.prover_pipelines = engine.prover_telemetry;
        Ok((engine, dev_info))
    }

    unsafe fn load_device_fns(
        gdpa: PfnVkGetDeviceProcAddr,
        device: VkDevice,
    ) -> Result<DeviceFns, VulkanError> {
        unsafe {
            Ok(DeviceFns {
                destroy_device: load_dev_fn(gdpa, device, c"vkDestroyDevice", "vkDestroyDevice")?,
                get_device_queue: load_dev_fn(
                    gdpa,
                    device,
                    c"vkGetDeviceQueue",
                    "vkGetDeviceQueue",
                )?,
                create_buffer: load_dev_fn(gdpa, device, c"vkCreateBuffer", "vkCreateBuffer")?,
                destroy_buffer: load_dev_fn(gdpa, device, c"vkDestroyBuffer", "vkDestroyBuffer")?,
                get_buffer_memory_requirements: load_dev_fn(
                    gdpa,
                    device,
                    c"vkGetBufferMemoryRequirements",
                    "vkGetBufferMemoryRequirements",
                )?,
                allocate_memory: load_dev_fn(
                    gdpa,
                    device,
                    c"vkAllocateMemory",
                    "vkAllocateMemory",
                )?,
                free_memory: load_dev_fn(gdpa, device, c"vkFreeMemory", "vkFreeMemory")?,
                map_memory: load_dev_fn(gdpa, device, c"vkMapMemory", "vkMapMemory")?,
                unmap_memory: load_dev_fn(gdpa, device, c"vkUnmapMemory", "vkUnmapMemory")?,
                bind_buffer_memory: load_dev_fn(
                    gdpa,
                    device,
                    c"vkBindBufferMemory",
                    "vkBindBufferMemory",
                )?,
                create_shader_module: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCreateShaderModule",
                    "vkCreateShaderModule",
                )?,
                destroy_shader_module: load_dev_fn(
                    gdpa,
                    device,
                    c"vkDestroyShaderModule",
                    "vkDestroyShaderModule",
                )?,
                create_descriptor_set_layout: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCreateDescriptorSetLayout",
                    "vkCreateDescriptorSetLayout",
                )?,
                destroy_descriptor_set_layout: load_dev_fn(
                    gdpa,
                    device,
                    c"vkDestroyDescriptorSetLayout",
                    "vkDestroyDescriptorSetLayout",
                )?,
                create_pipeline_layout: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCreatePipelineLayout",
                    "vkCreatePipelineLayout",
                )?,
                destroy_pipeline_layout: load_dev_fn(
                    gdpa,
                    device,
                    c"vkDestroyPipelineLayout",
                    "vkDestroyPipelineLayout",
                )?,
                create_compute_pipelines: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCreateComputePipelines",
                    "vkCreateComputePipelines",
                )?,
                destroy_pipeline: load_dev_fn(
                    gdpa,
                    device,
                    c"vkDestroyPipeline",
                    "vkDestroyPipeline",
                )?,
                create_descriptor_pool: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCreateDescriptorPool",
                    "vkCreateDescriptorPool",
                )?,
                destroy_descriptor_pool: load_dev_fn(
                    gdpa,
                    device,
                    c"vkDestroyDescriptorPool",
                    "vkDestroyDescriptorPool",
                )?,
                allocate_descriptor_sets: load_dev_fn(
                    gdpa,
                    device,
                    c"vkAllocateDescriptorSets",
                    "vkAllocateDescriptorSets",
                )?,
                update_descriptor_sets: load_dev_fn(
                    gdpa,
                    device,
                    c"vkUpdateDescriptorSets",
                    "vkUpdateDescriptorSets",
                )?,
                create_command_pool: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCreateCommandPool",
                    "vkCreateCommandPool",
                )?,
                destroy_command_pool: load_dev_fn(
                    gdpa,
                    device,
                    c"vkDestroyCommandPool",
                    "vkDestroyCommandPool",
                )?,
                reset_command_pool: load_dev_fn(
                    gdpa,
                    device,
                    c"vkResetCommandPool",
                    "vkResetCommandPool",
                )?,
                allocate_command_buffers: load_dev_fn(
                    gdpa,
                    device,
                    c"vkAllocateCommandBuffers",
                    "vkAllocateCommandBuffers",
                )?,
                begin_command_buffer: load_dev_fn(
                    gdpa,
                    device,
                    c"vkBeginCommandBuffer",
                    "vkBeginCommandBuffer",
                )?,
                end_command_buffer: load_dev_fn(
                    gdpa,
                    device,
                    c"vkEndCommandBuffer",
                    "vkEndCommandBuffer",
                )?,
                cmd_copy_buffer: load_dev_fn(gdpa, device, c"vkCmdCopyBuffer", "vkCmdCopyBuffer")?,
                cmd_fill_buffer: load_dev_fn(gdpa, device, c"vkCmdFillBuffer", "vkCmdFillBuffer")?,
                cmd_bind_pipeline: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCmdBindPipeline",
                    "vkCmdBindPipeline",
                )?,
                cmd_bind_descriptor_sets: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCmdBindDescriptorSets",
                    "vkCmdBindDescriptorSets",
                )?,
                cmd_push_constants: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCmdPushConstants",
                    "vkCmdPushConstants",
                )?,
                cmd_dispatch: load_dev_fn(gdpa, device, c"vkCmdDispatch", "vkCmdDispatch")?,
                cmd_pipeline_barrier: load_dev_fn(
                    gdpa,
                    device,
                    c"vkCmdPipelineBarrier",
                    "vkCmdPipelineBarrier",
                )?,
                create_fence: load_dev_fn(gdpa, device, c"vkCreateFence", "vkCreateFence")?,
                destroy_fence: load_dev_fn(gdpa, device, c"vkDestroyFence", "vkDestroyFence")?,
                reset_fences: load_dev_fn(gdpa, device, c"vkResetFences", "vkResetFences")?,
                wait_for_fences: load_dev_fn(gdpa, device, c"vkWaitForFences", "vkWaitForFences")?,
                queue_submit: load_dev_fn(gdpa, device, c"vkQueueSubmit", "vkQueueSubmit")?,
                device_wait_idle: load_dev_fn(
                    gdpa,
                    device,
                    c"vkDeviceWaitIdle",
                    "vkDeviceWaitIdle",
                )?,
            })
        }
    }

    unsafe fn query_pipeline_telemetry(
        &self,
        pipeline: VkPipeline,
    ) -> Result<(u32, crate::vulkan::PipelineTelemetry), VulkanError> {
        let Some((get_properties, get_statistics)) = self.executable_fns else {
            return Err(VulkanError::PipelineAuditFailed(
                "executable telemetry unavailable",
            ));
        };
        let info = PipelineInfo {
            s_type: 1000269001,
            p_next: null(),
            pipeline,
        };
        let mut count = 0;
        check_vk("vkGetPipelineExecutablePropertiesKHR(count)", unsafe {
            get_properties(self.device, &info, &mut count, null_mut())
        })?;
        let mut properties = std::vec![ExecutableProperties { s_type: 1000269002, p_next: null_mut(), stages: 0, name: [0; 256], description: [0; 256], subgroup_size: 0 }; count as usize];
        check_vk("vkGetPipelineExecutablePropertiesKHR", unsafe {
            get_properties(self.device, &info, &mut count, properties.as_mut_ptr())
        })?;
        properties.truncate(count as usize);
        if properties.len() != 1 {
            return Err(VulkanError::PipelineAuditFailed(
                "expected one compute executable",
            ));
        }
        let subgroup_size = properties[0].subgroup_size;
        let info = ExecutableInfo {
            s_type: 1000269003,
            p_next: null(),
            pipeline,
            index: 0,
        };
        let mut count = 0;
        check_vk("vkGetPipelineExecutableStatisticsKHR(count)", unsafe {
            get_statistics(self.device, &info, &mut count, null_mut())
        })?;
        let mut stats = std::vec![ExecutableStatistic { s_type: 1000269004, p_next: null_mut(), name: [0; 256], description: [0; 256], format: 0, value: 0 }; count as usize];
        check_vk("vkGetPipelineExecutableStatisticsKHR", unsafe {
            get_statistics(self.device, &info, &mut count, stats.as_mut_ptr())
        })?;
        stats.truncate(count as usize);
        let mut scratch = None;
        let mut vgprs = None;
        let mut sgprs = None;
        let mut lds = None;
        let mut spilled_vgprs = None;
        let mut spilled_sgprs = None;
        for stat in stats {
            let end = stat.name.iter().position(|b| *b == 0).unwrap_or(256);
            let name = core::str::from_utf8(&stat.name[..end]).unwrap_or("");
            if stat.format != 2 {
                continue;
            }
            match name {
                "Scratch size" | "scratch_memory" => scratch = Some(stat.value),
                "VGPRs" | "num_vgprs" => vgprs = Some(stat.value),
                "SGPRs" | "num_sgprs" => sgprs = Some(stat.value),
                "LDS size" | "lds_size" => lds = Some(stat.value),
                "Spilled VGPRs" => spilled_vgprs = Some(stat.value),
                "Spilled SGPRs" => spilled_sgprs = Some(stat.value),
                _ => {}
            }
        }
        let tel = crate::vulkan::PipelineTelemetry {
            subgroup_size: Some(subgroup_size),
            scratch_bytes: scratch,
            vgprs,
            sgprs,
            lds_bytes: lds,
            spilled_vgprs,
            spilled_sgprs,
        };
        Ok((subgroup_size, tel))
    }

    unsafe fn collect_telemetry(
        &mut self,
        slot: KernelSlot,
        pipeline: VkPipeline,
    ) -> Result<(), VulkanError> {
        if !self.require_exec_telemetry && self.executable_fns.is_none() {
            let sg = if self.wave32 {
                32
            } else {
                self.core_subgroup_size.unwrap_or(0)
            };
            if sg != 32 {
                return Err(VulkanError::UnexpectedSubgroupSize {
                    slot,
                    required: 32,
                    reported: sg,
                });
            }
            self.telemetry[slot as usize] = crate::vulkan::PipelineTelemetry {
                subgroup_size: Some(32),
                ..Default::default()
            };
            return Ok(());
        }
        let (subgroup_size, tel) = unsafe { self.query_pipeline_telemetry(pipeline)? };
        if !self.wave32 || subgroup_size != 32 {
            return Err(VulkanError::UnexpectedSubgroupSize {
                slot,
                required: 32,
                reported: subgroup_size,
            });
        }
        self.telemetry[slot as usize] = tel;
        tel.audit()
    }

    unsafe fn collect_prover_telemetry(
        &mut self,
        slot: ProverKernelSlot,
        pipeline: VkPipeline,
    ) -> Result<(), VulkanError> {
        if !self.require_exec_telemetry && self.executable_fns.is_none() {
            let sg = if self.wave32 {
                32
            } else {
                self.core_subgroup_size.unwrap_or(0)
            };
            if sg != 32 {
                return Err(VulkanError::UnexpectedProverSubgroupSize {
                    slot,
                    required: 32,
                    reported: sg,
                });
            }
            self.prover_telemetry[slot as usize] = crate::vulkan::PipelineTelemetry {
                subgroup_size: Some(32),
                ..Default::default()
            };
            return Ok(());
        }
        let (subgroup_size, tel) = unsafe { self.query_pipeline_telemetry(pipeline)? };
        if !self.wave32 || subgroup_size != 32 {
            return Err(VulkanError::UnexpectedProverSubgroupSize {
                slot,
                required: 32,
                reported: subgroup_size,
            });
        }
        self.prover_telemetry[slot as usize] = tel;
        tel.audit()
    }

    unsafe fn create_dsl(&self, num_bindings: u32) -> Result<VkDescriptorSetLayout, VulkanError> {
        let mut bindings = [VkDescriptorSetLayoutBinding {
            binding: 0,
            descriptor_type: VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
            descriptor_count: 1,
            stage_flags: VK_SHADER_STAGE_COMPUTE_BIT,
            p_immutable_samplers: null(),
        }; 6];
        for (i, b) in bindings.iter_mut().enumerate().take(num_bindings as usize) {
            b.binding = i as u32;
        }
        let info = VkDescriptorSetLayoutCreateInfo {
            s_type: VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO,
            p_next: null(),
            flags: 0,
            binding_count: num_bindings,
            p_bindings: bindings.as_ptr(),
        };
        let mut dsl: VkDescriptorSetLayout = 0;
        check_vk("vkCreateDescriptorSetLayout", unsafe {
            (self.fns.create_descriptor_set_layout)(self.device, &info, null(), &mut dsl)
        })?;
        Ok(dsl)
    }

    unsafe fn build_one_pipeline(
        &self,
        spv: &[u32],
        dsl: VkDescriptorSetLayout,
        pc_size: u32,
    ) -> Result<(KernelPipeline, i32), VulkanError> {
        let sm_info = VkShaderModuleCreateInfo {
            s_type: VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO,
            p_next: null(),
            flags: 0,
            code_size: spv.len() * 4,
            p_code: spv.as_ptr(),
        };
        let mut sm: VkShaderModule = 0;
        check_vk("vkCreateShaderModule", unsafe {
            (self.fns.create_shader_module)(self.device, &sm_info, null(), &mut sm)
        })?;

        let pc_range = VkPushConstantRange {
            stage_flags: VK_SHADER_STAGE_COMPUTE_BIT,
            offset: 0,
            size: pc_size,
        };
        let pl_info = VkPipelineLayoutCreateInfo {
            s_type: VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO,
            p_next: null(),
            flags: 0,
            set_layout_count: 1,
            p_set_layouts: &dsl,
            push_constant_range_count: 1,
            p_push_constant_ranges: &pc_range,
        };
        let mut pl: VkPipelineLayout = 0;
        if let Err(e) = check_vk("vkCreatePipelineLayout", unsafe {
            (self.fns.create_pipeline_layout)(self.device, &pl_info, null(), &mut pl)
        }) {
            unsafe {
                (self.fns.destroy_shader_module)(self.device, sm, null());
            }
            return Err(e);
        }

        let required = RequiredSubgroup {
            s_type: 1000225001,
            p_next: null(),
            size: 32,
        };
        let cp_info = VkComputePipelineCreateInfo {
            s_type: VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO,
            p_next: null(),
            flags: if self.executable_fns.is_some() {
                0x40
            } else {
                0
            },
            stage: VkPipelineShaderStageCreateInfo {
                s_type: VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO,
                p_next: if self.wave32 {
                    (&required as *const RequiredSubgroup).cast()
                } else {
                    null()
                },
                flags: 0,
                stage: VK_SHADER_STAGE_COMPUTE_BIT,
                module: sm,
                p_name: c"main".as_ptr(),
                p_specialization_info: null(),
            },
            layout: pl,
            base_pipeline_handle: 0,
            base_pipeline_index: -1,
        };
        let mut pipe: VkPipeline = 0;
        let rc = unsafe {
            (self.fns.create_compute_pipelines)(self.device, 0, 1, &cp_info, null(), &mut pipe)
        };
        Ok((
            KernelPipeline {
                shader_module: sm,
                pipeline_layout: pl,
                pipeline: pipe,
            },
            rc,
        ))
    }

    unsafe fn build_pipelines_and_pools(&mut self, qf_idx: u32) -> Result<(), VulkanError> {
        self.dsl_1buf = unsafe { self.create_dsl(1)? };
        self.dsl_2buf = unsafe { self.create_dsl(2)? };
        self.dsl_3buf = unsafe { self.create_dsl(3)? };
        self.dsl_6buf = unsafe { self.create_dsl(6)? };

        let specs: [(KernelSlot, VkDescriptorSetLayout, u32); KernelSlot::COUNT] = [
            (
                KernelSlot::BatchKeccakF1600,
                self.dsl_1buf,
                size_of::<BatchStatesPushConsts>() as u32,
            ),
            (
                KernelSlot::BatchPoseidon2Perm12,
                self.dsl_1buf,
                size_of::<BatchStatesPushConsts>() as u32,
            ),
            (
                KernelSlot::GoldilocksNtt,
                self.dsl_1buf,
                size_of::<NttPushConsts>() as u32,
            ),
            (
                KernelSlot::CosetLdeExt2,
                self.dsl_1buf,
                size_of::<CosetLdePushConsts>() as u32,
            ),
            (
                KernelSlot::MerkleLayerPoseidon2,
                self.dsl_2buf,
                size_of::<MerklePushConsts>() as u32,
            ),
            (
                KernelSlot::BdozGf2128BatchDot,
                self.dsl_3buf,
                size_of::<BdozDotPushConsts>() as u32,
            ),
        ];

        for (slot, dsl, pc_size) in specs {
            let spv = spirv_kernel_words(slot);
            let (kp, rc) = unsafe { self.build_one_pipeline(spv, dsl, pc_size)? };
            self.pipelines[slot as usize] = kp;
            check_vk("vkCreateComputePipelines", rc)?;
            unsafe {
                self.collect_telemetry(slot, kp.pipeline)?;
            }
        }

        let prover_specs: [(ProverKernelSlot, u32); ProverKernelSlot::COUNT] = [
            (
                ProverKernelSlot::WhirLdeCommitment,
                size_of::<WhirLdePushConsts>() as u32,
            ),
            (
                ProverKernelSlot::WhirFoldSumcheck,
                size_of::<WhirFoldPushConsts>() as u32,
            ),
            (
                ProverKernelSlot::AirRowGroupA,
                size_of::<AirGroupAPushConsts>() as u32,
            ),
            (
                ProverKernelSlot::AirRowGroupB,
                size_of::<AirGroupBPushConsts>() as u32,
            ),
        ];

        for (slot, pc_size) in prover_specs {
            let spv = prover_spirv_kernel_words(slot);
            let (kp, rc) = unsafe { self.build_one_pipeline(spv, self.dsl_6buf, pc_size)? };
            self.prover_pipelines[slot as usize] = kp;
            check_vk("vkCreateComputePipelines(prover)", rc)?;
            unsafe {
                self.collect_prover_telemetry(slot, kp.pipeline)?;
            }
        }

        // Descriptor pool: 5 sets (1 + 2 + 2 + 2 + 3 = 10 storage buffer descriptors).
        let pool_size = VkDescriptorPoolSize {
            ty: VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
            descriptor_count: 10,
        };
        let dp_info = VkDescriptorPoolCreateInfo {
            s_type: VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO,
            p_next: null(),
            flags: 0,
            max_sets: 5,
            pool_size_count: 1,
            p_pool_sizes: &pool_size,
        };
        check_vk("vkCreateDescriptorPool", unsafe {
            (self.fns.create_descriptor_pool)(self.device, &dp_info, null(), &mut self.desc_pool)
        })?;

        let set_layouts = [
            self.dsl_1buf,
            self.dsl_2buf,
            self.dsl_2buf,
            self.dsl_2buf,
            self.dsl_3buf,
        ];
        let mut sets = [0u64; 5];
        let dsa_info = VkDescriptorSetAllocateInfo {
            s_type: VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO,
            p_next: null(),
            descriptor_pool: self.desc_pool,
            descriptor_set_count: 5,
            p_set_layouts: set_layouts.as_ptr(),
        };
        check_vk("vkAllocateDescriptorSets", unsafe {
            (self.fns.allocate_descriptor_sets)(self.device, &dsa_info, sets.as_mut_ptr())
        })?;
        self.ds_1buf_a = sets[0];
        self.ds_2buf_ab = sets[1];
        self.ds_2buf_ba = sets[2];
        self.ds_2buf_aa = sets[3];
        self.ds_3buf_abc = sets[4];

        let cp_info = VkCommandPoolCreateInfo {
            s_type: VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO,
            p_next: null(),
            flags: VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT,
            queue_family_index: qf_idx,
        };
        check_vk("vkCreateCommandPool", unsafe {
            (self.fns.create_command_pool)(self.device, &cp_info, null(), &mut self.cmd_pool)
        })?;

        let cba_info = VkCommandBufferAllocateInfo {
            s_type: VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO,
            p_next: null(),
            command_pool: self.cmd_pool,
            level: VK_COMMAND_BUFFER_LEVEL_PRIMARY,
            command_buffer_count: 2,
        };
        let mut cmd_bufs = [null_mut(); 2];
        check_vk("vkAllocateCommandBuffers", unsafe {
            (self.fns.allocate_command_buffers)(self.device, &cba_info, cmd_bufs.as_mut_ptr())
        })?;
        self.cmd_buf = cmd_bufs[0];
        self.upload_cmd_buf = cmd_bufs[1];

        let fence_info = VkFenceCreateInfo {
            s_type: VK_STRUCTURE_TYPE_FENCE_CREATE_INFO,
            p_next: null(),
            flags: 0,
        };
        check_vk("vkCreateFence", unsafe {
            (self.fns.create_fence)(self.device, &fence_info, null(), &mut self.fence)
        })?;
        check_vk("vkCreateFence", unsafe {
            (self.fns.create_fence)(self.device, &fence_info, null(), &mut self.upload_fence)
        })?;

        // Pre-allocate initial workspace buffers and bind descriptor sets.
        unsafe {
            self.ensure_staging(MIN_BUFFER_ALLOC_BYTES)?;
            self.ensure_vram_buffers(
                MIN_BUFFER_ALLOC_BYTES,
                MIN_BUFFER_ALLOC_BYTES,
                MIN_BUFFER_ALLOC_BYTES,
            )?;
        }
        Ok(())
    }

    /// Free one buffer. Callers reach this only with idle established (`Ready`, or teardown
    /// after a successful `vkDeviceWaitIdle`), so the device no longer reads or writes it.
    /// A host mapping is zeroed over its whole capacity before it is released: staging may
    /// hold job inputs or outputs, including those of the job that is displacing it.
    unsafe fn destroy_gpu_buffer(&mut self, buf: &mut GpuBuffer) {
        if !buf.mapped.is_null() && buf.memory != 0 {
            unsafe {
                Self::wipe_mapping(buf.mapped, buf.capacity);
                #[cfg(test)]
                {
                    let bytes = core::slice::from_raw_parts(buf.mapped, buf.capacity as usize);
                    self.last_unmapped
                        .set(Some((buf.capacity, bytes.iter().all(|&b| b == 0))));
                }
                (self.fns.unmap_memory)(self.device, buf.memory);
            }
            buf.mapped = null_mut();
        }
        if buf.buffer != 0 {
            unsafe {
                (self.fns.destroy_buffer)(self.device, buf.buffer, null());
            }
            buf.buffer = 0;
        }
        if buf.memory != 0 {
            unsafe {
                (self.fns.free_memory)(self.device, buf.memory, null());
            }
            buf.memory = 0;
        }
        buf.capacity = 0;
        buf.used = 0;
    }

    /// Volatile zero fill of `len` bytes of a host mapping, followed by a compiler fence.
    unsafe fn wipe_mapping(base: *mut u8, len: u64) {
        let len = len as usize;
        unsafe {
            let align_off = base.align_offset(8).min(len);
            for offset in 0..align_off {
                core::ptr::write_volatile(base.add(offset), 0);
            }
            let words = (len - align_off) / 8;
            let ptr64 = base.add(align_off).cast::<u64>();
            for i in 0..words {
                core::ptr::write_volatile(ptr64.add(i), 0);
            }
            for offset in (align_off + words * 8)..len {
                core::ptr::write_volatile(base.add(offset), 0);
            }
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }

    unsafe fn alloc_gpu_buffer(
        &self,
        byte_size: u64,
        host_staging: bool,
    ) -> Result<GpuBuffer, VulkanError> {
        #[cfg(test)]
        {
            let (allocs, refreshes) = self.mutation_counters.get();
            self.mutation_counters.set((allocs + 1, refreshes));
        }
        #[cfg(test)]
        if let Some(rem) = self.fail_alloc_countdown.get() {
            if rem == 0 {
                self.fail_alloc_countdown.set(None);
                return Err(VulkanError::VkResult {
                    op: "vkAllocateMemory",
                    code: -2,
                });
            }
            self.fail_alloc_countdown.set(Some(rem - 1));
        }
        let cap = byte_size.max(MIN_BUFFER_ALLOC_BYTES);
        if cap > isize::MAX as u64 || (!host_staging && cap > self.max_storage_range) {
            return Err(VulkanError::BufferExceedsMaxStorageRange {
                requested: cap,
                limit: self.max_storage_range.min(isize::MAX as u64),
            });
        }
        let usage = if host_staging {
            VK_BUFFER_USAGE_TRANSFER_SRC_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT
        } else {
            VK_BUFFER_USAGE_STORAGE_BUFFER_BIT
                | VK_BUFFER_USAGE_TRANSFER_SRC_BIT
                | VK_BUFFER_USAGE_TRANSFER_DST_BIT
        };
        let b_info = VkBufferCreateInfo {
            s_type: VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO,
            p_next: null(),
            flags: 0,
            size: cap,
            usage,
            sharing_mode: VK_SHARING_MODE_EXCLUSIVE,
            queue_family_index_count: 0,
            p_queue_family_indices: null(),
        };
        let mut buffer: VkBuffer = 0;
        check_vk("vkCreateBuffer", unsafe {
            (self.fns.create_buffer)(self.device, &b_info, null(), &mut buffer)
        })?;

        let mut req = VkMemoryRequirements {
            size: 0,
            alignment: 0,
            memory_type_bits: 0,
            _pad: 0,
        };
        unsafe {
            (self.fns.get_buffer_memory_requirements)(self.device, buffer, &mut req);
        }

        let mem_type = if host_staging {
            find_memory_type(
                &self.mem_props,
                req.memory_type_bits,
                VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT,
                VK_MEMORY_PROPERTY_HOST_CACHED_BIT,
                VK_MEMORY_PROPERTY_DEVICE_UNCACHED_BIT_AMD,
            )
            .ok_or(VulkanError::NoSuitableMemoryType {
                what: "host-coherent staging buffer",
            })
        } else {
            find_memory_type(
                &self.mem_props,
                req.memory_type_bits,
                VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
                VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
                VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_DEVICE_UNCACHED_BIT_AMD,
            )
            .ok_or(VulkanError::NoSuitableMemoryType {
                what: "device-local VRAM storage buffer",
            })
        };

        let mem_type = match mem_type {
            Ok(idx) => idx,
            Err(e) => {
                unsafe {
                    (self.fns.destroy_buffer)(self.device, buffer, null());
                }
                return Err(e);
            }
        };

        let a_info = VkMemoryAllocateInfo {
            s_type: VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO,
            p_next: null(),
            allocation_size: req.size,
            memory_type_index: mem_type,
        };
        let mut memory: VkDeviceMemory = 0;
        if let Err(e) = check_vk("vkAllocateMemory", unsafe {
            (self.fns.allocate_memory)(self.device, &a_info, null(), &mut memory)
        }) {
            unsafe {
                (self.fns.destroy_buffer)(self.device, buffer, null());
            }
            return Err(e);
        }

        if let Err(e) = check_vk("vkBindBufferMemory", unsafe {
            (self.fns.bind_buffer_memory)(self.device, buffer, memory, 0)
        }) {
            unsafe {
                (self.fns.destroy_buffer)(self.device, buffer, null());
                (self.fns.free_memory)(self.device, memory, null());
            }
            return Err(e);
        }

        let mut mapped: *mut u8 = null_mut();
        if host_staging {
            let mut raw_ptr: *mut c_void = null_mut();
            if let Err(e) = check_vk("vkMapMemory", unsafe {
                (self.fns.map_memory)(self.device, memory, 0, cap, 0, &mut raw_ptr)
            }) {
                unsafe {
                    (self.fns.destroy_buffer)(self.device, buffer, null());
                    (self.fns.free_memory)(self.device, memory, null());
                }
                return Err(e);
            }
            mapped = raw_ptr.cast::<u8>();
        }

        Ok(GpuBuffer {
            buffer,
            memory,
            capacity: cap,
            used: 0,
            mapped,
        })
    }

    /// Verify that no prior submission remains potentially in flight before mutating staging
    /// memory, reallocating buffers, updating descriptors, or resetting the command pool.
    /// If a previous fence wait failed transiently, recovery is permitted ONLY after
    /// `vkDeviceWaitIdle` succeeds (`VK_SUCCESS`); the failed job's staging residue is wiped
    /// at that point, before anything else can use the buffer.
    unsafe fn ensure_ready(&mut self) -> Result<(), VulkanError> {
        const VK_ERROR_DEVICE_LOST: i32 = -4;
        match self.exec_state {
            EngineExecState::Ready => Ok(()),
            EngineExecState::DeviceLostQuarantined => Err(VulkanError::WorkspacePoisoned),
            EngineExecState::InFlightQuarantined => {
                let rc = unsafe { self.device_wait_idle_rc() };
                if rc == VK_SUCCESS {
                    self.exec_state = EngineExecState::Ready;
                    unsafe {
                        self.wipe_staging_residue();
                    }
                    Ok(())
                } else {
                    if rc == VK_ERROR_DEVICE_LOST {
                        self.exec_state = EngineExecState::DeviceLostQuarantined;
                    }
                    Err(VulkanError::WorkspacePoisoned)
                }
            }
        }
    }

    /// Test-only replacement of one driver result code; always `None` in a normal build.
    #[inline]
    fn injected_rc(&self, point: FaultPoint) -> Option<i32> {
        #[cfg(test)]
        {
            let mut rcs = self.injected_rcs.get();
            let rc = rcs[point as usize].take();
            self.injected_rcs.set(rcs);
            rc
        }
        #[cfg(not(test))]
        {
            let _ = point;
            None
        }
    }

    unsafe fn device_wait_idle_rc(&self) -> i32 {
        match self.injected_rc(FaultPoint::DeviceWaitIdle) {
            Some(rc) => rc,
            None => unsafe { (self.fns.device_wait_idle)(self.device) },
        }
    }

    unsafe fn ensure_staging(&mut self, required: u64) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        if self.staging.capacity < required || self.staging.buffer == 0 {
            let target = required
                .checked_next_power_of_two()
                .unwrap_or(required)
                .max(MIN_BUFFER_ALLOC_BYTES);
            let new_buf = unsafe { self.alloc_gpu_buffer(target, true)? };
            // `ensure_ready` returned `Ready`, so the device is done with the displaced mapping;
            // `destroy_gpu_buffer` zeroes it (it can hold what this same job staged earlier).
            let mut old = core::mem::replace(&mut self.staging, new_buf);
            unsafe {
                self.destroy_gpu_buffer(&mut old);
            }
        }
        Ok(())
    }

    /// Reserve the first `required` bytes of staging for the job being started and record them
    /// as residue. `required` is the job's whole staging extent (inputs and read-back).
    unsafe fn reserve_job_staging(&mut self, required: u64) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_staging(required)?;
        }
        self.staging_residue_bytes = self.staging_residue_bytes.max(required);
        Ok(())
    }

    /// Zero the recorded staging residue. The caller has established `Ready`.
    unsafe fn wipe_staging_residue(&mut self) {
        let bytes = core::mem::take(&mut self.staging_residue_bytes);
        if bytes != 0 {
            unsafe {
                self.scrub_staging(bytes);
            }
        }
    }

    /// Wipe what the finished or failed job left in staging, if and only if no submission can
    /// still be live (module docs, "Job data residue and the host wipe").
    unsafe fn settle_staging(&mut self) {
        if self.staging_residue_bytes == 0 {
            return;
        }
        if unsafe { self.ensure_ready() }.is_ok() {
            unsafe {
                self.wipe_staging_residue();
            }
        }
    }

    /// Run one job and settle staging on every way out of it, including an unwind.
    fn run_job<T>(
        &mut self,
        job: impl FnOnce(&mut Self) -> Result<T, VulkanError>,
    ) -> Result<T, VulkanError> {
        struct SettleOnExit<'a>(&'a mut RawVulkanEngine, bool);
        impl SettleOnExit<'_> {
            fn engine(&mut self) -> &mut RawVulkanEngine {
                self.0
            }
        }
        impl Drop for SettleOnExit<'_> {
            fn drop(&mut self) {
                unsafe {
                    self.0.settle_staging();
                    if self.1 && self.0.exec_state == EngineExecState::Ready {
                        let _ = self.0.scrub_batch_vram();
                    }
                }
            }
        }
        // No job touches staging, buffers, descriptors or the command pool while an earlier
        // submission may still be in flight.
        unsafe {
            self.ensure_ready()?;
        }
        let mut guard = SettleOnExit(self, true);
        let res = job(guard.engine());
        guard.1 = res.is_err();
        drop(guard);
        res
    }

    fn plan_vram_growth(&self, cur: &GpuBuffer, required: u64) -> Result<Option<u64>, VulkanError> {
        if required > self.max_storage_range {
            return Err(VulkanError::BufferExceedsMaxStorageRange {
                requested: required,
                limit: self.max_storage_range,
            });
        }
        if required == 0 || (cur.capacity >= required && cur.buffer != 0) {
            return Ok(None);
        }
        let target = if required > (256 << 20) {
            const ALIGN_16M: u64 = 16 << 20;
            required
                .saturating_add(ALIGN_16M - 1)
                .checked_div(ALIGN_16M)
                .map_or(required, |blocks| blocks.saturating_mul(ALIGN_16M))
                .min(self.max_storage_range & !0xFFFF)
                .max(required)
        } else {
            required
                .checked_next_power_of_two()
                .unwrap_or(required)
                .min(self.max_storage_range)
                .max(required)
                .max(MIN_BUFFER_ALLOC_BYTES)
        };
        Ok(Some(target))
    }

    /// Transactionally grow `vram_a`, `vram_b`, and `vram_c`:
    /// 1. Allocate all required replacements into temporary owners.
    /// 2. On any allocation failure, destroy ONLY the newly allocated temporaries, preserving
    ///    all existing buffers and bound descriptor sets untouched.
    /// 3. Commit all replacements, refresh all descriptor sets, and finally destroy displaced buffers.
    pub(crate) unsafe fn ensure_vram_buffers(
        &mut self,
        req_a: u64,
        req_b: u64,
        req_c: u64,
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let tgt_a = self.plan_vram_growth(&self.vram_a, req_a)?;
        let tgt_b = self.plan_vram_growth(&self.vram_b, req_b)?;
        let tgt_c = self.plan_vram_growth(&self.vram_c, req_c)?;
        if tgt_a.is_none() && tgt_b.is_none() && tgt_c.is_none() {
            return Ok(());
        }

        let mut new_a = match tgt_a {
            Some(sz) => Some(unsafe { self.alloc_gpu_buffer(sz, false)? }),
            None => None,
        };
        let mut new_b = match tgt_b {
            Some(sz) => match unsafe { self.alloc_gpu_buffer(sz, false) } {
                Ok(buf) => Some(buf),
                Err(e) => {
                    if let Some(ref mut a) = new_a {
                        unsafe {
                            self.destroy_gpu_buffer(a);
                        }
                    }
                    return Err(e);
                }
            },
            None => None,
        };
        let new_c = match tgt_c {
            Some(sz) => match unsafe { self.alloc_gpu_buffer(sz, false) } {
                Ok(buf) => Some(buf),
                Err(e) => {
                    if let Some(ref mut b) = new_b {
                        unsafe {
                            self.destroy_gpu_buffer(b);
                        }
                    }
                    if let Some(ref mut a) = new_a {
                        unsafe {
                            self.destroy_gpu_buffer(a);
                        }
                    }
                    return Err(e);
                }
            },
            None => None,
        };

        let mut old_a = new_a.map(|nb| core::mem::replace(&mut self.vram_a, nb));
        let mut old_b = new_b.map(|nb| core::mem::replace(&mut self.vram_b, nb));
        let mut old_c = new_c.map(|nb| core::mem::replace(&mut self.vram_c, nb));

        unsafe {
            self.refresh_descriptor_sets();
            if let Some(ref mut oa) = old_a {
                self.destroy_gpu_buffer(oa);
            }
            if let Some(ref mut ob) = old_b {
                self.destroy_gpu_buffer(ob);
            }
            if let Some(ref mut oc) = old_c {
                self.destroy_gpu_buffer(oc);
            }
        }
        Ok(())
    }

    unsafe fn refresh_descriptor_sets(&self) {
        let info_a = VkDescriptorBufferInfo {
            buffer: self.vram_a.buffer,
            offset: 0,
            range: VK_WHOLE_SIZE,
        };
        let info_b = VkDescriptorBufferInfo {
            buffer: self.vram_b.buffer,
            offset: 0,
            range: VK_WHOLE_SIZE,
        };
        let info_c = VkDescriptorBufferInfo {
            buffer: self.vram_c.buffer,
            offset: 0,
            range: VK_WHOLE_SIZE,
        };
        let mk_write =
            |dst_set: VkDescriptorSet, binding: u32, info: *const VkDescriptorBufferInfo| {
                VkWriteDescriptorSet {
                    s_type: VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET,
                    p_next: null(),
                    dst_set,
                    dst_binding: binding,
                    dst_array_element: 0,
                    descriptor_count: 1,
                    descriptor_type: VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                    p_image_info: null(),
                    p_buffer_info: info,
                    p_texel_buffer_view: null(),
                }
            };
        let writes = [
            mk_write(self.ds_1buf_a, 0, &info_a),
            mk_write(self.ds_2buf_ab, 0, &info_a),
            mk_write(self.ds_2buf_ab, 1, &info_b),
            mk_write(self.ds_2buf_ba, 0, &info_b),
            mk_write(self.ds_2buf_ba, 1, &info_a),
            mk_write(self.ds_2buf_aa, 0, &info_a),
            mk_write(self.ds_2buf_aa, 1, &info_a),
            mk_write(self.ds_3buf_abc, 0, &info_a),
            mk_write(self.ds_3buf_abc, 1, &info_b),
            mk_write(self.ds_3buf_abc, 2, &info_c),
        ];
        unsafe {
            (self.fns.update_descriptor_sets)(
                self.device,
                writes.len() as u32,
                writes.as_ptr(),
                0,
                null(),
            );
        }
    }

    /// Resetting the command pool while one of its command buffers is pending is undefined;
    /// only a `Ready` engine may record.
    unsafe fn begin_cmd(&self) -> Result<(), VulkanError> {
        if self.exec_state != EngineExecState::Ready {
            return Err(VulkanError::WorkspacePoisoned);
        }
        if let Some(code) = self.injected_rc(FaultPoint::BeginCmd) {
            return Err(VulkanError::VkResult {
                op: "vkResetCommandPool",
                code,
            });
        }
        check_vk("vkResetCommandPool", unsafe {
            (self.fns.reset_command_pool)(self.device, self.cmd_pool, 0)
        })?;
        let begin_info = VkCommandBufferBeginInfo {
            s_type: VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO,
            p_next: null(),
            flags: VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT,
            p_inheritance_info: null(),
        };
        check_vk("vkBeginCommandBuffer", unsafe {
            (self.fns.begin_command_buffer)(self.cmd_buf, &begin_info)
        })
    }

    unsafe fn cmd_barrier(&self, src_stage: u32, dst_stage: u32, src_access: u32, dst_access: u32) {
        let mb = VkMemoryBarrier {
            s_type: VK_STRUCTURE_TYPE_MEMORY_BARRIER,
            p_next: null(),
            src_access_mask: src_access,
            dst_access_mask: dst_access,
        };
        unsafe {
            (self.fns.cmd_pipeline_barrier)(
                self.cmd_buf,
                src_stage,
                dst_stage,
                0,
                1,
                &mb,
                0,
                null(),
                0,
                null(),
            );
        }
    }

    /// Record zero fills over the VRAM ranges a job used, after its result was copied to
    /// staging. Inputs, intermediates, and outputs may be secret (shares, witness columns,
    /// hash-chain states); none of them stays resident in device memory past a job that ran.
    /// The fills are commands of the job itself: a submission the device lost never reaches
    /// them, and the host has no other way to clear `DEVICE_LOCAL` memory.
    /// Every `bytes` is a multiple of 8 and at most the buffer's capacity.
    unsafe fn cmd_scrub_vram(&self, ranges: &[(VkBuffer, u64)]) {
        unsafe {
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT | VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_READ_BIT
                    | VK_ACCESS_SHADER_WRITE_BIT
                    | VK_ACCESS_TRANSFER_READ_BIT
                    | VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
            );
            for &(buffer, bytes) in ranges {
                if bytes != 0 {
                    (self.fns.cmd_fill_buffer)(self.cmd_buf, buffer, 0, bytes, 0);
                }
            }
        }
    }

    /// Scrub only batch-job VRAM buffers (`vram_a`, `vram_b`, `vram_c`) after a failed batch job
    /// so an active `ProverArena` session and `twiddles_24` are preserved untouched.
    unsafe fn scrub_batch_vram(&mut self) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        if self.cmd_buf.is_null() || self.vram_a.buffer == 0 {
            return Ok(());
        }
        unsafe {
            self.begin_cmd()?;
            self.cmd_scrub_vram(&[
                (self.vram_a.buffer, self.vram_a.capacity),
                (self.vram_b.buffer, self.vram_b.capacity),
                (self.vram_c.buffer, self.vram_c.capacity),
            ]);
            self.submit_and_wait()
        }
    }

    /// Best-effort explicit VRAM wipe after a failed job or before teardown.
    /// Only queue work once completion of all previous submissions is established.
    unsafe fn scrub_all_vram(&mut self) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        if self.cmd_buf.is_null() || self.vram_a.buffer == 0 {
            return Ok(());
        }
        unsafe {
            self.begin_cmd()?;
            self.cmd_scrub_vram(&[
                (self.vram_a.buffer, self.vram_a.capacity),
                (self.vram_b.buffer, self.vram_b.capacity),
                (self.vram_c.buffer, self.vram_c.capacity),
                (
                    self.prover.twiddles_24.buffer,
                    self.prover.twiddles_24.capacity,
                ),
                (
                    self.prover.vram_witness.buffer,
                    self.prover.vram_witness.capacity,
                ),
                (self.prover.vram_mono.buffer, self.prover.vram_mono.capacity),
                (self.prover.vram_cw0.buffer, self.prover.vram_cw0.capacity),
                (
                    self.prover.vram_tree0.buffer,
                    self.prover.vram_tree0.capacity,
                ),
                (
                    self.prover.vram_work_a.buffer,
                    self.prover.vram_work_a.capacity,
                ),
                (
                    self.prover.vram_work_b.buffer,
                    self.prover.vram_work_b.capacity,
                ),
                (
                    self.prover.vram_cw_stage[0].buffer,
                    self.prover.vram_cw_stage[0].capacity,
                ),
                (
                    self.prover.vram_cw_stage[1].buffer,
                    self.prover.vram_cw_stage[1].capacity,
                ),
                (
                    self.prover.vram_tree_stage[0].buffer,
                    self.prover.vram_tree_stage[0].capacity,
                ),
                (
                    self.prover.vram_tree_stage[1].buffer,
                    self.prover.vram_tree_stage[1].capacity,
                ),
                (
                    self.prover.vram_aux_in.buffer,
                    self.prover.vram_aux_in.capacity,
                ),
                (
                    self.prover.vram_aux_b.buffer,
                    self.prover.vram_aux_b.capacity,
                ),
                (
                    self.prover.vram_partials.buffer,
                    self.prover.vram_partials.capacity,
                ),
            ]);
            self.prover.twiddles_ready = false;
            self.prover.invalidate_session();
            self.submit_and_wait()?;
            // Every prover buffer was zeroed over its whole capacity.
            self.prover.scrub_pending = false;
            Ok(())
        }
    }

    /// Scrub all session-bearing buffers in `ProverArena` on session release while retaining
    /// precomputed public `twiddles_24` and buffer allocations for zero-alloc reuse.
    pub(crate) fn scrub_prover_session(&mut self) -> Result<(), VulkanError> {
        // Whatever happens below, nothing may read this session's buffers again until a new
        // round-0 commit re-establishes the arena.
        self.prover.invalidate_session();
        unsafe {
            self.settle_staging();
            self.ensure_ready()?;
        }
        let ranges = self
            .prover
            .session_buffers()
            .map(|b| (b.buffer, b.used.min(b.capacity) & !7));
        if !self.cmd_buf.is_null() && ranges.iter().any(|&(_, bytes)| bytes != 0) {
            unsafe {
                self.begin_cmd()?;
                self.cmd_scrub_vram(&ranges);
                self.submit_and_wait()?;
            }
            for buffer in self.prover.session_buffers() {
                buffer.used = 0;
            }
        }
        self.prover.scrub_pending = false;
        Ok(())
    }

    /// Zero the first `bytes` of the host-mapped staging buffer. Callers reach this only through
    /// `wipe_staging_residue` or teardown, both after device idle was established.
    unsafe fn scrub_staging(&mut self, bytes: u64) {
        if self.staging.mapped.is_null() {
            return;
        }
        unsafe {
            Self::wipe_mapping(self.staging.mapped, bytes.min(self.staging.capacity));
        }
    }

    unsafe fn submit_and_wait(&mut self) -> Result<(), VulkanError> {
        const VK_ERROR_DEVICE_LOST: i32 = -4;
        check_vk("vkEndCommandBuffer", unsafe {
            (self.fns.end_command_buffer)(self.cmd_buf)
        })?;
        check_vk("vkResetFences", unsafe {
            (self.fns.reset_fences)(self.device, 1, &self.fence)
        })?;
        let submit = VkSubmitInfo {
            s_type: VK_STRUCTURE_TYPE_SUBMIT_INFO,
            p_next: null(),
            wait_semaphore_count: 0,
            p_wait_semaphores: null(),
            p_wait_dst_stage_mask: null(),
            command_buffer_count: 1,
            p_command_buffers: &self.cmd_buf,
            signal_semaphore_count: 0,
            p_signal_semaphores: null(),
        };
        // Mark submission in flight BEFORE calling `vkQueueSubmit`; restore `Ready` ONLY after
        // both `vkQueueSubmit` and `vkWaitForFences` return `VK_SUCCESS`.
        self.exec_state = EngineExecState::InFlightQuarantined;
        let submit_rc = match self.injected_rc(FaultPoint::QueueSubmit) {
            Some(rc) => rc,
            None => unsafe { (self.fns.queue_submit)(self.queue, 1, &submit, self.fence) },
        };
        if submit_rc != VK_SUCCESS {
            if submit_rc == VK_ERROR_DEVICE_LOST {
                self.exec_state = EngineExecState::DeviceLostQuarantined;
            }
            return Err(VulkanError::VkResult {
                op: "vkQueueSubmit",
                code: submit_rc,
            });
        }
        let wait_rc = match self.injected_rc(FaultPoint::FenceWait) {
            Some(rc) => rc,
            None => unsafe {
                (self.fns.wait_for_fences)(self.device, 1, &self.fence, VK_TRUE, 5_000_000_000)
            },
        };
        if wait_rc != VK_SUCCESS {
            if wait_rc == VK_ERROR_DEVICE_LOST {
                self.exec_state = EngineExecState::DeviceLostQuarantined;
            }
            return Err(VulkanError::VkResult {
                op: "vkWaitForFences",
                code: wait_rc,
            });
        }
        self.exec_state = EngineExecState::Ready;
        Ok(())
    }

    unsafe fn write_staging_u64s(&mut self, offset_bytes: usize, src: &[u64]) {
        assert!(offset_bytes <= self.staging.capacity as usize);
        assert!(core::mem::size_of_val(src) <= self.staging.capacity as usize - offset_bytes);
        let dst = unsafe { self.staging.mapped.add(offset_bytes) };
        // Little-endian x86_64/aarch64 Linux: `u64` native representation is IEEE/SPIR-V little-endian.
        unsafe {
            core::ptr::copy_nonoverlapping(src.as_ptr().cast::<u8>(), dst, src.len() * 8);
        }
    }

    unsafe fn read_staging_u64s(&self, offset_bytes: usize, dst: &mut [u64]) {
        assert!(offset_bytes <= self.staging.capacity as usize);
        assert!(core::mem::size_of_val(dst) <= self.staging.capacity as usize - offset_bytes);
        let src = unsafe { self.staging.mapped.add(offset_bytes) };
        unsafe {
            core::ptr::copy_nonoverlapping(src, dst.as_mut_ptr().cast::<u8>(), dst.len() * 8);
        }
    }

    // maxStorageBufferRange is u32 bytes. Enforcing it BEFORE staging allocation
    // bounds every shader's u32 element/word index, ceil division, and grid stride.
    fn check_storage_bytes(&self, count: usize, element_bytes: usize) -> Result<(), VulkanError> {
        let bytes = count
            .checked_mul(element_bytes)
            .ok_or(crate::AccelError::LengthOverflow)?;
        if bytes as u64 > self.max_storage_range {
            return Err(VulkanError::BufferExceedsMaxStorageRange {
                requested: bytes as u64,
                limit: self.max_storage_range,
            });
        }
        Ok(())
    }

    /// Extent of one kernel buffer of `count` elements of `elem_bytes` each: the element
    /// count as the `u32` the shader indexes with, and the byte length the copies and scrubs
    /// use. Both are derived here from the slice length the job was handed, after the
    /// `maxStorageBufferRange` check, so no later cast can truncate.
    fn kernel_extent(&self, count: usize, elem_bytes: u64) -> Result<(u32, u64), VulkanError> {
        self.check_storage_bytes(
            count,
            usize::try_from(elem_bytes).map_err(|_| length_overflow())?,
        )?;
        Ok((to_u32(count)?, cmul(to_u64(count), elem_bytes)?))
    }

    /// The buffers a kernel job binds must hold the extents its shader indexes.
    fn kernel_buffers_fit(&self, need_a: u64, need_b: u64, need_c: u64) -> Result<(), VulkanError> {
        for (what, buf, need) in [
            ("vram_a (kernel job)", &self.vram_a, need_a),
            ("vram_b (kernel job)", &self.vram_b, need_b),
            ("vram_c (kernel job)", &self.vram_c, need_c),
        ] {
            if need > 0 && (buf.buffer == 0 || need > buf.capacity) {
                return Err(out_of_range(what, buf.capacity, need));
            }
        }
        Ok(())
    }

    unsafe fn exec_inplace_states<const LANES: usize>(
        &mut self,
        slot: KernelSlot,
        states: &mut [[u64; LANES]],
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let (num_states, byte_len) =
            self.kernel_extent(states.len(), cmul(to_u64(LANES), WORD_BYTES)?)?;
        if num_states == 0 {
            return Ok(());
        }
        // `byte_len` fits the storage range, so the word count fits `usize`.
        let total_words = states.len() * LANES;
        let total_wg = to_u32(u64::from(num_states).div_ceil(64))?;

        unsafe {
            self.reserve_job_staging(byte_len)?;
            self.ensure_vram_buffers(byte_len, 0, 0)?;
            self.kernel_buffers_fit(byte_len, 0, 0)?;

            let flat_in = core::slice::from_raw_parts(states.as_ptr().cast::<u64>(), total_words);
            self.write_staging_u64s(0, flat_in);

            self.begin_cmd()?;
            let copy = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: byte_len,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[slot as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);
            (self.fns.cmd_bind_descriptor_sets)(
                self.cmd_buf,
                VK_PIPELINE_BIND_POINT_COMPUTE,
                kp.pipeline_layout,
                0,
                1,
                &self.ds_1buf_a,
                0,
                null(),
            );

            let mut wg_done = 0u32;
            while wg_done < total_wg {
                let wg_chunk = (total_wg - wg_done).min(self.max_wg_x);
                let pc = BatchStatesPushConsts {
                    num_states,
                    base_state: wg_done * 64,
                    _pad0: 0,
                    _pad1: 0,
                };
                (self.fns.cmd_push_constants)(
                    self.cmd_buf,
                    kp.pipeline_layout,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<BatchStatesPushConsts>() as u32,
                    (&pc as *const BatchStatesPushConsts).cast::<c_void>(),
                );
                (self.fns.cmd_dispatch)(self.cmd_buf, wg_chunk, 1, 1);
                wg_done += wg_chunk;
            }

            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.vram_a.buffer,
                self.staging.buffer,
                1,
                &copy,
            );
            self.cmd_scrub_vram(&[(self.vram_a.buffer, byte_len)]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let flat_out =
                core::slice::from_raw_parts_mut(states.as_mut_ptr().cast::<u64>(), total_words);
            self.read_staging_u64s(0, flat_out);
        }
        Ok(())
    }

    pub(crate) fn exec_batch_keccak(
        &mut self,
        states: &mut [[u64; 25]],
    ) -> Result<(), VulkanError> {
        self.run_job(|engine| unsafe {
            engine.exec_inplace_states(KernelSlot::BatchKeccakF1600, states)
        })
    }

    pub(crate) fn exec_batch_poseidon2(
        &mut self,
        states: &mut [[u64; 12]],
    ) -> Result<(), VulkanError> {
        self.run_job(|engine| unsafe {
            engine.exec_inplace_states(KernelSlot::BatchPoseidon2Perm12, states)
        })
    }

    unsafe fn dispatch_ntt_mode(&self, pl: VkPipelineLayout, total_wg: u32, mut pc: NttPushConsts) {
        let mut wg_done = 0u32;
        while wg_done < total_wg {
            let chunk = (total_wg - wg_done).min(self.max_wg_x);
            pc.base_wg = wg_done;
            unsafe {
                (self.fns.cmd_push_constants)(
                    self.cmd_buf,
                    pl,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<NttPushConsts>() as u32,
                    (&pc as *const NttPushConsts).cast::<c_void>(),
                );
                (self.fns.cmd_dispatch)(self.cmd_buf, chunk, 1, 1);
            }
            wg_done += chunk;
        }
    }

    pub(crate) fn exec_goldilocks_ntt(
        &mut self,
        buf: &mut [u64],
        twiddles: &[u64],
        inverse: bool,
    ) -> Result<(), VulkanError> {
        self.run_job(|engine| engine.job_goldilocks_ntt(buf, twiddles, inverse))
    }

    fn job_goldilocks_ntt(
        &mut self,
        buf: &mut [u64],
        twiddles: &[u64],
        inverse: bool,
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let n = buf.len();
        if !n.is_power_of_two() || (n > 1 && twiddles.len() != n / 2) {
            return Err(VulkanError::Accel(crate::AccelError::LengthOverflow));
        }
        let (n32, byte_len) = self.kernel_extent(n, WORD_BYTES)?;
        let log2_n = n.trailing_zeros();

        unsafe {
            self.reserve_job_staging(byte_len)?;
            self.ensure_vram_buffers(byte_len, 0, 0)?;
            self.kernel_buffers_fit(byte_len, 0, 0)?;
            self.write_staging_u64s(0, buf);

            self.begin_cmd()?;
            let copy = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: byte_len,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::GoldilocksNtt as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);
            (self.fns.cmd_bind_descriptor_sets)(
                self.cmd_buf,
                VK_PIPELINE_BIND_POINT_COMPUTE,
                kp.pipeline_layout,
                0,
                1,
                &self.ds_1buf_a,
                0,
                null(),
            );

            // Stage 0: in-place canonical reduction + bit-reversal permutation (`mode = 0`).
            let wg_full = n32.div_ceil(256);
            self.dispatch_ntt_mode(
                kp.pipeline_layout,
                wg_full,
                NttPushConsts {
                    w_step: 0,
                    n: n32,
                    log2_n,
                    stage: 0,
                    mode: 0,
                    base_wg: 0,
                    _pad: 0,
                },
            );

            if n > 1 {
                let stage_root = |s: u32| -> u64 {
                    if s == 1 {
                        if !inverse {
                            gl_reduce_u64(twiddles[0])
                        } else {
                            1u64
                        }
                    } else {
                        let step = n >> s;
                        if !inverse {
                            gl_reduce_u64(twiddles[step])
                        } else {
                            gl_neg(gl_reduce_u64(twiddles[n / 2 - step]))
                        }
                    }
                };

                // The caller has checked the table with `check_goldilocks_twiddles`, so the
                // stage-9 root has order 512 and the fused LDS pass applies whenever it fits.
                let start_stage = if log2_n >= 9 {
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    let wg_blocks = n32 >> 9;
                    self.dispatch_ntt_mode(
                        kp.pipeline_layout,
                        wg_blocks,
                        NttPushConsts {
                            w_step: stage_root(9),
                            n: n32,
                            log2_n,
                            stage: 9,
                            mode: 1,
                            base_wg: 0,
                            _pad: 0,
                        },
                    );
                    10u32
                } else {
                    1u32
                };

                let wg_half = (n32 >> 1).div_ceil(256);
                for s in start_stage..=log2_n {
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    self.dispatch_ntt_mode(
                        kp.pipeline_layout,
                        wg_half,
                        NttPushConsts {
                            w_step: stage_root(s),
                            n: n32,
                            log2_n,
                            stage: s,
                            mode: 2,
                            base_wg: 0,
                            _pad: 0,
                        },
                    );
                }

                if inverse {
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    self.dispatch_ntt_mode(
                        kp.pipeline_layout,
                        wg_full,
                        NttPushConsts {
                            w_step: gl_inv_or_zero(n as u64),
                            n: n32,
                            log2_n,
                            stage: 0,
                            mode: 3,
                            base_wg: 0,
                            _pad: 0,
                        },
                    );
                }
            }

            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.vram_a.buffer,
                self.staging.buffer,
                1,
                &copy,
            );
            self.cmd_scrub_vram(&[(self.vram_a.buffer, byte_len)]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;
            self.read_staging_u64s(0, buf);
        }
        Ok(())
    }

    pub(crate) fn exec_goldilocks_ntt_canonical(
        &mut self,
        buf: &mut [u64],
        inverse: bool,
    ) -> Result<(), VulkanError> {
        self.run_job(|engine| engine.job_goldilocks_ntt_canonical(buf, inverse))
    }

    fn job_goldilocks_ntt_canonical(
        &mut self,
        buf: &mut [u64],
        inverse: bool,
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let n = buf.len();
        if !n.is_power_of_two() {
            return Err(VulkanError::Accel(crate::AccelError::NotPowerOfTwo {
                what: "NTT input",
                len: n,
            }));
        }
        let log2_n = n.trailing_zeros();
        let (n32, byte_len) = self.kernel_extent(n, WORD_BYTES)?;
        let stage_root = |s: u32| -> Result<u64, VulkanError> {
            let r = goldilocks_primitive_root(s).map_err(VulkanError::Accel)?;
            Ok(if inverse { gl_inv_or_zero(r) } else { r })
        };

        unsafe {
            self.reserve_job_staging(byte_len)?;
            self.ensure_vram_buffers(byte_len, 0, 0)?;
            self.kernel_buffers_fit(byte_len, 0, 0)?;
            self.write_staging_u64s(0, buf);

            self.begin_cmd()?;
            let copy = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: byte_len,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::GoldilocksNtt as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);
            (self.fns.cmd_bind_descriptor_sets)(
                self.cmd_buf,
                VK_PIPELINE_BIND_POINT_COMPUTE,
                kp.pipeline_layout,
                0,
                1,
                &self.ds_1buf_a,
                0,
                null(),
            );

            let wg_full = n32.div_ceil(256);
            self.dispatch_ntt_mode(
                kp.pipeline_layout,
                wg_full,
                NttPushConsts {
                    w_step: 0,
                    n: n32,
                    log2_n,
                    stage: 0,
                    mode: 0,
                    base_wg: 0,
                    _pad: 0,
                },
            );

            if n > 1 {
                let start_stage = if log2_n >= 9 {
                    let w9 = stage_root(9)?;
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    self.dispatch_ntt_mode(
                        kp.pipeline_layout,
                        n32 >> 9,
                        NttPushConsts {
                            w_step: w9,
                            n: n32,
                            log2_n,
                            stage: 9,
                            mode: 1,
                            base_wg: 0,
                            _pad: 0,
                        },
                    );
                    10u32
                } else {
                    1u32
                };

                let wg_half = (n32 >> 1).div_ceil(256);
                for s in start_stage..=log2_n {
                    let ws = stage_root(s)?;
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    self.dispatch_ntt_mode(
                        kp.pipeline_layout,
                        wg_half,
                        NttPushConsts {
                            w_step: ws,
                            n: n32,
                            log2_n,
                            stage: s,
                            mode: 2,
                            base_wg: 0,
                            _pad: 0,
                        },
                    );
                }

                if inverse {
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    self.dispatch_ntt_mode(
                        kp.pipeline_layout,
                        wg_full,
                        NttPushConsts {
                            w_step: gl_inv_or_zero(n as u64),
                            n: n32,
                            log2_n,
                            stage: 0,
                            mode: 3,
                            base_wg: 0,
                            _pad: 0,
                        },
                    );
                }
            }

            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.vram_a.buffer,
                self.staging.buffer,
                1,
                &copy,
            );
            self.cmd_scrub_vram(&[(self.vram_a.buffer, byte_len)]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;
            self.read_staging_u64s(0, buf);
        }
        Ok(())
    }

    unsafe fn dispatch_lde_mode(
        &self,
        pl: VkPipelineLayout,
        total_wg: u32,
        mut pc: CosetLdePushConsts,
    ) {
        let mut wg_done = 0u32;
        while wg_done < total_wg {
            let chunk = (total_wg - wg_done).min(self.max_wg_x);
            pc.base_wg = wg_done;
            unsafe {
                (self.fns.cmd_push_constants)(
                    self.cmd_buf,
                    pl,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<CosetLdePushConsts>() as u32,
                    (&pc as *const CosetLdePushConsts).cast::<c_void>(),
                );
                (self.fns.cmd_dispatch)(self.cmd_buf, chunk, 1, 1);
            }
            wg_done += chunk;
        }
    }

    unsafe fn record_ext2_ntt_stages(
        &self,
        pl: VkPipelineLayout,
        len: u32,
        inverse: bool,
    ) -> Result<(), VulkanError> {
        let log2_len = len.trailing_zeros();
        let wg_full = len.div_ceil(256);
        unsafe {
            self.dispatch_lde_mode(
                pl,
                wg_full,
                CosetLdePushConsts {
                    w_step: 0,
                    shift_c: 0,
                    len,
                    aux_n: 0,
                    log2_len,
                    stage: 0,
                    mode: 0,
                    base_wg: 0,
                },
            );
        }
        if len <= 1 {
            return Ok(());
        }

        let start_stage = if log2_len >= 9 {
            let r9 = goldilocks_primitive_root(9).map_err(VulkanError::Accel)?;
            let w9 = if inverse { gl_inv_or_zero(r9) } else { r9 };
            unsafe {
                self.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                self.dispatch_lde_mode(
                    pl,
                    len >> 9,
                    CosetLdePushConsts {
                        w_step: w9,
                        shift_c: 0,
                        len,
                        aux_n: 0,
                        log2_len,
                        stage: 9,
                        mode: 1,
                        base_wg: 0,
                    },
                );
            }
            10u32
        } else {
            1u32
        };

        let wg_half = (len >> 1).div_ceil(256);
        for s in start_stage..=log2_len {
            let root = goldilocks_primitive_root(s).map_err(VulkanError::Accel)?;
            let w_step = if inverse { gl_inv_or_zero(root) } else { root };
            unsafe {
                self.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                self.dispatch_lde_mode(
                    pl,
                    wg_half,
                    CosetLdePushConsts {
                        w_step,
                        shift_c: 0,
                        len,
                        aux_n: 0,
                        log2_len,
                        stage: s,
                        mode: 2,
                        base_wg: 0,
                    },
                );
            }
        }
        Ok(())
    }

    pub(crate) fn exec_coset_lde_ext2(
        &mut self,
        evals: &[[u64; 2]],
        blowup: usize,
        shift: u64,
        out: &mut [[u64; 2]],
    ) -> Result<(), VulkanError> {
        self.run_job(|engine| engine.job_coset_lde_ext2(evals, blowup, shift, out))
    }

    fn job_coset_lde_ext2(
        &mut self,
        evals: &[[u64; 2]],
        blowup: usize,
        shift: u64,
        out: &mut [[u64; 2]],
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let n = evals.len();
        let m = n
            .checked_mul(blowup)
            .ok_or(crate::AccelError::LengthOverflow)?;
        if !n.is_power_of_two() || !blowup.is_power_of_two() || out.len() != m {
            return Err(VulkanError::Accel(crate::AccelError::LengthOverflow));
        }
        let (m32, out_bytes) = self.kernel_extent(m, 2 * WORD_BYTES)?;
        let (n32, in_bytes) = self.kernel_extent(n, 2 * WORD_BYTES)?;

        unsafe {
            self.reserve_job_staging(out_bytes)?;
            self.ensure_vram_buffers(out_bytes, 0, 0)?;
            self.kernel_buffers_fit(out_bytes, 0, 0)?;

            let flat_in = core::slice::from_raw_parts(evals.as_ptr().cast::<u64>(), n * 2);
            self.write_staging_u64s(0, flat_in);

            self.begin_cmd()?;
            let copy_in = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: in_bytes,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy_in,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::CosetLdeExt2 as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);
            (self.fns.cmd_bind_descriptor_sets)(
                self.cmd_buf,
                VK_PIPELINE_BIND_POINT_COMPUTE,
                kp.pipeline_layout,
                0,
                1,
                &self.ds_1buf_a,
                0,
                null(),
            );

            // 1. Inverse NTT of length `n` on both coordinates in VRAM.
            self.record_ext2_ntt_stages(kp.pipeline_layout, n32, true)?;

            // 2. Multiply `[0..n)` by `inv_n * shift^j` and zero-pad `[n..m)` in VRAM.
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );
            let wg_m = m32.div_ceil(256);
            self.dispatch_lde_mode(
                kp.pipeline_layout,
                wg_m,
                CosetLdePushConsts {
                    w_step: gl_inv_or_zero(n as u64),
                    shift_c: gl_reduce_u64(shift),
                    len: m32,
                    aux_n: n32,
                    log2_len: m.trailing_zeros(),
                    stage: 0,
                    mode: 3,
                    base_wg: 0,
                },
            );

            // 3. Forward NTT of length `m` on both coordinates in VRAM.
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );
            self.record_ext2_ntt_stages(kp.pipeline_layout, m32, false)?;

            let copy_out = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: out_bytes,
            };
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.vram_a.buffer,
                self.staging.buffer,
                1,
                &copy_out,
            );
            self.cmd_scrub_vram(&[(self.vram_a.buffer, out_bytes)]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let flat_out = core::slice::from_raw_parts_mut(out.as_mut_ptr().cast::<u64>(), m * 2);
            self.read_staging_u64s(0, flat_out);
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    unsafe fn dispatch_merkle_layer_cmd_ext(
        &self,
        pl: VkPipelineLayout,
        ds: VkDescriptorSet,
        pk_seed: &[u64; 4],
        layer: u32,
        level: u32,
        domain_tag: u64,
        tree_idx: u64,
        mode: u32,
        start_parent_idx: u64,
        in_offset_u64: u64,
        out_offset_u64: u64,
        num_parents: u32,
    ) {
        unsafe {
            (self.fns.cmd_bind_descriptor_sets)(
                self.cmd_buf,
                VK_PIPELINE_BIND_POINT_COMPUTE,
                pl,
                0,
                1,
                &ds,
                0,
                null(),
            );
        }
        let total_wg = num_parents.div_ceil(64);
        let mut wg_done = 0u32;
        while wg_done < total_wg {
            let chunk = (total_wg - wg_done).min(self.max_wg_x);
            let pc = MerklePushConsts {
                s0: pk_seed[0],
                s1: pk_seed[1],
                s2: pk_seed[2],
                s3: pk_seed[3],
                start_parent_idx,
                num_parents: u64::from(num_parents),
                in_offset_u64,
                out_offset_u64,
                domain_tag,
                tree_idx,
                layer,
                base_parent: wg_done * 64,
                level,
                mode,
            };
            unsafe {
                (self.fns.cmd_push_constants)(
                    self.cmd_buf,
                    pl,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<MerklePushConsts>() as u32,
                    (&pc as *const MerklePushConsts).cast::<c_void>(),
                );
                (self.fns.cmd_dispatch)(self.cmd_buf, chunk, 1, 1);
            }
            wg_done += chunk;
        }
    }

    unsafe fn dispatch_merkle_layer_cmd(
        &self,
        pl: VkPipelineLayout,
        ds: VkDescriptorSet,
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        num_parents: u32,
    ) {
        unsafe {
            self.dispatch_merkle_layer_cmd_ext(
                pl,
                ds,
                pk_seed,
                layer,
                0,
                0,
                0,
                0,
                start_parent_idx,
                0,
                0,
                num_parents,
            );
        }
    }

    pub(crate) fn exec_merkle_layer(
        &mut self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.run_job(|engine| {
            engine.job_merkle_layer(children, pk_seed, layer, start_parent_idx, out_parents)
        })
    }

    fn job_merkle_layer(
        &mut self,
        children: &[[u64; 4]],
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let num_parents = out_parents.len();
        if num_parents.checked_mul(2) != Some(children.len()) {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        let (_, in_bytes) = self.kernel_extent(children.len(), 4 * WORD_BYTES)?;
        let (parents32, out_bytes) = self.kernel_extent(num_parents, 4 * WORD_BYTES)?;
        let max_parent_idx = if num_parents == 0 {
            start_parent_idx
        } else {
            start_parent_idx
                .checked_add((num_parents - 1) as u64)
                .ok_or(VulkanError::Accel(crate::AccelError::LengthOverflow))?
        };
        if max_parent_idx > u32::MAX as u64 {
            return Err(VulkanError::Accel(crate::AccelError::LengthOverflow));
        }
        if num_parents == 0 {
            return Ok(());
        }

        unsafe {
            self.reserve_job_staging(in_bytes)?;
            self.ensure_vram_buffers(in_bytes, out_bytes, 0)?;
            self.kernel_buffers_fit(in_bytes, out_bytes, 0)?;

            let flat_in =
                core::slice::from_raw_parts(children.as_ptr().cast::<u64>(), children.len() * 4);
            self.write_staging_u64s(0, flat_in);

            self.begin_cmd()?;
            let copy_in = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: in_bytes,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy_in,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::MerkleLayerPoseidon2 as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);
            self.dispatch_merkle_layer_cmd(
                kp.pipeline_layout,
                self.ds_2buf_ab,
                pk_seed,
                layer,
                start_parent_idx,
                parents32,
            );

            let copy_out = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: out_bytes,
            };
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.vram_b.buffer,
                self.staging.buffer,
                1,
                &copy_out,
            );
            self.cmd_scrub_vram(&[
                (self.vram_a.buffer, in_bytes),
                (self.vram_b.buffer, out_bytes),
            ]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let flat_out = core::slice::from_raw_parts_mut(
                out_parents.as_mut_ptr().cast::<u64>(),
                num_parents * 4,
            );
            self.read_staging_u64s(0, flat_out);
        }
        Ok(())
    }

    pub(crate) fn exec_merkle_full_tree(
        &mut self,
        leaves: &[[u64; 4]],
        pk_seed: &[u64; 4],
        base_layer: u32,
    ) -> Result<[u64; 4], VulkanError> {
        self.run_job(|engine| engine.job_merkle_full_tree(leaves, pk_seed, base_layer))
    }

    fn job_merkle_full_tree(
        &mut self,
        leaves: &[[u64; 4]],
        pk_seed: &[u64; 4],
        base_layer: u32,
    ) -> Result<[u64; 4], VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let num_leaves = leaves.len();
        if !num_leaves.is_power_of_two() {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        let (leaves32, leaf_bytes) = self.kernel_extent(num_leaves, 4 * WORD_BYTES)?;
        if num_leaves == 1 {
            return Ok([
                gl_reduce_u64(leaves[0][0]),
                gl_reduce_u64(leaves[0][1]),
                gl_reduce_u64(leaves[0][2]),
                gl_reduce_u64(leaves[0][3]),
            ]);
        }
        let height = num_leaves.trailing_zeros();
        // Level `lvl` is tweaked with `base_layer + lvl`: a wrapped sum would hash the top of
        // the tree under another layer's domain.
        if base_layer.checked_add(height - 1).is_none() {
            return Err(length_overflow());
        }
        let half_bytes = leaf_bytes / 2;

        unsafe {
            self.reserve_job_staging(leaf_bytes)?;
            self.ensure_vram_buffers(leaf_bytes, half_bytes, 0)?;
            self.kernel_buffers_fit(leaf_bytes, half_bytes, 0)?;

            let flat_in =
                core::slice::from_raw_parts(leaves.as_ptr().cast::<u64>(), num_leaves * 4);
            self.write_staging_u64s(0, flat_in);

            self.begin_cmd()?;
            let copy_in = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: leaf_bytes,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy_in,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::MerkleLayerPoseidon2 as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);

            for lvl in 0..height {
                if lvl > 0 {
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                }
                let ds = if lvl % 2 == 0 {
                    self.ds_2buf_ab
                } else {
                    self.ds_2buf_ba
                };
                let cur_parents = leaves32 >> (lvl + 1);
                self.dispatch_merkle_layer_cmd(
                    kp.pipeline_layout,
                    ds,
                    pk_seed,
                    base_layer + lvl,
                    0,
                    cur_parents,
                );
            }

            let root_buf = if (height - 1).is_multiple_of(2) {
                self.vram_b.buffer
            } else {
                self.vram_a.buffer
            };
            let copy_root = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: 32,
            };
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(self.cmd_buf, root_buf, self.staging.buffer, 1, &copy_root);
            self.cmd_scrub_vram(&[
                (self.vram_a.buffer, leaf_bytes),
                (self.vram_b.buffer, half_bytes),
            ]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let mut root = [0u64; 4];
            self.read_staging_u64s(0, &mut root);
            Ok(root)
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn exec_merkle_layer_mode(
        &mut self,
        children: &[[u64; 4]],
        s_words: &[u64; 4],
        layer: u32,
        level: u32,
        domain_tag: u64,
        tree_idx: u64,
        mode: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.run_job(|engine| {
            engine.job_merkle_layer_mode(
                children,
                s_words,
                layer,
                level,
                domain_tag,
                tree_idx,
                mode,
                start_parent_idx,
                out_parents,
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn job_merkle_layer_mode(
        &mut self,
        children: &[[u64; 4]],
        s_words: &[u64; 4],
        layer: u32,
        level: u32,
        domain_tag: u64,
        tree_idx: u64,
        mode: u32,
        start_parent_idx: u64,
        out_parents: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let num_parents = out_parents.len();
        if num_parents.checked_mul(2) != Some(children.len()) {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        if mode == 1 && (layer > 0xFFFE || level > 0xFFFF) {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        let (_, in_bytes) = self.kernel_extent(children.len(), 4 * WORD_BYTES)?;
        let (parents32, out_bytes) = self.kernel_extent(num_parents, 4 * WORD_BYTES)?;
        let max_parent_idx = if num_parents == 0 {
            start_parent_idx
        } else {
            start_parent_idx
                .checked_add((num_parents - 1) as u64)
                .ok_or(VulkanError::Accel(crate::AccelError::LengthOverflow))?
        };
        if max_parent_idx > u32::MAX as u64 {
            return Err(VulkanError::Accel(crate::AccelError::LengthOverflow));
        }
        if num_parents == 0 {
            return Ok(());
        }

        unsafe {
            self.reserve_job_staging(in_bytes)?;
            self.ensure_vram_buffers(in_bytes, out_bytes, 0)?;
            self.kernel_buffers_fit(in_bytes, out_bytes, 0)?;

            let flat_in =
                core::slice::from_raw_parts(children.as_ptr().cast::<u64>(), children.len() * 4);
            self.write_staging_u64s(0, flat_in);

            self.begin_cmd()?;
            let copy_in = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: in_bytes,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy_in,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::MerkleLayerPoseidon2 as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);
            self.dispatch_merkle_layer_cmd_ext(
                kp.pipeline_layout,
                self.ds_2buf_ab,
                s_words,
                layer,
                level,
                domain_tag,
                tree_idx,
                mode,
                start_parent_idx,
                0,
                0,
                parents32,
            );

            let copy_out = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: out_bytes,
            };
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.vram_b.buffer,
                self.staging.buffer,
                1,
                &copy_out,
            );
            self.cmd_scrub_vram(&[
                (self.vram_a.buffer, in_bytes),
                (self.vram_b.buffer, out_bytes),
            ]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let flat_out = core::slice::from_raw_parts_mut(
                out_parents.as_mut_ptr().cast::<u64>(),
                num_parents * 4,
            );
            self.read_staging_u64s(0, flat_out);
        }
        Ok(())
    }

    pub(crate) fn exec_merkle_full_tree_2block(
        &mut self,
        leaves: &[[u64; 4]],
        domain_tag: u64,
        pk_seed: &[u64; 4],
        layer: u32,
        tree_idx: u64,
        base_level: u32,
    ) -> Result<[u64; 4], VulkanError> {
        self.run_job(|engine| {
            engine.job_merkle_full_tree_2block(
                leaves, domain_tag, pk_seed, layer, tree_idx, base_level,
            )
        })
    }

    fn job_merkle_full_tree_2block(
        &mut self,
        leaves: &[[u64; 4]],
        domain_tag: u64,
        pk_seed: &[u64; 4],
        layer: u32,
        tree_idx: u64,
        base_level: u32,
    ) -> Result<[u64; 4], VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let num_leaves = leaves.len();
        if !num_leaves.is_power_of_two() || layer > 0xFFFE {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        let (leaves32, leaf_bytes) = self.kernel_extent(num_leaves, 4 * WORD_BYTES)?;
        if num_leaves == 1 {
            if base_level > 0xFFFF {
                return Err(length_overflow());
            }
            return Ok([
                gl_reduce_u64(leaves[0][0]),
                gl_reduce_u64(leaves[0][1]),
                gl_reduce_u64(leaves[0][2]),
                gl_reduce_u64(leaves[0][3]),
            ]);
        }
        let height = num_leaves.trailing_zeros();
        let Some(max_lvl) = base_level.checked_add(height - 1) else {
            return Err(length_overflow());
        };
        if max_lvl > 0xFFFF {
            return Err(length_overflow());
        }
        let half_bytes = leaf_bytes / 2;

        unsafe {
            self.reserve_job_staging(leaf_bytes)?;
            self.ensure_vram_buffers(leaf_bytes, half_bytes, 0)?;
            self.kernel_buffers_fit(leaf_bytes, half_bytes, 0)?;

            let flat_in =
                core::slice::from_raw_parts(leaves.as_ptr().cast::<u64>(), num_leaves * 4);
            self.write_staging_u64s(0, flat_in);

            self.begin_cmd()?;
            let copy_in = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: leaf_bytes,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy_in,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::MerkleLayerPoseidon2 as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);

            for lvl in 0..height {
                if lvl > 0 {
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                }
                let ds = if lvl % 2 == 0 {
                    self.ds_2buf_ab
                } else {
                    self.ds_2buf_ba
                };
                let cur_parents = leaves32 >> (lvl + 1);
                self.dispatch_merkle_layer_cmd_ext(
                    kp.pipeline_layout,
                    ds,
                    pk_seed,
                    layer,
                    base_level + lvl,
                    domain_tag,
                    tree_idx,
                    1,
                    0,
                    0,
                    0,
                    cur_parents,
                );
            }

            let root_buf = if (height - 1).is_multiple_of(2) {
                self.vram_b.buffer
            } else {
                self.vram_a.buffer
            };
            let copy_root = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: 32,
            };
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(self.cmd_buf, root_buf, self.staging.buffer, 1, &copy_root);
            self.cmd_scrub_vram(&[
                (self.vram_a.buffer, leaf_bytes),
                (self.vram_b.buffer, half_bytes),
            ]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let mut root = [0u64; 4];
            self.read_staging_u64s(0, &mut root);
            Ok(root)
        }
    }

    /// Build a complete 1-indexed binary heap Canopy Merkle tree (`out_nodes.len() == 2 * leaves.len()`)
    /// in `vram_a` within ONE `VkCommandBuffer` submission (`mode == 2`: Poseidon2 WHIR Canopy Jive;
    /// `mode == 1`: 2-block Poseidon2 node sponge).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn exec_canopy_tree_poseidon2(
        &mut self,
        leaves: &[[u64; 4]],
        s_words: &[u64; 4],
        layer: u32,
        domain_tag: u64,
        tree_idx: u64,
        mode: u32,
        out_nodes: &mut [[u64; 4]],
    ) -> Result<[u64; 4], VulkanError> {
        self.run_job(|engine| {
            engine.job_canopy_tree_poseidon2(
                leaves, s_words, layer, domain_tag, tree_idx, mode, out_nodes,
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn job_canopy_tree_poseidon2(
        &mut self,
        leaves: &[[u64; 4]],
        s_words: &[u64; 4],
        layer: u32,
        domain_tag: u64,
        tree_idx: u64,
        mode: u32,
        out_nodes: &mut [[u64; 4]],
    ) -> Result<[u64; 4], VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let num_leaves = leaves.len();
        if !num_leaves.is_power_of_two() || num_leaves == 0 {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        let total_nodes = num_leaves
            .checked_mul(2)
            .ok_or(crate::AccelError::LengthOverflow)?;
        if out_nodes.len() != total_nodes {
            return Err(crate::AccelError::LengthMismatch {
                what: "Canopy tree nodes",
                expected: total_nodes,
                actual: out_nodes.len(),
            }
            .into());
        }
        let log_leaves = num_leaves.trailing_zeros();
        if mode == 1 && (layer > 0xFFFE || log_leaves > 0x10000) {
            return Err(length_overflow());
        }
        let (_, total_bytes) = self.kernel_extent(total_nodes, 4 * WORD_BYTES)?;
        let (_, leaf_bytes) = self.kernel_extent(num_leaves, 4 * WORD_BYTES)?;
        if num_leaves == 1 {
            let top = [
                gl_reduce_u64(leaves[0][0]),
                gl_reduce_u64(leaves[0][1]),
                gl_reduce_u64(leaves[0][2]),
                gl_reduce_u64(leaves[0][3]),
            ];
            out_nodes[0] = [0u64; 4];
            out_nodes[1] = top;
            return Ok(top);
        }

        unsafe {
            self.reserve_job_staging(total_bytes)?;
            self.ensure_vram_buffers(total_bytes, 0, 0)?;
            self.kernel_buffers_fit(total_bytes, 0, 0)?;

            let flat_leaves =
                core::slice::from_raw_parts(leaves.as_ptr().cast::<u64>(), num_leaves * 4);
            self.write_staging_u64s(0, flat_leaves);

            self.begin_cmd()?;
            let copy_in = VkBufferCopy {
                src_offset: 0,
                dst_offset: leaf_bytes,
                size: leaf_bytes,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy_in,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::MerkleLayerPoseidon2 as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);

            for depth in (0..log_leaves).rev() {
                if depth + 1 < log_leaves {
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                }
                let half = 1u32 << depth;
                let level = log_leaves - 1 - depth;
                let start_idx = if mode == 2 { u64::from(half) } else { 0 };
                self.dispatch_merkle_layer_cmd_ext(
                    kp.pipeline_layout,
                    self.ds_2buf_aa,
                    s_words,
                    layer,
                    level,
                    domain_tag,
                    tree_idx,
                    mode,
                    start_idx,
                    u64::from(half) * 8,
                    u64::from(half) * 4,
                    half,
                );
            }

            let copy_all = VkBufferCopy {
                src_offset: 32,
                dst_offset: 32,
                size: total_bytes - 32,
            };
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.vram_a.buffer,
                self.staging.buffer,
                1,
                &copy_all,
            );
            self.cmd_scrub_vram(&[(self.vram_a.buffer, total_bytes)]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let flat_out = core::slice::from_raw_parts_mut(
                out_nodes[1..].as_mut_ptr().cast::<u64>(),
                (total_nodes - 1) * 4,
            );
            self.read_staging_u64s(32, flat_out);
            out_nodes[0] = [0u64; 4];
            Ok(out_nodes[1])
        }
    }

    pub(crate) fn exec_bdoz_gf2_128_dot(
        &mut self,
        shares: &[(u128, u128)],
        weights: &[(u128, u128)],
    ) -> Result<(u128, u128), VulkanError> {
        self.run_job(|engine| engine.job_bdoz_gf2_128_dot(shares, weights))
    }

    fn job_bdoz_gf2_128_dot(
        &mut self,
        shares: &[(u128, u128)],
        weights: &[(u128, u128)],
    ) -> Result<(u128, u128), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let n = shares.len();
        if weights.len() != n {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        let (n32, vec_bytes) = self.kernel_extent(n, 4 * WORD_BYTES)?;
        if n == 0 {
            return Ok((0, 0));
        }
        let staging_bytes = cmul(vec_bytes, 2)?;
        // Mode 0 strides each of `num_groups * 256` invocations over the whole input and
        // writes one partial per group; mode 1 folds at most 1024 partials in one group.
        let num_groups = n32.div_ceil(256).min(1024).min(self.max_wg_x);
        let partials_bytes = cmul(u64::from(num_groups), 4 * WORD_BYTES)?;

        unsafe {
            self.reserve_job_staging(staging_bytes)?;
            self.ensure_vram_buffers(vec_bytes, vec_bytes, partials_bytes)?;
            self.kernel_buffers_fit(vec_bytes, vec_bytes, partials_bytes)?;

            // Pack `(s0, s1)` and `(w0, w1)` deterministically as `[lo64, hi64, lo64, hi64]`.
            // Mapped allocation need not be initialized: raw writes avoid constructing
            // references to indeterminate u64 values before every input word is stored.
            let dst_u64 = self.staging.mapped.cast::<u64>();
            for (i, &(s0, s1)) in shares.iter().enumerate() {
                let b = i * 4;
                dst_u64.add(b).write(s0 as u64);
                dst_u64.add(b + 1).write((s0 >> 64) as u64);
                dst_u64.add(b + 2).write(s1 as u64);
                dst_u64.add(b + 3).write((s1 >> 64) as u64);
            }
            let w_off = n * 4;
            for (i, &(w0, w1)) in weights.iter().enumerate() {
                let b = w_off + i * 4;
                dst_u64.add(b).write(w0 as u64);
                dst_u64.add(b + 1).write((w0 >> 64) as u64);
                dst_u64.add(b + 2).write(w1 as u64);
                dst_u64.add(b + 3).write((w1 >> 64) as u64);
            }

            self.begin_cmd()?;
            let copy_s = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: vec_bytes,
            };
            let copy_w = VkBufferCopy {
                src_offset: vec_bytes,
                dst_offset: 0,
                size: vec_bytes,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_a.buffer,
                1,
                &copy_s,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.staging.buffer,
                self.vram_b.buffer,
                1,
                &copy_w,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            let kp = self.pipelines[KernelSlot::BdozGf2128BatchDot as usize];
            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);
            (self.fns.cmd_bind_descriptor_sets)(
                self.cmd_buf,
                VK_PIPELINE_BIND_POINT_COMPUTE,
                kp.pipeline_layout,
                0,
                1,
                &self.ds_3buf_abc,
                0,
                null(),
            );

            let pc0 = BdozDotPushConsts {
                num_elements: n32,
                num_groups,
                mode: 0,
                _pad: 0,
            };
            (self.fns.cmd_push_constants)(
                self.cmd_buf,
                kp.pipeline_layout,
                VK_SHADER_STAGE_COMPUTE_BIT,
                0,
                size_of::<BdozDotPushConsts>() as u32,
                (&pc0 as *const BdozDotPushConsts).cast::<c_void>(),
            );
            (self.fns.cmd_dispatch)(self.cmd_buf, num_groups, 1, 1);

            if num_groups > 1 {
                self.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                let pc1 = BdozDotPushConsts {
                    num_elements: n32,
                    num_groups,
                    mode: 1,
                    _pad: 0,
                };
                (self.fns.cmd_push_constants)(
                    self.cmd_buf,
                    kp.pipeline_layout,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<BdozDotPushConsts>() as u32,
                    (&pc1 as *const BdozDotPushConsts).cast::<c_void>(),
                );
                (self.fns.cmd_dispatch)(self.cmd_buf, 1, 1, 1);
            }

            let copy_out = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: 32,
            };
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.vram_c.buffer,
                self.staging.buffer,
                1,
                &copy_out,
            );
            self.cmd_scrub_vram(&[
                (self.vram_a.buffer, vec_bytes),
                (self.vram_b.buffer, vec_bytes),
                (self.vram_c.buffer, partials_bytes),
            ]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let mut res = [0u64; 4];
            self.read_staging_u64s(0, &mut res);
            let lane0 = (res[0] as u128) | ((res[1] as u128) << 64);
            let lane1 = (res[2] as u128) | ((res[3] as u128) << 64);
            Ok((lane0, lane1))
        }
    }

    fn run_prover_job<T>(
        &mut self,
        job: impl FnOnce(&mut Self) -> Result<T, VulkanError>,
    ) -> Result<T, VulkanError> {
        struct SettleProverOnExit<'a>(&'a mut RawVulkanEngine, bool);
        impl SettleProverOnExit<'_> {
            fn engine(&mut self) -> &mut RawVulkanEngine {
                self.0
            }
        }
        impl Drop for SettleProverOnExit<'_> {
            fn drop(&mut self) {
                if self.1 {
                    // Invalidate even when idle cannot yet be established: the partial job
                    // may have overwritten session data before its fence failed.
                    self.0.prover.invalidate_session();
                }
                unsafe {
                    self.0.settle_staging();
                    if self.1 && self.0.exec_state == EngineExecState::Ready {
                        let _ = self.0.scrub_prover_session();
                    }
                }
            }
        }
        unsafe {
            self.ensure_ready()?;
        }
        let mut guard = SettleProverOnExit(self, true);
        if guard.0.prover.scrub_pending {
            guard.0.scrub_prover_session()?;
        }
        let res = job(guard.engine());
        guard.1 = res.is_err();
        drop(guard);
        res
    }

    /// Reserve `required` bytes of scratch in one prover buffer for the job being started,
    /// replacing the buffer with a larger one if needed. The contents of a replaced buffer are
    /// NOT carried over: use this only for a buffer the job is about to write, never for one it
    /// reads (those go through [`GpuBuffer::check_read`]).
    ///
    /// A replacement is zero-filled, and the displaced buffer's session extent is zero-filled,
    /// in one submission before the old buffer is freed. If that submission does not complete,
    /// the old buffer stays installed, the new one is parked in `limbo` (the device may still
    /// reference it), and the call fails.
    unsafe fn ensure_one_prover_buf(
        &mut self,
        slot_offset: fn(&mut ProverArena) -> &mut GpuBuffer,
        required: u64,
    ) -> Result<bool, VulkanError> {
        // Defence in depth: never allocate, free or resubmit while a submission may be live.
        if self.exec_state != EngineExecState::Ready {
            return Err(VulkanError::WorkspacePoisoned);
        }
        let req = required.max(MIN_BUFFER_ALLOC_BYTES);
        let cur_snap = {
            let cur = slot_offset(&mut self.prover);
            GpuBuffer {
                buffer: cur.buffer,
                memory: cur.memory,
                capacity: cur.capacity,
                used: cur.used,
                mapped: cur.mapped,
            }
        };
        let grew = if let Some(tgt) = self.plan_vram_growth(&cur_snap, req)? {
            let mut new_buf = unsafe { self.alloc_gpu_buffer(tgt, false)? };
            let scrubbed = unsafe {
                self.begin_cmd().and_then(|()| {
                    self.cmd_scrub_vram(&[
                        (new_buf.buffer, new_buf.capacity & !7),
                        (cur_snap.buffer, cur_snap.used.min(cur_snap.capacity) & !7),
                    ]);
                    self.submit_and_wait()
                })
            };
            if let Err(e) = scrubbed {
                if self.exec_state == EngineExecState::Ready {
                    unsafe {
                        self.destroy_gpu_buffer(&mut new_buf);
                    }
                } else {
                    self.prover.limbo.push(new_buf);
                }
                return Err(e);
            }
            let mut old = core::mem::replace(slot_offset(&mut self.prover), new_buf);
            self.prover.descriptors_dirty = true;
            unsafe {
                self.destroy_gpu_buffer(&mut old);
            }
            true
        } else {
            false
        };
        let slot = slot_offset(&mut self.prover);
        let aligned_req = req.saturating_add(7) & !7;
        slot.used = slot.used.max(aligned_req).min(slot.capacity);
        Ok(grew)
    }

    /// The session established by a round-0 commit, or a clean error. Every prover entry point
    /// other than the commit calls this before it validates ranges or records a command.
    fn prover_session(&self) -> Result<ProverSessionDims, VulkanError> {
        if self.exec_state != EngineExecState::Ready {
            return Err(VulkanError::WorkspacePoisoned);
        }
        self.prover.session.ok_or_else(|| {
            out_of_range("prover session arena (no committed round-0 witness)", 1, 0)
        })
    }

    /// Reject a workgroup count the device cannot dispatch in one call.
    fn check_wg_count(&self, count: u64) -> Result<u32, VulkanError> {
        if count == 0 || count > u64::from(self.max_wg_x) {
            return Err(VulkanError::UnsupportedDeviceLimits);
        }
        to_u32(count)
    }

    #[allow(clippy::too_many_arguments)]
    unsafe fn ensure_prover_arena(
        &mut self,
        req_witness: u64,
        req_mono: u64,
        req_cw0: u64,
        req_tree0: u64,
        req_work_a: u64,
        req_work_b: u64,
        req_cw_stage: u64,
        req_tree_stage: u64,
        req_aux_in: u64,
        req_aux_b: u64,
        req_partials: u64,
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let mut first_init = false;
        if !self.prover.initialized {
            let pool_size = VkDescriptorPoolSize {
                ty: VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                descriptor_count: 60,
            };
            let dp_info = VkDescriptorPoolCreateInfo {
                s_type: VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO,
                p_next: null(),
                flags: 0,
                max_sets: 10,
                pool_size_count: 1,
                p_pool_sizes: &pool_size,
            };
            check_vk("vkCreateDescriptorPool(prover)", unsafe {
                (self.fns.create_descriptor_pool)(
                    self.device,
                    &dp_info,
                    null(),
                    &mut self.prover.desc_pool,
                )
            })?;
            let layouts = [self.dsl_6buf; 10];
            let mut sets = [0u64; 10];
            let dsa = VkDescriptorSetAllocateInfo {
                s_type: VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO,
                p_next: null(),
                descriptor_pool: self.prover.desc_pool,
                descriptor_set_count: 10,
                p_set_layouts: layouts.as_ptr(),
            };
            if let Err(e) = check_vk("vkAllocateDescriptorSets(prover)", unsafe {
                (self.fns.allocate_descriptor_sets)(self.device, &dsa, sets.as_mut_ptr())
            }) {
                unsafe {
                    (self.fns.destroy_descriptor_pool)(self.device, self.prover.desc_pool, null());
                }
                self.prover.desc_pool = 0;
                return Err(e);
            }
            self.prover.ds_lde_r0 = sets[0];
            self.prover.ds_gather_r0 = sets[1];
            self.prover.ds_lde_stage = [sets[2], sets[3]];
            self.prover.ds_gather_stage = [sets[4], sets[5]];
            self.prover.ds_fold_kronecker = sets[6];
            self.prover.ds_fold_mono = sets[7];
            self.prover.ds_fold_witness = sets[8];
            self.prover.ds_air = sets[9];
            self.prover.initialized = true;
            first_init = true;
        }

        let tw_bytes = (1u64 << 23) * 8;
        let mut changed = first_init;
        unsafe {
            if self.ensure_one_prover_buf(|p| &mut p.twiddles_24, tw_bytes)? {
                self.prover.twiddles_ready = false;
                changed = true;
            }
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_witness, req_witness)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_mono, req_mono)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_cw0, req_cw0)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_tree0, req_tree0)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_work_a, req_work_a)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_work_b, req_work_b)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_cw_stage[0], req_cw_stage)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_cw_stage[1], req_cw_stage)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_tree_stage[0], req_tree_stage)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_tree_stage[1], req_tree_stage)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_aux_in, req_aux_in)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_aux_b, req_aux_b)?;
            changed |= self.ensure_one_prover_buf(|p| &mut p.vram_partials, req_partials)?;
        }

        if changed || self.prover.descriptors_dirty {
            unsafe {
                self.refresh_prover_descriptor_sets()?;
            }
        }
        Ok(())
    }

    /// Rewrite all ten prover descriptor sets. Updating a set that a pending command buffer
    /// uses is undefined, so this refuses unless the engine is `Ready`.
    unsafe fn refresh_prover_descriptor_sets(&mut self) -> Result<(), VulkanError> {
        if self.exec_state != EngineExecState::Ready {
            return Err(VulkanError::WorkspacePoisoned);
        }
        #[cfg(test)]
        {
            let (allocs, refreshes) = self.mutation_counters.get();
            self.mutation_counters.set((allocs, refreshes + 1));
        }
        let mk_info = |buf: &GpuBuffer| VkDescriptorBufferInfo {
            buffer: buf.buffer,
            offset: 0,
            range: VK_WHOLE_SIZE,
        };
        let p = &self.prover;
        let i_tw = mk_info(&p.twiddles_24);
        let i_wit = mk_info(&p.vram_witness);
        let i_mono = mk_info(&p.vram_mono);
        let i_cw0 = mk_info(&p.vram_cw0);
        let i_tr0 = mk_info(&p.vram_tree0);
        let i_wa = mk_info(&p.vram_work_a);
        let i_wb = mk_info(&p.vram_work_b);
        let i_cws0 = mk_info(&p.vram_cw_stage[0]);
        let i_cws1 = mk_info(&p.vram_cw_stage[1]);
        let i_trs0 = mk_info(&p.vram_tree_stage[0]);
        let i_trs1 = mk_info(&p.vram_tree_stage[1]);
        let i_ain = mk_info(&p.vram_aux_in);
        let i_ab = mk_info(&p.vram_aux_b);
        let i_part = mk_info(&p.vram_partials);

        let table: [(VkDescriptorSet, [*const VkDescriptorBufferInfo; 6]); 10] = [
            (
                p.ds_lde_r0,
                [&i_mono, &i_wa, &i_cw0, &i_tw, &i_tr0, &i_part],
            ),
            (
                p.ds_gather_r0,
                [&i_mono, &i_wa, &i_cw0, &i_ain, &i_tr0, &i_part],
            ),
            (
                p.ds_lde_stage[0],
                [&i_wb, &i_cws0, &i_wa, &i_tw, &i_trs0, &i_part],
            ),
            (
                p.ds_lde_stage[1],
                [&i_wb, &i_cws1, &i_wa, &i_tw, &i_trs1, &i_part],
            ),
            (
                p.ds_gather_stage[0],
                [&i_wb, &i_cws0, &i_wa, &i_ain, &i_trs0, &i_part],
            ),
            (
                p.ds_gather_stage[1],
                [&i_wb, &i_cws1, &i_wa, &i_ain, &i_trs1, &i_part],
            ),
            (
                p.ds_fold_kronecker,
                [&i_ain, &i_wa, &i_wb, &i_ain, &i_ab, &i_part],
            ),
            (
                p.ds_fold_mono,
                [&i_mono, &i_wa, &i_wb, &i_ain, &i_ab, &i_part],
            ),
            (
                p.ds_fold_witness,
                [&i_wit, &i_wa, &i_wb, &i_ain, &i_ab, &i_part],
            ),
            (p.ds_air, [&i_wit, &i_wa, &i_ab, &i_ain, &i_wb, &i_part]),
        ];

        let mut writes = [VkWriteDescriptorSet {
            s_type: VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET,
            p_next: null(),
            dst_set: 0,
            dst_binding: 0,
            dst_array_element: 0,
            descriptor_count: 1,
            descriptor_type: VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
            p_image_info: null(),
            p_buffer_info: null(),
            p_texel_buffer_view: null(),
        }; 60];
        let mut cursor = 0usize;
        for (ds, infos) in table {
            for (binding, info_ptr) in infos.into_iter().enumerate() {
                writes[cursor].dst_set = ds;
                writes[cursor].dst_binding = binding as u32;
                writes[cursor].p_buffer_info = info_ptr;
                cursor += 1;
            }
        }
        unsafe {
            (self.fns.update_descriptor_sets)(self.device, 60, writes.as_ptr(), 0, null());
        }
        self.prover.descriptors_dirty = false;
        Ok(())
    }

    unsafe fn dispatch_whir_lde_1d(
        &self,
        pl: VkPipelineLayout,
        total_wg_x: u32,
        wg_y: u32,
        units_per_wg: u32,
        mut pc: WhirLdePushConsts,
    ) {
        let mut done = 0u32;
        while done < total_wg_x {
            let chunk = (total_wg_x - done).min(self.max_wg_x);
            pc.aux3 = done * units_per_wg;
            unsafe {
                (self.fns.cmd_push_constants)(
                    self.cmd_buf,
                    pl,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<WhirLdePushConsts>() as u32,
                    (&pc as *const WhirLdePushConsts).cast::<c_void>(),
                );
                (self.fns.cmd_dispatch)(self.cmd_buf, chunk, wg_y, 1);
            }
            done += chunk;
        }
    }

    unsafe fn dispatch_whir_fold_1d(
        &self,
        pl: VkPipelineLayout,
        total_wg_x: u32,
        wg_y: u32,
        mut pc: WhirFoldPushConsts,
    ) {
        let mut done = 0u32;
        while done < total_wg_x {
            let chunk = (total_wg_x - done).min(self.max_wg_x);
            pc.aux5 = done * 256;
            unsafe {
                (self.fns.cmd_push_constants)(
                    self.cmd_buf,
                    pl,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<WhirFoldPushConsts>() as u32,
                    (&pc as *const WhirFoldPushConsts).cast::<c_void>(),
                );
                (self.fns.cmd_dispatch)(self.cmd_buf, chunk, wg_y, 1);
            }
            done += chunk;
        }
    }

    #[inline]
    fn fp4_add_arr(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
        crate::goldilocks::ext4_add(a, b)
    }

    #[inline]
    fn fp4_mul_arr(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
        crate::goldilocks::ext4_mul(a, b)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn exec_prover_whir_commit_round0_with_mode<F>(
        &mut self,
        turboshake_canopy: bool,
        num_polys: usize,
        salt_seed: &[u8; 32],
        num_vars: usize,
        blowup: usize,
        group_arity: usize,
        max_stage1_domain_ext4: usize,
        max_stage1_groups: usize,
        extra_witness_words: usize,
        fill_chunk: F,
    ) -> Result<([u8; 32], u64), VulkanError>
    where
        F: FnMut(usize, usize, &mut [u64]),
    {
        self.run_prover_job(|engine| {
            engine.job_prover_whir_commit_round0(
                turboshake_canopy,
                num_polys,
                salt_seed,
                num_vars,
                blowup,
                group_arity,
                max_stage1_domain_ext4,
                max_stage1_groups,
                extra_witness_words,
                fill_chunk,
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn job_prover_whir_commit_round0<F>(
        &mut self,
        turboshake_canopy: bool,
        num_polys: usize,
        salt_seed: &[u8; 32],
        num_vars: usize,
        blowup: usize,
        group_arity: usize,
        max_stage1_domain_ext4: usize,
        max_stage1_groups: usize,
        extra_witness_words: usize,
        mut fill_chunk: F,
    ) -> Result<([u8; 32], u64), VulkanError>
    where
        F: FnMut(usize, usize, &mut [u64]),
    {
        // A commit re-establishes the arena; until it succeeds there is no session.
        if self.prover.session.is_some() {
            self.scrub_prover_session()?;
        }
        self.prover.session = None;
        self.prover.air = None;
        self.prover.last_fold_k_dst = None;
        if num_polys == 0
            || num_polys > 255
            || !(2..=26).contains(&num_vars)
            || !blowup.is_power_of_two()
            || blowup < 4
            || !group_arity.is_power_of_two()
            || group_arity == 0
            || group_arity > 128
        {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        let c_len = 1usize << num_vars;
        let domain_len = c_len
            .checked_mul(blowup)
            .ok_or(crate::AccelError::LengthOverflow)?;
        if !domain_len.is_multiple_of(group_arity) {
            return Err(crate::AccelError::LengthOverflow.into());
        }
        let num_groups = domain_len / group_arity;
        let log_d = domain_len.trailing_zeros();
        // These reach push constants and dispatch counts as `u32`.
        to_u32(domain_len)?;
        to_u32(num_polys)?;
        to_u32(blowup)?;

        let total_poly_words = num_polys
            .checked_mul(c_len)
            .ok_or(crate::AccelError::LengthOverflow)?;
        let (c, np, tpw) = (to_u64(c_len), to_u64(num_polys), to_u64(total_poly_words));
        let extra = to_u64(extra_witness_words);
        let req_witness = cmul(cadd(tpw, extra)?, WORD_BYTES)?;
        let req_mono = cmul(tpw, WORD_BYTES)?;
        let req_cw0 = cmul(cmul(np, to_u64(domain_len))?, WORD_BYTES)?;
        let req_tree0 = cmul(cmul(2, to_u64(num_groups))?, EXT4_BYTES)?;
        let batch_sc_ext4 = if num_polys > 1 {
            cadd(tpw, cmul(np, c / 2)?)?
        } else {
            tpw
        };
        // Ping-pong WHIR folding needs `(c + 2)` elements for the Stage-0 polynomial/kernel and
        // `((c / 2) + 2)` elements for the folded half (fits `<= 3.00 GiB < 4 GiB` at `nv = 26`).
        let ping_pong_fold_ext4 = cadd(cadd(c, 2)?, cadd(c / 2, 2)?)?;
        let work_a_ext4 = ping_pong_fold_ext4.max(batch_sc_ext4);
        let req_work_a = cmul(work_a_ext4, EXT4_BYTES)?.max(cmul(4 * c, WORD_BYTES)?);
        let max_shard_half = (extra / 256 / 2).max(1);
        let work_b_ext4 = ping_pong_fold_ext4
            .max(batch_sc_ext4)
            .max(cmul(cmul(8, max_shard_half)?, 12)?);
        let req_work_b = cmul(work_b_ext4, EXT4_BYTES)?;

        // Folded stages alternate between two slots (`stage_idx & 1`). `max_stage1_*` bound
        // every folded stage, and a later stage is not smaller than an earlier one when its
        // blowup grows faster than its variables fold, so each slot holds the largest.
        let req_cw_stage = cmul(to_u64(max_stage1_domain_ext4.max(1024)), EXT4_BYTES)?;
        let req_tree_stage = cmul(cmul(2, to_u64(max_stage1_groups.max(512)))?, EXT4_BYTES)?;
        let req_aux_in = 8 * 1024 * 1024;
        let req_aux_b = cmul(cmul(6, (extra / 256).max(1024))?, EXT4_BYTES)?.max(8 * 1024 * 1024);
        let req_partials = 4 * 1024 * 1024;

        unsafe {
            self.ensure_prover_arena(
                req_witness,
                req_mono,
                req_cw0,
                req_tree0,
                req_work_a,
                req_work_b,
                req_cw_stage,
                req_tree_stage,
                req_aux_in,
                req_aux_b,
                req_partials,
            )?;
        }
        for (i, slot) in self.prover.salt_seed_words.iter_mut().enumerate() {
            let mut b = [0u8; 8];
            b.copy_from_slice(&salt_seed[i * 8..(i + 1) * 8]);
            *slot = u64::from_le_bytes(b);
        }

        const CHUNK_WORDS: usize = 4 * 1024 * 1024; // 32 MiB total staging budget
        const HALF_WORDS: usize = CHUNK_WORDS / 2; // 16 MiB per ping-pong DMA slot
        let staging_cap_words = total_poly_words.clamp(4, CHUNK_WORDS);
        let mut subs = 0u64;

        unsafe {
            self.reserve_job_staging((staging_cap_words as u64) * 8)?;
            if total_poly_words <= HALF_WORDS
                || self.upload_cmd_buf.is_null()
                || self.upload_fence == 0
            {
                let mut dst_word_off = 0usize;
                for poly_idx in 0..num_polys {
                    let mut pos = 0usize;
                    while pos < c_len {
                        let take = (c_len - pos).min(CHUNK_WORDS);
                        {
                            let ptr = self.staging.mapped.cast::<u64>();
                            core::ptr::write_bytes(ptr, 0, take);
                            let dst = core::slice::from_raw_parts_mut(ptr, take);
                            fill_chunk(poly_idx, pos, dst);
                        }
                        self.begin_cmd()?;
                        let copy = VkBufferCopy {
                            src_offset: 0,
                            dst_offset: (dst_word_off as u64) * 8,
                            size: (take as u64) * 8,
                        };
                        (self.fns.cmd_copy_buffer)(
                            self.cmd_buf,
                            self.staging.buffer,
                            self.prover.vram_witness.buffer,
                            1,
                            &copy,
                        );
                        self.submit_and_wait()?;
                        subs += 1;
                        pos += take;
                        dst_word_off += take;
                    }
                }
            } else {
                const VK_ERROR_DEVICE_LOST: i32 = -4;
                if let Some(code) = self.injected_rc(FaultPoint::BeginCmd) {
                    return Err(VulkanError::VkResult {
                        op: "vkResetCommandPool",
                        code,
                    });
                }
                check_vk(
                    "vkResetCommandPool",
                    (self.fns.reset_command_pool)(self.device, self.cmd_pool, 0),
                )?;
                let cbs = [self.cmd_buf, self.upload_cmd_buf];
                let fences = [self.fence, self.upload_fence];
                let mut in_flight = [false, false];
                let mut chunk_idx = 0usize;
                let mut dst_word_off = 0usize;

                let wait_slot = |eng: &mut Self,
                                 in_flight: &mut [bool; 2],
                                 slot: usize|
                 -> Result<(), VulkanError> {
                    if !in_flight[slot] {
                        return Ok(());
                    }
                    let wait_rc = match eng.injected_rc(FaultPoint::FenceWait) {
                        Some(rc) => rc,
                        None => (eng.fns.wait_for_fences)(
                            eng.device,
                            1,
                            &fences[slot],
                            VK_TRUE,
                            5_000_000_000,
                        ),
                    };
                    if wait_rc != VK_SUCCESS {
                        if wait_rc == VK_ERROR_DEVICE_LOST {
                            eng.exec_state = EngineExecState::DeviceLostQuarantined;
                        }
                        return Err(VulkanError::VkResult {
                            op: "vkWaitForFences",
                            code: wait_rc,
                        });
                    }
                    in_flight[slot] = false;
                    if !in_flight[0] && !in_flight[1] {
                        eng.exec_state = EngineExecState::Ready;
                    }
                    Ok(())
                };

                for poly_idx in 0..num_polys {
                    let mut pos = 0usize;
                    while pos < c_len {
                        let slot = chunk_idx & 1;
                        wait_slot(self, &mut in_flight, slot)?;
                        let take = (c_len - pos).min(HALF_WORDS);
                        let src_word_off = slot * HALF_WORDS;
                        {
                            let ptr = self.staging.mapped.cast::<u64>().add(src_word_off);
                            core::ptr::write_bytes(ptr, 0, take);
                            let dst = core::slice::from_raw_parts_mut(ptr, take);
                            fill_chunk(poly_idx, pos, dst);
                        }
                        let begin_info = VkCommandBufferBeginInfo {
                            s_type: VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO,
                            p_next: null(),
                            flags: VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT,
                            p_inheritance_info: null(),
                        };
                        check_vk(
                            "vkBeginCommandBuffer",
                            (self.fns.begin_command_buffer)(cbs[slot], &begin_info),
                        )?;
                        let copy = VkBufferCopy {
                            src_offset: (src_word_off as u64) * 8,
                            dst_offset: (dst_word_off as u64) * 8,
                            size: (take as u64) * 8,
                        };
                        (self.fns.cmd_copy_buffer)(
                            cbs[slot],
                            self.staging.buffer,
                            self.prover.vram_witness.buffer,
                            1,
                            &copy,
                        );
                        check_vk(
                            "vkEndCommandBuffer",
                            (self.fns.end_command_buffer)(cbs[slot]),
                        )?;
                        check_vk(
                            "vkResetFences",
                            (self.fns.reset_fences)(self.device, 1, &fences[slot]),
                        )?;
                        let submit = VkSubmitInfo {
                            s_type: VK_STRUCTURE_TYPE_SUBMIT_INFO,
                            p_next: null(),
                            wait_semaphore_count: 0,
                            p_wait_semaphores: null(),
                            p_wait_dst_stage_mask: null(),
                            command_buffer_count: 1,
                            p_command_buffers: &cbs[slot],
                            signal_semaphore_count: 0,
                            p_signal_semaphores: null(),
                        };
                        self.exec_state = EngineExecState::InFlightQuarantined;
                        let submit_rc = match self.injected_rc(FaultPoint::QueueSubmit) {
                            Some(rc) => rc,
                            None => (self.fns.queue_submit)(self.queue, 1, &submit, fences[slot]),
                        };
                        if submit_rc != VK_SUCCESS {
                            if submit_rc == VK_ERROR_DEVICE_LOST {
                                self.exec_state = EngineExecState::DeviceLostQuarantined;
                            }
                            return Err(VulkanError::VkResult {
                                op: "vkQueueSubmit",
                                code: submit_rc,
                            });
                        }
                        in_flight[slot] = true;
                        subs += 1;
                        chunk_idx += 1;
                        pos += take;
                        dst_word_off += take;
                    }
                }
                let first = chunk_idx & 1;
                wait_slot(self, &mut in_flight, first)?;
                wait_slot(self, &mut in_flight, first ^ 1)?;
            }

            let kp = self.prover_pipelines[ProverKernelSlot::WhirLdeCommitment as usize];
            let omega_24 = goldilocks_primitive_root(24).map_err(VulkanError::Accel)?;
            let omega_d = goldilocks_primitive_root(log_d).map_err(VulkanError::Accel)?;

            self.begin_cmd()?;
            let copy_mono = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: req_mono,
            };
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.prover.vram_witness.buffer,
                self.prover.vram_mono.buffer,
                1,
                &copy_mono,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );

            (self.fns.cmd_bind_pipeline)(self.cmd_buf, VK_PIPELINE_BIND_POINT_COMPUTE, kp.pipeline);
            (self.fns.cmd_bind_descriptor_sets)(
                self.cmd_buf,
                VK_PIPELINE_BIND_POINT_COMPUTE,
                kp.pipeline_layout,
                0,
                1,
                &self.prover.ds_lde_r0,
                0,
                null(),
            );

            if !self.prover.twiddles_ready {
                let tw_len = 1u32 << 23;
                self.dispatch_whir_lde_1d(
                    kp.pipeline_layout,
                    tw_len.div_ceil(256),
                    1,
                    256,
                    WhirLdePushConsts {
                        scalar0: omega_24,
                        scalar1: 0,
                        scalar2: 0,
                        scalar3: 0,
                        mode: 14,
                        len: tw_len,
                        aux0: 0,
                        aux1: 0,
                        aux2: 0,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                self.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
            }

            // 1. Fused <=9-bit Mobius basis conversion across all `num_polys`.
            let wgs_per_poly = (c_len >> 9).max(1) as u32;
            self.dispatch_whir_lde_1d(
                kp.pipeline_layout,
                wgs_per_poly * (num_polys as u32),
                1,
                1,
                WhirLdePushConsts {
                    scalar0: 0,
                    scalar1: 0,
                    scalar2: 0,
                    scalar3: 0,
                    mode: 0,
                    len: c_len as u32,
                    aux0: num_vars as u32,
                    aux1: num_polys as u32,
                    aux2: c_len as u32,
                    aux3: 0,
                    aux4: 0,
                    aux5: 0,
                },
            );
            let mut bit = 9u32;
            let top_bit = num_vars as u32;
            let total_octs = (c_len >> 3) * num_polys;
            while bit + 3 <= top_bit {
                self.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                self.dispatch_whir_lde_1d(
                    kp.pipeline_layout,
                    total_octs.div_ceil(256) as u32,
                    1,
                    256,
                    WhirLdePushConsts {
                        scalar0: 0,
                        scalar1: 0,
                        scalar2: 0,
                        scalar3: 0,
                        mode: 17,
                        len: c_len as u32,
                        aux0: bit,
                        aux1: num_polys as u32,
                        aux2: c_len as u32,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                bit += 3;
            }
            let total_pairs = (c_len >> 1) * num_polys;
            while bit < top_bit {
                self.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                self.dispatch_whir_lde_1d(
                    kp.pipeline_layout,
                    total_pairs.div_ceil(256) as u32,
                    1,
                    256,
                    WhirLdePushConsts {
                        scalar0: 0,
                        scalar1: 0,
                        scalar2: 0,
                        scalar3: 0,
                        mode: 1,
                        len: c_len as u32,
                        aux0: bit,
                        aux1: num_polys as u32,
                        aux2: c_len as u32,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                bit += 1;
            }

            // 2. 4-way coset-decomposed base-field Reed-Solomon LDE into `vram_cw0`.
            for poly_idx in 0..num_polys {
                for r_base in (0..blowup).step_by(4) {
                    let batch_c = (blowup - r_base).min(4) as u32;
                    let s_coset = |off: usize| -> u64 {
                        gl_mul(7, gl_pow_pub(omega_d, (r_base + off) as u64))
                    };
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    self.dispatch_whir_lde_1d(
                        kp.pipeline_layout,
                        c_len.div_ceil(256) as u32,
                        batch_c,
                        256,
                        WhirLdePushConsts {
                            scalar0: s_coset(0),
                            scalar1: s_coset(1),
                            scalar2: s_coset(2),
                            scalar3: s_coset(3),
                            mode: 2,
                            len: c_len as u32,
                            aux0: num_vars as u32,
                            aux1: poly_idx as u32,
                            aux2: c_len as u32,
                            aux3: 0,
                            aux4: batch_c,
                            aux5: 0,
                        },
                    );
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    self.dispatch_whir_lde_1d(
                        kp.pipeline_layout,
                        (c_len >> 9).max(1) as u32,
                        batch_c,
                        1,
                        WhirLdePushConsts {
                            scalar0: 0,
                            scalar1: 0,
                            scalar2: 0,
                            scalar3: 0,
                            mode: 3,
                            len: c_len as u32,
                            aux0: num_vars as u32,
                            aux1: 0,
                            aux2: 0,
                            aux3: 0,
                            aux4: batch_c,
                            aux5: 0,
                        },
                    );
                    let mut stage = 10u32;
                    let top_stage = num_vars as u32;
                    while stage + 2 <= top_stage && stage + 2 <= 24 {
                        self.cmd_barrier(
                            VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                            VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                            VK_ACCESS_SHADER_WRITE_BIT,
                            VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                        );
                        self.dispatch_whir_lde_1d(
                            kp.pipeline_layout,
                            (c_len >> 9) as u32,
                            batch_c,
                            1,
                            WhirLdePushConsts {
                                scalar0: 0,
                                scalar1: 0,
                                scalar2: 0,
                                scalar3: 0,
                                mode: 15,
                                len: c_len as u32,
                                aux0: stage,
                                aux1: 0,
                                aux2: 0,
                                aux3: 0,
                                aux4: batch_c,
                                aux5: 0,
                            },
                        );
                        stage += 3;
                    }
                    while stage <= top_stage {
                        let w_hi = if stage > 24 {
                            goldilocks_primitive_root(stage).map_err(VulkanError::Accel)?
                        } else {
                            0
                        };
                        self.cmd_barrier(
                            VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                            VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                            VK_ACCESS_SHADER_WRITE_BIT,
                            VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                        );
                        self.dispatch_whir_lde_1d(
                            kp.pipeline_layout,
                            (c_len >> 1).div_ceil(256) as u32,
                            batch_c,
                            256,
                            WhirLdePushConsts {
                                scalar0: w_hi,
                                scalar1: 0,
                                scalar2: 0,
                                scalar3: 0,
                                mode: 4,
                                len: c_len as u32,
                                aux0: stage,
                                aux1: 0,
                                aux2: 0,
                                aux3: 0,
                                aux4: batch_c,
                                aux5: 0,
                            },
                        );
                        stage += 1;
                    }
                    self.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    self.dispatch_whir_lde_1d(
                        kp.pipeline_layout,
                        c_len.div_ceil(256) as u32,
                        1,
                        256,
                        WhirLdePushConsts {
                            scalar0: 0,
                            scalar1: 0,
                            scalar2: 0,
                            scalar3: 0,
                            mode: 5,
                            len: c_len as u32,
                            aux0: blowup as u32,
                            aux1: poly_idx as u32,
                            aux2: r_base as u32,
                            aux3: 0,
                            aux4: batch_c,
                            aux5: 0,
                        },
                    );
                }
            }

            // 3. Salted Round-0 Canopy leaves + full internal Merkle tree reduction.
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );
            let turbo_flag = if turboshake_canopy { 0x80u32 } else { 0u32 };
            let salt_w = self.prover.salt_seed_words;
            self.dispatch_whir_lde_1d(
                kp.pipeline_layout,
                num_groups.div_ceil(256) as u32,
                1,
                256,
                WhirLdePushConsts {
                    scalar0: salt_w[0],
                    scalar1: salt_w[1],
                    scalar2: salt_w[2],
                    scalar3: salt_w[3],
                    mode: 9 | turbo_flag,
                    len: num_groups as u32,
                    aux0: group_arity as u32,
                    aux1: num_polys as u32,
                    aux2: 0,
                    aux3: 0,
                    aux4: 0,
                    aux5: 0,
                },
            );
            let mut half = num_groups >> 1;
            while half > 256 {
                self.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                self.dispatch_whir_lde_1d(
                    kp.pipeline_layout,
                    half.div_ceil(256) as u32,
                    1,
                    256,
                    WhirLdePushConsts {
                        scalar0: 0,
                        scalar1: 0,
                        scalar2: 0,
                        scalar3: 0,
                        mode: 11 | turbo_flag,
                        len: half as u32,
                        aux0: 0,
                        aux1: 0,
                        aux2: 0,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                half >>= 1;
            }
            if half >= 1 {
                self.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                self.dispatch_whir_lde_1d(
                    kp.pipeline_layout,
                    1,
                    1,
                    256,
                    WhirLdePushConsts {
                        scalar0: 0,
                        scalar1: 0,
                        scalar2: 0,
                        scalar3: 0,
                        mode: 12 | turbo_flag,
                        len: half as u32,
                        aux0: 0,
                        aux1: 0,
                        aux2: 0,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
            }

            let copy_top = VkBufferCopy {
                src_offset: 32,
                dst_offset: 0,
                size: 32,
            };
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_TRANSFER_READ_BIT,
            );
            (self.fns.cmd_copy_buffer)(
                self.cmd_buf,
                self.prover.vram_tree0.buffer,
                self.staging.buffer,
                1,
                &copy_top,
            );
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;
            subs += 1;
            self.prover.twiddles_ready = true;

            let mut top_words = [0u64; 4];
            self.read_staging_u64s(0, &mut top_words);
            let mut top_node = [0u8; 32];
            for (i, w) in top_words.into_iter().enumerate() {
                top_node[i * 8..(i + 1) * 8].copy_from_slice(&w.to_le_bytes());
            }
            self.prover.session = Some(ProverSessionDims {
                num_polys,
                num_vars,
                turboshake_canopy,
            });
            self.prover.committed_trees[0] = Some(CommittedTree {
                stage_idx: 0,
                group_arity,
                num_groups,
            });
            Ok((top_node, subs))
        }
    }

    /// Extends a 3-byte (`768`-entry) geometric Kronecker table `[xi * z^k0, z^(256*k1), z^(65536*k2)]`
    /// to a 4-byte (`1024`-entry) table `[..., z^(16777216*k3)]` in staging at `byte_offset`.
    /// Entry `768` (`k3 = 0`) is always `[1, 0, 0, 0]`, so arbitrary non-geometric test tables
    /// evaluated at `gid < 2^24` (`k3 = 0`) also remain bit-identical.
    unsafe fn write_geometric_kronecker_as_1024(&mut self, byte_offset: usize, src: &[[u64; 4]]) {
        debug_assert!(src.len() == 768 || src.len() == 1024);
        unsafe {
            if src.len() == 1024 {
                let flat = core::slice::from_raw_parts(src.as_ptr().cast::<u64>(), 1024 * 4);
                self.write_staging_u64s(byte_offset, flat);
            } else {
                let flat_lo = core::slice::from_raw_parts(src.as_ptr().cast::<u64>(), 768 * 4);
                self.write_staging_u64s(byte_offset, flat_lo);
                let z_23 = src[512 + 128];
                let z_24 = Self::fp4_mul_arr(z_23, z_23);
                let mut byte3 = [[0u64; 4]; 256];
                let mut cur = [1u64, 0, 0, 0];
                for slot in &mut byte3 {
                    *slot = cur;
                    cur = Self::fp4_mul_arr(cur, z_24);
                }
                let flat_hi = core::slice::from_raw_parts(byte3.as_ptr().cast::<u64>(), 256 * 4);
                self.write_staging_u64s(byte_offset + 768 * 32, flat_hi);
            }
        }
    }

    pub(crate) fn exec_prover_whir_batch_sumcheck_init(
        &mut self,
        eq_kronecker: &[[u64; 4]],
        lambda_pows: &[[u64; 4]],
        num_vars: usize,
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            let num_polys = lambda_pows.len();
            let is_768 = num_polys.checked_mul(768) == Some(eq_kronecker.len());
            let is_1024 = num_polys.checked_mul(1024) == Some(eq_kronecker.len());
            if num_polys == 0 || (!is_768 && !is_1024) || (is_768 && num_vars > 24) {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            let c_len = pow2_len(num_vars, 26)?;
            let dims = engine.prover_session()?;
            engine.prover.air = None;
            if num_vars != dims.num_vars {
                return Err(out_of_range(
                    "batch sumcheck num_vars (committed session)",
                    to_u64(dims.num_vars),
                    to_u64(num_vars),
                ));
            }
            if num_polys != dims.num_polys {
                return Err(out_of_range(
                    "batch sumcheck num_polys (committed session)",
                    to_u64(dims.num_polys),
                    to_u64(num_polys),
                ));
            }
            let (np, c) = (to_u64(num_polys), to_u64(c_len));
            // One workgroup row per polynomial table.
            engine.check_wg_count(np)?;
            let need_work = cmul(cadd(cmul(np, c)?, cmul(np, c / 2)?)?, EXT4_BYTES)?;
            let eq_entries_1024 = cmul(np, 1024)?;
            let eq_bytes = cmul(eq_entries_1024, EXT4_BYTES)?;
            let lam_bytes = cmul(np, EXT4_BYTES)?;
            let stg_bytes = cadd(eq_bytes, lam_bytes)?;
            // Round 0 reads the committed witness as `num_polys` tables of `c_len` words.
            engine.prover.vram_witness.check_read(
                "vram_witness (batch sumcheck tables)",
                span_end(0, np, c, WORD_BYTES)?,
            )?;
            unsafe {
                engine.ensure_one_prover_buf(|p| &mut p.vram_work_a, need_work)?;
                engine.ensure_one_prover_buf(|p| &mut p.vram_work_b, need_work)?;
                engine.ensure_one_prover_buf(|p| &mut p.vram_aux_in, stg_bytes)?;
                engine.refresh_prover_descriptor_sets()?;
                engine.reserve_job_staging(stg_bytes)?;

                if is_1024 {
                    let eq_flat = core::slice::from_raw_parts(
                        eq_kronecker.as_ptr().cast::<u64>(),
                        eq_kronecker.len() * 4,
                    );
                    engine.write_staging_u64s(0, eq_flat);
                } else {
                    let one_768 = [1u64, 0, 0, 0];
                    let zero_pad = [0u64; 255 * 4];
                    for p in 0..num_polys {
                        let dst_off = p * 1024 * 32;
                        let flat_lo = core::slice::from_raw_parts(
                            eq_kronecker[p * 768..].as_ptr().cast::<u64>(),
                            768 * 4,
                        );
                        engine.write_staging_u64s(dst_off, flat_lo);
                        engine.write_staging_u64s(dst_off + 768 * 32, &one_768);
                        engine.write_staging_u64s(dst_off + 769 * 32, &zero_pad);
                    }
                }
                let lam_flat = core::slice::from_raw_parts(
                    lambda_pows.as_ptr().cast::<u64>(),
                    lambda_pows.len() * 4,
                );
                engine.write_staging_u64s(eq_bytes as usize, lam_flat);

                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                let c_eq = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: eq_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.staging.buffer,
                    engine.prover.vram_aux_in.buffer,
                    1,
                    &c_eq,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT,
                );
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                engine.dispatch_whir_fold_1d(
                    kp.pipeline_layout,
                    c_len.div_ceil(256) as u32,
                    num_polys as u32,
                    WhirFoldPushConsts {
                        c0: [c_len as u64, 0, 0, 0],
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 0,
                        len: c_len as u32,
                        aux0: 0,
                        aux1: num_polys as u32,
                        aux2: c_len as u32,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_READ_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                );
                let c_lam = VkBufferCopy {
                    src_offset: eq_bytes,
                    dst_offset: 0,
                    size: lam_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.staging.buffer,
                    engine.prover.vram_aux_in.buffer,
                    1,
                    &c_lam,
                );
                engine.submit_and_wait()
            }
        })
    }

    pub(crate) fn exec_prover_whir_batch_sumcheck_eval(
        &mut self,
        round: usize,
        cur_len: usize,
        num_polys: usize,
        src_base: u32,
    ) -> Result<([u64; 4], [u64; 4]), VulkanError> {
        self.run_prover_job(|engine| {
            engine.prover_session()?;
            if num_polys == 0 || cur_len < 2 || !cur_len.is_power_of_two() {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            to_u32(cur_len)?;
            to_u32(num_polys)?;
            let half = cur_len / 2;
            let total_wg = to_u32(half.div_ceil(256).max(1))?;
            let part_bytes = cmul(2 * u64::from(total_wg), EXT4_BYTES)?;
            let (np, len) = (to_u64(num_polys), to_u64(cur_len));
            // Mode 3 reads `src_base + p * cur_len + 2 * gid (+ 1)` for `p < num_polys`.
            let src_end = span_end(u64::from(src_base), np, len, EXT4_BYTES)?;
            engine
                .prover
                .vram_work_a
                .check_read("vram_work_a (sumcheck kernels)", src_end)?;
            if round > 0 {
                engine
                    .prover
                    .vram_work_b
                    .check_read("vram_work_b (sumcheck tables)", src_end)?;
            } else {
                engine.prover.vram_witness.check_read(
                    "vram_witness (sumcheck tables)",
                    span_end(0, np, len, WORD_BYTES)?,
                )?;
            }
            engine
                .prover
                .vram_aux_in
                .check_read("vram_aux_in (lambda powers)", cmul(np, EXT4_BYTES)?)?;
            unsafe {
                if engine.ensure_one_prover_buf(|p| &mut p.vram_partials, part_bytes)? {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(part_bytes)?;
                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_witness,
                    0,
                    null(),
                );
                let mut done = 0u32;
                while done < total_wg {
                    let chunk = (total_wg - done).min(engine.max_wg_x);
                    let pc = WhirFoldPushConsts {
                        c0: [0; 4],
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 3,
                        len: half as u32,
                        aux0: u32::from(round > 0),
                        aux1: num_polys as u32,
                        aux2: cur_len as u32,
                        aux3: src_base,
                        aux4: 2 * done,
                        aux5: done * 256,
                    };
                    (engine.fns.cmd_push_constants)(
                        engine.cmd_buf,
                        kp.pipeline_layout,
                        VK_SHADER_STAGE_COMPUTE_BIT,
                        0,
                        size_of::<WhirFoldPushConsts>() as u32,
                        (&pc as *const WhirFoldPushConsts).cast::<c_void>(),
                    );
                    (engine.fns.cmd_dispatch)(engine.cmd_buf, chunk, 1, 1);
                    done += chunk;
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT,
                );
                let copy = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: part_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_partials.buffer,
                    engine.staging.buffer,
                    1,
                    &copy,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;

                let mut raw = std::vec![0u64; (2 * total_wg as usize) * 4];
                engine.read_staging_u64s(0, &mut raw);
                let mut ev0 = [0u64; 4];
                let mut ev2 = [0u64; 4];
                for wg in 0..(total_wg as usize) {
                    let b0 = wg * 8;
                    let b2 = b0 + 4;
                    ev0 = Self::fp4_add_arr(ev0, [raw[b0], raw[b0 + 1], raw[b0 + 2], raw[b0 + 3]]);
                    ev2 = Self::fp4_add_arr(ev2, [raw[b2], raw[b2 + 1], raw[b2 + 2], raw[b2 + 3]]);
                }
                Ok((ev0, ev2))
            }
        })
    }

    pub(crate) fn exec_prover_whir_batch_sumcheck_fold(
        &mut self,
        round: usize,
        cur_len: usize,
        num_polys: usize,
        src_base: u32,
        dst_base: u32,
        chal: [u64; 4],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            engine.prover_session()?;
            if num_polys == 0 || cur_len < 2 || !cur_len.is_power_of_two() {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            to_u32(cur_len)?;
            to_u32(num_polys)?;
            let half = cur_len / 2;
            let total_wg = to_u32(half.div_ceil(256).max(1))?;
            let (np, len) = (to_u64(num_polys), to_u64(cur_len));
            // Mode 4 reads like mode 3 and writes `dst_base + p * half + gid` in both buffers.
            let src_end = span_end(u64::from(src_base), np, len, EXT4_BYTES)?;
            let dst_end = span_end(u64::from(dst_base), np, to_u64(half), EXT4_BYTES)?;
            check_disjoint(
                u64::from(src_base),
                cmul(np, len)?,
                u64::from(dst_base),
                cmul(np, to_u64(half))?,
            )?;
            engine
                .prover
                .vram_work_a
                .check_read("vram_work_a (sumcheck kernels)", src_end)?;
            if round > 0 {
                engine
                    .prover
                    .vram_work_b
                    .check_read("vram_work_b (sumcheck tables)", src_end)?;
            } else {
                engine.prover.vram_witness.check_read(
                    "vram_witness (sumcheck tables)",
                    span_end(0, np, len, WORD_BYTES)?,
                )?;
            }
            engine
                .prover
                .vram_work_a
                .reserve_write("vram_work_a (folded kernels)", dst_end)?;
            engine
                .prover
                .vram_work_b
                .reserve_write("vram_work_b (folded tables)", dst_end)?;
            unsafe {
                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_witness,
                    0,
                    null(),
                );
                engine.dispatch_whir_fold_1d(
                    kp.pipeline_layout,
                    total_wg,
                    1,
                    WhirFoldPushConsts {
                        c0: chal,
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 4,
                        len: half as u32,
                        aux0: u32::from(round > 0),
                        aux1: num_polys as u32,
                        aux2: cur_len as u32,
                        aux3: src_base,
                        aux4: dst_base,
                        aux5: 0,
                    },
                );
                engine.submit_and_wait()
            }
        })
    }

    pub(crate) fn exec_prover_whir_batch_sumcheck_read_tail(
        &mut self,
        cur_len: usize,
        num_polys: usize,
        src_base: u32,
        out_tables: &mut [[u64; 4]],
        out_kernels: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            let elems = cur_len
                .checked_mul(num_polys)
                .ok_or(crate::AccelError::LengthOverflow)?;
            if out_tables.len() != elems || out_kernels.len() != elems {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            engine.prover_session()?;
            if elems == 0 {
                return Ok(());
            }
            let slice_bytes = cmul(to_u64(elems), EXT4_BYTES)?;
            let both_bytes = cmul(slice_bytes, 2)?;
            let src_off = cmul(u64::from(src_base), EXT4_BYTES)?;
            // Refuse before staging grows: the source ranges must be session data.
            let src_end = cadd(src_off, slice_bytes)?;
            engine
                .prover
                .vram_work_b
                .check_read("vram_work_b (sumcheck tail tables)", src_end)?;
            engine
                .prover
                .vram_work_a
                .check_read("vram_work_a (sumcheck tail kernels)", src_end)?;
            unsafe {
                engine.reserve_job_staging(both_bytes)?;
                let stg_cap = engine.staging.capacity;
                let ct = checked_copy(
                    "vram_work_b (sumcheck tail tables)",
                    &engine.prover.vram_work_b,
                    src_off,
                    stg_cap,
                    0,
                    slice_bytes,
                )?;
                let ck = checked_copy(
                    "vram_work_a (sumcheck tail kernels)",
                    &engine.prover.vram_work_a,
                    src_off,
                    stg_cap,
                    slice_bytes,
                    slice_bytes,
                )?;
                engine.begin_cmd()?;
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_work_b.buffer,
                    engine.staging.buffer,
                    1,
                    &ct,
                );
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_work_a.buffer,
                    engine.staging.buffer,
                    1,
                    &ck,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;
                let flat_t = core::slice::from_raw_parts_mut(
                    out_tables.as_mut_ptr().cast::<u64>(),
                    elems * 4,
                );
                let flat_k = core::slice::from_raw_parts_mut(
                    out_kernels.as_mut_ptr().cast::<u64>(),
                    elems * 4,
                );
                engine.read_staging_u64s(0, flat_t);
                engine.read_staging_u64s(slice_bytes as usize, flat_k);
                Ok(())
            }
        })
    }

    pub(crate) fn exec_prover_whir_expand_monomial_and_dot(
        &mut self,
        mono_kronecker: &[[u64; 4]],
        num_vars: usize,
        dot_k_offset: u32,
        out_dots: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            if (mono_kronecker.len() != 768 && mono_kronecker.len() != 1024)
                || (mono_kronecker.len() == 768 && num_vars > 24)
            {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            let core_len = pow2_len(num_vars, 26)?;
            engine.prover_session()?;
            engine.prover.air = None;
            let k_len = core_len + 2;
            let num_dots = out_dots.len();
            let kron_bytes = 1024u64 * 32;
            let wg_k = to_u32(k_len.div_ceil(256))?;
            let wg_dot = to_u32(core_len.div_ceil(256))?;
            let nd = to_u64(num_dots);
            if num_dots > 0 {
                // One workgroup row per dot product.
                engine.check_wg_count(nd)?;
            }
            let part_bytes = cmul(cmul(nd, u64::from(wg_dot))?, EXT4_BYTES)?.max(32);
            // Mode 0 reads the 1024-entry table from `vram_aux_in` and writes `k_len` kernel
            // entries at the start of `vram_work_a`.
            engine
                .prover
                .vram_aux_in
                .reserve_write("vram_aux_in (monomial Kronecker table)", kron_bytes)?;
            engine.prover.vram_work_a.reserve_write(
                "vram_work_a (monomial kernel)",
                cmul(to_u64(k_len), EXT4_BYTES)?,
            )?;
            if num_dots > 0 {
                // Mode 1 reads `p * core_len + gid` words and `dot_k_offset + gid` kernels.
                engine.prover.vram_mono.check_read(
                    "vram_mono (dot product polynomials)",
                    span_end(0, nd, to_u64(core_len), WORD_BYTES)?,
                )?;
                engine.prover.vram_work_a.check_read(
                    "vram_work_a (dot product kernel)",
                    span_end(u64::from(dot_k_offset), to_u64(core_len), 1, EXT4_BYTES)?,
                )?;
            }
            unsafe {
                if engine.ensure_one_prover_buf(|p| &mut p.vram_partials, part_bytes)? {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(kron_bytes.max(part_bytes))?;
                engine.write_geometric_kronecker_as_1024(0, mono_kronecker);

                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                let c_in = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: kron_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.staging.buffer,
                    engine.prover.vram_aux_in.buffer,
                    1,
                    &c_in,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT,
                );
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                engine.dispatch_whir_fold_1d(
                    kp.pipeline_layout,
                    wg_k,
                    1,
                    WhirFoldPushConsts {
                        c0: [core_len as u64, 0, 0, 0],
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 0,
                        len: k_len as u32,
                        aux0: 0,
                        aux1: 1,
                        aux2: k_len as u32,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );

                if num_dots > 0 {
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT,
                    );
                    (engine.fns.cmd_bind_descriptor_sets)(
                        engine.cmd_buf,
                        VK_PIPELINE_BIND_POINT_COMPUTE,
                        kp.pipeline_layout,
                        0,
                        1,
                        &engine.prover.ds_fold_mono,
                        0,
                        null(),
                    );
                    let mut done = 0u32;
                    let mut out_ext4 = 0u32;
                    while done < wg_dot {
                        let chunk = (wg_dot - done).min(engine.max_wg_x);
                        let pc = WhirFoldPushConsts {
                            c0: [0; 4],
                            c1: [0; 4],
                            c2: [0; 4],
                            mode: 1,
                            len: core_len as u32,
                            aux0: 0,
                            aux1: num_dots as u32,
                            aux2: core_len as u32,
                            aux3: dot_k_offset,
                            aux4: out_ext4,
                            aux5: done * 256,
                        };
                        (engine.fns.cmd_push_constants)(
                            engine.cmd_buf,
                            kp.pipeline_layout,
                            VK_SHADER_STAGE_COMPUTE_BIT,
                            0,
                            size_of::<WhirFoldPushConsts>() as u32,
                            (&pc as *const WhirFoldPushConsts).cast::<c_void>(),
                        );
                        (engine.fns.cmd_dispatch)(engine.cmd_buf, chunk, num_dots as u32, 1);
                        done += chunk;
                        out_ext4 += (num_dots as u32) * chunk;
                    }
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_TRANSFER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_TRANSFER_READ_BIT,
                    );
                    let c_out = VkBufferCopy {
                        src_offset: 0,
                        dst_offset: 0,
                        size: part_bytes,
                    };
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.prover.vram_partials.buffer,
                        engine.staging.buffer,
                        1,
                        &c_out,
                    );
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_TRANSFER_BIT,
                        VK_PIPELINE_STAGE_HOST_BIT,
                        VK_ACCESS_TRANSFER_WRITE_BIT,
                        VK_ACCESS_HOST_READ_BIT,
                    );
                }
                engine.submit_and_wait()?;

                if num_dots > 0 {
                    let mut raw = std::vec![0u64; num_dots * (wg_dot as usize) * 4];
                    engine.read_staging_u64s(0, &mut raw);
                    for d in out_dots.iter_mut() {
                        *d = [0u64; 4];
                    }
                    let mut done = 0u32;
                    let mut base = 0usize;
                    while done < wg_dot {
                        let chunk = (wg_dot - done).min(engine.max_wg_x) as usize;
                        for (p, acc) in out_dots.iter_mut().enumerate() {
                            for w in 0..chunk {
                                let o = (base + p * chunk + w) * 4;
                                *acc = Self::fp4_add_arr(
                                    *acc,
                                    [raw[o], raw[o + 1], raw[o + 2], raw[o + 3]],
                                );
                            }
                        }
                        done += chunk as u32;
                        base += num_dots * chunk;
                    }
                }
                Ok(())
            }
        })
    }

    pub(crate) fn exec_prover_whir_open_init(
        &mut self,
        num_vars: usize,
        is_single: bool,
        weights: &[[[u64; 4]; 2]],
        z_ood_kronecker: &[[u64; 4]],
    ) -> Result<[[u64; 4]; 2], VulkanError> {
        self.run_prover_job(|engine| {
            let stride = match z_ood_kronecker.len() {
                1536 => 768usize,
                2048 => 1024usize,
                _ => return Err(crate::AccelError::LengthOverflow.into()),
            };
            let core_len = pow2_len(num_vars, 26)?;
            engine.prover_session()?;
            engine.prover.air = None;
            let coeff_len = core_len + 2;
            let num_polys = weights.len();
            to_u32(num_polys)?;
            let w_bytes = cmul(cmul(2, to_u64(num_polys.max(1)))?, EXT4_BYTES)?;
            let z_bytes = 2048u64 * 32;
            let wg_build = to_u32(coeff_len.div_ceil(256))?;
            let wg_c = to_u32(coeff_len.div_ceil(256))?;
            let part_bytes = cmul(2 * u64::from(wg_c), EXT4_BYTES)?;
            // Mode 2 reads `p * core_len + gid` words of `vram_mono` (one polynomial when
            // `is_single`) and writes `core_len + 2` coefficients at the start of `vram_work_b`.
            let mono_polys = if is_single { 1 } else { to_u64(num_polys) };
            engine.prover.vram_mono.check_read(
                "vram_mono (opening polynomials)",
                span_end(0, mono_polys, to_u64(core_len), WORD_BYTES)?,
            )?;
            engine.prover.vram_aux_in.reserve_write(
                "vram_aux_in (weights, OOD Kronecker tables)",
                w_bytes.max(z_bytes),
            )?;
            engine.prover.vram_work_b.reserve_write(
                "vram_work_b (opening coefficients)",
                cmul(to_u64(coeff_len), EXT4_BYTES)?,
            )?;
            unsafe {
                if engine.ensure_one_prover_buf(|p| &mut p.vram_partials, part_bytes)? {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging((w_bytes + z_bytes).max(part_bytes))?;
                if !is_single && !weights.is_empty() {
                    let flat_w = core::slice::from_raw_parts(
                        weights.as_ptr().cast::<u64>(),
                        weights.len() * 8,
                    );
                    engine.write_staging_u64s(0, flat_w);
                }
                engine.write_geometric_kronecker_as_1024(
                    w_bytes as usize,
                    &z_ood_kronecker[0..stride],
                );
                engine.write_geometric_kronecker_as_1024(
                    (w_bytes as usize) + 1024 * 32,
                    &z_ood_kronecker[stride..2 * stride],
                );

                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                if !is_single && !weights.is_empty() {
                    let cw = VkBufferCopy {
                        src_offset: 0,
                        dst_offset: 0,
                        size: w_bytes,
                    };
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.staging.buffer,
                        engine.prover.vram_aux_in.buffer,
                        1,
                        &cw,
                    );
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_TRANSFER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_TRANSFER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT,
                    );
                }
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_mono,
                    0,
                    null(),
                );
                engine.dispatch_whir_fold_1d(
                    kp.pipeline_layout,
                    wg_build,
                    1,
                    WhirFoldPushConsts {
                        c0: [0; 4],
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 2,
                        len: core_len as u32,
                        aux0: u32::from(is_single),
                        aux1: num_polys as u32,
                        aux2: core_len as u32,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );

                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT | VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT | VK_ACCESS_SHADER_READ_BIT,
                );
                let cz = VkBufferCopy {
                    src_offset: w_bytes,
                    dst_offset: 0,
                    size: z_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.staging.buffer,
                    engine.prover.vram_aux_in.buffer,
                    1,
                    &cz,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                let mut done = 0u32;
                let mut out_ext4 = 0u32;
                while done < wg_c {
                    let chunk = (wg_c - done).min(engine.max_wg_x);
                    let pc = WhirFoldPushConsts {
                        c0: [0; 4],
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 0,
                        len: coeff_len as u32,
                        aux0: 2,
                        aux1: 2,
                        aux2: 0,
                        aux3: 0,
                        aux4: out_ext4,
                        aux5: done * 256,
                    };
                    (engine.fns.cmd_push_constants)(
                        engine.cmd_buf,
                        kp.pipeline_layout,
                        VK_SHADER_STAGE_COMPUTE_BIT,
                        0,
                        size_of::<WhirFoldPushConsts>() as u32,
                        (&pc as *const WhirFoldPushConsts).cast::<c_void>(),
                    );
                    (engine.fns.cmd_dispatch)(engine.cmd_buf, chunk, 2, 1);
                    done += chunk;
                    out_ext4 += 2 * chunk;
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT,
                );
                let co = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: part_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_partials.buffer,
                    engine.staging.buffer,
                    1,
                    &co,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;

                let mut raw = std::vec![0u64; 2 * (wg_c as usize) * 4];
                engine.read_staging_u64s(0, &mut raw);
                let mut evals = [[0u64; 4]; 2];
                let mut done = 0u32;
                let mut base = 0usize;
                while done < wg_c {
                    let chunk = (wg_c - done).min(engine.max_wg_x) as usize;
                    for (t, dst) in evals.iter_mut().enumerate() {
                        for w in 0..chunk {
                            let o = (base + t * chunk + w) * 4;
                            *dst = Self::fp4_add_arr(
                                *dst,
                                [raw[o], raw[o + 1], raw[o + 2], raw[o + 3]],
                            );
                        }
                    }
                    done += chunk as u32;
                    base += 2 * chunk;
                }
                Ok(evals)
            }
        })
    }

    pub(crate) fn exec_prover_whir_add_ood_claims(
        &mut self,
        k_len: usize,
        k_base: u32,
        xi_z_kronecker: &[[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            let stride = match xi_z_kronecker.len() {
                1536 => 768usize,
                2048 => 1024usize,
                _ => return Err(crate::AccelError::LengthOverflow.into()),
            };
            engine.prover_session()?;
            engine.prover.air = None;
            to_u32(k_len)?;
            let one_bytes = 1024u64 * 32;
            let both_bytes = 2048u64 * 32;
            let wg = to_u32(k_len.div_ceil(256))?;
            // Mode 0 accumulates into `k_base + gid` for `gid < k_len`; the kernel must already
            // be session data.
            engine.prover.vram_work_a.check_read(
                "vram_work_a (OOD kernel)",
                span_end(u64::from(k_base), to_u64(k_len), 1, EXT4_BYTES)?,
            )?;
            engine
                .prover
                .vram_aux_in
                .reserve_write("vram_aux_in (OOD Kronecker table)", one_bytes)?;
            unsafe {
                engine.reserve_job_staging(both_bytes)?;
                engine.write_geometric_kronecker_as_1024(0, &xi_z_kronecker[0..stride]);
                engine.write_geometric_kronecker_as_1024(
                    1024 * 32,
                    &xi_z_kronecker[stride..2 * stride],
                );

                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                for idx in 0..2u64 {
                    if idx > 0 {
                        engine.cmd_barrier(
                            VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                            VK_PIPELINE_STAGE_TRANSFER_BIT | VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                            VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                            VK_ACCESS_TRANSFER_WRITE_BIT
                                | VK_ACCESS_SHADER_READ_BIT
                                | VK_ACCESS_SHADER_WRITE_BIT,
                        );
                    }
                    let cp = VkBufferCopy {
                        src_offset: idx * one_bytes,
                        dst_offset: 0,
                        size: one_bytes,
                    };
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.staging.buffer,
                        engine.prover.vram_aux_in.buffer,
                        1,
                        &cp,
                    );
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_TRANSFER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_TRANSFER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    engine.dispatch_whir_fold_1d(
                        kp.pipeline_layout,
                        wg,
                        1,
                        WhirFoldPushConsts {
                            c0: [0; 4],
                            c1: [0; 4],
                            c2: [0; 4],
                            mode: 0,
                            len: k_len as u32,
                            aux0: 1,
                            aux1: 1,
                            aux2: 0,
                            aux3: k_base,
                            aux4: 0,
                            aux5: 0,
                        },
                    );
                }
                engine.submit_and_wait()
            }
        })
    }

    pub(crate) fn exec_prover_whir_fold_pass_a(
        &mut self,
        pairs_ck: usize,
        c_base: u32,
        k_base: u32,
    ) -> Result<[[u64; 4]; 3], VulkanError> {
        self.run_prover_job(|engine| {
            engine.prover_session()?;
            to_u32(pairs_ck)?;
            let total_wg = to_u32(pairs_ck.div_ceil(256).max(1))?;
            let part_bytes = cmul(3 * u64::from(total_wg), EXT4_BYTES)?;
            // Mode 5 reads `base + 2 * gid (+ 1)` for `gid < pairs_ck` in both buffers.
            engine.prover.vram_work_b.check_read(
                "vram_work_b (fold coefficients)",
                span_end(u64::from(c_base), to_u64(pairs_ck), 2, EXT4_BYTES)?,
            )?;
            engine.prover.vram_work_a.check_read(
                "vram_work_a (fold kernel)",
                span_end(u64::from(k_base), to_u64(pairs_ck), 2, EXT4_BYTES)?,
            )?;
            unsafe {
                if engine.ensure_one_prover_buf(|p| &mut p.vram_partials, part_bytes)? {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(part_bytes)?;
                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                let mut done = 0u32;
                while done < total_wg {
                    let chunk = (total_wg - done).min(engine.max_wg_x);
                    let pc = WhirFoldPushConsts {
                        c0: [0; 4],
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 5,
                        len: pairs_ck as u32,
                        aux0: c_base,
                        aux1: k_base,
                        aux2: 0,
                        aux3: 0,
                        aux4: 3 * done,
                        aux5: done * 256,
                    };
                    (engine.fns.cmd_push_constants)(
                        engine.cmd_buf,
                        kp.pipeline_layout,
                        VK_SHADER_STAGE_COMPUTE_BIT,
                        0,
                        size_of::<WhirFoldPushConsts>() as u32,
                        (&pc as *const WhirFoldPushConsts).cast::<c_void>(),
                    );
                    (engine.fns.cmd_dispatch)(engine.cmd_buf, chunk, 1, 1);
                    done += chunk;
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT,
                );
                let co = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: part_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_partials.buffer,
                    engine.staging.buffer,
                    1,
                    &co,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;

                let mut raw = std::vec![0u64; 3 * (total_wg as usize) * 4];
                engine.read_staging_u64s(0, &mut raw);
                let mut wires = [[0u64; 4]; 3];
                for wg in 0..(total_wg as usize) {
                    for (j, dst) in wires.iter_mut().enumerate() {
                        let o = (wg * 3 + j) * 4;
                        *dst =
                            Self::fp4_add_arr(*dst, [raw[o], raw[o + 1], raw[o + 2], raw[o + 3]]);
                    }
                }
                Ok(wires)
            }
        })
    }

    pub(crate) fn exec_prover_whir_fold_pass_b(
        &mut self,
        pairs_c: usize,
        c_base: u32,
        k_src: u32,
        k_half: u32,
        k_dst: u32,
        phi: [u64; 4],
    ) -> Result<[[u64; 4]; 2], VulkanError> {
        self.run_prover_job(|engine| {
            engine.prover_session()?;
            to_u32(pairs_c)?;
            let max_threads = pairs_c.max(k_half as usize + 1);
            let total_wg = to_u32(max_threads.div_ceil(256).max(1))?;
            let part_bytes = cmul(2 * u64::from(total_wg), EXT4_BYTES)?;
            // Mode 6 reads `k_src + 2 * gid (+ 1)` for `gid < k_half`, reads
            // `c_base + 2 * gid (+ 1)` for `gid < min(pairs_c, k_half - 1)`, and writes
            // `k_dst + gid` for `gid <= k_half`.
            let kh = u64::from(k_half);
            check_disjoint(
                u64::from(k_src),
                cmul(kh, 2)?,
                u64::from(k_dst),
                cadd(kh, 1)?,
            )?;
            engine.prover.vram_work_a.check_read(
                "vram_work_a (fold kernel)",
                span_end(u64::from(k_src), kh, 2, EXT4_BYTES)?,
            )?;
            engine.prover.vram_work_b.check_read(
                "vram_work_b (fold coefficients)",
                span_end(
                    u64::from(c_base),
                    to_u64(pairs_c).min(kh.saturating_sub(1)),
                    2,
                    EXT4_BYTES,
                )?,
            )?;
            engine.prover.vram_work_a.reserve_write(
                "vram_work_a (folded kernel)",
                span_end(u64::from(k_dst), cadd(kh, 1)?, 1, EXT4_BYTES)?,
            )?;
            engine.prover.last_fold_k_dst = Some(k_dst);
            unsafe {
                if engine.ensure_one_prover_buf(|p| &mut p.vram_partials, part_bytes)? {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(part_bytes)?;
                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                let mut done = 0u32;
                while done < total_wg {
                    let chunk = (total_wg - done).min(engine.max_wg_x);
                    let pc = WhirFoldPushConsts {
                        c0: phi,
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 6,
                        len: pairs_c as u32,
                        aux0: c_base,
                        aux1: k_src,
                        aux2: k_half,
                        aux3: k_dst,
                        aux4: 2 * done,
                        aux5: done * 256,
                    };
                    (engine.fns.cmd_push_constants)(
                        engine.cmd_buf,
                        kp.pipeline_layout,
                        VK_SHADER_STAGE_COMPUTE_BIT,
                        0,
                        size_of::<WhirFoldPushConsts>() as u32,
                        (&pc as *const WhirFoldPushConsts).cast::<c_void>(),
                    );
                    (engine.fns.cmd_dispatch)(engine.cmd_buf, chunk, 1, 1);
                    done += chunk;
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT,
                );
                let co = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: part_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_partials.buffer,
                    engine.staging.buffer,
                    1,
                    &co,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;

                let mut raw = std::vec![0u64; 2 * (total_wg as usize) * 4];
                engine.read_staging_u64s(0, &mut raw);
                let mut wires = [[0u64; 4]; 2];
                for wg in 0..(total_wg as usize) {
                    for (j, dst) in wires.iter_mut().enumerate() {
                        let o = (wg * 2 + j) * 4;
                        *dst =
                            Self::fp4_add_arr(*dst, [raw[o], raw[o + 1], raw[o + 2], raw[o + 3]]);
                    }
                }
                Ok(wires)
            }
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn exec_prover_whir_fold_pass_c(
        &mut self,
        m: usize,
        c_src: u32,
        c_dst: u32,
        theta: [u64; 4],
        alpha: [u64; 4],
        beta: [u64; 4],
        normalize_to_zero: bool,
        norm_len: usize,
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            engine.prover_session()?;
            to_u32(m)?;
            let total_wg = to_u32(cadd(to_u64(m), 1)?.div_ceil(256).max(1))?;
            check_disjoint(
                u64::from(c_src),
                cmul(to_u64(m), 2)?,
                u64::from(c_dst),
                cadd(to_u64(m), 1)?,
            )?;
            // Mode 7 reads `c_src + 2 * gid (+ 1)` for `gid < m` and writes `c_dst + gid` for
            // `gid <= m`, both in `vram_work_b`.
            engine.prover.vram_work_b.check_read(
                "vram_work_b (fold coefficients)",
                span_end(u64::from(c_src), to_u64(m), 2, EXT4_BYTES)?,
            )?;
            engine.prover.vram_work_b.reserve_write(
                "vram_work_b (folded coefficients)",
                span_end(u64::from(c_dst), cadd(to_u64(m), 1)?, 1, EXT4_BYTES)?,
            )?;
            let k_dst = engine.prover.last_fold_k_dst.unwrap_or(c_dst);
            let norm_bytes = if normalize_to_zero && norm_len > 0 {
                cmul(to_u64(norm_len), EXT4_BYTES)?
            } else {
                0
            };
            let norm_copy_b = if norm_bytes > 0 && c_dst != 0 {
                let src_off = cmul(u64::from(c_dst), EXT4_BYTES)?;
                if norm_bytes > src_off {
                    return Err(out_of_range(
                        "fold normalisation length (overlaps its source)",
                        src_off,
                        norm_bytes,
                    ));
                }
                Some(checked_copy(
                    "vram_work_b (fold normalisation)",
                    &engine.prover.vram_work_b,
                    src_off,
                    engine.prover.vram_work_b.capacity,
                    0,
                    norm_bytes,
                )?)
            } else {
                None
            };
            let norm_copy_a = if norm_bytes > 0 && k_dst != 0 {
                let src_off_a = cmul(u64::from(k_dst), EXT4_BYTES)?;
                if norm_bytes > src_off_a {
                    return Err(out_of_range(
                        "fold kernel normalisation length (overlaps its source)",
                        src_off_a,
                        norm_bytes,
                    ));
                }
                Some(checked_copy(
                    "vram_work_a (fold normalisation)",
                    &engine.prover.vram_work_a,
                    src_off_a,
                    engine.prover.vram_work_a.capacity,
                    0,
                    norm_bytes,
                )?)
            } else {
                None
            };
            unsafe {
                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                engine.dispatch_whir_fold_1d(
                    kp.pipeline_layout,
                    total_wg,
                    1,
                    WhirFoldPushConsts {
                        c0: theta,
                        c1: alpha,
                        c2: beta,
                        mode: 7,
                        len: m as u32,
                        aux0: c_src,
                        aux1: c_dst,
                        aux2: 0,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                if norm_copy_b.is_some() || norm_copy_a.is_some() {
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_TRANSFER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_TRANSFER_READ_BIT,
                    );
                    if let Some(cp_b) = norm_copy_b {
                        (engine.fns.cmd_copy_buffer)(
                            engine.cmd_buf,
                            engine.prover.vram_work_b.buffer,
                            engine.prover.vram_work_b.buffer,
                            1,
                            &cp_b,
                        );
                    }
                    if let Some(cp_a) = norm_copy_a {
                        (engine.fns.cmd_copy_buffer)(
                            engine.cmd_buf,
                            engine.prover.vram_work_a.buffer,
                            engine.prover.vram_work_a.buffer,
                            1,
                            &cp_a,
                        );
                    }
                }
                if normalize_to_zero && norm_len > 0 {
                    engine.prover.last_fold_k_dst = Some(0);
                }
                engine.submit_and_wait()
            }
        })
    }

    pub(crate) fn exec_prover_whir_commit_stage(
        &mut self,
        stage_idx: usize,
        coeff_len: usize,
        domain_len: usize,
        group_arity: usize,
    ) -> Result<[u8; 32], VulkanError> {
        self.run_prover_job(|engine| {
            if stage_idx == 0
                || stage_idx > 255
                || coeff_len > domain_len
                || !domain_len.is_power_of_two()
                || !group_arity.is_power_of_two()
                || group_arity == 0
                || group_arity > 128
                || !domain_len.is_multiple_of(group_arity)
            {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            let dims = engine.prover_session()?;
            let turbo_flag = if dims.turboshake_canopy { 0x80u32 } else { 0u32 };
            let num_groups = domain_len / group_arity;
            let log_d = domain_len.trailing_zeros();
            to_u32(domain_len)?;
            to_u32(coeff_len)?;
            to_u32(stage_idx)?;
            let slot_idx = stage_idx & 1;
            let cw_base = 0u32;
            let tree_base = 0u32;
            // Mode 6 reads `coeff_len` coefficients from the start of `vram_work_b` and writes
            // `domain_len` codeword entries into `vram_cw_stage[slot_idx]`; modes 10-12 write
            // tree nodes `1 .. 2 * num_groups` into `vram_tree_stage[slot_idx]`.
            engine.prover.vram_work_b.check_read(
                "vram_work_b (stage coefficients)",
                cmul(to_u64(coeff_len), EXT4_BYTES)?,
            )?;
            engine.prover.vram_cw_stage[slot_idx].reserve_write(
                "vram_cw_stage (stage codeword)",
                span_end(0, to_u64(domain_len), 1, EXT4_BYTES)?,
            )?;
            engine.prover.vram_tree_stage[slot_idx].reserve_write(
                "vram_tree_stage (stage Merkle tree)",
                span_end(0, to_u64(num_groups), 2, EXT4_BYTES)?,
            )?;

            unsafe {
                engine.reserve_job_staging(32)?;
                let kp = engine.prover_pipelines[ProverKernelSlot::WhirLdeCommitment as usize];
                engine.begin_cmd()?;
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_lde_stage[slot_idx],
                    0,
                    null(),
                );

                // 1. Shifted bit-reverse copy (`cur_coeffs[0..coeff_len] -> vram_cw_stage[cw_base..]`).
                engine.dispatch_whir_lde_1d(
                    kp.pipeline_layout,
                    domain_len.div_ceil(256) as u32,
                    1,
                    256,
                    WhirLdePushConsts {
                        scalar0: 0,
                        scalar1: 0,
                        scalar2: 0,
                        scalar3: 0,
                        mode: 6,
                        len: domain_len as u32,
                        aux0: log_d,
                        aux1: coeff_len as u32,
                        aux2: cw_base,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                // 2. Fused <=9-stage LDS `Ext4` NTT + remaining global stages.
                engine.dispatch_whir_lde_1d(
                    kp.pipeline_layout,
                    (domain_len >> 9).max(1) as u32,
                    1,
                    1,
                    WhirLdePushConsts {
                        scalar0: 0,
                        scalar1: 0,
                        scalar2: 0,
                        scalar3: 0,
                        mode: 7,
                        len: domain_len as u32,
                        aux0: log_d,
                        aux1: 0,
                        aux2: cw_base,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                let mut stage = 10u32;
                while stage + 2 <= log_d && stage + 2 <= 24 {
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    engine.dispatch_whir_lde_1d(
                        kp.pipeline_layout,
                        (domain_len >> 9) as u32,
                        1,
                        1,
                        WhirLdePushConsts {
                            scalar0: 0,
                            scalar1: 0,
                            scalar2: 0,
                            scalar3: 0,
                            mode: 16,
                            len: domain_len as u32,
                            aux0: stage,
                            aux1: 0,
                            aux2: cw_base,
                            aux3: 0,
                            aux4: 0,
                            aux5: 0,
                        },
                    );
                    stage += 3;
                }
                while stage <= log_d {
                    let w_hi = if stage > 24 {
                        goldilocks_primitive_root(stage).map_err(VulkanError::Accel)?
                    } else {
                        0
                    };
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    engine.dispatch_whir_lde_1d(
                        kp.pipeline_layout,
                        (domain_len >> 1).div_ceil(256) as u32,
                        1,
                        256,
                        WhirLdePushConsts {
                            scalar0: w_hi,
                            scalar1: 0,
                            scalar2: 0,
                            scalar3: 0,
                            mode: 8,
                            len: domain_len as u32,
                            aux0: stage,
                            aux1: 0,
                            aux2: cw_base,
                            aux3: 0,
                            aux4: 0,
                            aux5: 0,
                        },
                    );
                    stage += 1;
                }

                // 3. Canopy `Ext4` leaf hashing + internal Merkle layers.
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                engine.dispatch_whir_lde_1d(
                    kp.pipeline_layout,
                    num_groups.div_ceil(256) as u32,
                    1,
                    256,
                    WhirLdePushConsts {
                        scalar0: 0,
                        scalar1: 0,
                        scalar2: 0,
                        scalar3: 0,
                        mode: 10 | turbo_flag,
                        len: num_groups as u32,
                        aux0: group_arity as u32,
                        aux1: cw_base,
                        aux2: stage_idx as u32,
                        aux3: 0,
                        aux4: tree_base,
                        aux5: 0,
                    },
                );
                let mut half = num_groups >> 1;
                while half > 256 {
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    engine.dispatch_whir_lde_1d(
                        kp.pipeline_layout,
                        half.div_ceil(256) as u32,
                        1,
                        256,
                        WhirLdePushConsts {
                            scalar0: 0,
                            scalar1: 0,
                            scalar2: 0,
                            scalar3: 0,
                            mode: 11 | turbo_flag,
                            len: half as u32,
                            aux0: 0,
                            aux1: 0,
                            aux2: tree_base,
                            aux3: 0,
                            aux4: 0,
                            aux5: 0,
                        },
                    );
                    half >>= 1;
                }
                if half >= 1 {
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_SHADER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                    );
                    engine.dispatch_whir_lde_1d(
                        kp.pipeline_layout,
                        1,
                        1,
                        256,
                        WhirLdePushConsts {
                            scalar0: 0,
                            scalar1: 0,
                            scalar2: 0,
                            scalar3: 0,
                            mode: 12 | turbo_flag,
                            len: half as u32,
                            aux0: 0,
                            aux1: 0,
                            aux2: tree_base,
                            aux3: 0,
                            aux4: 0,
                            aux5: 0,
                        },
                    );
                }

                let copy_top = checked_copy(
                    "vram_tree_stage (stage top node)",
                    &engine.prover.vram_tree_stage[slot_idx],
                    EXT4_BYTES,
                    engine.staging.capacity,
                    0,
                    32,
                )?;
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT,
                );
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_tree_stage[slot_idx].buffer,
                    engine.staging.buffer,
                    1,
                    &copy_top,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;

                let mut top_words = [0u64; 4];
                engine.read_staging_u64s(0, &mut top_words);
                let mut top_node = [0u8; 32];
                for (i, w) in top_words.into_iter().enumerate() {
                    top_node[i * 8..(i + 1) * 8].copy_from_slice(&w.to_le_bytes());
                }
                engine.prover.committed_trees[1 + slot_idx] = Some(CommittedTree {
                    stage_idx,
                    group_arity,
                    num_groups,
                });
                Ok(top_node)
            }
        })
    }

    pub(crate) fn exec_prover_whir_eval_univariate_2(
        &mut self,
        coeff_len: usize,
        c_base: u32,
        z_ood_kronecker: &[[u64; 4]],
    ) -> Result<[[u64; 4]; 2], VulkanError> {
        self.run_prover_job(|engine| {
            let stride = match z_ood_kronecker.len() {
                1536 => 768usize,
                2048 => 1024usize,
                _ => return Err(crate::AccelError::LengthOverflow.into()),
            };
            engine.prover_session()?;
            engine.prover.air = None;
            to_u32(coeff_len)?;
            let z_bytes = 2048u64 * 32;
            let wg = to_u32(coeff_len.div_ceil(256).max(1))?;
            let part_bytes = cmul(2 * u64::from(wg), EXT4_BYTES)?;
            // Mode 0 (`sub_op == 2`) reads `c_base + gid` for `gid < coeff_len`.
            engine.prover.vram_work_b.check_read(
                "vram_work_b (stage coefficients)",
                span_end(u64::from(c_base), to_u64(coeff_len), 1, EXT4_BYTES)?,
            )?;
            engine
                .prover
                .vram_aux_in
                .reserve_write("vram_aux_in (OOD Kronecker tables)", z_bytes)?;
            unsafe {
                if engine.ensure_one_prover_buf(|p| &mut p.vram_partials, part_bytes)? {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(z_bytes.max(part_bytes))?;
                engine.write_geometric_kronecker_as_1024(0, &z_ood_kronecker[0..stride]);
                engine.write_geometric_kronecker_as_1024(
                    1024 * 32,
                    &z_ood_kronecker[stride..2 * stride],
                );

                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                let cz = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: z_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.staging.buffer,
                    engine.prover.vram_aux_in.buffer,
                    1,
                    &cz,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT,
                );
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                let mut done = 0u32;
                let mut out_ext4 = 0u32;
                while done < wg {
                    let chunk = (wg - done).min(engine.max_wg_x);
                    let pc = WhirFoldPushConsts {
                        c0: [0; 4],
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 0,
                        len: coeff_len as u32,
                        aux0: 2,
                        aux1: 2,
                        aux2: 0,
                        aux3: c_base,
                        aux4: out_ext4,
                        aux5: done * 256,
                    };
                    (engine.fns.cmd_push_constants)(
                        engine.cmd_buf,
                        kp.pipeline_layout,
                        VK_SHADER_STAGE_COMPUTE_BIT,
                        0,
                        size_of::<WhirFoldPushConsts>() as u32,
                        (&pc as *const WhirFoldPushConsts).cast::<c_void>(),
                    );
                    (engine.fns.cmd_dispatch)(engine.cmd_buf, chunk, 2, 1);
                    done += chunk;
                    out_ext4 += 2 * chunk;
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT,
                );
                let co = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: part_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_partials.buffer,
                    engine.staging.buffer,
                    1,
                    &co,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;

                let mut raw = std::vec![0u64; 2 * (wg as usize) * 4];
                engine.read_staging_u64s(0, &mut raw);
                let mut evals = [[0u64; 4]; 2];
                let mut done = 0u32;
                let mut base = 0usize;
                while done < wg {
                    let chunk = (wg - done).min(engine.max_wg_x) as usize;
                    for (t, dst) in evals.iter_mut().enumerate() {
                        for w in 0..chunk {
                            let o = (base + t * chunk + w) * 4;
                            *dst = Self::fp4_add_arr(
                                *dst,
                                [raw[o], raw[o + 1], raw[o + 2], raw[o + 3]],
                            );
                        }
                    }
                    done += chunk as u32;
                    base += 2 * chunk;
                }
                Ok(evals)
            }
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn exec_prover_whir_gather_queries(
        &mut self,
        stage_idx: usize,
        group_arity: usize,
        num_polys: usize,
        num_groups: usize,
        q_indices: &[u64],
        sib_indices: &[u64],
        out_words: &mut [u64],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            let num_q = q_indices.len();
            let num_s = sib_indices.len();
            let is_ext4 = stage_idx > 0;
            let (nq, ns) = (to_u64(num_q), to_u64(num_s));
            let (arity, np, ng) = (to_u64(group_arity), to_u64(num_polys), to_u64(num_groups));
            let salt_words = if is_ext4 { 0 } else { cmul(2, nq)? };
            let fiber_words = if is_ext4 {
                cmul(cmul(4, arity)?, nq)?
            } else {
                cmul(cmul(np, arity)?, nq)?
            };
            let expected_out = cadd(cadd(salt_words, fiber_words)?, cmul(4, ns)?)?;
            if to_u64(out_words.len()) != expected_out
                || stage_idx > 255
                || group_arity > 128
                || num_polys > 255
            {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            let session_dims = engine.prover_session()?;
            let turbo_flag = if session_dims.turboshake_canopy {
                0x80u32
            } else {
                0u32
            };
            if expected_out == 0 {
                return Ok(());
            }
            engine.prover.air = None;
            to_u32(num_q)?;
            to_u32(num_s)?;
            to_u32(group_arity)?;
            to_u32(num_polys)?;
            to_u32(num_groups)?;

            let in_words = num_q + num_s;
            let in_bytes = cmul(to_u64(in_words.max(1)), WORD_BYTES)?;
            let out_bytes = cmul(expected_out, WORD_BYTES)?;
            let slot_idx = stage_idx & 1;
            // The gather must name the tree actually resident in its slot: a parity slot
            // is reused by stage `s + 2`, and a folded stage holds a single Ext4 polynomial.
            let (tree_slot, committed_polys) = if is_ext4 {
                (1 + slot_idx, 1)
            } else {
                (0, engine.prover_session()?.num_polys)
            };
            let requested = CommittedTree {
                stage_idx,
                group_arity,
                num_groups,
            };
            if engine.prover.committed_trees[tree_slot] != Some(requested)
                || num_polys != committed_polys
            {
                return Err(length_overflow());
            }
            let t_base = 0u64;
            let c_base = 0u64;
            let max_threads = num_q.max(num_s).max(1);
            // Mode 13 indexes the codeword and the tree through the uploaded index lists, so
            // their contents are validated here: a query names a group, a sibling names a node.
            if let Some(&bad) = q_indices.iter().find(|&&g| g >= ng) {
                return Err(out_of_range("query group index", ng, bad));
            }
            let nodes = cmul(2, ng)?;
            if let Some(&bad) = sib_indices.iter().find(|&&n| n >= nodes) {
                return Err(out_of_range("Merkle sibling node index", nodes, bad));
            }
            if is_ext4 {
                if num_q > 0 {
                    engine.prover.vram_cw_stage[slot_idx].check_read(
                        "vram_cw_stage (query fibers)",
                        span_end(c_base, arity, ng, EXT4_BYTES)?,
                    )?;
                }
                if num_s > 0 {
                    engine.prover.vram_tree_stage[slot_idx].check_read(
                        "vram_tree_stage (query siblings)",
                        span_end(t_base, nodes, 1, EXT4_BYTES)?,
                    )?;
                }
            } else {
                if num_q > 0 {
                    engine.prover.vram_cw0.check_read(
                        "vram_cw0 (query fibers)",
                        span_end(0, cmul(np, arity)?, ng, WORD_BYTES)?,
                    )?;
                }
                if num_s > 0 {
                    engine.prover.vram_tree0.check_read(
                        "vram_tree0 (query siblings)",
                        span_end(0, nodes, 1, EXT4_BYTES)?,
                    )?;
                }
            }

            unsafe {
                let mut regrew = false;
                regrew |= engine.ensure_one_prover_buf(|p| &mut p.vram_aux_in, in_bytes)?;
                regrew |= engine.ensure_one_prover_buf(|p| &mut p.vram_partials, out_bytes)?;
                if regrew {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(in_bytes.max(out_bytes))?;
                engine.write_staging_u64s(0, q_indices);
                engine.write_staging_u64s(num_q * 8, sib_indices);

                let kp = engine.prover_pipelines[ProverKernelSlot::WhirLdeCommitment as usize];
                let ds = if is_ext4 {
                    engine.prover.ds_gather_stage[slot_idx]
                } else {
                    engine.prover.ds_gather_r0
                };
                engine.begin_cmd()?;
                if in_words > 0 {
                    let ci = VkBufferCopy {
                        src_offset: 0,
                        dst_offset: 0,
                        size: in_bytes,
                    };
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.staging.buffer,
                        engine.prover.vram_aux_in.buffer,
                        1,
                        &ci,
                    );
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_TRANSFER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_TRANSFER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT,
                    );
                }
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &ds,
                    0,
                    null(),
                );
                let (sc0, sc1, sc2, sc3) = if is_ext4 {
                    (t_base, c_base, 0, 0)
                } else {
                    let s = engine.prover.salt_seed_words;
                    (s[0], s[1], s[2], s[3])
                };
                let pc = WhirLdePushConsts {
                    scalar0: sc0,
                    scalar1: sc1,
                    scalar2: sc2,
                    scalar3: sc3,
                    mode: 13 | turbo_flag,
                    len: num_q as u32,
                    aux0: group_arity as u32,
                    aux1: num_polys as u32,
                    aux2: num_s as u32,
                    aux3: 0,
                    aux4: u32::from(is_ext4),
                    aux5: num_groups as u32,
                };
                (engine.fns.cmd_push_constants)(
                    engine.cmd_buf,
                    kp.pipeline_layout,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<WhirLdePushConsts>() as u32,
                    (&pc as *const WhirLdePushConsts).cast::<c_void>(),
                );
                let gather_wg = engine.check_wg_count(to_u64(max_threads.div_ceil(256)))?;
                (engine.fns.cmd_dispatch)(engine.cmd_buf, gather_wg, 1, 1);
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT,
                );
                let co = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: out_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_partials.buffer,
                    engine.staging.buffer,
                    1,
                    &co,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;
                engine.read_staging_u64s(0, out_words);
                Ok(())
            }
        })
    }

    pub(crate) fn exec_prover_whir_accumulate_shift_claims(
        &mut self,
        k_len: usize,
        k_base: u32,
        z_pow_256: &[u64],
        claims_meta: &[[u64; 8]],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            let num_claims = claims_meta.len();
            if num_claims == 0 {
                return Ok(());
            }
            if num_claims.checked_mul(256) != Some(z_pow_256.len()) {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            engine.prover_session()?;
            engine.prover.air = None;
            to_u32(num_claims)?;
            to_u32(k_len)?;
            let z_bytes = cmul(to_u64(z_pow_256.len()), WORD_BYTES)?;
            let m_bytes = cmul(to_u64(num_claims), 64)?;
            let total_wg = to_u32(k_len.div_ceil(256).max(1))?;
            // Mode 8 accumulates into `k_base + gid` for `gid < k_len`.
            engine.prover.vram_work_a.check_read(
                "vram_work_a (shift-claim kernel)",
                span_end(u64::from(k_base), to_u64(k_len), 1, EXT4_BYTES)?,
            )?;
            unsafe {
                let mut regrew = false;
                regrew |= engine.ensure_one_prover_buf(|p| &mut p.vram_aux_in, z_bytes)?;
                regrew |= engine.ensure_one_prover_buf(|p| &mut p.vram_aux_b, m_bytes)?;
                if regrew {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(z_bytes + m_bytes)?;
                engine.write_staging_u64s(0, z_pow_256);
                let flat_m =
                    core::slice::from_raw_parts(claims_meta.as_ptr().cast::<u64>(), num_claims * 8);
                engine.write_staging_u64s(z_bytes as usize, flat_m);

                let kp = engine.prover_pipelines[ProverKernelSlot::WhirFoldSumcheck as usize];
                engine.begin_cmd()?;
                let cz = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: z_bytes,
                };
                let cm = VkBufferCopy {
                    src_offset: z_bytes,
                    dst_offset: 0,
                    size: m_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.staging.buffer,
                    engine.prover.vram_aux_in.buffer,
                    1,
                    &cz,
                );
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.staging.buffer,
                    engine.prover.vram_aux_b.buffer,
                    1,
                    &cm,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_fold_kronecker,
                    0,
                    null(),
                );
                engine.dispatch_whir_fold_1d(
                    kp.pipeline_layout,
                    total_wg,
                    1,
                    WhirFoldPushConsts {
                        c0: [0; 4],
                        c1: [0; 4],
                        c2: [0; 4],
                        mode: 8,
                        len: k_len as u32,
                        aux0: k_base,
                        aux1: num_claims as u32,
                        aux2: 0,
                        aux3: 0,
                        aux4: 0,
                        aux5: 0,
                    },
                );
                engine.submit_and_wait()
            }
        })
    }

    pub(crate) fn exec_prover_whir_read_final_coeffs(
        &mut self,
        c_base: u32,
        out_coeffs: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            engine.prover_session()?;
            let bytes = cmul(to_u64(out_coeffs.len()), EXT4_BYTES)?;
            if bytes == 0 {
                return Ok(());
            }
            let src_off = cmul(u64::from(c_base), EXT4_BYTES)?;
            engine
                .prover
                .vram_work_b
                .check_read("vram_work_b (final coefficients)", cadd(src_off, bytes)?)?;
            unsafe {
                engine.reserve_job_staging(bytes)?;
                let cp = checked_copy(
                    "vram_work_b (final coefficients)",
                    &engine.prover.vram_work_b,
                    src_off,
                    engine.staging.capacity,
                    0,
                    bytes,
                )?;
                engine.begin_cmd()?;
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_work_b.buffer,
                    engine.staging.buffer,
                    1,
                    &cp,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;
                let flat = core::slice::from_raw_parts_mut(
                    out_coeffs.as_mut_ptr().cast::<u64>(),
                    out_coeffs.len() * 4,
                );
                engine.read_staging_u64s(0, flat);
                Ok(())
            }
        })
    }

    pub(crate) fn exec_prover_air_init_shard(
        &mut self,
        witness_word_offset: u32,
        cols_base_word_offset: u32,
        total_rows: usize,
        shift_tables_3m: &[[u64; 4]],
        static_gammas_ext4: &[[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            if total_rows < 2
                || !total_rows.is_power_of_two()
                || total_rows.checked_mul(3) != Some(shift_tables_3m.len())
            {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            to_u32(total_rows)?;
            engine.prover_session()?;
            engine.prover.air = None;
            let rows = to_u64(total_rows);
            let sh_bytes = cmul(to_u64(shift_tables_3m.len()), EXT4_BYTES)?;
            let gm_bytes = cmul(to_u64(static_gammas_ext4.len().max(1)), EXT4_BYTES)?;
            let half_m = rows / 2;
            let need_wa = cmul(cmul(2 * 256, half_m)?, EXT4_BYTES)?;
            let need_wb = cmul(cmul(8 * 12, half_m)?, EXT4_BYTES)?;
            let need_ab = cmul(sh_bytes, 2)?;
            let need_ain = cadd(gm_bytes, 4 * 1024 * 1024)?;
            check_disjoint(
                u64::from(witness_word_offset),
                cmul(rows, 256)?,
                u64::from(cols_base_word_offset),
                cmul(rows, 256)?,
            )?;
            // Mode 0 reads the row-major shard (`col_src + row * 256 + col`) and writes it
            // column-major (`col_dst + col * rows + row`), both in `vram_witness`. The witness
            // is session data from the commit: it is checked, never regrown.
            engine.prover.vram_witness.check_read(
                "vram_witness (shard witness rows)",
                span_end(u64::from(witness_word_offset), rows, 256, WORD_BYTES)?,
            )?;
            engine.prover.vram_witness.reserve_write(
                "vram_witness (shard witness columns)",
                span_end(u64::from(cols_base_word_offset), rows, 256, WORD_BYTES)?,
            )?;
            unsafe {
                let mut regrew = false;
                regrew |= engine.ensure_one_prover_buf(|p| &mut p.vram_work_a, need_wa)?;
                regrew |= engine.ensure_one_prover_buf(|p| &mut p.vram_work_b, need_wb)?;
                regrew |= engine.ensure_one_prover_buf(|p| &mut p.vram_aux_b, need_ab)?;
                regrew |= engine.ensure_one_prover_buf(|p| &mut p.vram_aux_in, need_ain)?;
                if regrew {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(sh_bytes + gm_bytes)?;
                let flat_sh = core::slice::from_raw_parts(
                    shift_tables_3m.as_ptr().cast::<u64>(),
                    shift_tables_3m.len() * 4,
                );
                engine.write_staging_u64s(0, flat_sh);
                if !static_gammas_ext4.is_empty() {
                    let flat_gm = core::slice::from_raw_parts(
                        static_gammas_ext4.as_ptr().cast::<u64>(),
                        static_gammas_ext4.len() * 4,
                    );
                    engine.write_staging_u64s(sh_bytes as usize, flat_gm);
                }

                let kp = engine.prover_pipelines[ProverKernelSlot::AirRowGroupA as usize];
                engine.begin_cmd()?;
                let c_sh = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: sh_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.staging.buffer,
                    engine.prover.vram_aux_b.buffer,
                    1,
                    &c_sh,
                );
                if !static_gammas_ext4.is_empty() {
                    let c_gm = VkBufferCopy {
                        src_offset: sh_bytes,
                        dst_offset: 0,
                        size: gm_bytes,
                    };
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.staging.buffer,
                        engine.prover.vram_aux_in.buffer,
                        1,
                        &c_gm,
                    );
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_air,
                    0,
                    null(),
                );
                let total_tiles_x = total_rows.div_ceil(8).max(1) as u32;
                let mut done = 0u32;
                while done < total_tiles_x {
                    let chunk = (total_tiles_x - done).min(engine.max_wg_x);
                    let pc = AirGroupAPushConsts {
                        chal: [0; 4],
                        mode: 0,
                        cur_m: total_rows as u32,
                        cur_r: 0,
                        flags: 0,
                        col_src: witness_word_offset,
                        col_dst: cols_base_word_offset,
                        sh_src: 0,
                        steps_off: 0,
                        out_off: 0,
                        base_x: done,
                        aux0: 0,
                        aux1: 0,
                        _pad_align: [0; 4],
                    };
                    (engine.fns.cmd_push_constants)(
                        engine.cmd_buf,
                        kp.pipeline_layout,
                        VK_SHADER_STAGE_COMPUTE_BIT,
                        0,
                        size_of::<AirGroupAPushConsts>() as u32,
                        (&pc as *const AirGroupAPushConsts).cast::<c_void>(),
                    );
                    (engine.fns.cmd_dispatch)(engine.cmd_buf, chunk, 32, 1);
                    done += chunk;
                }
                engine.submit_and_wait()?;
                let flat_static = core::slice::from_raw_parts(
                    static_gammas_ext4.as_ptr().cast::<u64>(),
                    static_gammas_ext4.len() * 4,
                );
                engine.prover.air = Some(AirShardState {
                    total_rows: rows,
                    static_words: flat_static.to_vec(),
                });
                Ok(())
            }
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn exec_prover_air_eval_round(
        &mut self,
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
        self.run_prover_job(|engine| {
            if cur_m < 2
                || !cur_m.is_power_of_two()
                || !cur_r.is_power_of_two()
                || cur_s == 0
                || (folding_signer && (cur_s < 2 || !cur_s.is_power_of_two()))
            {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            to_u32(cur_m)?;
            to_u32(cur_r)?;
            to_u32(cur_s)?;
            engine.prover_session()?;
            let (m, r, sg) = (to_u64(cur_m), to_u64(cur_r), to_u64(cur_s));
            let half_m = cur_m / 2;
            let hm = m / 2;
            let wgs_x = engine.check_wg_count(to_u64(half_m.div_ceil(64).max(1)))?;
            // Rows index the step table (`idx & (cur_r - 1)` when folding signers, otherwise
            // `idx` and `idx + cur_r / 2`) and the signer table (`idx / cur_r + cur_s / 2`).
            let row_capacity = if folding_signer { cmul(sg, r)? } else { r };
            if m > row_capacity {
                return Err(out_of_range(
                    "AIR round rows (step/signer tables)",
                    row_capacity,
                    m,
                ));
            }
            let dyn_bytes = cmul(to_u64(dyn_words.len().max(1)), WORD_BYTES)?;
            let dyn_dst_off = cmul(u64::from(dyn_ext4_off), EXT4_BYTES)?;
            let dyn_word0 = cmul(u64::from(dyn_ext4_off), 4)?;
            let part_bytes = cmul(8 * u64::from(wgs_x), EXT4_BYTES)?;
            let (static_len, total_rows) = match engine.prover.air.as_ref() {
                Some(air) => (to_u64(air.static_words.len()), air.total_rows),
                None => {
                    return Err(out_of_range(
                        "AIR shard tables (not initialised, or overwritten since)",
                        1,
                        0,
                    ));
                }
            };
            if m > total_rows {
                return Err(out_of_range("AIR round rows (shard)", total_rows, m));
            }
            // Group A reads 206 constraint gammas and 44 shift gammas from the static table.
            if static_len < 250 * 4 {
                return Err(out_of_range("AIR static gamma table", 250 * 4, static_len));
            }
            if dyn_word0 < static_len {
                return Err(out_of_range(
                    "AIR dynamic table offset (overlaps the static tables)",
                    static_len,
                    dyn_word0,
                ));
            }
            // The dynamic tables share `vram_aux_in` with the static ones: reserve, never regrow.
            engine.prover.vram_aux_in.reserve_write(
                "vram_aux_in (AIR dynamic tables)",
                cadd(dyn_dst_off, dyn_bytes)?,
            )?;
            engine.prover.vram_aux_in.check_read(
                "vram_aux_in (AIR signer table)",
                span_end(
                    u64::from(signers_off),
                    if folding_signer { sg } else { 1 },
                    14,
                    EXT4_BYTES,
                )?,
            )?;
            engine.prover.vram_aux_in.check_read(
                "vram_aux_in (AIR step table)",
                span_end(u64::from(steps_off), r, 3, EXT4_BYTES)?,
            )?;
            engine.prover.vram_aux_b.check_read(
                "vram_aux_b (AIR shift tables)",
                span_end(u64::from(sh_src), m, 3, EXT4_BYTES)?,
            )?;
            if is_round0_base {
                engine.prover.vram_witness.check_read(
                    "vram_witness (AIR base columns)",
                    span_end(u64::from(col_src), m, 256, WORD_BYTES)?,
                )?;
            } else {
                engine.prover.vram_work_a.check_read(
                    "vram_work_a (AIR folded columns)",
                    span_end(u64::from(col_src), m, 256, EXT4_BYTES)?,
                )?;
            }
            // Group A writes 12 permutation outputs per row and evaluation point.
            engine.prover.vram_work_b.reserve_write(
                "vram_work_b (AIR permutation outputs)",
                cmul(cmul(8 * 12, hm)?, EXT4_BYTES)?,
            )?;
            {
                let air = engine.prover.air.as_ref().ok_or_else(length_overflow)?;
                AirTables {
                    static_words: &air.static_words,
                    dyn_words,
                    dyn_word0,
                }
                .validate_op_tables(
                    hm,
                    folding_signer.then(|| r - 1),
                    if folding_signer { r } else { hm },
                    u64::from(sorted_u64_off),
                    u64::from(op_hdr_off),
                    u64::from(op_ent_off),
                )?;
            }

            unsafe {
                if engine.ensure_one_prover_buf(|p| &mut p.vram_partials, part_bytes)? {
                    engine.refresh_prover_descriptor_sets()?;
                }
                engine.reserve_job_staging(dyn_bytes.max(part_bytes))?;
                if !dyn_words.is_empty() {
                    engine.write_staging_u64s(0, dyn_words);
                }

                let kp_a = engine.prover_pipelines[ProverKernelSlot::AirRowGroupA as usize];
                let kp_b = engine.prover_pipelines[ProverKernelSlot::AirRowGroupB as usize];
                let flags = u32::from(folding_signer);

                engine.begin_cmd()?;
                if !dyn_words.is_empty() {
                    let cd = VkBufferCopy {
                        src_offset: 0,
                        dst_offset: dyn_dst_off,
                        size: dyn_bytes,
                    };
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.staging.buffer,
                        engine.prover.vram_aux_in.buffer,
                        1,
                        &cd,
                    );
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_TRANSFER_BIT,
                        VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                        VK_ACCESS_TRANSFER_WRITE_BIT,
                        VK_ACCESS_SHADER_READ_BIT,
                    );
                }

                // 1. Group A (`mode = 1` base-field Round 0, `mode = 2` `Ext4` Rounds >= 1):
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp_a.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp_a.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_air,
                    0,
                    null(),
                );
                let pc_a = AirGroupAPushConsts {
                    chal: [0; 4],
                    mode: if is_round0_base { 1 } else { 2 },
                    cur_m: cur_m as u32,
                    cur_r: cur_r as u32,
                    flags,
                    col_src,
                    col_dst: col_src,
                    sh_src,
                    steps_off,
                    out_off: 0,
                    base_x: 0,
                    aux0: 0,
                    aux1: 0,
                    _pad_align: [0; 4],
                };
                (engine.fns.cmd_push_constants)(
                    engine.cmd_buf,
                    kp_a.pipeline_layout,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<AirGroupAPushConsts>() as u32,
                    (&pc_a as *const AirGroupAPushConsts).cast::<c_void>(),
                );
                (engine.fns.cmd_dispatch)(engine.cmd_buf, wgs_x, 8, 1);

                // 2. Group B (consumes `perm_out` in `b4` and accumulates onto `b5`):
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp_b.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp_b.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_air,
                    0,
                    null(),
                );
                let pc_b = AirGroupBPushConsts {
                    is_base: u32::from(is_round0_base),
                    cur_m: cur_m as u32,
                    cur_r: cur_r as u32,
                    cur_s: cur_s as u32,
                    flags,
                    col_src,
                    sh_src,
                    signers_off,
                    steps_off,
                    op_hdr_off,
                    op_ent_off,
                    sorted_u64_off,
                    out_off: 0,
                    base_x: 0,
                    _pad0: 0,
                    _pad1: 0,
                };
                (engine.fns.cmd_push_constants)(
                    engine.cmd_buf,
                    kp_b.pipeline_layout,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<AirGroupBPushConsts>() as u32,
                    (&pc_b as *const AirGroupBPushConsts).cast::<c_void>(),
                );
                let wg_y_b = if is_round0_base { 7 } else { 8 };
                (engine.fns.cmd_dispatch)(engine.cmd_buf, wgs_x, wg_y_b, 1);

                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT,
                );
                let co = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: part_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    engine.prover.vram_partials.buffer,
                    engine.staging.buffer,
                    1,
                    &co,
                );
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;

                let mut raw = std::vec![0u64; 8 * (wgs_x as usize) * 4];
                engine.read_staging_u64s(0, &mut raw);
                let mut evals = [[0u64; 4]; 8];
                let wgs_usize = wgs_x as usize;
                for (k_slot, dst) in evals.iter_mut().enumerate() {
                    for wg in 0..wgs_usize {
                        let o = (k_slot * wgs_usize + wg) * 4;
                        *dst =
                            Self::fp4_add_arr(*dst, [raw[o], raw[o + 1], raw[o + 2], raw[o + 3]]);
                    }
                }
                Ok(evals)
            }
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn exec_prover_air_fold_round(
        &mut self,
        is_round0_base: bool,
        cur_m: usize,
        col_src: u32,
        col_dst: u32,
        sh_src: u32,
        sh_dst: u32,
        chal: [u64; 4],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            if cur_m < 2 || !cur_m.is_power_of_two() {
                return Err(crate::AccelError::LengthOverflow.into());
            }
            to_u32(cur_m)?;
            engine.prover_session()?;
            let m = to_u64(cur_m);
            let hm = m / 2;
            let half_m = cur_m / 2;
            let wgs_x = engine.check_wg_count(to_u64(half_m.div_ceil(64).max(1)))?;
            match engine.prover.air.as_ref() {
                Some(air) if m <= air.total_rows => {}
                Some(air) => return Err(out_of_range("AIR round rows (shard)", air.total_rows, m)),
                None => {
                    return Err(out_of_range(
                        "AIR shard tables (not initialised, or overwritten since)",
                        1,
                        0,
                    ));
                }
            }
            // Modes 3/4 read 256 columns of `cur_m` rows and write 256 columns of half as many
            // into `vram_work_a`; mode 5 does the same for the 3 shift tables in `vram_aux_b`.
            if !is_round0_base {
                check_disjoint(
                    u64::from(col_src),
                    cmul(m, 256)?,
                    u64::from(col_dst),
                    cmul(hm, 256)?,
                )?;
            }
            check_disjoint(
                u64::from(sh_src),
                cmul(m, 3)?,
                u64::from(sh_dst),
                cmul(hm, 3)?,
            )?;
            if is_round0_base {
                engine.prover.vram_witness.check_read(
                    "vram_witness (AIR base columns)",
                    span_end(u64::from(col_src), m, 256, WORD_BYTES)?,
                )?;
            } else {
                engine.prover.vram_work_a.check_read(
                    "vram_work_a (AIR folded columns)",
                    span_end(u64::from(col_src), m, 256, EXT4_BYTES)?,
                )?;
            }
            engine.prover.vram_aux_b.check_read(
                "vram_aux_b (AIR shift tables)",
                span_end(u64::from(sh_src), m, 3, EXT4_BYTES)?,
            )?;
            engine.prover.vram_work_a.reserve_write(
                "vram_work_a (AIR folded columns)",
                span_end(u64::from(col_dst), hm, 256, EXT4_BYTES)?,
            )?;
            engine.prover.vram_aux_b.reserve_write(
                "vram_aux_b (AIR folded shift tables)",
                span_end(u64::from(sh_dst), hm, 3, EXT4_BYTES)?,
            )?;
            unsafe {
                let kp_a = engine.prover_pipelines[ProverKernelSlot::AirRowGroupA as usize];
                engine.begin_cmd()?;
                (engine.fns.cmd_bind_pipeline)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp_a.pipeline,
                );
                (engine.fns.cmd_bind_descriptor_sets)(
                    engine.cmd_buf,
                    VK_PIPELINE_BIND_POINT_COMPUTE,
                    kp_a.pipeline_layout,
                    0,
                    1,
                    &engine.prover.ds_air,
                    0,
                    null(),
                );
                let pc_cols = AirGroupAPushConsts {
                    chal,
                    mode: if is_round0_base { 3 } else { 4 },
                    cur_m: cur_m as u32,
                    cur_r: 0,
                    flags: 0,
                    col_src,
                    col_dst,
                    sh_src: 0,
                    steps_off: 0,
                    out_off: 0,
                    base_x: 0,
                    aux0: 0,
                    aux1: 0,
                    _pad_align: [0; 4],
                };
                (engine.fns.cmd_push_constants)(
                    engine.cmd_buf,
                    kp_a.pipeline_layout,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<AirGroupAPushConsts>() as u32,
                    (&pc_cols as *const AirGroupAPushConsts).cast::<c_void>(),
                );
                (engine.fns.cmd_dispatch)(engine.cmd_buf, wgs_x, 256, 1);

                let pc_sh = AirGroupAPushConsts {
                    chal,
                    mode: 5,
                    cur_m: cur_m as u32,
                    cur_r: 0,
                    flags: 0,
                    col_src: 0,
                    col_dst: 0,
                    sh_src,
                    steps_off: 0,
                    out_off: sh_dst,
                    base_x: 0,
                    aux0: 0,
                    aux1: 0,
                    _pad_align: [0; 4],
                };
                (engine.fns.cmd_push_constants)(
                    engine.cmd_buf,
                    kp_a.pipeline_layout,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    size_of::<AirGroupAPushConsts>() as u32,
                    (&pc_sh as *const AirGroupAPushConsts).cast::<c_void>(),
                );
                (engine.fns.cmd_dispatch)(engine.cmd_buf, wgs_x, 3, 1);
                engine.submit_and_wait()
            }
        })
    }

    pub(crate) fn exec_prover_air_read_tail(
        &mut self,
        col_src_ext4: u32,
        sh_src_ext4: u32,
        out_cols: &mut [[u64; 4]],
        out_shifts: &mut [[u64; 4]],
    ) -> Result<(), VulkanError> {
        self.run_prover_job(|engine| {
            engine.prover_session()?;
            let col_bytes = cmul(to_u64(out_cols.len()), EXT4_BYTES)?;
            let sh_bytes = cmul(to_u64(out_shifts.len()), EXT4_BYTES)?;
            let total_bytes = cadd(col_bytes, sh_bytes)?;
            if total_bytes == 0 {
                return Ok(());
            }
            let col_off = cmul(u64::from(col_src_ext4), EXT4_BYTES)?;
            let sh_off = cmul(u64::from(sh_src_ext4), EXT4_BYTES)?;
            // Refuse before staging grows: both sources must be session data.
            if col_bytes > 0 {
                engine.prover.vram_work_a.check_read(
                    "vram_work_a (AIR folded columns)",
                    cadd(col_off, col_bytes)?,
                )?;
            }
            if sh_bytes > 0 {
                engine
                    .prover
                    .vram_aux_b
                    .check_read("vram_aux_b (AIR shift tables)", cadd(sh_off, sh_bytes)?)?;
            }
            unsafe {
                engine.reserve_job_staging(total_bytes)?;
                let stg_cap = engine.staging.capacity;
                engine.begin_cmd()?;
                if col_bytes > 0 {
                    let cp = checked_copy(
                        "vram_work_a (AIR folded columns)",
                        &engine.prover.vram_work_a,
                        col_off,
                        stg_cap,
                        0,
                        col_bytes,
                    )?;
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.prover.vram_work_a.buffer,
                        engine.staging.buffer,
                        1,
                        &cp,
                    );
                }
                if sh_bytes > 0 {
                    let cs = checked_copy(
                        "vram_aux_b (AIR shift tables)",
                        &engine.prover.vram_aux_b,
                        sh_off,
                        stg_cap,
                        col_bytes,
                        sh_bytes,
                    )?;
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.prover.vram_aux_b.buffer,
                        engine.staging.buffer,
                        1,
                        &cs,
                    );
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;
                if col_bytes > 0 {
                    let flat = core::slice::from_raw_parts_mut(
                        out_cols.as_mut_ptr().cast::<u64>(),
                        out_cols.len() * 4,
                    );
                    engine.read_staging_u64s(0, flat);
                }
                if sh_bytes > 0 {
                    let flat_sh = core::slice::from_raw_parts_mut(
                        out_shifts.as_mut_ptr().cast::<u64>(),
                        out_shifts.len() * 4,
                    );
                    engine.read_staging_u64s(col_bytes as usize, flat_sh);
                }
                Ok(())
            }
        })
    }

    unsafe fn teardown_device_only(&mut self) {
        if !self.device.is_null() {
            unsafe {
                let idle_rc = self.device_wait_idle_rc();
                if idle_rc != VK_SUCCESS {
                    // `vkDeviceWaitIdle` failed to establish device idle; detach handles rather
                    // than freeing buffers/command pools that may still be accessed by GPU work.
                    // For the same reason staging is not wiped: the device may still be reading
                    // or writing it. Its contents stay mapped until the process exits (module
                    // docs, "Limit").
                    self.device = null_mut();
                    self.instance = null_mut();
                    self.lib_handle = null_mut();
                    self.radv_lib_handle = null_mut();
                    return;
                }
                self.exec_state = EngineExecState::Ready;
                if self.scrub_all_vram().is_err() {
                    self.device = null_mut();
                    self.instance = null_mut();
                    self.lib_handle = null_mut();
                    self.radv_lib_handle = null_mut();
                    return;
                }
                // Idle is established. Clear the whole mapping, not just recorded residue.
                self.scrub_staging(self.staging.capacity);
                self.staging_residue_bytes = 0;
                let mut st = core::mem::take(&mut self.staging);
                let mut va = core::mem::take(&mut self.vram_a);
                let mut vb = core::mem::take(&mut self.vram_b);
                let mut vc = core::mem::take(&mut self.vram_c);
                self.destroy_gpu_buffer(&mut st);
                self.destroy_gpu_buffer(&mut va);
                self.destroy_gpu_buffer(&mut vb);
                self.destroy_gpu_buffer(&mut vc);

                let mut p_tw = core::mem::take(&mut self.prover.twiddles_24);
                let mut p_wt = core::mem::take(&mut self.prover.vram_witness);
                let mut p_mn = core::mem::take(&mut self.prover.vram_mono);
                let mut p_c0 = core::mem::take(&mut self.prover.vram_cw0);
                let mut p_t0 = core::mem::take(&mut self.prover.vram_tree0);
                let mut p_wa = core::mem::take(&mut self.prover.vram_work_a);
                let mut p_wb = core::mem::take(&mut self.prover.vram_work_b);
                let [mut p_cs0, mut p_cs1] = core::mem::take(&mut self.prover.vram_cw_stage);
                let [mut p_ts0, mut p_ts1] = core::mem::take(&mut self.prover.vram_tree_stage);
                let mut p_ai = core::mem::take(&mut self.prover.vram_aux_in);
                let mut p_ab = core::mem::take(&mut self.prover.vram_aux_b);
                let mut p_pt = core::mem::take(&mut self.prover.vram_partials);
                self.destroy_gpu_buffer(&mut p_tw);
                self.destroy_gpu_buffer(&mut p_wt);
                self.destroy_gpu_buffer(&mut p_mn);
                self.destroy_gpu_buffer(&mut p_c0);
                self.destroy_gpu_buffer(&mut p_t0);
                self.destroy_gpu_buffer(&mut p_wa);
                self.destroy_gpu_buffer(&mut p_wb);
                self.destroy_gpu_buffer(&mut p_cs0);
                self.destroy_gpu_buffer(&mut p_cs1);
                self.destroy_gpu_buffer(&mut p_ts0);
                self.destroy_gpu_buffer(&mut p_ts1);
                self.destroy_gpu_buffer(&mut p_ai);
                self.destroy_gpu_buffer(&mut p_ab);
                self.destroy_gpu_buffer(&mut p_pt);
                for mut parked in core::mem::take(&mut self.prover.limbo) {
                    self.destroy_gpu_buffer(&mut parked);
                }
                self.prover.session = None;
                self.prover.air = None;

                if self.prover.desc_pool != 0 {
                    (self.fns.destroy_descriptor_pool)(self.device, self.prover.desc_pool, null());
                    self.prover.desc_pool = 0;
                }
                self.prover.initialized = false;
                self.prover.twiddles_ready = false;
                crate::ct::ct_zeroize_u64s(&mut self.prover.salt_seed_words);

                if self.upload_fence != 0 {
                    (self.fns.destroy_fence)(self.device, self.upload_fence, null());
                    self.upload_fence = 0;
                }
                if self.fence != 0 {
                    (self.fns.destroy_fence)(self.device, self.fence, null());
                    self.fence = 0;
                }
                if self.desc_pool != 0 {
                    (self.fns.destroy_descriptor_pool)(self.device, self.desc_pool, null());
                    self.desc_pool = 0;
                }
                if self.cmd_pool != 0 {
                    (self.fns.destroy_command_pool)(self.device, self.cmd_pool, null());
                    self.cmd_pool = 0;
                    self.cmd_buf = null_mut();
                    self.upload_cmd_buf = null_mut();
                }
                for kp in self
                    .pipelines
                    .iter_mut()
                    .chain(self.prover_pipelines.iter_mut())
                {
                    if kp.pipeline != 0 {
                        (self.fns.destroy_pipeline)(self.device, kp.pipeline, null());
                        kp.pipeline = 0;
                    }
                    if kp.pipeline_layout != 0 {
                        (self.fns.destroy_pipeline_layout)(self.device, kp.pipeline_layout, null());
                        kp.pipeline_layout = 0;
                    }
                    if kp.shader_module != 0 {
                        (self.fns.destroy_shader_module)(self.device, kp.shader_module, null());
                        kp.shader_module = 0;
                    }
                }
                for dsl in [
                    &mut self.dsl_1buf,
                    &mut self.dsl_2buf,
                    &mut self.dsl_3buf,
                    &mut self.dsl_6buf,
                ] {
                    if *dsl != 0 {
                        (self.fns.destroy_descriptor_set_layout)(self.device, *dsl, null());
                        *dsl = 0;
                    }
                }
                (self.fns.destroy_device)(self.device, null());
                self.device = null_mut();
            }
        }
    }
}

impl Drop for RawVulkanEngine {
    fn drop(&mut self) {
        unsafe {
            self.teardown_device_only();
            if !self.instance.is_null() {
                (self.destroy_instance)(self.instance, null());
                self.instance = null_mut();
            }
            if !self.radv_lib_handle.is_null() {
                let _ = dlclose(self.radv_lib_handle);
                self.radv_lib_handle = null_mut();
            }
            if !self.lib_handle.is_null() {
                let _ = dlclose(self.lib_handle);
                self.lib_handle = null_mut();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AcceleratorBackend, CpuReferenceBackend};

    #[test]
    fn finished_job_leaves_no_residue_in_staging_or_vram() {
        let (mut engine, _info) = match RawVulkanEngine::try_new() {
            Ok(v) => v,
            Err(VulkanError::LibraryLoadFailed | VulkanError::NoDiscreteGpuFound) => return,
            Err(other) => panic!("unexpected engine init error: {other}"),
        };

        let mut gpu_states = [[0xA5A5_5A5A_DEAD_BEEFu64; 25]; 70];
        let mut cpu_states = gpu_states;
        engine.exec_batch_keccak(&mut gpu_states).expect("keccak");
        CpuReferenceBackend.batch_keccak_f1600(&mut cpu_states);
        assert_eq!(gpu_states, cpu_states);

        let words = 70 * 25;
        let mut seen = std::vec![u64::MAX; words];
        unsafe {
            engine.read_staging_u64s(0, &mut seen);
        }
        assert!(seen.iter().all(|&w| w == 0), "staging keeps job data");

        // Read the device-local buffer back through a fresh transfer.
        seen.fill(u64::MAX);
        unsafe {
            engine.begin_cmd().expect("begin");
            let copy = VkBufferCopy {
                src_offset: 0,
                dst_offset: 0,
                size: (words * 8) as u64,
            };
            (engine.fns.cmd_copy_buffer)(
                engine.cmd_buf,
                engine.vram_a.buffer,
                engine.staging.buffer,
                1,
                &copy,
            );
            engine.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            engine.submit_and_wait().expect("readback");
            engine.read_staging_u64s(0, &mut seen);
        }
        assert!(seen.iter().all(|&w| w == 0), "VRAM keeps job data");
    }

    #[test]
    fn transactional_vram_growth_and_quarantine_state_machine() {
        let (mut engine, _info) = match RawVulkanEngine::try_new() {
            Ok(v) => v,
            Err(VulkanError::LibraryLoadFailed | VulkanError::NoDiscreteGpuFound) => return,
            Err(other) => panic!("unexpected engine init error: {other}"),
        };

        let orig_a = engine.vram_a.buffer;
        let orig_b = engine.vram_b.buffer;
        let orig_cap_a = engine.vram_a.capacity;
        let orig_cap_b = engine.vram_b.capacity;

        // 1. Partial VRAM allocation failure: `new_a` succeeds (alloc #0), `new_b` fails (alloc #1).
        //    `ensure_vram_buffers` must destroy `new_a`, preserve `vram_a` / `vram_b` and bound
        //    descriptors untouched, and allow subsequent small dispatches to run cleanly!
        engine.fail_alloc_countdown.set(Some(1));
        let res = unsafe { engine.ensure_vram_buffers(orig_cap_a * 2, orig_cap_b * 2, 0) };
        assert!(matches!(
            res,
            Err(VulkanError::VkResult {
                op: "vkAllocateMemory",
                code: -2
            })
        ));
        assert_eq!(engine.vram_a.buffer, orig_a);
        assert_eq!(engine.vram_b.buffer, orig_b);
        assert_eq!(engine.vram_a.capacity, orig_cap_a);
        assert_eq!(engine.vram_b.capacity, orig_cap_b);

        let mut gpu_states = [[0x1234_5678_9ABC_DEF0u64; 25]; 4];
        let mut cpu_states = gpu_states;
        engine
            .exec_batch_keccak(&mut gpu_states)
            .expect("keccak after rollback");
        CpuReferenceBackend.batch_keccak_f1600(&mut cpu_states);
        assert_eq!(gpu_states, cpu_states);

        // 2. `InFlightQuarantined` recovers cleanly once `vkDeviceWaitIdle` returns `VK_SUCCESS`.
        engine.exec_state = EngineExecState::InFlightQuarantined;
        engine
            .exec_batch_keccak(&mut gpu_states)
            .expect("keccak after idle drain");
        CpuReferenceBackend.batch_keccak_f1600(&mut cpu_states);
        assert_eq!(gpu_states, cpu_states);
        assert_eq!(engine.exec_state, EngineExecState::Ready);

        // 3. `DeviceLostQuarantined` rejects every execution & resize entry point before touching
        //    staging or VRAM buffers.
        let cap_before = engine.vram_a.capacity;
        engine.exec_state = EngineExecState::DeviceLostQuarantined;
        assert!(matches!(
            engine.exec_batch_keccak(&mut gpu_states),
            Err(VulkanError::WorkspacePoisoned)
        ));
        assert!(matches!(
            unsafe { engine.ensure_vram_buffers(cap_before * 4, 0, 0) },
            Err(VulkanError::WorkspacePoisoned)
        ));
        assert_eq!(engine.vram_a.capacity, cap_before);

        // Restore `Ready` so test teardown frees the live test device cleanly.
        engine.exec_state = EngineExecState::Ready;
    }

    fn live_engine() -> Option<RawVulkanEngine> {
        match RawVulkanEngine::try_new() {
            Ok((engine, _info)) => Some(engine),
            Err(VulkanError::LibraryLoadFailed | VulkanError::NoDiscreteGpuFound) => {
                // The audit gate must not turn missing hardware into a green skip.
                assert!(
                    std::env::var_os("QSAG_REQUIRE_GPU_AUDIT").is_none(),
                    "QSAG_REQUIRE_GPU_AUDIT is set but no Vulkan GPU is available"
                );
                None
            }
            Err(other) => panic!("unexpected engine init error: {other}"),
        }
    }

    fn staging_words(engine: &RawVulkanEngine, words: usize) -> std::vec::Vec<u64> {
        let mut seen = std::vec![u64::MAX; words];
        unsafe {
            engine.read_staging_u64s(0, &mut seen);
        }
        seen
    }

    fn inject(engine: &RawVulkanEngine, point: FaultPoint, rc: i32) {
        let mut rcs = engine.injected_rcs.get();
        rcs[point as usize] = Some(rc);
        engine.injected_rcs.set(rcs);
    }

    const SECRET_WORD: u64 = 0x5EC2_E75E_C2E7_5EC2;
    const VK_ERROR_OUT_OF_HOST_MEMORY: i32 = -1;
    const VK_ERROR_DEVICE_LOST: i32 = -4;

    #[test]
    fn failed_job_wipes_staging_once_no_submission_is_live() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        let words = 70 * 25;

        // Not submitted at all, submit refused, and a real submission whose fence wait is
        // reported as failed while the job is still running on the device.
        for point in [
            FaultPoint::BeginCmd,
            FaultPoint::QueueSubmit,
            FaultPoint::FenceWait,
        ] {
            let input = [[SECRET_WORD; 25]; 70];
            let mut states = input;
            inject(&engine, point, VK_ERROR_OUT_OF_HOST_MEMORY);
            let err = engine.exec_batch_keccak(&mut states);
            assert!(
                matches!(
                    err,
                    Err(VulkanError::VkResult {
                        code: VK_ERROR_OUT_OF_HOST_MEMORY,
                        ..
                    })
                ),
                "{point:?}: {err:?}"
            );
            assert_eq!(states, input, "{point:?}: failed job wrote caller memory");
            assert_eq!(engine.exec_state, EngineExecState::Ready, "{point:?}");
            assert_eq!(engine.staging_residue_bytes, 0, "{point:?}");
            // For `FenceWait` the job's copy-back lands in staging after the call returned
            // from the (skipped) wait; a wipe that did not wait for idle would lose to it.
            assert!(
                staging_words(&engine, words).iter().all(|&w| w == 0),
                "{point:?}: staging keeps the failed job's data"
            );

            let mut gpu = [[0x1234_5678_9ABC_DEF0u64; 25]; 4];
            let mut cpu = gpu;
            engine
                .exec_batch_keccak(&mut gpu)
                .expect("job after failure");
            CpuReferenceBackend.batch_keccak_f1600(&mut cpu);
            assert_eq!(gpu, cpu, "{point:?}");
        }

        // The secret-bearing BDOZ slot packs staging by hand; same guarantee.
        let shares = [(SECRET_WORD as u128, !(SECRET_WORD as u128)); 300];
        let weights = [(3u128, 5u128); 300];
        inject(
            &engine,
            FaultPoint::QueueSubmit,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        assert!(engine.exec_bdoz_gf2_128_dot(&shares, &weights).is_err());
        assert_eq!(engine.staging_residue_bytes, 0);
        assert!(
            staging_words(&engine, 300 * 8).iter().all(|&w| w == 0),
            "staging keeps BDOZ shares after a failed job"
        );
        assert_eq!(
            engine
                .exec_bdoz_gf2_128_dot(&shares, &weights)
                .expect("bdoz"),
            CpuReferenceBackend
                .bdoz_gf2_128_batch_dot(&shares, &weights)
                .expect("cpu bdoz")
        );
    }

    #[test]
    fn wipe_is_deferred_while_idle_is_unproven_and_the_engine_fails_closed() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        let words = 70 * 25;
        let byte_len = (words * 8) as u64;
        let input = [[SECRET_WORD; 25]; 70];
        let flat_input = std::vec![SECRET_WORD; words];

        // 1. Submit fails and `vkDeviceWaitIdle` fails too: nothing proves the device is done,
        //    so the host must not touch staging yet.
        let mut states = input;
        inject(
            &engine,
            FaultPoint::QueueSubmit,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        inject(
            &engine,
            FaultPoint::DeviceWaitIdle,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        assert!(engine.exec_batch_keccak(&mut states).is_err());
        assert_eq!(engine.exec_state, EngineExecState::InFlightQuarantined);
        assert_eq!(engine.staging_residue_bytes, byte_len);
        assert_eq!(staging_words(&engine, words), flat_input);

        //    The next job first establishes idle, wipes the whole old extent, then runs in a
        //    prefix of it.
        let mut gpu = [[0x0F0F_F0F0_1234_4321u64; 25]; 4];
        let mut cpu = gpu;
        engine.exec_batch_keccak(&mut gpu).expect("job after idle");
        CpuReferenceBackend.batch_keccak_f1600(&mut cpu);
        assert_eq!(gpu, cpu);
        assert_eq!(engine.staging_residue_bytes, 0);
        assert!(staging_words(&engine, words).iter().all(|&w| w == 0));

        // 2. Device lost: no wipe, and every later job is refused before it writes anything.
        let mut states = input;
        inject(&engine, FaultPoint::QueueSubmit, VK_ERROR_DEVICE_LOST);
        assert!(matches!(
            engine.exec_batch_keccak(&mut states),
            Err(VulkanError::VkResult {
                op: "vkQueueSubmit",
                code: VK_ERROR_DEVICE_LOST
            })
        ));
        assert_eq!(engine.exec_state, EngineExecState::DeviceLostQuarantined);
        assert_eq!(engine.staging_residue_bytes, byte_len);
        assert_eq!(staging_words(&engine, words), flat_input);
        let mut other = [[7u64; 25]; 2];
        assert!(matches!(
            engine.exec_batch_keccak(&mut other),
            Err(VulkanError::WorkspacePoisoned)
        ));
        assert!(matches!(
            engine.exec_bdoz_gf2_128_dot(&[(1, 2)], &[(3, 4)]),
            Err(VulkanError::WorkspacePoisoned)
        ));
        assert_eq!(other, [[7u64; 25]; 2]);
        assert_eq!(staging_words(&engine, words), flat_input);

        // 3. Teardown that cannot establish idle detaches without wiping or freeing.
        let (device, instance, lib_handle, radv_lib_handle) = (
            engine.device,
            engine.instance,
            engine.lib_handle,
            engine.radv_lib_handle,
        );
        inject(&engine, FaultPoint::DeviceWaitIdle, VK_ERROR_DEVICE_LOST);
        unsafe {
            engine.teardown_device_only();
        }
        assert!(engine.device.is_null());
        assert_ne!(engine.staging.buffer, 0);
        assert_eq!(staging_words(&engine, words), flat_input);

        // Hand the (really idle) device back so dropping the engine wipes and frees it.
        engine.device = device;
        engine.instance = instance;
        engine.lib_handle = lib_handle;
        engine.radv_lib_handle = radv_lib_handle;
        engine.exec_state = EngineExecState::Ready;
    }

    /// `(buffer, memory, capacity, used)` of staging and of every prover buffer.
    fn buffer_snapshot(engine: &RawVulkanEngine) -> std::vec::Vec<(u64, u64, u64, u64)> {
        let p = &engine.prover;
        [
            &engine.staging,
            &p.twiddles_24,
            &p.vram_witness,
            &p.vram_mono,
            &p.vram_cw0,
            &p.vram_tree0,
            &p.vram_work_a,
            &p.vram_work_b,
            &p.vram_cw_stage[0],
            &p.vram_cw_stage[1],
            &p.vram_tree_stage[0],
            &p.vram_tree_stage[1],
            &p.vram_aux_in,
            &p.vram_aux_b,
            &p.vram_partials,
        ]
        .iter()
        .map(|b| (b.buffer, b.memory, b.capacity, b.used))
        .collect()
    }

    /// A one-polynomial, 12-variable session with room for one 16-row AIR shard.
    fn commit_small_session(engine: &mut RawVulkanEngine) {
        let poly: std::vec::Vec<u64> = (0..4096u64).map(|i| i * 7 + 1).collect();
        engine
            .exec_prover_whir_commit_round0_with_mode(
                false,
                1,
                &[7; 32],
                12,
                4,
                16,
                0,
                0,
                4096,
                |_, pos, dst| {
                    dst.copy_from_slice(&poly[pos..pos + dst.len()]);
                },
            )
            .expect("round-0 commit");
        assert_eq!(
            engine.prover.session,
            Some(ProverSessionDims {
                num_polys: 1,
                num_vars: 12,
                turboshake_canopy: false,
            })
        );
    }

    #[test]
    fn canopy_submission_failure_preserves_all_caller_nodes() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        let leaves = [[1, 2, 3, 4]; 4];
        for mode in [1, 2] {
            for point in [
                FaultPoint::BeginCmd,
                FaultPoint::QueueSubmit,
                FaultPoint::FenceWait,
            ] {
                let mut nodes = [[SECRET_WORD; 4]; 8];
                inject(&engine, point, VK_ERROR_OUT_OF_HOST_MEMORY);
                assert!(
                    engine
                        .exec_canopy_tree_poseidon2(&leaves, &[0; 4], 0, 0, 0, mode, &mut nodes,)
                        .is_err()
                );
                assert_eq!(nodes, [[SECRET_WORD; 4]; 8], "mode={mode} point={point:?}");
                assert_eq!(engine.exec_state, EngineExecState::Ready);
            }
        }
    }

    #[test]
    fn partial_prover_resize_refreshes_bindings_on_smaller_retry() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        commit_small_session(&mut engine);
        let old_witness = engine.prover.vram_witness.buffer;
        engine.fail_alloc_countdown.set(Some(1));
        let res = engine.exec_prover_whir_commit_round0_with_mode(
            false,
            1,
            &[7; 32],
            13,
            4,
            16,
            0,
            0,
            4096,
            |_, _, dst| dst.fill(1),
        );
        assert!(res.is_err());
        assert_ne!(engine.prover.vram_witness.buffer, old_witness);
        assert!(engine.prover.descriptors_dirty);
        assert!(engine.prover.session.is_none());
        let before = engine.mutation_counters.get();
        // This smaller retry fits every allocation: a local `changed` flag alone misses
        // the binding invalidated by the previous partially successful resize.
        commit_small_session(&mut engine);
        let after = engine.mutation_counters.get();
        assert_eq!(after.0, before.0);
        assert_eq!(after.1, before.1 + 1);
        assert!(!engine.prover.descriptors_dirty);
        let eq = [[1, 0, 0, 0]; 1024];
        engine
            .exec_prover_whir_batch_sumcheck_init(&eq, &[[1, 0, 0, 0]], 12)
            .unwrap();
        let (ev0, _) = engine
            .exec_prover_whir_batch_sumcheck_eval(0, 4096, 1, 0)
            .unwrap();
        let expected: u64 = (0..2048u64).map(|i| 14 * i + 1).sum();
        assert_eq!(ev0, [expected, 0, 0, 0]);
    }

    #[test]
    fn failed_prover_submission_invalidates_before_idle_and_retries_scrub() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        commit_small_session(&mut engine);
        inject(&engine, FaultPoint::FenceWait, VK_ERROR_OUT_OF_HOST_MEMORY);
        inject(
            &engine,
            FaultPoint::DeviceWaitIdle,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        let mut out = [[u64::MAX; 4]; 1];
        assert!(
            engine
                .exec_prover_whir_read_final_coeffs(0, &mut out)
                .is_err()
        );
        assert_eq!(out, [[u64::MAX; 4]; 1]);
        assert_eq!(engine.exec_state, EngineExecState::InFlightQuarantined);
        assert!(engine.prover.session.is_none());
        assert!(engine.prover.scrub_pending);
        assert_eq!(engine.prover.salt_seed_words, [0; 4]);
        // Recovery must scrub, and must not revive the failed session.
        assert!(
            engine
                .exec_prover_whir_read_final_coeffs(0, &mut out)
                .is_err()
        );
        assert_eq!(engine.exec_state, EngineExecState::Ready);
        assert!(!engine.prover.scrub_pending);
        assert!(buffer_snapshot(&engine)[2..].iter().all(|b| b.3 == 0));
        commit_small_session(&mut engine);
        // Both parity slots contain identifiable data before release.
        engine.exec_prover_whir_commit_stage(1, 16, 64, 4).unwrap();
        engine.exec_prover_whir_commit_stage(2, 16, 64, 4).unwrap();
        engine.scrub_prover_session().unwrap();
        for idx in 0..2 {
            assert_eq!(engine.prover.vram_cw_stage[idx].used, 0);
            assert_eq!(engine.prover.vram_tree_stage[idx].used, 0);
            // Read the device allocations themselves, not just the host bookkeeping.
            for buffer in [
                engine.prover.vram_cw_stage[idx].buffer,
                engine.prover.vram_tree_stage[idx].buffer,
            ] {
                unsafe {
                    engine.reserve_job_staging(2048).unwrap();
                    engine.begin_cmd().unwrap();
                    let copy = VkBufferCopy {
                        src_offset: 0,
                        dst_offset: 0,
                        size: 2048,
                    };
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        buffer,
                        engine.staging.buffer,
                        1,
                        &copy,
                    );
                    engine.cmd_barrier(
                        VK_PIPELINE_STAGE_TRANSFER_BIT,
                        VK_PIPELINE_STAGE_HOST_BIT,
                        VK_ACCESS_TRANSFER_WRITE_BIT,
                        VK_ACCESS_HOST_READ_BIT,
                    );
                    engine.submit_and_wait().unwrap();
                    assert!(staging_words(&engine, 256).iter().all(|&w| w == 0));
                    engine.settle_staging();
                }
            }
        }
    }

    #[test]
    fn either_stage_slot_holds_the_largest_folded_stage() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        // A schedule whose blowup grows as fast as its variables fold keeps every folded
        // stage at the same domain, so stage 2 needs as much room as stage 1.
        const DOMAIN: usize = 1 << 16;
        const ARITY: usize = 4;
        engine
            .exec_prover_whir_commit_round0_with_mode(
                false,
                1,
                &[7; 32],
                12,
                4,
                16,
                DOMAIN,
                DOMAIN / ARITY,
                0,
                |_, pos, dst| {
                    for (i, word) in dst.iter_mut().enumerate() {
                        *word = (pos + i) as u64 * 7 + 1;
                    }
                },
            )
            .expect("round-0 commit");
        for stage_idx in [1, 2, 3] {
            engine
                .exec_prover_whir_commit_stage(stage_idx, 16, DOMAIN, ARITY)
                .expect("largest stage");
            let mut fiber = [0u64; 4 * ARITY];
            engine
                .exec_prover_whir_gather_queries(
                    stage_idx,
                    ARITY,
                    1,
                    DOMAIN / ARITY,
                    &[(DOMAIN / ARITY - 1) as u64],
                    &[],
                    &mut fiber,
                )
                .expect("last group of the largest stage");
        }
        engine.scrub_prover_session().unwrap();
    }

    #[test]
    fn quarantined_engine_refuses_prover_growth_before_touching_any_buffer() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        commit_small_session(&mut engine);
        let before = buffer_snapshot(&engine);
        let counters = engine.mutation_counters.get();
        let eq = std::vec![[1u64, 0, 0, 0]; 768];
        let lam = [[1u64, 0, 0, 0]];
        // 2^14 rows need work buffers far beyond the 12-variable arena: this call would grow
        // (replace and free) `vram_work_a`, `vram_work_b` and `vram_aux_b`.
        let rows = 1usize << 14;
        let shifts = std::vec![[0u64; 4]; 3 * rows];
        let gammas = std::vec![[1u64, 0, 0, 0]; 250];

        // A prior submission may still be in flight, and idle cannot be established.
        engine.exec_state = EngineExecState::InFlightQuarantined;
        inject(
            &engine,
            FaultPoint::DeviceWaitIdle,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        assert!(matches!(
            engine.exec_prover_air_init_shard(0, 0, rows, &shifts, &gammas),
            Err(VulkanError::WorkspacePoisoned)
        ));
        inject(
            &engine,
            FaultPoint::DeviceWaitIdle,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        assert!(matches!(
            engine.exec_prover_whir_batch_sumcheck_init(&eq, &lam, 12),
            Err(VulkanError::WorkspacePoisoned)
        ));
        inject(
            &engine,
            FaultPoint::DeviceWaitIdle,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        assert!(matches!(
            engine.exec_prover_whir_batch_sumcheck_eval(0, 4096, 1, 0),
            Err(VulkanError::WorkspacePoisoned)
        ));
        // The inner guards refuse on their own, without consulting the device.
        let grow_to = engine.prover.vram_partials.capacity * 4;
        unsafe {
            assert!(matches!(
                engine.ensure_one_prover_buf(|p| &mut p.vram_partials, grow_to),
                Err(VulkanError::WorkspacePoisoned)
            ));
            assert!(matches!(
                engine.refresh_prover_descriptor_sets(),
                Err(VulkanError::WorkspacePoisoned)
            ));
            assert!(matches!(
                engine.begin_cmd(),
                Err(VulkanError::WorkspacePoisoned)
            ));
        }
        assert_eq!(engine.exec_state, EngineExecState::InFlightQuarantined);
        assert_eq!(
            buffer_snapshot(&engine),
            before,
            "a buffer was freed or reallocated"
        );
        assert_eq!(
            engine.mutation_counters.get(),
            counters,
            "an allocation or a descriptor write was attempted"
        );
        assert!(engine.prover.session.is_some());

        // Device lost: the same, permanently.
        engine.exec_state = EngineExecState::DeviceLostQuarantined;
        assert!(matches!(
            engine.exec_prover_air_init_shard(0, 0, rows, &shifts, &gammas),
            Err(VulkanError::WorkspacePoisoned)
        ));
        assert!(matches!(
            engine.exec_prover_whir_batch_sumcheck_read_tail(1, 1, 0, &mut [[0; 4]], &mut [[0; 4]]),
            Err(VulkanError::WorkspacePoisoned)
        ));
        assert_eq!(buffer_snapshot(&engine), before);
        assert_eq!(engine.mutation_counters.get(), counters);

        // The test device really is idle: once that is established the engine works again,
        // and growth is allowed.
        engine.exec_state = EngineExecState::InFlightQuarantined;
        engine
            .exec_prover_whir_batch_sumcheck_init(&eq, &lam, 12)
            .expect("init after idle");
        assert_eq!(engine.exec_state, EngineExecState::Ready);
        let old_partials = engine.prover.vram_partials.buffer;
        assert!(unsafe {
            engine
                .ensure_one_prover_buf(|p| &mut p.vram_partials, grow_to)
                .expect("growth when ready")
        });
        assert_ne!(engine.prover.vram_partials.buffer, old_partials);
        assert!(engine.prover.vram_partials.capacity >= grow_to);
        unsafe {
            engine.refresh_prover_descriptor_sets().expect("refresh");
        }
    }

    /// Every non-prover kernel job derives its extents from the slices it was handed and
    /// refuses, before touching the device, what the storage range or the layer tweak cannot
    /// hold. The storage limit is lowered here so the refusals need no large allocation.
    #[test]
    fn kernel_jobs_rederive_their_ranges_and_refuse_before_dispatch() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        let real_limit = engine.max_storage_range;
        let seed = [1u64, 2, 3, 4];
        let leaves: std::vec::Vec<[u64; 4]> = (0..4u64).map(|i| [i, i + 1, i + 2, i + 3]).collect();

        // 96 bytes: one Poseidon2 state fits, two do not; twelve words fit, sixteen do not.
        engine.max_storage_range = 96;
        let submissions = engine.mutation_counters.get();
        let too_big = |res: Result<(), VulkanError>| {
            assert!(
                matches!(res, Err(VulkanError::BufferExceedsMaxStorageRange { .. })),
                "{res:?}"
            );
        };
        too_big(engine.exec_batch_keccak(&mut [[0u64; 25]; 1]));
        too_big(engine.exec_batch_poseidon2(&mut [[0u64; 12]; 2]));
        too_big(engine.exec_goldilocks_ntt_canonical(&mut [0u64; 16], false));
        too_big(engine.exec_goldilocks_ntt(&mut [0u64; 16], &[1u64; 8], false));
        too_big(engine.exec_coset_lde_ext2(&[[0u64; 2]; 4], 2, 7, &mut [[0u64; 2]; 8]));
        too_big(engine.exec_merkle_layer(&leaves, &seed, 0, 0, &mut [[0u64; 4]; 2]));
        too_big(engine.exec_merkle_full_tree(&leaves, &seed, 0).map(|_| ()));
        too_big(
            engine
                .exec_bdoz_gf2_128_dot(&[(1, 2); 4], &[(3, 4); 4])
                .map(|_| ()),
        );
        assert_eq!(
            engine.mutation_counters.get(),
            submissions,
            "a refused job allocated or rebound a buffer"
        );
        assert_eq!(engine.exec_state, EngineExecState::Ready);
        engine.max_storage_range = real_limit;

        // Shapes the shaders assume.
        let shape = |res: Result<(), VulkanError>| {
            assert!(matches!(res, Err(VulkanError::Accel(_))), "{res:?}");
        };
        shape(engine.exec_goldilocks_ntt_canonical(&mut [], false));
        shape(engine.exec_goldilocks_ntt_canonical(&mut [0u64; 12], false));
        shape(engine.exec_goldilocks_ntt(&mut [0u64; 8], &[1u64; 3], false));
        shape(engine.exec_coset_lde_ext2(&[[0u64; 2]; 3], 2, 7, &mut [[0u64; 2]; 6]));
        shape(engine.exec_coset_lde_ext2(&[[0u64; 2]; 4], 2, 7, &mut [[0u64; 2]; 4]));
        shape(engine.exec_merkle_layer(&leaves, &seed, 0, 0, &mut [[0u64; 4]; 1]));
        shape(engine.exec_merkle_layer(
            &leaves,
            &seed,
            0,
            u64::from(u32::MAX),
            &mut [[0u64; 4]; 2],
        ));
        shape(
            engine
                .exec_merkle_full_tree(&leaves[..3], &seed, 0)
                .map(|_| ()),
        );
        shape(engine.exec_merkle_full_tree(&[], &seed, 0).map(|_| ()));
        shape(
            engine
                .exec_bdoz_gf2_128_dot(&[(1, 2); 4], &[(3, 4); 3])
                .map(|_| ()),
        );

        // A four-leaf tree uses layers `base` and `base + 1`: the last base that fits is
        // `u32::MAX - 1`, and it must agree with the CPU reference layer by layer.
        shape(
            engine
                .exec_merkle_full_tree(&leaves, &seed, u32::MAX)
                .map(|_| ()),
        );
        let base = u32::MAX - 1;
        let mut mid = [[0u64; 4]; 2];
        let mut root = [[0u64; 4]; 1];
        crate::poseidon2::merkle_layer_poseidon2_at_cpu(&leaves, &seed, base, 0, &mut mid)
            .expect("cpu layer 0");
        crate::poseidon2::merkle_layer_poseidon2_at_cpu(&mid, &seed, base + 1, 0, &mut root)
            .expect("cpu layer 1");
        assert_eq!(
            engine
                .exec_merkle_full_tree(&leaves, &seed, base)
                .expect("gpu tree"),
            root[0]
        );
        assert_eq!(engine.exec_state, EngineExecState::Ready);
    }

    /// What the driver reports for each pipeline on this device, and that it passes the gate
    /// the engine applied at construction.
    #[test]
    fn live_driver_reports_scratch_and_spill_statistics_for_every_pipeline() {
        let Ok((_engine, info)) = RawVulkanEngine::try_new() else {
            assert!(
                std::env::var_os("QSAG_REQUIRE_GPU_AUDIT").is_none(),
                "QSAG_REQUIRE_GPU_AUDIT is set but no Vulkan GPU is available"
            );
            return;
        };
        for tel in info.pipelines.iter().chain(info.prover_pipelines.iter()) {
            std::eprintln!("PIPELINE_TELEMETRY {tel:?}");
            assert_eq!(tel.audit(), Ok(()));
            assert_eq!(tel.subgroup_size, Some(32));
        }
    }

    #[test]
    fn displaced_buffers_are_wiped_before_they_are_released() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        // 1. Host-mapped staging displaced by a second, larger reservation inside one job.
        let first = engine.staging.capacity.max(4096);
        let words = (first / 8) as usize;
        unsafe {
            engine.reserve_job_staging(first).expect("reserve");
            engine.write_staging_u64s(0, &std::vec![SECRET_WORD; words]);
            assert!(
                staging_words(&engine, words)
                    .iter()
                    .all(|&w| w == SECRET_WORD)
            );
            let old = engine.staging.buffer;
            engine.last_unmapped.set(None);
            engine.reserve_job_staging(first * 2 + 8).expect("grow");
            assert_ne!(engine.staging.buffer, old);
            assert_eq!(
                engine.last_unmapped.get(),
                Some((first, true)),
                "the displaced mapping still held job data when it was unmapped"
            );
            engine.settle_staging();
        }
        assert_eq!(engine.staging_residue_bytes, 0);

        // 2. A device-local prover buffer displaced mid-session: if its scrub cannot complete,
        //    it stays installed and nothing is freed while the device may still be using it.
        commit_small_session(&mut engine);
        let before = buffer_snapshot(&engine);
        let grow_to = engine.prover.vram_work_b.capacity * 2;
        assert!(engine.prover.vram_work_b.used > 0);
        inject(
            &engine,
            FaultPoint::QueueSubmit,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        inject(
            &engine,
            FaultPoint::DeviceWaitIdle,
            VK_ERROR_OUT_OF_HOST_MEMORY,
        );
        let res = unsafe { engine.ensure_one_prover_buf(|p| &mut p.vram_work_b, grow_to) };
        assert!(matches!(
            res,
            Err(VulkanError::VkResult {
                op: "vkQueueSubmit",
                code: VK_ERROR_OUT_OF_HOST_MEMORY
            })
        ));
        assert_eq!(engine.exec_state, EngineExecState::InFlightQuarantined);
        assert_eq!(buffer_snapshot(&engine), before);
        assert_eq!(
            engine.prover.limbo.len(),
            1,
            "the replacement must be parked, not freed"
        );
        // Drain the unused idle fault, then recover and grow for real.
        assert!(unsafe { engine.ensure_ready() }.is_err());
        unsafe {
            engine.ensure_ready().expect("idle");
            assert!(
                engine
                    .ensure_one_prover_buf(|p| &mut p.vram_work_b, grow_to)
                    .expect("growth")
            );
            engine.refresh_prover_descriptor_sets().expect("refresh");
        }
        assert_ne!(engine.prover.vram_work_b.buffer, before[7].0);
        // The replacement starts out zero: read its first words back.
        let probe = 512usize;
        unsafe {
            engine
                .reserve_job_staging((probe * 8) as u64)
                .expect("reserve");
            engine.write_staging_u64s(0, &std::vec![SECRET_WORD; probe]);
            let copy = checked_copy(
                "probe",
                &engine.prover.vram_work_b,
                0,
                engine.staging.capacity,
                0,
                (probe * 8) as u64,
            )
            .expect("range");
            engine.begin_cmd().expect("begin");
            (engine.fns.cmd_copy_buffer)(
                engine.cmd_buf,
                engine.prover.vram_work_b.buffer,
                engine.staging.buffer,
                1,
                &copy,
            );
            engine.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            engine.submit_and_wait().expect("readback");
        }
        assert!(staging_words(&engine, probe).iter().all(|&w| w == 0));
        unsafe {
            engine.settle_staging();
        }
    }

    #[test]
    fn prover_entry_points_need_a_committed_session_and_in_range_arguments() {
        let Some(mut engine) = live_engine() else {
            return;
        };
        fn clean<T: core::fmt::Debug>(res: Result<T, VulkanError>) {
            assert!(
                matches!(
                    res,
                    Err(VulkanError::Accel(
                        crate::AccelError::LengthOverflow
                            | crate::AccelError::LengthMismatch { .. }
                    ))
                ),
                "{res:?}"
            );
        }
        let mut one = [[0u64; 4]; 1];
        let mut other = [[0u64; 4]; 1];
        // No arena at all: nothing is bound, copied or dispatched.
        let counters = engine.mutation_counters.get();
        clean(engine.exec_prover_whir_batch_sumcheck_read_tail(1, 1, 0, &mut one, &mut other));
        clean(engine.exec_prover_whir_batch_sumcheck_eval(0, 4096, 1, 0));
        clean(engine.exec_prover_air_read_tail(0, 0, &mut one, &mut other));
        clean(engine.exec_prover_whir_read_final_coeffs(0, &mut one));
        assert_eq!(engine.mutation_counters.get(), counters);

        commit_small_session(&mut engine);
        let work_b_used = engine.prover.vram_work_b.used;
        // The last element of the reserved extent is readable, one past it is not.
        let last = (work_b_used / 32 - 1) as u32;
        engine
            .exec_prover_whir_read_final_coeffs(last, &mut one)
            .expect("in range");
        clean(engine.exec_prover_whir_read_final_coeffs(last + 1, &mut one));
        // A rejected call ends the session: its buffers are scrubbed and unreadable.
        assert_eq!(engine.prover.session, None);
        assert_eq!(engine.prover.vram_work_b.used, 0);
        clean(engine.exec_prover_whir_read_final_coeffs(0, &mut one));

        commit_small_session(&mut engine);
        clean(engine.exec_prover_whir_batch_sumcheck_read_tail(
            1,
            1,
            u32::MAX,
            &mut one,
            &mut other,
        ));
        commit_small_session(&mut engine);
        let eq = std::vec![[1u64, 0, 0, 0]; 768];
        let lam = [[1u64, 0, 0, 0]];
        for num_vars in [27usize, 63, 64, usize::BITS as usize, usize::MAX] {
            clean(engine.exec_prover_whir_batch_sumcheck_init(&eq, &lam, num_vars));
            commit_small_session(&mut engine);
        }
        // Dimensions other than the committed ones.
        clean(engine.exec_prover_whir_batch_sumcheck_init(&eq, &lam, 11));
        // 3-byte 768-entry equality table cannot represent `num_vars > 24`.
        clean(engine.exec_prover_whir_batch_sumcheck_init(&eq, &lam, 25));
        engine.exec_state = EngineExecState::Ready;
    }

    #[test]
    fn macos_portability_candidates_and_device_type_policy() {
        let names: std::vec::Vec<&str> = MACOS_VULKAN_LIB_CANDIDATES
            .iter()
            .map(|c| c.to_str().expect("utf8 dylib path"))
            .collect();
        assert_eq!(
            names,
            [
                "/opt/homebrew/lib/libvulkan.1.dylib",
                "/opt/homebrew/lib/libMoltenVK.dylib",
            ]
        );
        assert!(names.iter().all(|p| p.starts_with('/')));
        assert_eq!(
            VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR,
            0x0000_0001
        );
        // Linux: accepts integrated & discrete hardware GPUs; rejects virtual & CPU ICDs (`llvmpipe = 4`).
        assert!(is_accepted_gpu_device_type(
            VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU,
            false
        ));
        assert!(is_accepted_gpu_device_type(
            VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU,
            false
        ));
        assert!(!is_accepted_gpu_device_type(
            VK_PHYSICAL_DEVICE_TYPE_VIRTUAL_GPU,
            false
        ));
        assert!(!is_accepted_gpu_device_type(4, false));
        assert!(!is_accepted_gpu_device_type(0, false));
        // macOS MoltenVK: accepts integrated, discrete, and virtualized Apple Silicon GPUs; still rejects CPU (`4`).
        assert!(is_accepted_gpu_device_type(
            VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU,
            true
        ));
        assert!(is_accepted_gpu_device_type(
            VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU,
            true
        ));
        assert!(is_accepted_gpu_device_type(
            VK_PHYSICAL_DEVICE_TYPE_VIRTUAL_GPU,
            true
        ));
        assert!(!is_accepted_gpu_device_type(4, true));
        assert!(!is_accepted_gpu_device_type(0, true));
    }
}
