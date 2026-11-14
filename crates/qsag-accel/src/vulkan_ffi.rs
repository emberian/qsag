//! Minimal zero-dependency Linux x86_64/aarch64 Vulkan 1.2+ dynamic loader (`dlopen("libvulkan.so.1")`)
//! and RAII compute engine targeting discrete RDNA2/SPIR-V GPUs with `shaderInt64`.
//!
//! All `unsafe` FFI calls in `qsag-accel` are strictly isolated inside this single module.

use core::ffi::{c_char, c_void};
use core::mem::{MaybeUninit, size_of};
use core::ptr::{null, null_mut};

use crate::KernelSlot;
use crate::goldilocks::{
    gl_inv_or_zero, gl_neg, gl_reduce_u64, goldilocks_primitive_root,
};
use crate::spirv_kernels::spirv_kernel_words;
use crate::vulkan::{VulkanDeviceInfo, VulkanError};

const RTLD_NOW: i32 = 2;
const RTLD_LOCAL: i32 = 0;

#[link(name = "dl")]
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

const VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU: u32 = 2;

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
    layer: u32,
    base_parent: u32,
}
const _: () = assert!(size_of::<MerklePushConsts>() == 72);

#[repr(C)]
struct BdozDotPushConsts {
    num_elements: u32,
    num_groups: u32,
    mode: u32,
    _pad: u32,
}
const _: () = assert!(size_of::<BdozDotPushConsts>() == 16);

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
    mapped: *mut u8,
}

impl Default for GpuBuffer {
    fn default() -> Self {
        Self {
            buffer: 0,
            memory: 0,
            capacity: 0,
            mapped: null_mut(),
        }
    }
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

pub(crate) struct RawVulkanEngine {
    lib_handle: *mut c_void,
    destroy_instance: PfnVkDestroyInstance,
    instance: VkInstance,
    device: VkDevice,
    fns: DeviceFns,
    queue: VkQueue,
    mem_props: VkPhysicalDeviceMemoryProperties,
    wave32: bool,
    executable_fns: Option<(GetExecutables, GetStatistics)>,
    telemetry: [crate::vulkan::PipelineTelemetry; KernelSlot::COUNT],
    max_wg_x: u32,
    max_storage_range: u64,
    exec_state: EngineExecState,
    #[cfg(test)]
    fail_alloc_countdown: core::cell::Cell<Option<u32>>,
    dsl_1buf: VkDescriptorSetLayout,
    dsl_2buf: VkDescriptorSetLayout,
    dsl_3buf: VkDescriptorSetLayout,
    pipelines: [KernelPipeline; KernelSlot::COUNT],
    desc_pool: VkDescriptorPool,
    ds_1buf_a: VkDescriptorSet,
    ds_2buf_ab: VkDescriptorSet,
    ds_2buf_ba: VkDescriptorSet,
    ds_3buf_abc: VkDescriptorSet,
    cmd_pool: VkCommandPool,
    cmd_buf: VkCommandBuffer,
    fence: VkFence,
    staging: GpuBuffer,
    vram_a: GpuBuffer,
    vram_b: GpuBuffer,
    vram_c: GpuBuffer,
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
        if (type_bits & bit) != 0 && (mt.property_flags & required) == required {
            return Some(idx as u32);
        }
    }
    None
}

impl RawVulkanEngine {
    pub(crate) fn try_new() -> Result<(Self, VulkanDeviceInfo), VulkanError> {
        if cfg!(target_endian = "big") {
            return Err(VulkanError::UnsupportedPlatform);
        }
        let lib_handle = unsafe { dlopen(c"libvulkan.so.1".as_ptr(), RTLD_NOW | RTLD_LOCAL) };
        if lib_handle.is_null() {
            return Err(VulkanError::LibraryLoadFailed);
        }

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
            flags: 0,
            p_application_info: &app_info,
            enabled_layer_count: 0,
            pp_enabled_layer_names: null(),
            enabled_extension_count: 0,
            pp_enabled_extension_names: null(),
        };
        let mut instance: VkInstance = null_mut();
        let rc = unsafe { create_instance(&inst_info, null(), &mut instance) };
        if rc != VK_SUCCESS {
            unsafe {
                let _ = dlclose(lib_handle);
            }
            // VK_ERROR_INITIALIZATION_FAILED (-3) / VK_ERROR_INCOMPATIBLE_DRIVER (-9)
            // occur on headless hosts where libvulkan.so.1 is present without any GPU ICD.
            if rc == -3 || rc == -9 {
                return Err(VulkanError::NoDiscreteGpuFound);
            }
            return Err(VulkanError::VkResult {
                op: "vkCreateInstance",
                code: rc,
            });
        }

        let destroy_instance: PfnVkDestroyInstance = match unsafe {
            load_inst_fn(gipa, instance, c"vkDestroyInstance", "vkDestroyInstance")
        } {
            Ok(f) => f,
            Err(e) => {
                unsafe {
                    let _ = dlclose(lib_handle);
                }
                return Err(e);
            }
        };

        let mut lib_slot = lib_handle;
        let init_res = unsafe {
            Self::init_with_instance(&mut lib_slot, gipa, &mut instance, destroy_instance)
        };
        if init_res.is_err() {
            unsafe {
                if !instance.is_null() {
                    destroy_instance(instance, null());
                }
                if !lib_slot.is_null() {
                    let _ = dlclose(lib_slot);
                }
            }
        }
        init_res
    }

    unsafe fn init_with_instance(
        lib_handle: &mut *mut c_void,
        gipa: PfnVkGetInstanceProcAddr,
        instance_slot: &mut VkInstance,
        destroy_instance: PfnVkDestroyInstance,
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

        // Select discrete GPU (`VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU`), preferring AMD (`0x1002`).
        let mut chosen: Option<(
            VkPhysicalDevice,
            VkPhysicalDevicePropertiesRaw,
            VkPhysicalDeviceFeatures,
        )> = None;
        let mut saw_discrete_without_int64 = false;
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
            if props.device_type == VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU {
                if feats.flags[FEATURE_SHADER_INT64_INDEX] == 0 {
                    saw_discrete_without_int64 = true;
                    continue;
                }
                let replace = match &chosen {
                    None => true,
                    Some((_, prev_props, _)) => {
                        (prev_props.vendor_id != 0x1002 && props.vendor_id == 0x1002)
                            || (prev_props.vendor_id == props.vendor_id
                                && props.read_limits_u32(512 - 296)
                                    > prev_props.read_limits_u32(512 - 296))
                    }
                };
                if replace {
                    chosen = Some((pd, props, feats));
                }
            }
        }

        let (phys_dev, props, _) = match chosen {
            Some(c) => c,
            None if saw_discrete_without_int64 => return Err(VulkanError::MissingShaderInt64),
            None => return Err(VulkanError::NoDiscreteGpuFound),
        };

        // SPIR-V modules target Vulkan 1.2. Check all fixed shader resource limits
        // before creating any device objects (not merely before dispatch).
        if props.api_version < VK_API_VERSION_1_2
            || props.max_compute_work_group_invocations() < 256
            || props.read_limits_u32(532 - 296) < 256
            || props.max_push_constants_size() < 72
            || props.read_limits_u32(512 - 296) < 8192
            || props.max_compute_work_group_count_x() == 0
        {
            return Err(VulkanError::UnsupportedDeviceLimits);
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
        let mut sg_props = SubgroupProperties {
            s_type: 1000225000,
            p_next: null_mut(),
            min: 0,
            max: 0,
            max_compute_subgroups: 0,
            required_stages: 0,
        };
        if has_subgroup {
            let get_properties2: unsafe extern "C" fn(VkPhysicalDevice, *mut Properties2) = unsafe {
                load_inst_fn(
                    gipa,
                    instance,
                    c"vkGetPhysicalDeviceProperties2",
                    "vkGetPhysicalDeviceProperties2",
                )?
            };
            let mut p2 = Properties2 {
                s_type: 1000059001,
                p_next: (&mut sg_props as *mut SubgroupProperties).cast(),
                properties: unsafe { core::mem::zeroed() },
            };
            unsafe {
                get_properties2(phys_dev, &mut p2);
            }
        }
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
            destroy_instance,
            instance: core::mem::replace(instance_slot, null_mut()),
            device,
            fns,
            queue,
            mem_props,
            wave32,
            executable_fns: None,
            telemetry: [crate::vulkan::PipelineTelemetry::default(); KernelSlot::COUNT],
            max_wg_x: props.max_compute_work_group_count_x(),
            max_storage_range: props.max_storage_buffer_range() as u64,
            exec_state: EngineExecState::Ready,
            #[cfg(test)]
            fail_alloc_countdown: core::cell::Cell::new(None),
            dsl_1buf: 0,
            dsl_2buf: 0,
            dsl_3buf: 0,
            pipelines: [KernelPipeline {
                shader_module: 0,
                pipeline_layout: 0,
                pipeline: 0,
            }; KernelSlot::COUNT],
            desc_pool: 0,
            ds_1buf_a: 0,
            ds_2buf_ab: 0,
            ds_2buf_ba: 0,
            ds_3buf_abc: 0,
            cmd_pool: 0,
            cmd_buf: null_mut(),
            fence: 0,
            staging: GpuBuffer::default(),
            vram_a: GpuBuffer::default(),
            vram_b: GpuBuffer::default(),
            vram_c: GpuBuffer::default(),
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

    unsafe fn collect_telemetry(
        &mut self,
        slot: KernelSlot,
        pipeline: VkPipeline,
    ) -> Result<(), VulkanError> {
        let Some((get_properties, get_statistics)) = self.executable_fns else {
            return Ok(());
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
        // These are single-stage compute pipelines. Refuse ambiguous telemetry rather
        // than silently reporting one executable's statistics as the whole pipeline.
        if properties.len() != 1 {
            return Err(VulkanError::PipelineAuditFailed(
                "expected one compute executable",
            ));
        }
        let subgroup_size = properties[0].subgroup_size;
        if self.wave32 && subgroup_size != 32 {
            return Err(VulkanError::UnexpectedSubgroupSize {
                slot,
                required: 32,
                reported: subgroup_size,
            });
        }
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
            // UINT64 is the only accepted representation; absence is never zero.
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
        self.telemetry[slot as usize] = crate::vulkan::PipelineTelemetry {
            subgroup_size: Some(subgroup_size),
            scratch_bytes: scratch,
            vgprs,
            sgprs,
            lds_bytes: lds,
            spilled_vgprs,
            spilled_sgprs,
        };
        if scratch.is_some_and(|bytes| bytes != 0) {
            return Err(VulkanError::PipelineAuditFailed(
                "nonzero private scratch memory",
            ));
        }
        if spilled_vgprs.is_some_and(|n| n != 0) || spilled_sgprs.is_some_and(|n| n != 0) {
            return Err(VulkanError::PipelineAuditFailed("spilled registers"));
        }
        Ok(())
    }

    unsafe fn create_dsl(&self, num_bindings: u32) -> Result<VkDescriptorSetLayout, VulkanError> {
        let mut bindings = [VkDescriptorSetLayoutBinding {
            binding: 0,
            descriptor_type: VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
            descriptor_count: 1,
            stage_flags: VK_SHADER_STAGE_COMPUTE_BIT,
            p_immutable_samplers: null(),
        }; 3];
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

    unsafe fn build_pipelines_and_pools(&mut self, qf_idx: u32) -> Result<(), VulkanError> {
        self.dsl_1buf = unsafe { self.create_dsl(1)? };
        self.dsl_2buf = unsafe { self.create_dsl(2)? };
        self.dsl_3buf = unsafe { self.create_dsl(3)? };

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
            self.pipelines[slot as usize].shader_module = sm;

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
            check_vk("vkCreatePipelineLayout", unsafe {
                (self.fns.create_pipeline_layout)(self.device, &pl_info, null(), &mut pl)
            })?;
            self.pipelines[slot as usize].pipeline_layout = pl;

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
            // Retain any returned handle even on failure so RAII owns its cleanup.
            self.pipelines[slot as usize].pipeline = pipe;
            check_vk("vkCreateComputePipelines", rc)?;
            unsafe {
                self.collect_telemetry(slot, pipe)?;
            }
        }

        // Descriptor pool: 4 sets (1 + 2 + 2 + 3 = 8 storage buffer descriptors).
        let pool_size = VkDescriptorPoolSize {
            ty: VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
            descriptor_count: 8,
        };
        let dp_info = VkDescriptorPoolCreateInfo {
            s_type: VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO,
            p_next: null(),
            flags: 0,
            max_sets: 4,
            pool_size_count: 1,
            p_pool_sizes: &pool_size,
        };
        check_vk("vkCreateDescriptorPool", unsafe {
            (self.fns.create_descriptor_pool)(self.device, &dp_info, null(), &mut self.desc_pool)
        })?;

        let set_layouts = [self.dsl_1buf, self.dsl_2buf, self.dsl_2buf, self.dsl_3buf];
        let mut sets = [0u64; 4];
        let dsa_info = VkDescriptorSetAllocateInfo {
            s_type: VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO,
            p_next: null(),
            descriptor_pool: self.desc_pool,
            descriptor_set_count: 4,
            p_set_layouts: set_layouts.as_ptr(),
        };
        check_vk("vkAllocateDescriptorSets", unsafe {
            (self.fns.allocate_descriptor_sets)(self.device, &dsa_info, sets.as_mut_ptr())
        })?;
        self.ds_1buf_a = sets[0];
        self.ds_2buf_ab = sets[1];
        self.ds_2buf_ba = sets[2];
        self.ds_3buf_abc = sets[3];

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
            command_buffer_count: 1,
        };
        check_vk("vkAllocateCommandBuffers", unsafe {
            (self.fns.allocate_command_buffers)(self.device, &cba_info, &mut self.cmd_buf)
        })?;

        let fence_info = VkFenceCreateInfo {
            s_type: VK_STRUCTURE_TYPE_FENCE_CREATE_INFO,
            p_next: null(),
            flags: 0,
        };
        check_vk("vkCreateFence", unsafe {
            (self.fns.create_fence)(self.device, &fence_info, null(), &mut self.fence)
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

    unsafe fn destroy_gpu_buffer(&mut self, buf: &mut GpuBuffer) {
        if !buf.mapped.is_null() && buf.memory != 0 {
            unsafe {
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
    }

    unsafe fn alloc_gpu_buffer(
        &self,
        byte_size: u64,
        host_staging: bool,
    ) -> Result<GpuBuffer, VulkanError> {
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
            mapped,
        })
    }

    /// Verify that no prior submission remains potentially in flight before mutating staging
    /// memory, reallocating buffers, updating descriptors, or resetting the command pool.
    /// If a previous fence wait failed transiently, recovery is permitted ONLY after
    /// `vkDeviceWaitIdle` succeeds (`VK_SUCCESS`).
    unsafe fn ensure_ready(&mut self) -> Result<(), VulkanError> {
        const VK_ERROR_DEVICE_LOST: i32 = -4;
        match self.exec_state {
            EngineExecState::Ready => Ok(()),
            EngineExecState::DeviceLostQuarantined => Err(VulkanError::WorkspacePoisoned),
            EngineExecState::InFlightQuarantined => {
                let rc = unsafe { (self.fns.device_wait_idle)(self.device) };
                if rc == VK_SUCCESS {
                    self.exec_state = EngineExecState::Ready;
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

    unsafe fn ensure_staging(&mut self, required: u64) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        if self.staging.capacity >= required && self.staging.buffer != 0 {
            return Ok(());
        }
        let target = required
            .checked_next_power_of_two()
            .unwrap_or(required)
            .max(MIN_BUFFER_ALLOC_BYTES);
        let new_buf = unsafe { self.alloc_gpu_buffer(target, true)? };
        let mut old = core::mem::replace(&mut self.staging, new_buf);
        unsafe {
            self.destroy_gpu_buffer(&mut old);
        }
        Ok(())
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
        let target = required
            .checked_next_power_of_two()
            .unwrap_or(required)
            .min(self.max_storage_range)
            .max(required)
            .max(MIN_BUFFER_ALLOC_BYTES);
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

    unsafe fn begin_cmd(&self) -> Result<(), VulkanError> {
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
    /// hash-chain states); none of them stays resident in device memory past the job.
    /// Every `bytes` is a multiple of 8 and at most the buffer's capacity.
    unsafe fn cmd_scrub_vram(&self, ranges: &[(VkBuffer, u64)]) {
        unsafe {
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT | VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT | VK_ACCESS_TRANSFER_READ_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
            );
            for &(buffer, bytes) in ranges {
                if bytes != 0 {
                    (self.fns.cmd_fill_buffer)(self.cmd_buf, buffer, 0, bytes, 0);
                }
            }
        }
    }

    /// Zero the first `bytes` of the host-mapped staging buffer once a job's result has been
    /// read back (or before the mapping is released).
    unsafe fn scrub_staging(&mut self, bytes: u64) {
        if self.staging.mapped.is_null() {
            return;
        }
        let len = bytes.min(self.staging.capacity) as usize;
        unsafe {
            core::ptr::write_bytes(self.staging.mapped, 0, len);
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
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
        let submit_rc = unsafe { (self.fns.queue_submit)(self.queue, 1, &submit, self.fence) };
        if submit_rc != VK_SUCCESS {
            if submit_rc == VK_ERROR_DEVICE_LOST {
                self.exec_state = EngineExecState::DeviceLostQuarantined;
            }
            return Err(VulkanError::VkResult {
                op: "vkQueueSubmit",
                code: submit_rc,
            });
        }
        let wait_rc =
            unsafe { (self.fns.wait_for_fences)(self.device, 1, &self.fence, VK_TRUE, u64::MAX) };
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

    unsafe fn exec_inplace_states<const LANES: usize>(
        &mut self,
        slot: KernelSlot,
        states: &mut [[u64; LANES]],
    ) -> Result<(), VulkanError> {
        unsafe {
            self.ensure_ready()?;
        }
        let num_states = states.len();
        self.check_storage_bytes(num_states, LANES * 8)?;
        if num_states == 0 {
            return Ok(());
        }
        let total_words =
            num_states
                .checked_mul(LANES)
                .ok_or(VulkanError::BufferExceedsMaxStorageRange {
                    requested: u64::MAX,
                    limit: self.max_storage_range,
                })?;
        let byte_len = (total_words as u64).checked_mul(8).ok_or(
            VulkanError::BufferExceedsMaxStorageRange {
                requested: u64::MAX,
                limit: self.max_storage_range,
            },
        )?;

        unsafe {
            self.ensure_staging(byte_len)?;
            self.ensure_vram_buffers(byte_len, 0, 0)?;

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

            let total_wg = (num_states as u64).div_ceil(64) as u32;
            let mut wg_done = 0u32;
            while wg_done < total_wg {
                let wg_chunk = (total_wg - wg_done).min(self.max_wg_x);
                let pc = BatchStatesPushConsts {
                    num_states: num_states as u32,
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
            self.scrub_staging(byte_len);
        }
        Ok(())
    }

    pub(crate) fn exec_batch_keccak(
        &mut self,
        states: &mut [[u64; 25]],
    ) -> Result<(), VulkanError> {
        unsafe { self.exec_inplace_states(KernelSlot::BatchKeccakF1600, states) }
    }

    pub(crate) fn exec_batch_poseidon2(
        &mut self,
        states: &mut [[u64; 12]],
    ) -> Result<(), VulkanError> {
        unsafe { self.exec_inplace_states(KernelSlot::BatchPoseidon2Perm12, states) }
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
        unsafe {
            self.ensure_ready()?;
        }
        let n = buf.len();
        if !n.is_power_of_two() || (n > 1 && twiddles.len() != n / 2) {
            return Err(VulkanError::Accel(crate::AccelError::LengthOverflow));
        }
        self.check_storage_bytes(n, 8)?;
        let log2_n = n.trailing_zeros();
        let byte_len = (n as u64) * 8;

        unsafe {
            self.ensure_staging(byte_len)?;
            self.ensure_vram_buffers(byte_len, 0, 0)?;
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
            let wg_full = (n as u64).div_ceil(256) as u32;
            self.dispatch_ntt_mode(
                kp.pipeline_layout,
                wg_full,
                NttPushConsts {
                    w_step: 0,
                    n: n as u32,
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
                    let wg_blocks = (n >> 9) as u32;
                    self.dispatch_ntt_mode(
                        kp.pipeline_layout,
                        wg_blocks,
                        NttPushConsts {
                            w_step: stage_root(9),
                            n: n as u32,
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

                let wg_half = ((n >> 1) as u64).div_ceil(256) as u32;
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
                            n: n as u32,
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
                            n: n as u32,
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
            self.scrub_staging(byte_len);
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
        len: usize,
        inverse: bool,
    ) -> Result<(), VulkanError> {
        let log2_len = len.trailing_zeros();
        let wg_full = (len as u64).div_ceil(256) as u32;
        unsafe {
            self.dispatch_lde_mode(
                pl,
                wg_full,
                CosetLdePushConsts {
                    w_step: 0,
                    shift_c: 0,
                    len: len as u32,
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
                    (len >> 9) as u32,
                    CosetLdePushConsts {
                        w_step: w9,
                        shift_c: 0,
                        len: len as u32,
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

        let wg_half = ((len >> 1) as u64).div_ceil(256) as u32;
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
                        len: len as u32,
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
        self.check_storage_bytes(m, 16)?;
        let in_bytes = (n as u64) * 16;
        let out_bytes = (m as u64) * 16;

        unsafe {
            self.ensure_staging(out_bytes)?;
            self.ensure_vram_buffers(out_bytes, 0, 0)?;

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
            self.record_ext2_ntt_stages(kp.pipeline_layout, n, true)?;

            // 2. Multiply `[0..n)` by `inv_n * shift^j` and zero-pad `[n..m)` in VRAM.
            self.cmd_barrier(
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                VK_ACCESS_SHADER_WRITE_BIT,
                VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
            );
            let wg_m = (m as u64).div_ceil(256) as u32;
            self.dispatch_lde_mode(
                kp.pipeline_layout,
                wg_m,
                CosetLdePushConsts {
                    w_step: gl_inv_or_zero(n as u64),
                    shift_c: gl_reduce_u64(shift),
                    len: m as u32,
                    aux_n: n as u32,
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
            self.record_ext2_ntt_stages(kp.pipeline_layout, m, false)?;

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
            self.scrub_staging(out_bytes);
        }
        Ok(())
    }

    unsafe fn dispatch_merkle_layer_cmd(
        &self,
        pl: VkPipelineLayout,
        ds: VkDescriptorSet,
        pk_seed: &[u64; 4],
        layer: u32,
        start_parent_idx: u64,
        num_parents: usize,
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
        let total_wg = (num_parents as u64).div_ceil(64) as u32;
        let mut wg_done = 0u32;
        while wg_done < total_wg {
            let chunk = (total_wg - wg_done).min(self.max_wg_x);
            let pc = MerklePushConsts {
                s0: pk_seed[0],
                s1: pk_seed[1],
                s2: pk_seed[2],
                s3: pk_seed[3],
                start_parent_idx,
                num_parents: num_parents as u64,
                in_offset_u64: 0,
                out_offset_u64: 0,
                layer,
                base_parent: wg_done * 64,
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

    pub(crate) fn exec_merkle_layer(
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
        self.check_storage_bytes(children.len(), 32)?;
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
        let in_bytes = (children.len() as u64) * 32;
        let out_bytes = (num_parents as u64) * 32;

        unsafe {
            self.ensure_staging(in_bytes)?;
            self.ensure_vram_buffers(in_bytes, out_bytes, 0)?;

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
                num_parents,
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
            self.cmd_scrub_vram(&[(self.vram_a.buffer, in_bytes), (self.vram_b.buffer, out_bytes)]);
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
            self.scrub_staging(in_bytes);
        }
        Ok(())
    }

    pub(crate) fn exec_merkle_full_tree(
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
        self.check_storage_bytes(num_leaves, 32)?;
        if num_leaves == 1 {
            return Ok([
                gl_reduce_u64(leaves[0][0]),
                gl_reduce_u64(leaves[0][1]),
                gl_reduce_u64(leaves[0][2]),
                gl_reduce_u64(leaves[0][3]),
            ]);
        }
        let height = num_leaves.trailing_zeros();
        let leaf_bytes = (num_leaves as u64) * 32;
        let half_bytes = leaf_bytes / 2;

        unsafe {
            self.ensure_staging(leaf_bytes)?;
            self.ensure_vram_buffers(leaf_bytes, half_bytes, 0)?;

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
                let cur_parents = num_leaves >> (lvl + 1);
                self.dispatch_merkle_layer_cmd(
                    kp.pipeline_layout,
                    ds,
                    pk_seed,
                    base_layer + lvl,
                    0,
                    cur_parents,
                );
            }

            let root_buf = if (height - 1) % 2 == 0 {
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
            self.cmd_scrub_vram(&[(self.vram_a.buffer, leaf_bytes), (self.vram_b.buffer, half_bytes)]);
            self.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            self.submit_and_wait()?;

            let mut root = [0u64; 4];
            self.read_staging_u64s(0, &mut root);
            self.scrub_staging(leaf_bytes);
            Ok(root)
        }
    }

    pub(crate) fn exec_bdoz_gf2_128_dot(
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
        self.check_storage_bytes(n, 32)?;
        if n == 0 {
            return Ok((0, 0));
        }
        let vec_bytes =
            (n as u64)
                .checked_mul(32)
                .ok_or(VulkanError::BufferExceedsMaxStorageRange {
                    requested: u64::MAX,
                    limit: self.max_storage_range,
                })?;
        let staging_bytes =
            vec_bytes
                .checked_mul(2)
                .ok_or(VulkanError::BufferExceedsMaxStorageRange {
                    requested: u64::MAX,
                    limit: self.max_storage_range,
                })?;
        let num_groups = n.div_ceil(256).min(1024).min(self.max_wg_x as usize) as u32;
        let partials_bytes = (num_groups as u64) * 32;

        unsafe {
            self.ensure_staging(staging_bytes)?;
            self.ensure_vram_buffers(vec_bytes, vec_bytes, partials_bytes)?;

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
                num_elements: n as u32,
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
                    num_elements: n as u32,
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
            self.scrub_staging(staging_bytes);
            let lane0 = (res[0] as u128) | ((res[1] as u128) << 64);
            let lane1 = (res[2] as u128) | ((res[3] as u128) << 64);
            Ok((lane0, lane1))
        }
    }

    unsafe fn teardown_device_only(&mut self) {
        if !self.device.is_null() {
            unsafe {
                let idle_rc = (self.fns.device_wait_idle)(self.device);
                if idle_rc != VK_SUCCESS {
                    // `vkDeviceWaitIdle` failed to establish device idle; detach handles rather
                    // than freeing buffers/command pools that may still be accessed by GPU work.
                    self.device = null_mut();
                    self.instance = null_mut();
                    self.lib_handle = null_mut();
                    return;
                }
                // A job that failed before readback leaves its input in the mapping.
                self.scrub_staging(self.staging.capacity);
                let mut st = core::mem::take(&mut self.staging);
                let mut va = core::mem::take(&mut self.vram_a);
                let mut vb = core::mem::take(&mut self.vram_b);
                let mut vc = core::mem::take(&mut self.vram_c);
                self.destroy_gpu_buffer(&mut st);
                self.destroy_gpu_buffer(&mut va);
                self.destroy_gpu_buffer(&mut vb);
                self.destroy_gpu_buffer(&mut vc);

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
                }
                for kp in &mut self.pipelines {
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
                for dsl in [&mut self.dsl_1buf, &mut self.dsl_2buf, &mut self.dsl_3buf] {
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
}
