//! Minimal zero-dependency Linux x86_64/aarch64 Vulkan 1.2+ dynamic loader (`dlopen("libvulkan.so.1")`)
//! and RAII compute engine targeting discrete RDNA2/SPIR-V GPUs with `shaderInt64`.
//!
//! All `unsafe` FFI calls in `qsag-accel` are strictly isolated inside this single module.

use core::ffi::{c_char, c_void};
use core::mem::{MaybeUninit, size_of};
use core::ptr::{null, null_mut};

use crate::KernelSlot;
use crate::goldilocks::{
    GOLDILOCKS_PRIME, gl_inv_or_zero, gl_neg, gl_pow_pub, gl_reduce_u64, goldilocks_primitive_root,
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

struct DeviceFns {
    destroy_device: unsafe extern "C" fn(VkDevice, *const c_void),
    get_device_queue: unsafe extern "C" fn(VkDevice, u32, u32, *mut VkQueue),
    create_buffer:
        unsafe extern "C" fn(VkDevice, *const VkBufferCreateInfo, *const c_void, *mut VkBuffer) -> i32,
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
    create_fence:
        unsafe extern "C" fn(VkDevice, *const VkFenceCreateInfo, *const c_void, *mut VkFence) -> i32,
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

pub(crate) struct RawVulkanEngine {
    lib_handle: *mut c_void,
    destroy_instance: PfnVkDestroyInstance,
    instance: VkInstance,
    device: VkDevice,
    fns: DeviceFns,
    queue: VkQueue,
    mem_props: VkPhysicalDeviceMemoryProperties,
    max_wg_x: u32,
    max_storage_range: u64,
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
        let lib_handle =
            unsafe { dlopen(c"libvulkan.so.1".as_ptr(), RTLD_NOW | RTLD_LOCAL) };
        if lib_handle.is_null() {
            return Err(VulkanError::LibraryLoadFailed);
        }

        let gipa_raw =
            unsafe { dlsym(lib_handle, c"vkGetInstanceProcAddr".as_ptr()) };
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

        let init_res = unsafe { Self::init_with_instance(lib_handle, gipa, instance, destroy_instance) };
        if init_res.is_err() {
            unsafe {
                destroy_instance(instance, null());
                let _ = dlclose(lib_handle);
            }
        }
        init_res
    }

    unsafe fn init_with_instance(
        lib_handle: *mut c_void,
        gipa: PfnVkGetInstanceProcAddr,
        instance: VkInstance,
        destroy_instance: PfnVkDestroyInstance,
    ) -> Result<(Self, VulkanDeviceInfo), VulkanError> {
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

        let mut dev_count = 0u32;
        let enum_rc = unsafe { enum_devs(instance, &mut dev_count, null_mut()) };
        if enum_rc == -3 || enum_rc == -9 {
            return Err(VulkanError::NoDiscreteGpuFound);
        }
        check_vk("vkEnumeratePhysicalDevices(count)", enum_rc)?;
        if dev_count == 0 {
            return Err(VulkanError::NoDiscreteGpuFound);
        }
        let mut phys_devs = std::vec![null_mut(); dev_count as usize];
        check_vk("vkEnumeratePhysicalDevices(list)", unsafe {
            enum_devs(instance, &mut dev_count, phys_devs.as_mut_ptr())
        })?;

        // Select discrete GPU (`VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU`), preferring AMD (`0x1002`).
        let mut chosen: Option<(VkPhysicalDevice, VkPhysicalDevicePropertiesRaw, VkPhysicalDeviceFeatures)> =
            None;
        let mut saw_discrete_without_int64 = false;
