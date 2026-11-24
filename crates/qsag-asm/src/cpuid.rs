//! Lock-free, zero-dependency runtime CPU capability detection (`CPUID` + `XGETBV` on `x86_64`,
//! `getauxval(AT_HWCAP)` on `aarch64-unknown-linux-*`, `sysctlbyname` on `aarch64-apple-*`,
//! and `MSR DIT, #1` hardware constant-time activation on `FEAT_DIT`-capable `aarch64`).

use core::sync::atomic::{AtomicU8, AtomicU32, Ordering};

/// Selected constant-time execution tier for `qsag-asm` kernels.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum SimdBackend {
    /// 100% branchless, table-free portable constant-time fallback.
    Portable = 1,
    /// `x86_64` with `AVX2` + `PCLMULQDQ` + `BMI1` + `BMI2` + `ADX`.
    X86Avx2Pclmul = 2,
    /// `x86_64` with `AVX2` + `GFNI` + `VPCLMULQDQ` + `BMI1` + `BMI2` + `ADX`.
    X86Avx2GfniVpclmul = 3,
    /// `aarch64` with `NEON` + `FEAT_SHA3` (`eor3`/`rax1`/`xar`/`bcax`) + `PMULL`.
    Aarch64NeonSha3Pmull = 4,
    /// `x86_64` with `AVX-512` (`F/DQ/BW/VL` + OS `XCR0[7:5]=0b111`) + `GFNI` + `VPCLMULQDQ` + `BMI1` + `BMI2` + `ADX`.
    X86Avx512GfniVpclmul = 5,
}

/// Detailed snapshot of CPU constant-time & SIMD instruction extensions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuCapabilities {
    pub avx2: bool,
    pub bmi1: bool,
    pub bmi2: bool,
    pub adx: bool,
    pub pclmulqdq: bool,
    pub gfni: bool,
    pub vpclmulqdq: bool,
    pub vaes: bool,
    /// `CPUID.(EAX=7, ECX=0):EDX[29]` — indicates `IA32_ARCH_CAPABILITIES` MSR (`0x10A`) exists
    /// (ring-0 readable via `RDMSR`; does NOT by itself prove bit 12 `DOITM` is set).
    pub x86_arch_capabilities_msr: bool,
    /// Always `false` in unprivileged ring-3 userland: confirming `IA32_ARCH_CAPABILITIES[DOITM]`
    /// (`MSR 0x10A` bit 12) and activating `IA32_UARCH_MISC_CTL[DOITM]` (`MSR 0x1B01` bit 0)
    /// require ring-0 `RDMSR`/`WRMSR` privileges (never inferred from `CPUID.7.0:EDX[29]` alone).
    pub x86_doit_enumerated: bool,
    pub aarch64_neon: bool,
    pub aarch64_sha3: bool,
    pub aarch64_pmull: bool,
    pub aarch64_dit: bool,
    pub avx512: bool,
    pub sha_ni: bool,
    pub aarch64_sha2: bool,
}

/// Hardware Data-Independent Timing (`Intel DOIT` / `ARMv8.4-DIT`) status report.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HardwareDitStatus {
    /// Scoped kernels enable ARM PSTATE.DIT and restore it on return.
    EnabledByGuard,
    /// Hardware timing protection is managed by the kernel.
    SupportedKernelControlled,
    /// No hardware timing mode is exposed by this capability snapshot.
    UnsupportedOnCpu,
}

impl CpuCapabilities {
    /// Query how hardware timing protection is provided, without changing processor state.
    /// `None` means DOITM support is unknown: CPUID enumerates `IA32_ARCH_CAPABILITIES`
    /// (0x10A), but reading bit 12 requires ring 0. Confirmed support is represented by
    /// `x86_doit_enumerated`; enabling `IA32_UARCH_MISC_CTL` (0x1B01) bit 0 also requires
    /// ring 0, and this query never claims that the kernel has enabled it.
    pub fn hardware_dit_status(&self) -> Option<HardwareDitStatus> {
        if self.aarch64_dit {
            Some(HardwareDitStatus::EnabledByGuard)
        } else if self.x86_doit_enumerated {
            Some(HardwareDitStatus::SupportedKernelControlled)
        } else if self.x86_arch_capabilities_msr {
            None
        } else {
            Some(HardwareDitStatus::UnsupportedOnCpu)
        }
    }
}

static CACHED_BACKEND: AtomicU8 = AtomicU8::new(0);
static CACHED_CAPS: AtomicU32 = AtomicU32::new(0);

const CAP_INITIALIZED: u32 = 1 << 31;
pub(crate) const CAP_AVX2: u32 = 1 << 0;
const CAP_BMI1: u32 = 1 << 1;
const CAP_BMI2: u32 = 1 << 2;
const CAP_ADX: u32 = 1 << 3;
pub(crate) const CAP_PCLMULQDQ: u32 = 1 << 4;
pub(crate) const CAP_GFNI: u32 = 1 << 5;
pub(crate) const CAP_VPCLMULQDQ: u32 = 1 << 6;
const CAP_VAES: u32 = 1 << 7;
const CAP_X86_DOIT: u32 = 1 << 8;
pub(crate) const CAP_A64_NEON: u32 = 1 << 9;
const CAP_A64_SHA3: u32 = 1 << 10;
const CAP_A64_PMULL: u32 = 1 << 11;
const CAP_A64_DIT: u32 = 1 << 12;
const CAP_X86_ARCH_CAP_MSR: u32 = 1 << 13;
pub(crate) const CAP_AVX512: u32 = 1 << 14;
pub(crate) const CAP_SHA_NI: u32 = 1 << 15;
pub(crate) const CAP_A64_SHA2: u32 = 1 << 16;

#[inline]
fn decode_caps(bits: u32) -> CpuCapabilities {
    CpuCapabilities {
        avx2: (bits & CAP_AVX2) != 0,
        bmi1: (bits & CAP_BMI1) != 0,
        bmi2: (bits & CAP_BMI2) != 0,
        adx: (bits & CAP_ADX) != 0,
        pclmulqdq: (bits & CAP_PCLMULQDQ) != 0,
        gfni: (bits & CAP_GFNI) != 0,
        vpclmulqdq: (bits & CAP_VPCLMULQDQ) != 0,
        vaes: (bits & CAP_VAES) != 0,
        x86_arch_capabilities_msr: (bits & CAP_X86_ARCH_CAP_MSR) != 0,
        x86_doit_enumerated: (bits & CAP_X86_DOIT) != 0,
        aarch64_neon: (bits & CAP_A64_NEON) != 0,
        aarch64_sha3: (bits & CAP_A64_SHA3) != 0,
        aarch64_pmull: (bits & CAP_A64_PMULL) != 0,
        aarch64_dit: (bits & CAP_A64_DIT) != 0,
        avx512: (bits & CAP_AVX512) != 0,
        sha_ni: (bits & CAP_SHA_NI) != 0,
        aarch64_sha2: (bits & CAP_A64_SHA2) != 0,
    }
}

#[inline]
fn encode_caps(c: CpuCapabilities) -> u32 {
    CAP_INITIALIZED
        | if c.avx2 { CAP_AVX2 } else { 0 }
        | if c.bmi1 { CAP_BMI1 } else { 0 }
        | if c.bmi2 { CAP_BMI2 } else { 0 }
        | if c.adx { CAP_ADX } else { 0 }
        | if c.pclmulqdq { CAP_PCLMULQDQ } else { 0 }
        | if c.gfni { CAP_GFNI } else { 0 }
        | if c.vpclmulqdq { CAP_VPCLMULQDQ } else { 0 }
        | if c.vaes { CAP_VAES } else { 0 }
        | if c.x86_arch_capabilities_msr {
            CAP_X86_ARCH_CAP_MSR
        } else {
            0
        }
        | if c.x86_doit_enumerated {
            CAP_X86_DOIT
        } else {
            0
        }
        | if c.aarch64_neon { CAP_A64_NEON } else { 0 }
        | if c.aarch64_sha3 { CAP_A64_SHA3 } else { 0 }
        | if c.aarch64_pmull { CAP_A64_PMULL } else { 0 }
        | if c.aarch64_dit { CAP_A64_DIT } else { 0 }
        | if c.avx512 { CAP_AVX512 } else { 0 }
        | if c.sha_ni { CAP_SHA_NI } else { 0 }
        | if c.aarch64_sha2 { CAP_A64_SHA2 } else { 0 }
}

const fn empty_caps() -> CpuCapabilities {
    CpuCapabilities {
        avx2: false,
        bmi1: false,
        bmi2: false,
        adx: false,
        pclmulqdq: false,
        gfni: false,
        vpclmulqdq: false,
        vaes: false,
        x86_arch_capabilities_msr: false,
        x86_doit_enumerated: false,
        aarch64_neon: false,
        aarch64_sha3: false,
        aarch64_pmull: false,
        aarch64_dit: false,
        avx512: false,
        sha_ni: false,
        aarch64_sha2: false,
    }
}

/// Probe detailed hardware capabilities once and serve subsequent queries from a single relaxed
/// `AtomicU32` load (`0` repeated `cpuid` serialization / KVM VM-exits).
#[inline]
pub fn probe_capabilities() -> CpuCapabilities {
    let fast = CACHED_CAPS.load(Ordering::Relaxed);
    if (fast & CAP_INITIALIZED) != 0 {
        return decode_caps(fast);
    }
    probe_capabilities_slow()
}

/// Fast internal register-only capability bitmask query (`0` stack `sret` materialization).
/// Only the `x86_64` / `aarch64` kernel dispatchers consume the raw bitmask.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[inline]
pub(crate) fn probe_capabilities_bits() -> u32 {
    let fast = CACHED_CAPS.load(Ordering::Relaxed);
    if (fast & CAP_INITIALIZED) != 0 {
        return fast;
    }
    probe_capabilities_bits_slow()
}

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[cold]
fn probe_capabilities_bits_slow() -> u32 {
    encode_caps(probe_capabilities_slow())
}

#[cold]
fn probe_capabilities_slow() -> CpuCapabilities {
    // Miri interprets portable Rust and cannot execute CPUID or hardware kernels.
    #[cfg(miri)]
    let raw = empty_caps();
    #[cfg(not(miri))]
    let raw = {
        #[cfg(target_arch = "x86_64")]
        {
            probe_x86_64()
        }
        #[cfg(target_arch = "aarch64")]
        {
            probe_aarch64()
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        {
            empty_caps()
        }
    };
    CACHED_CAPS.store(encode_caps(raw), Ordering::Relaxed);
    raw
}

#[cfg(all(target_arch = "x86_64", not(miri)))]
fn probe_x86_64() -> CpuCapabilities {
    use core::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};

    // SAFETY: `cpuid` is unconditionally supported on all `x86_64` processors, and `_xgetbv(0)`
    // is guarded by `CPUID.01H:ECX.OSXSAVE[bit 27] == 1`.
    unsafe {
        let leaf0 = __cpuid(0);
        if leaf0.eax < 7 {
            return empty_caps();
        }

        let leaf1 = __cpuid(1);
        let pclmulqdq = (leaf1.ecx & (1 << 1)) != 0;
        let ssse3 = (leaf1.ecx & (1 << 9)) != 0;
        let sse41 = (leaf1.ecx & (1 << 19)) != 0;
        let osxsave = (leaf1.ecx & (1 << 27)) != 0;
        let avx_hw = (leaf1.ecx & (1 << 28)) != 0;

        let xcr0 = if osxsave { _xgetbv(0) } else { 0 };
        // Verify OS preserves XMM (bit 1) and YMM (bit 2) register state across context switches.
        let os_ymm = osxsave && avx_hw && ((xcr0 & 0x06) == 0x06);
        // Verify OS preserves XMM/YMM (bits 2:1) AND AVX-512 opmask k0..k7 + ZMM_Hi256 + Hi16_ZMM (bits 7:5 == 0b111).
        let os_zmm = os_ymm && ((xcr0 & 0xE6) == 0xE6);

        let leaf7_0 = __cpuid_count(7, 0);
        let bmi1 = (leaf7_0.ebx & (1 << 3)) != 0;
        let avx2 = os_ymm && ((leaf7_0.ebx & (1 << 5)) != 0);
        let bmi2 = (leaf7_0.ebx & (1 << 8)) != 0;
        let avx512f = (leaf7_0.ebx & (1 << 16)) != 0;
        let avx512dq = (leaf7_0.ebx & (1 << 17)) != 0;
        let adx = (leaf7_0.ebx & (1 << 19)) != 0;
        let sha_ni = ssse3 && sse41 && ((leaf7_0.ebx & (1 << 29)) != 0);
        let avx512bw = (leaf7_0.ebx & (1 << 30)) != 0;
        let avx512vl = (leaf7_0.ebx & (1 << 31)) != 0;
        // The AVX-512 kernels also run AVX2 code, so AVX2 is part of the capability.
        let avx512 = os_zmm && avx2 && avx512f && avx512dq && avx512bw && avx512vl;

        let gfni = os_ymm && ((leaf7_0.ecx & (1 << 8)) != 0);
        let vaes = os_ymm && ((leaf7_0.ecx & (1 << 9)) != 0);
        let vpclmulqdq = os_ymm && ((leaf7_0.ecx & (1 << 10)) != 0);

        // `CPUID.(EAX=7, ECX=0):EDX[29]` enumerates existence of ring-0 `IA32_ARCH_CAPABILITIES`
        // (MSR 0x10A), NOT `DOITM` (`MSR 0x10A` bit 12) or active `IA32_UARCH_MISC_CTL[DOITM]`
        // (`MSR 0x1B01` bit 0). In unprivileged userland we report `x86_doit_enumerated = false`.
        let arch_cap_msr = (leaf7_0.edx & (1 << 29)) != 0;

        CpuCapabilities {
            avx2,
            avx512,
            bmi1,
            bmi2,
            adx,
            pclmulqdq: os_ymm && pclmulqdq,
            gfni,
            vpclmulqdq,
            vaes,
            sha_ni,
            x86_arch_capabilities_msr: arch_cap_msr,
            x86_doit_enumerated: false,
            aarch64_neon: false,
            aarch64_sha2: false,
            aarch64_sha3: false,
            aarch64_pmull: false,
            aarch64_dit: false,
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "linux"))]
fn probe_aarch64() -> CpuCapabilities {
    // Linux `arch/arm64/include/uapi/asm/hwcap.h`:
    const AT_HWCAP: usize = 16;
    const HWCAP_ASIMD: usize = 1 << 1;
    const HWCAP_PMULL: usize = 1 << 4;
    const HWCAP_SHA2: usize = 1 << 6;
    const HWCAP_SHA3: usize = 1 << 17;
    const HWCAP_DIT: usize = 1 << 24;

    unsafe extern "C" {
        fn getauxval(type_: usize) -> usize;
    }

    // SAFETY: `getauxval(AT_HWCAP)` is a thread-safe, read-only libc query of the kernel ELF
    // auxiliary vector on all `aarch64-unknown-linux-*` targets (`0` external crate deps).
    let hwcap = unsafe { getauxval(AT_HWCAP) };
    CpuCapabilities {
        aarch64_neon: (hwcap & HWCAP_ASIMD) != 0,
        aarch64_sha2: (hwcap & HWCAP_SHA2) != 0,
        aarch64_sha3: (hwcap & HWCAP_SHA3) != 0,
        aarch64_pmull: (hwcap & HWCAP_PMULL) != 0,
        aarch64_dit: (hwcap & HWCAP_DIT) != 0,
        ..empty_caps()
    }
}

#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
fn apple_sysctl_flag(nul_terminated_name: &[u8]) -> bool {
    debug_assert_eq!(nul_terminated_name.last().copied(), Some(0));
    unsafe extern "C" {
        fn sysctlbyname(
            name: *const u8,
            oldp: *mut u8,
            oldlenp: *mut usize,
            newp: *const u8,
            newlen: usize,
        ) -> i32;
    }
    let mut val: u32 = 0;
    let mut len: usize = core::mem::size_of::<u32>();
    // SAFETY: `nul_terminated_name` is NUL-terminated, `val` is a valid 4-byte buffer, and
    // `newp` is null (`0` write length) for a read-only `libSystem` kernel capability query.
    let rc = unsafe {
        sysctlbyname(
            nul_terminated_name.as_ptr(),
            (&mut val as *mut u32).cast::<u8>(),
            &mut len,
            core::ptr::null(),
            0,
        )
    };
    rc == 0 && val != 0
}

#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
fn probe_aarch64() -> CpuCapabilities {
    // Query runtime Darwin `hw.optional.*` sysctls so pre-v8.4 Apple cores (A11-A13 without
    // `FEAT_DIT` / A11 without `FEAT_SHA3`) NEVER execute `msr dit, #1` (`SIGILL`).
    // All Apple Silicon `macos` systems implement AdvSIMD, FEAT_SHA256, FEAT_SHA3, and FEAT_PMULL.
    let neon = cfg!(target_os = "macos")
        || apple_sysctl_flag(b"hw.optional.arm.AdvSIMD\0")
        || apple_sysctl_flag(b"hw.optional.AdvSIMD\0")
        || apple_sysctl_flag(b"hw.optional.neon\0");
    let sha2 = cfg!(target_os = "macos")
        || apple_sysctl_flag(b"hw.optional.arm.FEAT_SHA256\0")
        || apple_sysctl_flag(b"hw.optional.armv8_sha2\0");
    let sha3 = cfg!(target_os = "macos")
        || apple_sysctl_flag(b"hw.optional.arm.FEAT_SHA3\0")
        || apple_sysctl_flag(b"hw.optional.armv8_2_sha3\0")
        || apple_sysctl_flag(b"hw.optional.armv8_sha3\0");
    let pmull = cfg!(target_os = "macos")
        || apple_sysctl_flag(b"hw.optional.arm.FEAT_PMULL\0")
        || apple_sysctl_flag(b"hw.optional.arm.FEAT_AES\0");
    let dit = apple_sysctl_flag(b"hw.optional.arm.FEAT_DIT\0");

    CpuCapabilities {
        aarch64_neon: neon,
        aarch64_sha2: sha2,
        aarch64_sha3: sha3,
        aarch64_pmull: pmull,
        aarch64_dit: dit,
        ..empty_caps()
    }
}

#[cfg(all(
    target_arch = "aarch64",
    not(any(target_os = "linux", target_vendor = "apple"))
))]
fn probe_aarch64() -> CpuCapabilities {
    CpuCapabilities {
        aarch64_neon: cfg!(target_feature = "neon"),
        aarch64_sha2: cfg!(target_feature = "sha2"),
        aarch64_sha3: cfg!(target_feature = "sha3"),
        aarch64_pmull: cfg!(target_feature = "aes"),
        aarch64_dit: cfg!(target_feature = "dit"),
        ..empty_caps()
    }
}

/// Detect and cache the highest verified constant-time SIMD backend supported by the host CPU.
#[inline]
pub fn detect_backend() -> SimdBackend {
    let cached = CACHED_BACKEND.load(Ordering::Relaxed);
    match cached {
        1 => return SimdBackend::Portable,
        2 => return SimdBackend::X86Avx2Pclmul,
        3 => return SimdBackend::X86Avx2GfniVpclmul,
        4 => return SimdBackend::Aarch64NeonSha3Pmull,
        5 => return SimdBackend::X86Avx512GfniVpclmul,
        _ => {}
    }

    let selected = backend_for_capabilities(probe_capabilities());
    CACHED_BACKEND.store(selected as u8, Ordering::Relaxed);
    selected
}

fn backend_for_capabilities(caps: CpuCapabilities) -> SimdBackend {
    if caps.avx512
        && caps.avx2
        && caps.bmi1
        && caps.bmi2
        && caps.adx
        && caps.gfni
        && caps.vpclmulqdq
    {
        SimdBackend::X86Avx512GfniVpclmul
    } else if caps.avx2 && caps.bmi1 && caps.bmi2 && caps.adx && caps.gfni && caps.vpclmulqdq {
        SimdBackend::X86Avx2GfniVpclmul
    } else if caps.avx2 && caps.bmi1 && caps.bmi2 && caps.adx && caps.pclmulqdq {
        SimdBackend::X86Avx2Pclmul
    } else if caps.aarch64_neon && caps.aarch64_sha3 && caps.aarch64_pmull {
        SimdBackend::Aarch64NeonSha3Pmull
    } else {
        SimdBackend::Portable
    }
}

#[test]
fn arm_acceleration_does_not_require_optional_dit() {
    let mut caps = decode_caps(CAP_A64_NEON | CAP_A64_SHA3 | CAP_A64_PMULL);
    assert!(!caps.aarch64_dit);
    assert_eq!(
        backend_for_capabilities(caps),
        SimdBackend::Aarch64NeonSha3Pmull
    );
    caps.aarch64_dit = true;
    assert_eq!(
        backend_for_capabilities(caps),
        SimdBackend::Aarch64NeonSha3Pmull
    );
    caps.aarch64_pmull = false;
    assert_eq!(backend_for_capabilities(caps), SimdBackend::Portable);
}

/// Activate per-thread `PSTATE.DIT = 1` on `FEAT_DIT`-capable `aarch64` cores before entering
/// cryptographic assembly kernels (safe no-op on pre-v8.4 cores without `FEAT_DIT`).
#[cfg(target_arch = "aarch64")]
#[inline]
pub(crate) fn ensure_aarch64_dit_enabled() -> DitGuard {
    #[cfg(all(test, feature = "std"))]
    DIT_GUARDS_TAKEN.with(|n| n.set(n.get() + 1));
    let mut previous = None;
    if probe_capabilities().aarch64_dit {
        let saved: u64;
        // SAFETY: FEAT_DIT has been checked, and these registers are accessible at EL0.
        unsafe {
            core::arch::asm!("mrs {saved}, S3_3_C4_C2_5", saved = out(reg) saved, options(nostack));
            crate::aarch64_asm::enable_dit_aarch64();
        }
        previous = Some(saved);
    }
    DitGuard(previous, core::marker::PhantomData)
}

#[cfg(all(test, feature = "std", target_arch = "aarch64"))]
std::thread_local! {
    /// Guards taken on this thread, so tests can see which entry points enter DIT.
    pub(crate) static DIT_GUARDS_TAKEN: core::cell::Cell<u64> = const { core::cell::Cell::new(0) };
}

#[cfg(target_arch = "aarch64")]
pub(crate) struct DitGuard(Option<u64>, core::marker::PhantomData<*mut ()>);
#[cfg(target_arch = "aarch64")]
impl Drop for DitGuard {
    fn drop(&mut self) {
        if let Some(saved) = self.0 {
            // SAFETY: this guard was created only after checking FEAT_DIT.
            unsafe {
                core::arch::asm!("msr S3_3_C4_C2_5, {saved}", "isb",
                saved = in(reg) saved, options(nostack));
            }
        }
    }
}

/// Whether a caller permits execution without a hardware timing guarantee.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DitRequirement {
    RequireHardwareDit,
    BestEffort,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HardwareDitUnavailable;

/// Keeps hardware DIT enabled for the lexical lifetime of a sensitive operation.
/// Strict mode rejects x86 too: userspace cannot establish that DOITM is enabled.
/// The guard is neither Send nor Sync: processor state belongs to its creating thread.
///
/// ```compile_fail
/// let guard = qsag_asm::DitRequirement::BestEffort.enter().unwrap();
/// std::thread::spawn(move || drop(guard));
/// ```
pub struct HardwareDitGuard {
    _thread: core::marker::PhantomData<*mut ()>,
    #[cfg(target_arch = "aarch64")]
    _guard: DitGuard,
}
impl DitRequirement {
    pub fn enter(self) -> Result<HardwareDitGuard, HardwareDitUnavailable> {
        if self == Self::RequireHardwareDit && !cfg!(target_arch = "aarch64") {
            return Err(HardwareDitUnavailable);
        }
        #[cfg(target_arch = "aarch64")]
        {
            if self == Self::RequireHardwareDit && !probe_capabilities().aarch64_dit {
                return Err(HardwareDitUnavailable);
            }
            Ok(HardwareDitGuard {
                _guard: ensure_aarch64_dit_enabled(),
                _thread: core::marker::PhantomData,
            })
        }
        #[cfg(not(target_arch = "aarch64"))]
        Ok(HardwareDitGuard {
            _thread: core::marker::PhantomData,
        })
    }
}

/// Enable userspace hardware Data-Independent Timing (`PSTATE.DIT = 1` on `FEAT_DIT`-capable
/// ARM64; reports only ring-0 MSR existence on x86, not DOITM support or activation).
/// Prefer [`CpuCapabilities::hardware_dit_status`] for a side-effect-free capability query.
pub fn enable_hardware_dit() -> HardwareDitStatus {
    let caps = probe_capabilities();
    #[cfg(target_arch = "aarch64")]
    {
        if caps.aarch64_dit {
            // SAFETY: `probe_capabilities()` verified runtime `FEAT_DIT` (`HWCAP_DIT` on Linux or
            // `hw.optional.arm.FEAT_DIT == 1` on Apple Darwin), guaranteeing `msr dit, #1` is safe.
            unsafe {
                crate::aarch64_asm::enable_dit_aarch64();
            }
            return HardwareDitStatus::EnabledByGuard;
        }
    }
    if caps.x86_arch_capabilities_msr {
        HardwareDitStatus::SupportedKernelControlled
    } else {
        HardwareDitStatus::UnsupportedOnCpu
    }
}

#[cfg(test)]
mod dit_tests {
    #[test]
    fn strict_guard_requires_usable_hardware() {
        assert!(super::DitRequirement::BestEffort.enter().is_ok());
        #[cfg(not(target_arch = "aarch64"))]
        assert!(super::DitRequirement::RequireHardwareDit.enter().is_err());
    }

    use super::*;

    #[test]
    fn timing_status_distinguishes_support_from_msr_existence() {
        let mut caps = empty_caps();
        assert_eq!(
            caps.hardware_dit_status(),
            Some(HardwareDitStatus::UnsupportedOnCpu)
        );
        caps.x86_arch_capabilities_msr = true;
        assert_eq!(caps.hardware_dit_status(), None);
        caps.x86_doit_enumerated = true;
        assert_eq!(
            caps.hardware_dit_status(),
            Some(HardwareDitStatus::SupportedKernelControlled)
        );
        caps = empty_caps();
        caps.aarch64_dit = true;
        assert_eq!(
            caps.hardware_dit_status(),
            Some(HardwareDitStatus::EnabledByGuard)
        );
        assert_eq!(decode_caps(encode_caps(caps)), caps);
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn userspace_probe_does_not_claim_doitm() {
        let caps = probe_capabilities();
        assert!(!caps.x86_doit_enumerated);
        assert_ne!(
            caps.hardware_dit_status(),
            Some(HardwareDitStatus::SupportedKernelControlled)
        );
    }

    #[test]
    #[cfg(target_arch = "aarch64")]
    fn nested_guards_restore_dit() {
        if !probe_capabilities().aarch64_dit {
            return;
        }
        fn dit() -> u64 {
            let value;
            // SAFETY: the test first checks FEAT_DIT.
            unsafe {
                core::arch::asm!("mrs {value}, S3_3_C4_C2_5", value = out(reg) value, options(nostack));
            }
            value
        }
        let before = dit();
        {
            let _outer = ensure_aarch64_dit_enabled();
            assert_ne!(dit() & (1 << 24), 0);
            {
                let _inner = ensure_aarch64_dit_enabled();
            }
            assert_ne!(dit() & (1 << 24), 0);
        }
        assert_eq!(dit(), before);
    }
}
