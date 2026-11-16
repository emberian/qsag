//! Optional trusted-host Vulkan execution. The WHIR wire format and hash domains are unchanged.
//! Enable with `--features vulkan` and `QSAG_ACCEL=vulkan`; failures retain CPU semantics.

use crate::field::{Goldilocks, GoldilocksOps as _};
use alloc::vec::Vec;
use qsag_accel::{
    CertifiedBackend, CertifiedProverKernelPin, KernelTargetArch, ProverKernelSlot,
    VerifiedKernelDigestRegistry, VulkanSpirvBackend,
};

struct Device {
    backend: CertifiedBackend<VulkanSpirvBackend>,
    prover_pins: [CertifiedProverKernelPin; ProverKernelSlot::COUNT],
    session_owner: std::sync::Mutex<Option<std::thread::ThreadId>>,
    session_cv: std::sync::Condvar,
    stages: core::sync::atomic::AtomicU64,
    fallbacks: core::sync::atomic::AtomicU64,
}

fn device() -> Option<&'static Device> {
    static DEVICE: std::sync::OnceLock<Option<Device>> = std::sync::OnceLock::new();
    DEVICE
        .get_or_init(|| {
            if std::env::var("QSAG_ACCEL").ok().as_deref() != Some("vulkan") {
                return None;
            }
            let init = || -> Result<Device, alloc::string::String> {
                let raw =
                    VulkanSpirvBackend::try_new_audited().map_err(|e| alloc::format!("{e}"))?;
                let pins = VulkanSpirvBackend::measure_embedded_spirv_pins();
                let prover_pins = VulkanSpirvBackend::measure_embedded_prover_spirv_pins();
                for slot in ProverKernelSlot::ALL {
                    if raw.prover_kernel_pin(slot) != prover_pins[slot as usize] {
                        return Err(alloc::format!("prover kernel pin mismatch on {slot:?}"));
                    }
                }
                let mut registry = VerifiedKernelDigestRegistry::<4>::with_cpu_reference_pins();
                registry
                    .register_measured_profile(KernelTargetArch::SpirV15, pins)
                    .map_err(|e| alloc::format!("{e:?}"))?;
                let backend = CertifiedBackend::try_new_measured(raw, &registry, &pins)
                    .map_err(|e| alloc::format!("{e:?}"))?;
                std::eprintln!(
                    "qsag_accel: audited {}",
                    backend.inner().device_info().device_name()
                );
                Ok(Device {
                    backend,
                    prover_pins,
                    session_owner: std::sync::Mutex::new(None),
                    session_cv: std::sync::Condvar::new(),
                    stages: core::sync::atomic::AtomicU64::new(0),
                    fallbacks: core::sync::atomic::AtomicU64::new(0),
                })
            };
            match init() {
                Ok(device) => Some(device),
                Err(error) => {
                    std::eprintln!("qsag_accel: CPU fallback: {error}");
                    None
                }
            }
        })
        .as_ref()
}

/// Exclusive lease on the persistent VRAM prover arena (`ProverArena`) of the audited Vulkan
/// device. Releases the lease back to the engine on `Drop`.
pub(crate) struct GpuWhirSession {
    device: &'static Device,
}

impl Drop for GpuWhirSession {
    fn drop(&mut self) {
        self.device.backend.inner().release_prover_session();
        if let Ok(mut owner) = self.device.session_owner.lock() {
            *owner = None;
            self.device.session_cv.notify_one();
        }
    }
}

pub(crate) fn try_acquire_whir_session() -> Option<GpuWhirSession> {
    let d = device()?;
    let cur_tid = std::thread::current().id();
    let mut owner = d.session_owner.lock().ok()?;
    if *owner == Some(cur_tid) {
        // A fresh commit would overwrite the live owner's arena. Existing-state
        // opens/row proofs borrow that state's session directly instead. A nested
        // independent commitment must use CPU storage until there are multiple arenas.
        d.fallbacks
            .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        std::eprintln!(
            "qsag_accel: nested independent commitment uses CPU; live VRAM arena retained"
        );
        return None;
    }
    while owner.is_some() {
        owner = d.session_cv.wait(owner).ok()?;
    }
    if d.backend.inner().try_acquire_prover_session().is_ok() {
        *owner = Some(cur_tid);
        Some(GpuWhirSession { device: d })
    } else {
        None
    }
}

impl GpuWhirSession {
    #[inline]
    pub(crate) fn raw(&self) -> &VulkanSpirvBackend {
        self.device.backend.inner()
    }

    /// Record a completed stage against its actual embedded prover kernel pin.
    /// This is trusted-host telemetry, not a cryptographic execution receipt.
    pub(crate) fn record_stage(&self, slot: ProverKernelSlot) -> bool {
        let valid = self.raw().prover_kernel_pin(slot) == self.device.prover_pins[slot as usize];
        if valid {
            self.device
                .stages
                .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        } else {
            self.device
                .fallbacks
                .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        }
        valid
    }

    pub(crate) fn record_fallback(&self, stage: &str, err: impl core::fmt::Display) {
        self.device
            .fallbacks
            .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        std::eprintln!("qsag_accel: {stage} failed ({err}); recomputing on CPU");
    }
}

/// Physical GPU submissions, completed pinned stages, and operation fallbacks.
/// Stage counts are telemetry, not authenticated execution receipts.
/// `None` means the optional device is disabled or failed initialization.
pub fn vulkan_execution_counts() -> Option<(u64, u64, u64)> {
    let d = device()?;
    Some((
        d.backend.inner().gpu_submission_count(),
        d.stages.load(core::sync::atomic::Ordering::Relaxed),
        d.fallbacks.load(core::sync::atomic::Ordering::Relaxed),
    ))
}

// Measured RX 6750 XT windows, including both transfer directions: queueing
// beats CPU parallel-launch overhead at 2^14..2^16, but CPU wins the middle
// sizes. Large transfers first break even near 2^22. Smaller transforms stay CPU.
const NTT_GPU_MIN: usize = 1 << 22;
fn gpu_ntt_length(length: usize) -> bool {
    (1 << 14..=1 << 16).contains(&length) || length >= NTT_GPU_MIN
}

/// Transactional adapter: a failed GPU operation never publishes a partial result.
/// No host hash of the buffers is presented as evidence of shader correctness.
pub(crate) fn ntt(values: &mut [Goldilocks], inverse: bool) -> bool {
    if !gpu_ntt_length(values.len()) || !values.len().is_power_of_two() {
        return false;
    }
    let Some(device) = device() else {
        return false;
    };
    let mut words: Vec<u64> = values.iter().map(|v| v.to_canonical_u64()).collect();
    let _phase = crate::profile::span("gpu_ntt_kernel_and_transfer");
    let result = device
        .backend
        .inner()
        .goldilocks_ntt_canonical_inplace(&mut words, inverse);
    let valid = result.is_ok()
        && words
            .iter()
            .all(|&v| Goldilocks::from_canonical_u64(v).is_some());
    if valid {
        for (out, &word) in values.iter_mut().zip(&words) {
            *out = Goldilocks::from_u64_reduced(word);
        }
    }
    // Hiding callers transform witness tables: the host copy is erased either way.
    qsag_asm::volatile_fill(&mut words, 0u64);
    if !valid {
        device
            .fallbacks
            .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        std::eprintln!("qsag_accel: NTT failed; recomputing on CPU");
        return false;
    }
    device
        .stages
        .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    true
}

/// Report the missing Poseidon2 canopy pipeline once per process. GPU NTT may still run.
pub(crate) fn report_cpu_poseidon_canopy() {
    static REPORT: std::sync::Once = std::sync::Once::new();
    if device().is_some() {
        REPORT.call_once(|| {
            std::eprintln!(
                "qsag_accel: Poseidon2 WHIR canopy/open runs on CPU; eligible NTTs use Vulkan"
            )
        });
    }
}

// Whole coset encodings against the host's coset-decomposed encoder (RX 6750 XT against an
// i9-12900 with 22 workers, blowup 4, `encode_crossover`): the single GPU transform wins only
// in the small queueing window (1.24 ms against 1.42 ms on a 2^16 domain) and loses above it
// (63 against 50 ms at 2^22, 257 against 240 ms at 2^24, 1,331 against 981 ms at 2^26). A
// shard commitment that does not fit the VRAM arena therefore encodes on the host.
fn gpu_encode_length(domain_len: usize) -> bool {
    (1 << 14..=1 << 16).contains(&domain_len)
}

pub(crate) fn encode(coeffs: &[Goldilocks], domain_len: usize) -> Option<Vec<Goldilocks>> {
    if !gpu_encode_length(domain_len) || device().is_none() {
        return None;
    }
    gpu_encode(coeffs, domain_len)
}

/// One coset encoding as a single GPU transform of the shifted coefficients.
fn gpu_encode(coeffs: &[Goldilocks], domain_len: usize) -> Option<Vec<Goldilocks>> {
    let mut values = alloc::vec![Goldilocks::ZERO; domain_len];
    let mut shift = Goldilocks::ONE;
    for (out, &c) in values.iter_mut().zip(coeffs) {
        *out = c * shift;
        shift *= Goldilocks::NON_RESIDUE;
    }
    ntt(&mut values, false).then_some(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "RX 6750 XT crossover, run with QSAG_ACCEL=vulkan --ignored --nocapture"]
    fn ntt_crossover() {
        let device = device().expect("audited GPU required");
        for log in [14, 16, 18, 20, 22] {
            let input: Vec<_> = (0..1usize << log)
                .map(|i| Goldilocks::from_u64_reduced(i as u64 * 7919 + 17))
                .collect();
            let mut cpu_ms = Vec::new();
            let mut gpu_ms = Vec::new();
            for _ in 0..4 {
                let mut cpu = input.clone();
                let t = std::time::Instant::now();
                crate::field::ntt_goldilocks_cpu(&mut cpu);
                cpu_ms.push(t.elapsed().as_secs_f64() * 1000.);
                let t = std::time::Instant::now();
                let mut words: Vec<_> = input.iter().map(|v| v.to_canonical_u64()).collect();
                device
                    .backend
                    .inner()
                    .goldilocks_ntt_canonical_inplace(&mut words, false)
                    .unwrap();
                let gpu: Vec<_> = words
                    .iter()
                    .map(|&v| Goldilocks::from_canonical_u64(v).unwrap())
                    .collect();
                gpu_ms.push(t.elapsed().as_secs_f64() * 1000.);
                assert_eq!(cpu, gpu);
                device
                    .backend
                    .inner()
                    .goldilocks_ntt_canonical_inplace(&mut words, true)
                    .unwrap();
                assert!(
                    words
                        .iter()
                        .zip(&input)
                        .all(|(&a, b)| a == b.to_canonical_u64())
                );
            }
            cpu_ms.remove(0);
            gpu_ms.remove(0);
            cpu_ms.sort_by(f64::total_cmp);
            gpu_ms.sort_by(f64::total_cmp);
            std::println!(
                "NTT_CROSSOVER log={log} cpu_ms={:.3} gpu_ms={:.3}",
                cpu_ms[1],
                gpu_ms[1]
            );
        }
    }

    /// Whole coset encodings: the host's coset-decomposed encoder against one GPU transform
    /// with both transfers, at the sizes shard commitments use.
    #[test]
    #[ignore = "RX 6750 XT crossover, run with QSAG_ACCEL=vulkan --ignored --nocapture"]
    fn encode_crossover() {
        device().expect("audited GPU required");
        for log in [14usize, 20, 22, 24] {
            let coeffs: Vec<_> = (0..1usize << log)
                .map(|i| Goldilocks::from_u64_reduced(i as u64 * 7919 + 17))
                .collect();
            let mut cpu_ms = Vec::new();
            let mut gpu_ms = Vec::new();
            for _ in 0..4 {
                let t = std::time::Instant::now();
                let cpu = crate::field::encode_rs_coset_goldilocks_cpu(&coeffs, 4);
                cpu_ms.push(t.elapsed().as_secs_f64() * 1000.);
                let t = std::time::Instant::now();
                let gpu = gpu_encode(&coeffs, 4 << log).expect("GPU encode");
                gpu_ms.push(t.elapsed().as_secs_f64() * 1000.);
                assert_eq!(cpu, gpu);
            }
            cpu_ms.remove(0);
            gpu_ms.remove(0);
            cpu_ms.sort_by(f64::total_cmp);
            gpu_ms.sort_by(f64::total_cmp);
            std::println!(
                "ENCODE_CROSSOVER log={log} blowup=4 cpu_ms={:.3} gpu_ms={:.3}",
                cpu_ms[1],
                gpu_ms[1]
            );
        }
    }

    #[test]
    fn nested_commit_preserves_the_live_session() {
        if std::env::var("QSAG_ACCEL").ok().as_deref() != Some("vulkan") {
            return;
        }
        let first = try_acquire_whir_session().expect("GPU session");
        assert!(try_acquire_whir_session().is_none());
        drop(first);
        assert!(try_acquire_whir_session().is_some());
    }

    #[test]
    fn selected_gpu_ntt_matches_independent_horner() {
        if std::env::var("QSAG_ACCEL").ok().as_deref() != Some("vulkan") {
            return;
        }
        let n = NTT_GPU_MIN;
        let coeffs: Vec<_> = (0..17)
            .map(|i| Goldilocks::from_u64_reduced(i * 7919 + 11))
            .collect();
        let mut values = alloc::vec![Goldilocks::ZERO; n];
        values[..coeffs.len()].copy_from_slice(&coeffs);
        assert!(
            ntt(&mut values, false),
            "explicit GPU test must execute the audited device"
        );
        let omega = Goldilocks::two_adic_generator(n.trailing_zeros() as usize);
        for i in [0, 1, 7, 511, 8191, 16383] {
            let x = omega.pow(i as u64);
            let expected = coeffs
                .iter()
                .rev()
                .fold(Goldilocks::ZERO, |a, &c| a * x + c);
            assert_eq!(values[i], expected);
        }
        assert!(ntt(&mut values, true));
        assert_eq!(&values[..coeffs.len()], &coeffs);
        assert!(
            values[coeffs.len()..]
                .iter()
                .all(|v| *v == Goldilocks::ZERO)
        );
        // The device computes the coset encoding; the host encoder is preferred at this size.
        assert!(encode(&coeffs, n).is_none());
        let shifted = gpu_encode(&coeffs, n).expect("GPU coset encoding");
        for i in [0, 1, 7, 511, 8191, 16383] {
            let x = Goldilocks::NON_RESIDUE * omega.pow(i as u64);
            let expected = coeffs
                .iter()
                .rev()
                .fold(Goldilocks::ZERO, |a, &c| a * x + c);
            assert_eq!(shifted[i], expected);
        }
    }
}
