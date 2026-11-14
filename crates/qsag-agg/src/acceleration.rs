//! Optional trusted-host Vulkan execution. The WHIR wire format and hash domains are unchanged.
//! Enable with `--features vulkan` and `QSAG_ACCEL=vulkan`; failures retain CPU semantics.

use crate::field::Goldilocks;
use alloc::vec::Vec;
use qsag_accel::{
    AcceleratorBackend, BackendAttestationKey, BatchJobDescriptor, CertifiedBackend,
    ExecutionReceipt, KernelSlot, KernelTargetArch, VerifiedKernelDigestRegistry,
    VulkanRdna2Backend, VulkanSpirvBackend,
};

struct Device {
    backend: CertifiedBackend<VulkanRdna2Backend>,
    registry: VerifiedKernelDigestRegistry<4>,
    key: BackendAttestationKey,
    receipts: core::sync::atomic::AtomicU64,
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
                use std::io::Read;
                let raw =
                    VulkanRdna2Backend::try_new_audited().map_err(|e| alloc::format!("{e}"))?;
                let pins = VulkanSpirvBackend::measure_embedded_spirv_pins();
                let mut registry = VerifiedKernelDigestRegistry::with_cpu_reference_pins();
                registry
                    .register_measured_profile(KernelTargetArch::SpirV15, pins)
                    .map_err(|e| alloc::format!("{e:?}"))?;
                let backend = CertifiedBackend::try_new_measured(raw, &registry, &pins)
                    .map_err(|e| alloc::format!("{e:?}"))?;
                let mut secret = [0u8; 32];
                std::fs::File::open("/dev/urandom")
                    .and_then(|mut f| f.read_exact(&mut secret))
                    .map_err(|e| alloc::format!("{e}"))?;
                let key = BackendAttestationKey::derive(&secret, b"qsag-agg/vulkan/ntt/v1");
                qsag_accel::ct::ct_zeroize_bytes(&mut secret);
                std::eprintln!(
                    "qsag_accel: audited {}",
                    backend.inner().device_info().device_name()
                );
                Ok(Device {
                    backend,
                    registry,
                    key,
                    receipts: core::sync::atomic::AtomicU64::new(0),
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

/// Physical submissions, accepted V5 receipts, and operation fallbacks for this process.
/// `None` means the optional device is disabled or failed initialization.
pub fn vulkan_execution_counts() -> Option<(u64, u64, u64)> {
    let d = device()?;
    Some((
        d.backend.inner().gpu_submission_count(),
        d.receipts.load(core::sync::atomic::Ordering::Relaxed),
        d.fallbacks.load(core::sync::atomic::Ordering::Relaxed),
    ))
}

/// Transactional adapter: never publish a partial GPU result after a driver/receipt failure.
/// Receipts authenticate the trusted host report; they do not prove shader equivalence.
pub(crate) fn ntt(values: &mut [Goldilocks]) -> bool {
    if values.len() < 16_384 {
        return false;
    }
    let Some(device) = device() else {
        return false;
    };
    let mut words: Vec<u64> = values.iter().map(|v| v.to_canonical_u64()).collect();
    let Ok(twiddles) = qsag_accel::goldilocks::precompute_goldilocks_twiddles(values.len()) else {
        return false;
    };
    let _phase = crate::profile::span("gpu_ntt_with_receipt");
    // The standard accelerator receipt helper hashes hundreds of MB serially. Bind
    // the same job to an explicitly domain-separated parallel digest tree instead.
    let input_digest = crate::sponge::cshake256_32(
        b"QSAG.HEM.NTT.INPUT/v1",
        &crate::sponge::encode_multi_frame(&[&digest_words(&words), &digest_words(&twiddles)]),
    );
    let result = {
        let _phase = crate::profile::span("gpu_ntt_kernel_and_queue");
        device
            .backend
            .goldilocks_ntt_inplace(&mut words, &twiddles, false)
    };
    let receipt = result.and_then(|()| {
        ExecutionReceipt::compute_audited(
            &device.key,
            &device.backend.kernel_pin(KernelSlot::GoldilocksNtt),
            BatchJobDescriptor::GoldilocksNtt {
                length: words.len(),
                inverse: false,
            },
            device.backend.inner().device_info().audit_evidence_digest(),
            input_digest,
            digest_words(&words),
            device.backend.hardware_audit_digest(),
        )
    });
    let valid = receipt
        .as_ref()
        .is_ok_and(|r| device.registry.verify_keyed_receipt(r, &device.key).is_ok());
    if !valid
        || words
            .iter()
            .any(|&v| Goldilocks::from_canonical_u64(v).is_none())
    {
        device
            .fallbacks
            .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        std::eprintln!("qsag_accel: NTT/receipt failed; recomputing on CPU");
        qsag_accel::ct::ct_zeroize_u64s(&mut words);
        return false;
    }
    for (out, &word) in values.iter_mut().zip(&words) {
        *out = Goldilocks::from_u64_reduced(word);
    }
    device
        .receipts
        .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    qsag_accel::ct::ct_zeroize_u64s(&mut words);
    true
}

/// Fixed-size leaves and an ordered, length-bound root; distinct from the accelerator's
/// sequential NTT digest domains. Four independent leaf sponges use the existing SIMD kernel.
fn digest_words(words: &[u64]) -> [u8; 32] {
    use crate::sponge::{cshake256_32, cshake256_from_midstate_32_x4, cshake256_static_midstate};
    const WORDS: usize = 4096;
    const MID: [u64; 25] = cshake256_static_midstate(b"QSAG.HEM.NTT.WORDS.LEAF/v1");
    let batches: Vec<_> = words.chunks(4 * WORDS).collect();
    let hashes = crate::map_chunks_bounded(&batches, |batches| {
        let mut out = Vec::with_capacity(batches.len() * 128);
        let mut bufs = alloc::vec![[0u8; WORDS * 8]; 4];
        for batch in batches {
            for (lane, buf) in bufs.iter_mut().enumerate() {
                buf.fill(0);
                let start = (lane * WORDS).min(batch.len());
                let end = (start + WORDS).min(batch.len());
                for (dst, word) in buf.chunks_exact_mut(8).zip(&batch[start..end]) {
                    dst.copy_from_slice(&word.to_le_bytes());
                }
            }
            let digests =
                cshake256_from_midstate_32_x4(&MID, [&bufs[0], &bufs[1], &bufs[2], &bufs[3]]);
            for digest in digests {
                out.extend_from_slice(&digest);
            }
        }
        for buf in &mut bufs {
            qsag_accel::ct::ct_zeroize_bytes(buf);
        }
        out
    });
    let mut frame = Vec::with_capacity(8 + batches.len() * 128);
    frame.extend_from_slice(&(words.len() as u64).to_le_bytes());
    for part in hashes {
        frame.extend_from_slice(&part);
    }
    cshake256_32(b"QSAG.HEM.NTT.WORDS.ROOT/v1", &frame)
}

pub(crate) fn encode(coeffs: &[Goldilocks], domain_len: usize) -> Option<Vec<Goldilocks>> {
    if domain_len < 16_384 || device().is_none() {
        return None;
    }
    let mut values = alloc::vec![Goldilocks::ZERO; domain_len];
    let mut shift = Goldilocks::ONE;
    for (out, &c) in values.iter_mut().zip(coeffs) {
        *out = c * shift;
        shift *= Goldilocks::NON_RESIDUE;
    }
    ntt(&mut values).then_some(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digest_tree_binds_length_order_and_tail() {
        let mut words: Vec<_> = (0..16_387).collect();
        let original = digest_words(&words);
        words[16_386] ^= 1;
        assert_ne!(digest_words(&words), original);
        words[16_386] ^= 1;
        words.swap(0, 8192);
        assert_ne!(digest_words(&words), original);
        assert_ne!(digest_words(&[0]), digest_words(&[0, 0]));
        assert_ne!(digest_words(&[]), digest_words(&[0]));
    }

    #[test]
    fn selected_gpu_ntt_matches_independent_horner() {
        if std::env::var("QSAG_ACCEL").ok().as_deref() != Some("vulkan") {
            return;
        }
        let n = 16_384;
        let coeffs: Vec<_> = (0..17)
            .map(|i| Goldilocks::from_u64_reduced(i * 7919 + 11))
            .collect();
        let mut values = alloc::vec![Goldilocks::ZERO; n];
        values[..coeffs.len()].copy_from_slice(&coeffs);
        assert!(
            ntt(&mut values),
            "explicit GPU test must execute the audited device"
        );
        let omega = Goldilocks::two_adic_generator(14);
        for i in [0, 1, 7, 511, 8191, 16383] {
            let x = omega.pow(i as u64);
            let expected = coeffs
                .iter()
                .rev()
                .fold(Goldilocks::ZERO, |a, &c| a * x + c);
            assert_eq!(values[i], expected);
        }
        let shifted = encode(&coeffs, n).expect("GPU coset encoding");
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
