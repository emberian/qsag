//! Backend-dispatched cSHAKE commitments. Secret states are wiped on drop.
use crate::{secret::SecretVec, zk_engine::PartyView};
use alloc::vec::Vec;
use qsag_accel::AcceleratorBackend;

fn left_encode(n: usize, out: &mut Vec<u8>) {
    let bytes = n.to_be_bytes();
    let first = bytes
        .iter()
        .position(|&b| b != 0)
        .unwrap_or(bytes.len() - 1);
    out.push((bytes.len() - first) as u8);
    out.extend_from_slice(&bytes[first..]);
}

/// Hash independent framed messages in lockstep, including unequal lengths and
/// exact rate boundaries. Only public message lengths control scheduling.
fn framed<B: AcceleratorBackend>(accel: &B, custom: &[u8], frames: &[Vec<&[u8]>]) -> Vec<[u8; 32]> {
    let mut prefix = Vec::new();
    if !custom.is_empty() {
        left_encode(136, &mut prefix);
        left_encode(0, &mut prefix);
        left_encode(custom.len() * 8, &mut prefix);
        prefix.extend_from_slice(custom);
        prefix.resize(prefix.len().div_ceil(136) * 136, 0);
    }
    let mut streams: Vec<_> = frames
        .iter()
        .map(|f| {
            prefix
                .iter()
                .copied()
                .chain((f.len() as u64).to_le_bytes())
                .chain(f.iter().flat_map(|frame| {
                    (frame.len() as u64)
                        .to_le_bytes()
                        .into_iter()
                        .chain(frame.iter().copied())
                }))
        })
        .collect();
    let mut states: SecretVec<[u64; 25]> = (0..frames.len()).map(|_| [0; 25]).collect();
    let mut active: Vec<_> = (0..frames.len()).collect();
    let mut result = alloc::vec![[0; 32]; frames.len()];
    let mut finished = Vec::new();
    while !active.is_empty() {
        finished.clear();
        for (i, &index) in active.iter().enumerate() {
            let stream = &mut streams[index];
            for offset in 0..136 {
                let byte = match stream.next() {
                    Some(byte) => byte,
                    None => {
                        states[i][offset / 8] ^=
                            (if custom.is_empty() { 0x1f } else { 0x04 }) << (8 * (offset % 8));
                        states[i][16] ^= 0x8000_0000_0000_0000;
                        finished.push(i);
                        break;
                    }
                };
                states[i][offset / 8] ^= u64::from(byte) << (8 * (offset % 8));
            }
        }
        accel.batch_keccak_f1600(&mut states);
        for &i in finished.iter().rev() {
            for (out, word) in result[active[i]].chunks_exact_mut(8).zip(&states[i]) {
                out.copy_from_slice(&word.to_le_bytes());
            }
            let last = states.len() - 1;
            states.swap(i, last);
            states.truncate(last);
            active.swap_remove(i);
        }
    }
    result
}

pub(crate) fn commit_views<B: AcceleratorBackend>(
    accel: &B,
    views: &[[PartyView; 3]],
) -> Vec<[u8; 32]> {
    let indexed: Vec<_> = views
        .iter()
        .enumerate()
        .flat_map(|(r, v)| v.iter().enumerate().map(move |(p, v)| (r, p, v)))
        .collect();
    commit_indexed(accel, &indexed)
}

pub(crate) fn commit_indexed<B: AcceleratorBackend>(
    accel: &B,
    views: &[(usize, usize, &PartyView)],
) -> Vec<[u8; 32]> {
    let reps: Vec<_> = views
        .iter()
        .map(|(r, _, _)| (*r as u64).to_le_bytes())
        .collect();
    let parties: Vec<_> = views.iter().map(|(_, p, _)| [*p as u8]).collect();
    let frames: Vec<_> = views
        .iter()
        .enumerate()
        .map(|(i, (_, _, v))| {
            alloc::vec![
                reps[i].as_slice(),
                parties[i].as_slice(),
                &v.seed,
                &v.inputs,
                &v.products,
                &v.outputs,
            ]
        })
        .collect();
    framed(accel, b"QSAG.MIGRATE.VIEW.V3", &frames)
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_accel::{CpuReferenceBackend, keccak::cshake256_framed_32};

    fn exercise<B: AcceleratorBackend>(backend: &B) {
        let messages: Vec<Vec<u8>> = [0, 1, 119, 120, 121, 135, 136, 137, 272, 4096]
            .into_iter()
            .map(|len| (0..len).map(|i| i as u8).collect())
            .collect();
        let frames: Vec<_> = messages.iter().map(|m| alloc::vec![m.as_slice()]).collect();
        for custom in [b"".as_slice(), b"QSAG.MIGRATE.VIEW.V3", &[42; 200]] {
            let actual = framed(backend, custom, &frames);
            let expected: Vec<_> = frames
                .iter()
                .map(|f| cshake256_framed_32(custom, f))
                .collect();
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn batch_sponge_matches_scalar_at_rate_boundaries() {
        exercise(&CpuReferenceBackend);
    }

    #[test]
    #[cfg(feature = "vulkan")]
    fn vulkan_batch_sponge_matches_cpu() {
        let gpu = qsag_accel::VulkanSpirvBackend::try_new()
            .expect("opt-in Vulkan test requires a supported device");
        std::eprintln!("GPU: {}", gpu.device_name());
        let before = gpu.cpu_fallback_count();
        exercise(&gpu);
        assert_eq!(
            gpu.cpu_fallback_count(),
            before,
            "GPU test must not fall back to CPU"
        );
    }
}
