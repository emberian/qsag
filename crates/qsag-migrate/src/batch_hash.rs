//! Backend-dispatched cSHAKE commitments. Secret states are wiped on drop.
use crate::{secret::SecretVec, zk_engine::PartyView};
use alloc::vec::Vec;
use qsag_accel::AcceleratorBackend;

/// Hash independent framed messages in lockstep, including unequal lengths and
/// exact rate boundaries. Only public message lengths control scheduling.
fn framed<B: AcceleratorBackend>(accel: &B, custom: &[u8], frames: &[Vec<&[u8]>]) -> Vec<[u8; 32]> {
    let prefix = if custom.is_empty() {
        Vec::new()
    } else {
        qsag_core::sponge::keccak::cshake256_customization_prefix(custom)
    };
    // Keep payloads borrowed. Only the small framing headers are owned.
    let headers: Vec<Vec<[u8; 8]>> = frames
        .iter()
        .map(|f| {
            core::iter::once((f.len() as u64).to_le_bytes())
                .chain(f.iter().map(|frame| (frame.len() as u64).to_le_bytes()))
                .collect()
        })
        .collect();
    let mut streams: Vec<_> = frames
        .iter()
        .zip(&headers)
        .map(|(f, h)| {
            let pieces: Vec<&[u8]> = core::iter::once(prefix.as_slice())
                .chain(core::iter::once(h[0].as_slice()))
                .chain(
                    f.iter()
                        .zip(&h[1..])
                        .flat_map(|(frame, len)| [len.as_slice(), *frame]),
                )
                .collect();
            (pieces, 0usize, 0usize)
        })
        .collect();
    let mut states: SecretVec<[u64; 25]> = (0..frames.len()).map(|_| [0; 25]).collect();
    let mut active: Vec<_> = (0..frames.len()).collect();
    let mut result = alloc::vec![[0; 32]; frames.len()];
    let mut finished = Vec::new();
    while !active.is_empty() {
        finished.clear();
        for (i, &index) in active.iter().enumerate() {
            let (pieces, piece, offset) = &mut streams[index];
            let mut block = [0u8; 136];
            let mut filled = 0;
            while filled < block.len() && *piece < pieces.len() {
                let input = &pieces[*piece][*offset..];
                let take = input.len().min(block.len() - filled);
                block[filled..filled + take].copy_from_slice(&input[..take]);
                filled += take;
                *offset += take;
                if *offset == pieces[*piece].len() {
                    *piece += 1;
                    *offset = 0;
                }
            }
            if filled < block.len() {
                block[filled] = if custom.is_empty() { 0x1f } else { 0x04 };
                block[135] |= 0x80;
                finished.push(i);
            }
            for (word, bytes) in states[i].iter_mut().zip(block.chunks_exact(8)) {
                *word ^= u64::from_le_bytes(bytes.try_into().unwrap());
            }
            qsag_accel::ct::ct_zeroize_bytes(&mut block);
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
        let mut frames: Vec<_> = messages.iter().map(|m| alloc::vec![m.as_slice()]).collect();
        frames.push(alloc::vec![]);
        frames.push(alloc::vec![&[], &[], &[]]);
        for m in &messages {
            for split in 0..=m.len().min(136) {
                frames.push(alloc::vec![&m[..split], &[], &m[split..]]);
            }
        }
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
