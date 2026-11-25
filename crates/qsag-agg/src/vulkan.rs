//! Canonical field encodings shared by the GPU prover paths.
use super::field::Goldilocks as F;
use crate::zk_hem::v2::{
    field5::Fp5,
    hash::{CanopyHash, CanopyTree},
};
use alloc::vec::Vec;
use qsag_accel::vulkan::{CanopyProfile, VulkanError, VulkanFp5Session};
use qsag_core::wipe::SecretBuffer;

pub(crate) fn base_words(values: &[F]) -> SecretBuffer<Vec<[u64; 1]>> {
    SecretBuffer::new(values.iter().map(|x| [x.to_canonical_u64()]).collect())
}
pub(crate) fn ext_words(values: &[Fp5]) -> SecretBuffer<Vec<[u64; 5]>> {
    SecretBuffer::new(
        values
            .iter()
            .map(|x| x.0.map(F::to_canonical_u64))
            .collect(),
    )
}

pub(crate) fn encode_base(
    gpu: &VulkanFp5Session<'_>,
    values: &[F],
    log: usize,
) -> Result<Vec<F>, VulkanError> {
    let words = SecretBuffer::new(gpu.coset_lde(
        &base_words(values),
        1 << log,
        F::NON_RESIDUE.to_canonical_u64(),
    )?);
    Ok(words.iter().map(|x| F::from_u64_reduced(x[0])).collect())
}

pub(crate) fn encode_ext(
    gpu: &VulkanFp5Session<'_>,
    values: &[Fp5],
    log: usize,
    shift: F,
) -> Result<Vec<Fp5>, VulkanError> {
    let words =
        SecretBuffer::new(gpu.coset_lde(&ext_words(values), 1 << log, shift.to_canonical_u64())?);
    Ok(words
        .iter()
        .map(|x| Fp5(x.map(F::from_u64_reduced)))
        .collect())
}

pub(crate) fn tree<const N: usize, const L: usize>(
    gpu: &VulkanFp5Session<'_>,
    hasher: impl CanopyHash<N>,
    profile: CanopyProfile<'_>,
    stage: u8,
    arity: usize,
    code: &[[u64; L]],
) -> Result<CanopyTree<N>, VulkanError> {
    let heap = gpu.canopy(profile, stage, arity, code)?;
    let nodes = heap
        .iter()
        .map(|limbs| core::array::from_fn(|i| limbs[i / 8].to_le_bytes()[i % 8]))
        .collect();
    Ok(CanopyTree::from_heap(hasher, stage, nodes))
}

/// Guard the first codeword while the second dispatch can still fail.
type Stage0Code = (SecretBuffer<Vec<F>>, SecretBuffer<Vec<Fp5>>);
pub(crate) fn encode_stage0(
    gpu: &VulkanFp5Session<'_>,
    coeffs: &[F],
    mask: &[Fp5],
    log: usize,
    step: usize,
) -> Result<Stage0Code, VulkanError> {
    let z = SecretBuffer::new(encode_base(gpu, coeffs, log)?);
    let r = SecretBuffer::new(encode_ext(
        gpu,
        mask,
        log - step,
        F::NON_RESIDUE.pow(1 << step),
    )?);
    Ok((z, r))
}
