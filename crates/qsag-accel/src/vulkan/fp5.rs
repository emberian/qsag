//! Explicit GPU jobs over packed, canonical Goldilocks limbs.
use super::*;
use crate::goldilocks::{
    GOLDILOCKS_ROOT_2_32, gl_inv_or_zero, gl_mul, gl_pow_pub, gl_reduce_u64, gl_sq,
};
use crate::poseidon2::POSEIDON2_GL24_RC;
use alloc::{vec, vec::Vec};

pub(crate) enum ComputePass {
    Dispatch {
        constants: Vec<u32>,
        groups: u32,
        base_word: usize,
        base_scale: u32,
    },
    CanonicalNtt {
        size: u32,
        inverse: bool,
    },
}

/// Customization midstate and framing for one binary Canopy.
pub enum CanopyProfile<'a> {
    HemTurbo(&'a [u64; 25]),
    HemGl24,
    IvcStage0 {
        nonce: [u64; 4],
        salts: &'a [[u64; 4]],
        mask_code: &'a [[u64; 5]],
    },
    IvcExtension,
    ZkStage0 {
        midstate: &'a [u64; 25],
        turbo: bool,
        salt_seed: [u64; 4],
        nonce: [u64; 4],
        mask_code: &'a [[u64; 5]],
    },
    ZkExtension {
        midstate: &'a [u64; 25],
        turbo: bool,
    },
}

struct ReceiptLog<'a> {
    key: &'a BackendAttestationKey,
    anchor: [u8; 32],
    entries: std::sync::Mutex<Vec<ExecutionReceipt>>,
}

/// Uses the backend's persistent staging and device-local allocations. A session
/// can optionally authenticate each completed job with a host attestation key.
pub struct VulkanFp5Session<'a> {
    log: Option<ReceiptLog<'a>>,
    backend: &'a VulkanSpirvBackend,
}

impl VulkanSpirvBackend {
    /// Begin a quintic session after checking the loaded pipelines’ hardware telemetry.
    pub fn fp5_session(&self) -> Result<VulkanFp5Session<'_>, VulkanError> {
        self.device_info().secret_slot_audit()?;
        Ok(VulkanFp5Session {
            backend: self,
            log: None,
        })
    }
}

fn count(n: usize) -> Result<u32, VulkanError> {
    u32::try_from(n).map_err(|_| AccelError::LengthOverflow.into())
}

impl<'a> VulkanFp5Session<'a> {
    /// Authenticate each successful job with this key and transcript anchor.
    pub fn with_receipts(mut self, key: &'a BackendAttestationKey, anchor: [u8; 32]) -> Self {
        self.log = Some(ReceiptLog {
            key,
            anchor,
            entries: Default::default(),
        });
        self
    }

    /// Drain the job receipts accumulated since the previous call.
    pub fn take_receipts(&mut self) -> Vec<ExecutionReceipt> {
        self.log.as_mut().map_or_else(Vec::new, |log| {
            core::mem::take(log.entries.get_mut().unwrap_or_else(|p| p.into_inner()))
        })
    }

    #[cfg(all(
        any(target_os = "linux", target_os = "macos"),
        target_pointer_width = "64"
    ))]
    fn record(
        &self,
        slot: KernelSlot,
        inputs: [&[u64]; 3],
        output: usize,
        out: &[u64],
        passes: &[ComputePass],
    ) -> Result<(), VulkanError> {
        let Some(log) = &self.log else { return Ok(()) };
        let mut hash = crate::sha2::Sha256Hasher::new();
        hash.update(b"QSAG.FP5.VULKAN.JOB.V1");
        hash.update(&[slot as u8, output as u8]);
        hash.update(&(passes.len() as u64).to_le_bytes());
        for pass in passes {
            match pass {
                ComputePass::Dispatch {
                    constants,
                    groups,
                    base_word,
                    base_scale,
                } => {
                    hash.update(&[0, *base_word as u8, constants.len() as u8]);
                    hash.update(&groups.to_le_bytes());
                    hash.update(&base_scale.to_le_bytes());
                    for w in constants {
                        hash.update(&w.to_le_bytes());
                    }
                }
                ComputePass::CanonicalNtt { size, inverse } => {
                    let pin = self.backend.kernel_pin(KernelSlot::GoldilocksNtt);
                    if pin != VulkanSpirvBackend::canonical_pin(KernelSlot::GoldilocksNtt) {
                        return Err(AccelError::BackendFailure.into());
                    }
                    hash.update(&[1, u8::from(*inverse)]);
                    hash.update(&pin.sha256_digest);
                    hash.update(&size.to_le_bytes());
                }
            }
        }
        for words in inputs {
            hash.update(&(words.len() as u64).to_le_bytes());
            for w in words {
                hash.update(&w.to_le_bytes());
            }
        }
        let elements = out.len();
        let descriptor = match slot {
            KernelSlot::Fp5CosetLde => BatchJobDescriptor::Fp5CosetLde { elements },
            KernelSlot::Fp5SumcheckReduce => BatchJobDescriptor::Fp5SumcheckReduce { elements },
            KernelSlot::Fp5WhirFold => BatchJobDescriptor::Fp5WhirFold { elements },
            KernelSlot::Poseidon2Gl24Merkle => BatchJobDescriptor::Poseidon2Gl24Merkle { elements },
            KernelSlot::TurboShake400Canopy => BatchJobDescriptor::TurboShake400Canopy { elements },
            _ => unreachable!(),
        };
        let mut digest = crate::sha2::Sha256Hasher::new();
        digest.update(b"QSAG.FP5.VULKAN.RESULT.V1");
        digest.update(&(elements as u64).to_le_bytes());
        for w in out {
            digest.update(&w.to_le_bytes());
        }
        let receipt = ExecutionReceipt::compute_audited(
            log.key,
            &self.backend.kernel_pin(slot),
            descriptor,
            log.anchor,
            hash.finalize(),
            digest.finalize(),
            self.backend.hardware_audit_digest(),
        )?;
        log.entries
            .lock()
            .map_err(|_| VulkanError::WorkspacePoisoned)?
            .push(receipt);
        Ok(())
    }

    fn job(
        &self,
        slot: KernelSlot,
        inputs: [&[u64]; 3],
        output: usize,
        out: &mut [u64],
        passes: &[ComputePass],
    ) -> Result<(), VulkanError> {
        #[cfg(all(
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            self.backend
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?
                .exec_fp5(slot, inputs, output, out, passes)?;
            self.backend.gpu_submissions.fetch_add(1, Ordering::Relaxed);
            self.record(slot, inputs, output, out, passes)
                .inspect_err(|_| qsag_asm::volatile_fill(out, 0))
        }
        #[cfg(not(all(
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (slot, inputs, output, out, passes);
            Err(VulkanError::UnsupportedPlatform)
        }
    }

    /// Bound allocations and all u32 shader word indices before dispatch.
    fn extent(&self, n: usize, words: usize) -> Result<(), VulkanError> {
        let bytes = n
            .checked_mul(words)
            .and_then(|v| v.checked_mul(8))
            .ok_or(AccelError::LengthOverflow)? as u64;
        let limit = self.backend.device_info().max_storage_buffer_range as u64;
        if bytes > limit {
            return Err(VulkanError::BufferExceedsMaxStorageRange {
                requested: bytes,
                limit,
            });
        }
        Ok(())
    }

    /// Evaluate one- or five-limb coefficients on shift times the canonical NTT subgroup.
    pub fn coset_lde<const L: usize>(
        &self,
        coeffs: &[[u64; L]],
        n: usize,
        shift: u64,
    ) -> Result<Vec<[u64; L]>, VulkanError> {
        self.transform(coeffs, n, shift, false)
    }

    /// Forward or normalized inverse radix-2 NTT on one or five limbs.
    pub fn ntt<const L: usize>(
        &self,
        values: &[[u64; L]],
        inverse: bool,
    ) -> Result<Vec<[u64; L]>, VulkanError> {
        self.transform(values, values.len(), 1, inverse)
    }

    fn transform<const L: usize>(
        &self,
        coeffs: &[[u64; L]],
        n: usize,
        shift: u64,
        inverse: bool,
    ) -> Result<Vec<[u64; L]>, VulkanError> {
        if !matches!(L, 1 | 5)
            || !n.is_power_of_two()
            || coeffs.len() > n
            || gl_reduce_u64(shift) == 0
        {
            return Err(AccelError::LengthOverflow.into());
        }
        self.extent(n, L)?;
        let n32 = count(n)?;
        let mut passes = Vec::with_capacity(3 * L);
        let dispatch = |limb: usize, mode: u32| ComputePass::Dispatch {
            constants: vec![
                shift as u32,
                (shift >> 32) as u32,
                n32,
                coeffs.len() as u32,
                n.trailing_zeros(),
                0,
                limb as u32,
                mode,
                0,
                0,
            ],
            groups: n32.div_ceil(256),
            base_word: 8,
            base_scale: 1,
        };
        for limb in 0..L {
            passes.push(dispatch(limb, if L == 1 { 2 } else { 3 }));
            if n32 > 1 {
                passes.push(ComputePass::CanonicalNtt { size: n32, inverse });
            }
            if L == 5 {
                passes.push(dispatch(limb, 4));
            }
        }
        let mut out = vec![[0; L]; n];
        self.job(
            KernelSlot::Fp5CosetLde,
            [&[], &[], coeffs.as_flattened()],
            usize::from(L == 5),
            out.as_flattened_mut(),
            &passes,
        )?;
        Ok(out)
    }

    /// Evaluate the quadratic product sumcheck round at 0, 1, and 2.
    pub fn sumcheck_round<const L: usize>(
        &self,
        z: &[[u64; L]],
        m: &[[u64; 5]],
    ) -> Result<[[u64; 5]; 3], VulkanError> {
        if !matches!(L, 1 | 5) || z.len() != m.len() || z.is_empty() || !z.len().is_multiple_of(2) {
            return Err(AccelError::LengthOverflow.into());
        }
        self.extent(z.len(), 5)?;
        let n = count(z.len() / 2)?;
        let groups = n.div_ceil(256);
        let pass = ComputePass::Dispatch {
            constants: vec![0, n, 0, 0, 3, 0, 0, (L == 1) as u32, 0, 6],
            groups,
            base_word: 8,
            base_scale: 1,
        };
        let final_pass = ComputePass::Dispatch {
            constants: vec![0, groups, 0, 0, 3, 0, 0, 0, 0, 7],
            groups: 1,
            base_word: 8,
            base_scale: 1,
        };
        let mut result = [[0; 5]; 3];
        self.job(
            KernelSlot::Fp5SumcheckReduce,
            [z.as_flattened(), m.as_flattened(), &[]],
            2,
            result.as_flattened_mut(),
            &[pass, final_pass],
        )?;
        Ok(result)
    }

    /// Fold a complete coset codeword, pairing opposite evaluations at each challenge.
    pub fn fold_fibers(
        &self,
        code: &[[u64; 5]],
        shift: u64,
        challenges: &[[[u64; 5]; 3]],
    ) -> Result<Vec<[u64; 5]>, VulkanError> {
        let n = code
            .len()
            .checked_shr(count(challenges.len())?)
            .ok_or(AccelError::LengthOverflow)?;
        crate::fp5_batch::whir_shape(code.len(), shift, challenges.len(), n)?;
        self.extent(code.len(), 5)?;
        let mut out = vec![[0; 5]; n];
        self.whir_stage_fold_fp5(Fp5Table::Extension(code), shift, challenges, &mut out)?;
        Ok(out)
    }

    /// Build the full heap (top at index 1) in one submission. A 400-bit digest
    /// occupies seven little-endian words with zero padding in the last word.
    pub fn canopy<const L: usize>(
        &self,
        profile: CanopyProfile<'_>,
        stage: u8,
        arity: usize,
        code: &[[u64; L]],
    ) -> Result<Vec<[u64; 7]>, VulkanError> {
        if !matches!(L, 1 | 5)
            || !arity.is_power_of_two()
            || arity > 64
            || !code.len().is_power_of_two()
            || arity > code.len()
        {
            return Err(AccelError::LengthOverflow.into());
        }
        let n = code.len() / arity;
        self.extent(n, 14)?;
        self.extent(code.len(), L)?;
        let ivc = matches!(
            profile,
            CanopyProfile::IvcStage0 { .. } | CanopyProfile::IvcExtension
        );
        let gl = ivc || matches!(profile, CanopyProfile::HemGl24);
        let (slot, mut meta, mode, tag, turbo) = match profile {
            CanopyProfile::IvcStage0 {
                nonce,
                salts,
                mask_code,
            } if L == 1 && stage == 0 && salts.len() == n && mask_code.len() == n => {
                let mut meta = Vec::with_capacity(240 + 9 * n);
                meta.extend(POSEIDON2_GL24_RC);
                meta.extend(nonce);
                meta.extend_from_slice(salts.as_flattened());
                meta.extend_from_slice(mask_code.as_flattened());
                (KernelSlot::Poseidon2Gl24Merkle, meta, 2, 0, false)
            }
            CanopyProfile::IvcExtension if L == 5 && stage > 0 => (
                KernelSlot::Poseidon2Gl24Merkle,
                POSEIDON2_GL24_RC.to_vec(),
                2,
                0,
                false,
            ),
            CanopyProfile::HemGl24 => (
                KernelSlot::Poseidon2Gl24Merkle,
                POSEIDON2_GL24_RC.to_vec(),
                1,
                0,
                false,
            ),
            CanopyProfile::HemTurbo(mid) => {
                (KernelSlot::TurboShake400Canopy, mid.to_vec(), 1, 1, true)
            }
            CanopyProfile::ZkExtension { midstate, turbo } if L == 5 => (
                KernelSlot::TurboShake400Canopy,
                midstate.to_vec(),
                3,
                0,
                turbo,
            ),
            CanopyProfile::ZkStage0 {
                midstate,
                turbo,
                salt_seed,
                nonce,
                mask_code,
            } if L == 1 && stage == 0 && mask_code.len() == n => {
                let mut meta = Vec::with_capacity(33 + 5 * n);
                meta.extend_from_slice(midstate);
                meta.extend(salt_seed);
                meta.extend(nonce);
                meta.extend_from_slice(mask_code.as_flattened());
                (KernelSlot::TurboShake400Canopy, meta, 2, 0, turbo)
            }
            _ => return Err(AccelError::LengthOverflow.into()),
        };
        let mut passes = Vec::new();
        let mut width = count(n)?;
        while width > 0 {
            let leaf = width == n as u32;
            let mode = if leaf { mode } else { 0 };
            let constants = if gl {
                let domain = if ivc {
                    u64::from(stage)
                } else {
                    u64::from_le_bytes(*b"HQM2TREE")
                };
                vec![
                    domain as u32,
                    (domain >> 32) as u32,
                    if ivc {
                        (n as u32 / width).trailing_zeros().saturating_sub(1)
                    } else {
                        width
                    },
                    0,
                    14 * width,
                    0,
                    7 * width,
                    0,
                    width,
                    0,
                    u32::from(!ivc),
                    stage.into(),
                    arity as u32,
                    n as u32,
                    (L == 1) as u32,
                    mode,
                ]
            } else {
                vec![
                    14 * width,
                    0,
                    7 * width,
                    0,
                    width,
                    0,
                    width,
                    tag,
                    if turbo { 12 } else { 0 },
                    if turbo { 7 } else { 4 },
                    stage.into(),
                    arity as u32,
                    arity.trailing_zeros(),
                    n as u32,
                    (L == 1) as u32,
                    mode,
                ]
            };
            passes.push(ComputePass::Dispatch {
                constants,
                groups: width.div_ceil(64),
                base_word: if gl { 9 } else { 5 },
                base_scale: 64,
            });
            width /= 2;
        }
        let mut nodes = vec![[0; 7]; 2 * n];
        let result = self.job(
            slot,
            [code.as_flattened(), &[], &meta],
            1,
            nodes.as_flattened_mut(),
            &passes,
        );
        qsag_asm::volatile_fill(&mut meta, 0);
        result?;
        Ok(nodes)
    }
}

#[path = "fp5_resident.rs"]
mod resident;
pub(crate) use resident::{Region, ResidentStep};
pub use resident::{RowEvaluations, WhirChallenges};
