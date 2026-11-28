//! Transfer inputs once, record dependent dispatches against the persistent
//! storage buffers, then download one result and scrub all job data.
use super::*;
use crate::AccelError;
use crate::vulkan::ComputePass;

impl RawVulkanEngine {
    unsafe fn record_fp5_dispatch(
        &self,
        slot: KernelSlot,
        constants: &[u32],
        groups: u32,
        base_word: usize,
        base_scale: u32,
    ) {
        unsafe {
            let kp = self.pipelines[slot.index()];
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
            let mut pc = constants.to_vec();
            let mut done = 0;
            while done < groups {
                let chunk = (groups - done).min(self.max_wg_x);
                pc[base_word] = done * base_scale;
                (self.fns.cmd_push_constants)(
                    self.cmd_buf,
                    kp.pipeline_layout,
                    VK_SHADER_STAGE_COMPUTE_BIT,
                    0,
                    (pc.len() * 4) as u32,
                    pc.as_ptr().cast(),
                );
                (self.fns.cmd_dispatch)(self.cmd_buf, chunk, 1, 1);
                done += chunk;
            }
        }
    }

    pub(crate) fn exec_fp5(
        &mut self,
        slot: KernelSlot,
        inputs: [&[u64]; 3],
        output: usize,
        out: &mut [u64],
        passes: &[ComputePass],
    ) -> Result<(), VulkanError> {
        self.run_job(|engine| {
            let sizes = inputs.map(|s| core::mem::size_of_val(s) as u64);
            let output_bytes = core::mem::size_of_val(out) as u64;
            let mut needs = sizes.map(|s| s.max(8));
            needs[output] = needs[output].max(output_bytes);
            // Each first-pass workgroup writes three Fp5 values in buffer C.
            if let (KernelSlot::Fp5SumcheckReduce, Some(ComputePass::Dispatch { groups, .. })) =
                (slot, passes.first())
            {
                needs[2] = needs[2].max(u64::from(*groups) * 15 * 8);
            }
            for pass in passes {
                if let ComputePass::CanonicalNtt { size: n, .. } = pass {
                    needs[0] = needs[0].max(8 * u64::from(*n));
                }
            }
            for &n in &needs {
                engine.check_storage_bytes(n as usize, 1)?;
            }
            let offsets = [0, sizes[0], sizes[0] + sizes[1]];
            unsafe {
                engine.ensure_vram_buffers(needs[0], needs[1], needs[2])?;
                engine.reserve_job_staging(sizes.iter().sum::<u64>().max(output_bytes))?;
                let buffers = [
                    engine.vram_a.buffer,
                    engine.vram_b.buffer,
                    engine.vram_c.buffer,
                ];
                engine.begin_cmd()?;
                for i in 0..3 {
                    if sizes[i] == 0 {
                        continue;
                    }
                    engine.write_staging_u64s(offsets[i] as usize, inputs[i]);
                    let copy = VkBufferCopy {
                        src_offset: offsets[i],
                        dst_offset: 0,
                        size: sizes[i],
                    };
                    (engine.fns.cmd_copy_buffer)(
                        engine.cmd_buf,
                        engine.staging.buffer,
                        buffers[i],
                        1,
                        &copy,
                    );
                }
                // Heap index zero is reserved. Initialize it before downloading the heap.
                if matches!(
                    slot,
                    KernelSlot::Poseidon2Gl24Merkle | KernelSlot::TurboShake400Canopy
                ) {
                    (engine.fns.cmd_fill_buffer)(engine.cmd_buf, buffers[output], 0, 56, 0);
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                );
                for (i, pass) in passes.iter().enumerate() {
                    if i != 0 {
                        engine.cmd_barrier(
                            VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                            VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                            VK_ACCESS_SHADER_WRITE_BIT,
                            VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT,
                        );
                    }
                    let (constants, groups, base_word, base_scale) = match pass {
                        ComputePass::Dispatch {
                            constants,
                            groups,
                            base_word,
                            base_scale,
                        } => (constants, *groups, *base_word, *base_scale),
                        ComputePass::CanonicalNtt { size, inverse } => {
                            engine.record_canonical_ntt(*size, *inverse)?;
                            continue;
                        }
                    };
                    engine.record_fp5_dispatch(slot, constants, groups, base_word, base_scale);
                }
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT | VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_ACCESS_SHADER_WRITE_BIT | VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_TRANSFER_READ_BIT | VK_ACCESS_TRANSFER_WRITE_BIT,
                );
                let copy = VkBufferCopy {
                    src_offset: 0,
                    dst_offset: 0,
                    size: output_bytes,
                };
                (engine.fns.cmd_copy_buffer)(
                    engine.cmd_buf,
                    buffers[output],
                    engine.staging.buffer,
                    1,
                    &copy,
                );
                engine.cmd_scrub_vram(&[
                    (buffers[0], needs[0]),
                    (buffers[1], needs[1]),
                    (buffers[2], needs[2]),
                ]);
                engine.cmd_barrier(
                    VK_PIPELINE_STAGE_TRANSFER_BIT,
                    VK_PIPELINE_STAGE_HOST_BIT,
                    VK_ACCESS_TRANSFER_WRITE_BIT,
                    VK_ACCESS_HOST_READ_BIT,
                );
                engine.submit_and_wait()?;
                engine.read_staging_u64s(0, out);
            }
            Ok(())
        })
    }
}

use crate::vulkan::fp5::{Region, ResidentStep};

/// Exclusively borrowed for a complete interactive protocol. Capacities and
/// copy coordinates use u64 words. Each exchange ends at a completed fence.
pub(crate) struct Resident<'a> {
    engine: &'a mut RawVulkanEngine,
    buffers: [VkBuffer; 3],
    lengths: [usize; 3],
    submissions: &'a core::sync::atomic::AtomicU64,
}

impl RawVulkanEngine {
    pub(crate) fn with_resident<R>(
        &mut self,
        lengths: [usize; 3],
        submissions: &core::sync::atomic::AtomicU64,
        run: impl FnOnce(&mut Resident<'_>) -> Result<R, VulkanError>,
    ) -> Result<R, VulkanError> {
        for n in lengths {
            self.check_storage_bytes(n, 8)?;
        }
        self.run_job(|engine| unsafe {
            let sizes = lengths.map(|n| (n.max(1) * 8) as u64);
            engine.ensure_vram_buffers(sizes[0], sizes[1], sizes[2])?;
            let buffers = [
                engine.vram_a.buffer,
                engine.vram_b.buffer,
                engine.vram_c.buffer,
            ];
            let result = run(&mut Resident {
                engine,
                buffers,
                lengths,
                submissions,
            });
            let scrub = engine.begin_cmd().and_then(|()| {
                engine.cmd_scrub_vram(&[
                    (buffers[0], sizes[0]),
                    (buffers[1], sizes[1]),
                    (buffers[2], sizes[2]),
                ]);
                engine.submit_and_wait()
            });
            let value = result?;
            scrub?;
            Ok(value)
        })
    }
}

impl Resident<'_> {
    fn bounds(&self, r: Region, len: usize) -> Result<(), VulkanError> {
        if r.word
            .checked_add(len)
            .is_none_or(|n| n > self.lengths[r.buffer])
        {
            return Err(AccelError::LengthOverflow.into());
        }
        Ok(())
    }

    pub(crate) fn exchange(
        &mut self,
        inputs: &[(Region, &[u64])],
        steps: &[ResidentStep],
        outputs: &mut [(Region, &mut [u64])],
    ) -> Result<(), VulkanError> {
        for &(r, s) in inputs {
            self.bounds(r, s.len())?;
        }
        for (r, s) in outputs.iter() {
            self.bounds(*r, s.len())?;
        }
        for step in steps {
            if let ResidentStep::Copy(src, dst, len) = *step {
                self.bounds(src, len)?;
                self.bounds(dst, len)?;
                if src.buffer == dst.buffer && src.word.abs_diff(dst.word) < len {
                    return Err(AccelError::LengthOverflow.into());
                }
            }
        }
        let upload: usize = inputs.iter().map(|(_, s)| s.len()).sum();
        let download: usize = outputs.iter().map(|(_, s)| s.len()).sum();
        let engine = &mut *self.engine;
        unsafe {
            engine.reserve_job_staging((upload.max(download).max(1) * 8) as u64)?;
            engine.begin_cmd()?;
            let command = engine.cmd_buf;
            let copy_buffer = engine.fns.cmd_copy_buffer;
            let copy = |src, dst, from: usize, to: usize, len: usize| {
                if len != 0 {
                    let region = VkBufferCopy {
                        src_offset: (from * 8) as u64,
                        dst_offset: (to * 8) as u64,
                        size: (len * 8) as u64,
                    };
                    copy_buffer(command, src, dst, 1, &region);
                }
            };
            let stages = VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT | VK_PIPELINE_STAGE_TRANSFER_BIT;
            let access = VK_ACCESS_SHADER_READ_BIT
                | VK_ACCESS_SHADER_WRITE_BIT
                | VK_ACCESS_TRANSFER_READ_BIT
                | VK_ACCESS_TRANSFER_WRITE_BIT;

            // Include writes from prior submissions on the same queue.
            engine.cmd_barrier(stages, stages, access, access);
            let mut off = 0;
            for &(r, words) in inputs {
                engine.write_staging_u64s(off * 8, words);
                copy(
                    engine.staging.buffer,
                    self.buffers[r.buffer],
                    off,
                    r.word,
                    words.len(),
                );
                off += words.len();
            }
            for step in steps {
                engine.cmd_barrier(stages, stages, access, access);
                match *step {
                    ResidentStep::Dispatch {
                        slot,
                        ref constants,
                        groups,
                        base_word,
                    } => engine.record_fp5_dispatch(slot, constants, groups, base_word, 1),
                    ResidentStep::Copy(a, b, len) => copy(
                        self.buffers[a.buffer],
                        self.buffers[b.buffer],
                        a.word,
                        b.word,
                        len,
                    ),
                }
            }
            engine.cmd_barrier(stages, stages, access, access);
            let mut off = 0;
            for (r, s) in outputs.iter() {
                copy(
                    self.buffers[r.buffer],
                    engine.staging.buffer,
                    r.word,
                    off,
                    s.len(),
                );
                off += s.len();
            }
            engine.cmd_barrier(
                VK_PIPELINE_STAGE_TRANSFER_BIT,
                VK_PIPELINE_STAGE_HOST_BIT,
                VK_ACCESS_TRANSFER_WRITE_BIT,
                VK_ACCESS_HOST_READ_BIT,
            );
            engine.submit_and_wait()?;
            self.submissions
                .fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            let mut off = 0;
            for (_, s) in outputs {
                engine.read_staging_u64s(off * 8, s);
                off += s.len();
            }
        }
        Ok(())
    }
}
