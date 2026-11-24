//! Transfer inputs once, record dependent dispatches against the persistent
//! storage buffers, then download one result and scrub all job data.
use super::*;
use crate::vulkan::ComputePass;

impl RawVulkanEngine {
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
                    let kp = engine.pipelines[slot.index()];
                    (engine.fns.cmd_bind_pipeline)(
                        engine.cmd_buf,
                        VK_PIPELINE_BIND_POINT_COMPUTE,
                        kp.pipeline,
                    );
                    (engine.fns.cmd_bind_descriptor_sets)(
                        engine.cmd_buf,
                        VK_PIPELINE_BIND_POINT_COMPUTE,
                        kp.pipeline_layout,
                        0,
                        1,
                        &engine.ds_3buf_abc,
                        0,
                        null(),
                    );
                    let mut pc = constants.clone();
                    let mut done = 0;
                    while done < groups {
                        let chunk = (groups - done).min(engine.max_wg_x);
                        pc[base_word] = done * base_scale;
                        (engine.fns.cmd_push_constants)(
                            engine.cmd_buf,
                            kp.pipeline_layout,
                            VK_SHADER_STAGE_COMPUTE_BIT,
                            0,
                            (pc.len() * 4) as u32,
                            pc.as_ptr().cast(),
                        );
                        (engine.fns.cmd_dispatch)(engine.cmd_buf, chunk, 1, 1);
                        done += chunk;
                    }
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
