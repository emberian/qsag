//! Word-addressed transfers for an exclusively owned quintic job.
use super::*;
use crate::sha2::Sha256Hasher;

#[derive(Clone, Copy)]
pub(crate) struct Region {
    pub(crate) buffer: usize,
    pub(crate) word: usize,
}
fn at(buffer: usize, word: usize) -> Region {
    Region { buffer, word }
}
pub(crate) enum ResidentStep {
    Copy(Region, Region, usize),
    Dispatch {
        slot: KernelSlot,
        constants: Vec<u32>,
        groups: u32,
        base_word: usize,
    },
}

fn fold(n: u32, m: u32, base: bool, mode: u32, sub_mode: u32) -> ResidentStep {
    ResidentStep::Dispatch {
        slot: KernelSlot::Fp5WhirFold,
        constants: vec![n, m, 0, base as u32, 0, 0, mode, sub_mode],
        groups: n.div_ceil(256),
        base_word: 5,
    }
}
fn reduction(
    mode: u32,
    range: core::ops::Range<u32>,
    stride: u32,
    terms: u32,
    base: bool,
    params: u32,
    out: u32,
) -> [ResidentStep; 2] {
    let groups = (range.end - range.start).div_ceil(256);
    let step = |constants, groups| ResidentStep::Dispatch {
        slot: KernelSlot::Fp5SumcheckReduce,
        constants,
        groups,
        base_word: 8,
    };
    [
        step(
            vec![
                range.start,
                range.end,
                stride,
                stride,
                terms,
                params,
                out,
                base as u32,
                0,
                mode,
            ],
            groups,
        ),
        step(vec![0, groups, 0, 0, terms, out, out, 0, 0, 7], 1),
    ]
}
trait Exchange {
    fn run(
        &mut self,
        inputs: &[(Region, &[u64])],
        steps: &[ResidentStep],
        outputs: &mut [(Region, &mut [u64])],
    ) -> Result<(), VulkanError>;
}
#[cfg(all(
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
struct Logged<'a, 'b> {
    resident: &'a mut crate::vulkan_ffi::Resident<'b>,
    session: &'a VulkanFp5Session<'a>,
    hash: Option<Sha256Hasher>,
    primary: KernelSlot,
}
#[cfg(all(
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
impl Exchange for Logged<'_, '_> {
    fn run(
        &mut self,
        inputs: &[(Region, &[u64])],
        steps: &[ResidentStep],
        outputs: &mut [(Region, &mut [u64])],
    ) -> Result<(), VulkanError> {
        if let Some(h) = &mut self.hash {
            let coord = |h: &mut Sha256Hasher, r: Region, len: usize| {
                h.update(&[r.buffer as u8]);
                h.update(&(r.word as u64).to_le_bytes());
                h.update(&(len as u64).to_le_bytes());
            };
            h.update(&(inputs.len() as u64).to_le_bytes());
            for &(r, data) in inputs {
                coord(h, r, data.len());
                for x in data {
                    h.update(&x.to_le_bytes());
                }
            }
            h.update(&(steps.len() as u64).to_le_bytes());
            for step in steps {
                match step {
                    ResidentStep::Copy(a, b, n) => {
                        h.update(&[0]);
                        coord(h, *a, *n);
                        coord(h, *b, *n);
                    }
                    ResidentStep::Dispatch {
                        slot,
                        constants,
                        groups,
                        base_word,
                    } => {
                        let pin = self.session.backend.kernel_pin(*slot);
                        if *slot != self.primary && pin != VulkanSpirvBackend::canonical_pin(*slot)
                        {
                            return Err(AccelError::BackendFailure.into());
                        }
                        h.update(&[1, *slot as u8, *base_word as u8]);
                        h.update(&pin.sha256_digest);
                        h.update(&groups.to_le_bytes());
                        h.update(&(constants.len() as u64).to_le_bytes());
                        for c in constants {
                            h.update(&c.to_le_bytes());
                        }
                    }
                }
            }
            h.update(&(outputs.len() as u64).to_le_bytes());
            for (r, s) in outputs.iter() {
                coord(h, *r, s.len());
            }
        }
        self.resident.exchange(inputs, steps, outputs)?;
        if let Some(h) = &mut self.hash {
            for (_, words) in outputs {
                for w in words.iter() {
                    h.update(&w.to_le_bytes());
                }
            }
        }
        Ok(())
    }
}

impl VulkanFp5Session<'_> {
    fn resident(
        &self,
        primary: KernelSlot,
        lengths: [usize; 3],
        out: &mut [u64],
        run: impl FnOnce(&mut dyn Exchange, &mut [u64]) -> Result<(), VulkanError>,
    ) -> Result<(), VulkanError> {
        #[cfg(all(
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        ))]
        {
            let mut engine = self
                .backend
                .engine
                .lock()
                .map_err(|_| VulkanError::WorkspacePoisoned)?;
            let result = engine
                .with_resident(lengths, &self.backend.gpu_submissions, |resident| {
                    let hash = self.log.as_ref().map(|_| {
                        let mut h = Sha256Hasher::new();
                        h.update(b"QSAG.FP5.RESIDENT.V1");
                        for n in lengths {
                            h.update(&(n as u64).to_le_bytes());
                        }
                        h
                    });
                    let mut job = Logged {
                        session: self,
                        resident,
                        primary,
                        hash,
                    };
                    run(&mut job, out)?;
                    Ok(job.hash.map(|h| h.finalize()))
                })
                .and_then(|trace| {
                    if let Some(trace) = trace {
                        let words = core::array::from_fn::<_, 4, _>(|i| {
                            u64::from_le_bytes(trace.as_chunks::<8>().0[i])
                        });
                        self.record(primary, [&words, &[], &[]], 0, out, &[])?;
                    }
                    Ok(())
                });
            result.inspect_err(|_| qsag_asm::volatile_fill(out, 0))
        }
        #[cfg(not(all(
            any(target_os = "linux", target_os = "macos"),
            target_pointer_width = "64"
        )))]
        {
            let _ = (primary, lengths, out, run);
            Err(VulkanError::UnsupportedPlatform)
        }
    }

    pub(in crate::vulkan) fn fp5_fold_even_odd(
        &self,
        t: Fp5Table<'_>,
        phi: [u64; 5],
        out: &mut [[u64; 5]],
    ) -> Result<(), VulkanError> {
        crate::fp5_batch::equal_len(crate::fp5_batch::pairs(t.len())?, out.len())?;
        self.extent(t.len(), t.width())?;
        self.extent(out.len(), 5)?;
        let n = count(out.len())?;
        self.job(
            KernelSlot::Fp5WhirFold,
            [t.words(), &[], &phi],
            1,
            out.as_flattened_mut(),
            &[ComputePass::Dispatch {
                constants: vec![n, 0, 0, t.is_base() as u32, 0, 0, 5, 0],
                groups: n.div_ceil(256),
                base_word: 5,
                base_scale: 1,
            }],
        )
    }

    pub(in crate::vulkan) fn fp5_sumcheck_quad_evals(
        &self,
        t: Fp5Table<'_>,
        w: &[[u64; 5]],
    ) -> Result<[[u64; 5]; 3], VulkanError> {
        match t {
            Fp5Table::Base(z) => self.sumcheck_round(z.as_chunks::<1>().0, w),
            Fp5Table::Extension(z) => self.sumcheck_round(z, w),
        }
    }

    pub(in crate::vulkan) fn fp5_dot_batch(
        &self,
        t: Fp5Table<'_>,
        w: &[[u64; 5]],
    ) -> Result<[u64; 5], VulkanError> {
        crate::fp5_batch::equal_len(t.len(), w.len())?;
        if w.is_empty() {
            return Ok([0; 5]);
        }
        self.extent(w.len(), 5)?;
        let n = count(w.len())?;
        let mut result = [0; 5];
        self.resident(
            KernelSlot::Fp5SumcheckReduce,
            [t.words().len(), w.len() * 5, n.div_ceil(256) as usize * 5],
            &mut result,
            |job, out| {
                job.run(
                    &[(at(0, 0), t.words()), (at(1, 0), w.as_flattened())],
                    &reduction(3, 0..n, n, 1, t.is_base(), 0, 0),
                    &mut [(at(2, 0), out)],
                )
            },
        )?;
        Ok(result)
    }

    pub(in crate::vulkan) fn whir_stage_fold_fp5(
        &self,
        t: Fp5Table<'_>,
        mut shift: u64,
        cs: &[[[u64; 5]; 3]],
        out: &mut [[u64; 5]],
    ) -> Result<(), VulkanError> {
        crate::fp5_batch::whir_shape(t.len(), shift, cs.len(), out.len())?;
        self.extent(t.len(), 5)?;
        if cs.is_empty() {
            for (i, x) in out.iter_mut().enumerate() {
                *x = t.at(i);
            }
            return Ok(());
        }
        let param_words = 15 * cs.len() + 2 * (t.len() - out.len());
        self.extent(param_words, 1)?;
        // The coset shader reads quintic evaluations even for a base input.
        let mut lifted = Vec::new();
        let values = match t {
            Fp5Table::Extension(v) => v,
            Fp5Table::Base(v) => {
                lifted.extend(v.iter().map(|&x| [x, 0, 0, 0, 0]));
                &lifted
            }
        };
        let mut omega = gl_pow_pub(
            GOLDILOCKS_ROOT_2_32,
            1u64 << (32 - values.len().trailing_zeros()),
        );
        // All challenges are known for a coset query. Upload the public
        // parameters together, run every contraction and download the final fiber.
        let n0 = values.len();
        let mut params = Vec::with_capacity(param_words);
        let mut steps = Vec::with_capacity(3 * cs.len());
        let mut n = n0;
        for (i, c) in cs.iter().enumerate() {
            n /= 2;
            let offset = params.len();
            params.extend_from_slice(c.as_flattened());
            let mut y2 = gl_sq(shift);
            let mut inv = gl_mul(0x7fff_ffff_8000_0001, gl_inv_or_zero(shift));
            let inv_omega = gl_inv_or_zero(omega);
            let next_omega = gl_sq(omega);
            for _ in 0..n {
                params.extend([inv, y2]);
                inv = gl_mul(inv, inv_omega);
                y2 = gl_mul(y2, next_omega);
            }
            if i != 0 {
                steps.push(ResidentStep::Copy(
                    at(2, offset),
                    at(2, 0),
                    params.len() - offset,
                ));
            }
            steps.push(fold(count(n)?, 0, false, 6, 0));
            if i + 1 < cs.len() {
                steps.push(ResidentStep::Copy(at(1, 0), at(0, 0), 5 * n));
            }
            shift = gl_sq(shift);
            omega = next_omega;
        }
        let result = self.resident(
            KernelSlot::Fp5WhirFold,
            [n0 * 5, n0 / 2 * 5, param_words],
            out.as_flattened_mut(),
            |job, out| {
                job.run(
                    &[(at(0, 0), values.as_flattened()), (at(2, 0), &params)],
                    &steps,
                    &mut [(at(1, 0), out)],
                )
            },
        );
        qsag_asm::volatile_fill(&mut lifted, [0; 5]);
        result
    }

    /// Keep both multilinear tables in device memory across Fiat-Shamir rounds.
    /// The callback consumes the three evaluations and returns the fold challenge.
    /// Returns the final folded weight. The callback holds the device workspace
    /// exclusively and must perform its transcript work on the host.
    pub fn column_sumcheck(
        &self,
        t: Fp5Table<'_>,
        weights: &[[u64; 5]],
        mut challenge: impl FnMut([[u64; 5]; 3]) -> [u64; 5],
    ) -> Result<[u64; 5], VulkanError> {
        crate::fp5_batch::equal_len(t.len(), weights.len())?;
        if !t.len().is_power_of_two() {
            return Err(AccelError::LengthOverflow.into());
        }
        if t.len() == 1 {
            return Ok(weights[0].map(gl_reduce_u64));
        }
        let len = t.len();
        self.extent(len, 5)?;
        let n = count(len)?;
        let mut result = [0; 5];
        // C stores the weight table behind the scratch used by reduction and folding.
        let scratch = 15 * (len / 2).div_ceil(256);
        self.resident(
            KernelSlot::Fp5SumcheckReduce,
            [len * 5, len * 5, scratch + len * 5],
            &mut result,
            |job, out| {
                let mut n = n;
                let mut base = t.is_base();
                let mut first = true;
                while n > 1 {
                    let half = n / 2;
                    let words = n as usize * 5;
                    let mut evals = [[0; 5]; 3];
                    let inputs = if first {
                        vec![
                            (at(0, 0), t.words()),
                            (at(2, scratch), weights.as_flattened()),
                        ]
                    } else {
                        vec![]
                    };
                    let mut steps = vec![ResidentStep::Copy(at(2, scratch), at(1, 0), words)];
                    steps.extend(reduction(6, 0..half, n, 3, base, 0, 0));
                    job.run(&inputs, &steps, &mut [(at(2, 0), evals.as_flattened_mut())])?;
                    let r = challenge(evals);
                    qsag_asm::volatile_fill(&mut evals, [0; 5]);
                    // Save folded Z behind the active weight prefix. After the
                    // first contraction both halves fit in the original B.
                    let hw = words / 2;
                    let steps = [
                        fold(half, 0, base, 5, 0),
                        ResidentStep::Copy(at(1, 0), at(1, hw), hw),
                        ResidentStep::Copy(at(2, scratch), at(0, 0), words),
                        fold(half, 0, false, 5, 0),
                        ResidentStep::Copy(at(1, 0), at(2, scratch), hw),
                        ResidentStep::Copy(at(1, hw), at(0, 0), hw),
                    ];
                    if half == 1 {
                        job.run(&[(at(2, 0), &r)], &steps, &mut [(at(1, 0), out)])?;
                    } else {
                        job.run(&[(at(2, 0), &r)], &steps, &mut [])?;
                    }
                    n = half;
                    base = false;
                    first = false;
                }
                Ok(())
            },
        )?;
        Ok(result)
    }
}

/// Weighted gate evaluations. The single pair straddling the selector boundary
/// has separate S-box and multiplication polynomials for affine interpolation.
#[derive(Default)]
pub struct RowEvaluations {
    pub sbox: [[u64; 5]; 8],
    pub mul: [[u64; 5]; 3],
    pub boundary_sbox: [[u64; 5]; 8],
    pub boundary_mul: [[u64; 5]; 3],
}
impl VulkanFp5Session<'_> {
    /// Evaluate and contract three gate tables and their equality weights in VRAM.
    /// The challenge callback runs on the host with the workspace held exclusively.
    pub fn row_sumcheck(
        &self,
        tables: [&[u64]; 3],
        eq: &[[u64; 5]],
        mut prefix: usize,
        mut challenge: impl FnMut(RowEvaluations) -> [u64; 5],
    ) -> Result<[[u64; 5]; 3], VulkanError> {
        let len = tables[0].len();
        if len < 2
            || !len.is_power_of_two()
            || tables.iter().any(|t| t.len() != len)
            || eq.len() != len / 2
            || prefix > len
        {
            return Err(AccelError::LengthOverflow.into());
        }
        self.extent(len, 15)?;
        let mut n = count(len)?;
        let partial = 110;
        let weights = partial + (len / 2).div_ceil(256) * 40;
        let saved = weights + eq.len() * 5;
        let mut result = [[0; 5]; 3];
        self.resident(
            KernelSlot::Fp5SumcheckReduce,
            [15 * len / 2, 15 * len / 2, saved + 15 * len / 2],
            result.as_flattened_mut(),
            |job, out| {
                let mut first = true;
                while n > 1 {
                    let half = n / 2;
                    let middle = (prefix / 2) as u32;
                    let mut inputs = vec![(at(2, 0), &[0u64; 110][..])];
                    if first {
                        for (i, t) in tables.iter().enumerate() {
                            inputs.push((at(0, i * len), t));
                        }
                        inputs.push((at(2, weights), eq.as_flattened()));
                    }
                    let mut steps = vec![ResidentStep::Copy(
                        at(2, weights),
                        at(1, 0),
                        half as usize * 5,
                    )];
                    for (mode, range, terms, dest) in [
                        (4, 0..middle, 8, 0),
                        (5, (middle + 1).min(half)..half, 3, 40),
                        (4, middle..(middle + 1).min(half), 8, 55),
                        (5, middle..(middle + 1).min(half), 3, 95),
                    ] {
                        if !range.is_empty() {
                            let [a, mut b] =
                                reduction(mode, range, n, terms, first, 0, partial as u32);
                            if let ResidentStep::Dispatch { constants, .. } = &mut b {
                                constants[6] = dest;
                            }
                            steps.extend([a, b]);
                        }
                    }
                    let mut evals = RowEvaluations::default();
                    job.run(
                        &inputs,
                        &steps,
                        &mut [
                            (at(2, 0), evals.sbox.as_flattened_mut()),
                            (at(2, 40), evals.mul.as_flattened_mut()),
                            (at(2, 55), evals.boundary_sbox.as_flattened_mut()),
                            (at(2, 95), evals.boundary_mul.as_flattened_mut()),
                        ],
                    )?;
                    let r = challenge(evals);
                    let mut steps = vec![fold(3 * half, 0, first, 5, 0)];
                    if half > 1 {
                        let size = half as usize * 15;
                        steps.extend([
                            ResidentStep::Copy(at(1, 0), at(2, saved), size),
                            ResidentStep::Copy(at(2, weights), at(0, 0), half as usize * 5),
                            fold(half / 2, 0, false, 5, 1),
                            ResidentStep::Copy(at(1, 0), at(2, weights), half as usize / 2 * 5),
                            ResidentStep::Copy(at(2, saved), at(0, 0), size),
                        ]);
                        job.run(&[(at(2, 0), &r)], &steps, &mut [])?;
                    } else {
                        job.run(&[(at(2, 0), &r)], &steps, &mut [(at(1, 0), out)])?;
                    }
                    n = half;
                    prefix /= 2;
                    first = false;
                }
                Ok(())
            },
        )?;
        Ok(result)
    }
}

impl Drop for RowEvaluations {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.sbox, [0; 5]);
        qsag_asm::volatile_fill(&mut self.mul, [0; 5]);
        qsag_asm::volatile_fill(&mut self.boundary_sbox, [0; 5]);
        qsag_asm::volatile_fill(&mut self.boundary_mul, [0; 5]);
    }
}

/// Host-side transcript for a sequence of WHIR coefficient folds.
pub trait WhirChallenges {
    fn kernel_tail(&self, len: usize) -> [[u64; 5]; 3];
    fn phi(&mut self, products: [[u64; 5]; 3]) -> Option<[u64; 5]>;
    fn mix(&mut self, products: [[u64; 5]; 2]) -> [[u64; 5]; 3];
}

impl VulkanFp5Session<'_> {
    /// Fold monomial coefficients and their dual kernel. Interior tables stay
    /// resident until the last challenge. Each round exchanges five products.
    /// The transcript callbacks run on the host with the workspace held exclusively.
    pub fn whir_coefficients(
        &self,
        t: Fp5Table<'_>,
        kernel: &[[u64; 5]],
        rounds: usize,
        ch: &mut impl WhirChallenges,
        out: &mut [[u64; 5]],
        dual: &mut [[u64; 5]],
    ) -> Result<(), VulkanError> {
        let n = t.len();
        crate::fp5_batch::equal_len(n, kernel.len())?;
        if n == 0 || rounds == 0 || rounds > 32 {
            return Err(AccelError::LengthOverflow.into());
        }
        self.extent(n.max(3), 5)?;
        let final_n = (0..rounds).fold(n, |m, _| m.div_ceil(2) + 1);
        crate::fp5_batch::equal_len(final_n, out.len())?;
        crate::fp5_batch::equal_len(final_n, dual.len())?;
        let capacity = n.max(3) * 5;
        let saved = 20 + 15 * n.div_ceil(512);
        // The receipt binds every download, including the second output.
        self.resident(
            KernelSlot::Fp5WhirFold,
            [capacity, capacity, saved + capacity],
            out.as_flattened_mut(),
            |job, out| {
                let mut m = n;
                for i in 0..rounds {
                    let half = m.div_ceil(2);
                    let next = half + 1;
                    let base = i == 0 && t.is_base();
                    let tail = ch.kernel_tail(m);
                    let mut inputs = vec![(at(2, 0), tail.as_flattened())];
                    if i == 0 {
                        inputs.extend([(at(0, 0), t.words()), (at(1, 0), kernel.as_flattened())]);
                    }
                    let mut products = [[0; 5]; 3];
                    job.run(
                        &inputs,
                        &reduction(0, 0..count(half)?, count(m)?, 3, base, 0, 20),
                        &mut [(at(2, 20), products.as_flattened_mut())],
                    )?;
                    let phi = ch.phi(products).ok_or(VulkanError::FoldChallengeRejected)?;
                    let p_words = m * if base { 1 } else { 5 };
                    let mut steps = vec![
                        ResidentStep::Copy(at(0, 0), at(2, saved), p_words),
                        ResidentStep::Copy(at(1, 0), at(0, 0), m * 5),
                        fold(count(next)?, count(m)?, false, 2, 0),
                        ResidentStep::Copy(at(2, saved), at(0, 0), p_words),
                    ];
                    steps.extend(reduction(1, 0..count(half)?, count(m)?, 2, base, 0, 20));
                    let mut b = [[0; 5]; 2];
                    job.run(
                        &[(at(2, 0), &phi), (at(2, 5), tail.as_flattened())],
                        &steps,
                        &mut [(at(2, 20), b.as_flattened_mut())],
                    )?;
                    let c = ch.mix(b);
                    let steps = [
                        ResidentStep::Copy(at(1, 0), at(2, saved), next * 5),
                        fold(count(next)?, count(m)?, base, 3, 0),
                        ResidentStep::Copy(at(1, 0), at(0, 0), next * 5),
                        ResidentStep::Copy(at(2, saved), at(1, 0), next * 5),
                    ];
                    if i + 1 == rounds {
                        job.run(
                            &[(at(2, 0), c.as_flattened())],
                            &steps,
                            &mut [(at(0, 0), out), (at(1, 0), dual.as_flattened_mut())],
                        )?;
                    } else {
                        job.run(&[(at(2, 0), c.as_flattened())], &steps, &mut [])?;
                    }
                    m = next;
                }
                Ok(())
            },
        )
        .inspect_err(|_| qsag_asm::volatile_fill(dual, [0; 5]))
    }
}
