//! Empirical `1,000,000`-trace (`10^6`) Welch's $t$-test (`dudect` methodology, Reparaz et al.
//! DATE 2017) + scalar-vs-SIMD cycle-accurate throughput benchmark suite for `qsag-asm`.
//!
//! Implements the strict three-phase `dudect` chunk protocol (`CHUNK = 256` traces per batch):
//! 1. **`prepare_inputs`:** Generate random inputs and apply branchless arithmetic class masks
//!    (`mask = 0u64.wrapping_sub(cls)`) into uniform contiguous buffers *before* timing begins,
//!    eliminating harness branch-predictor / store-forwarding / cache-set cross-talk.
//! 2. **`measure_batch`:** Tight `lfence + rdtsc ... rdtscp + lfence` loop over `0..CHUNK`.
//! 3. **`update_statistics`:** Online Welford accumulation across BOTH the **uncropped (`raw`,
//!    100% of traces)** estimator AND cropped quantile tiers (`p50, p75, p90, p95, p99`).

use core::hint::black_box;
use qsag_asm::{
    GOLDILOCKS_PRIME, KeccakRow256, KeccakState4x, SimdBackend, ct_eq_32, detect_backend,
    enable_hardware_dit, gf256_shamir_mac_with_backend, gf256_shamir_mul_with_backend,
    goldilocks_dot2_ct, goldilocks_mul_ct_with_backend, goldilocks_pow7_ct_with_backend,
    keccak_chi_mpc_row256_with_backend, keccak_f1600_x4_with_backend, probe_capabilities,
    tower128_bdoz_2lane_mac_with_backend, tower128_bdoz_2lane_poly_mac_with_backend,
};

const CHUNK: usize = 256;
const DEFAULT_TRACES_PER_KERNEL: usize = 1_000_000;
const WARMUP_CHUNKS: usize = 40;
const T_THRESHOLD: f64 = 4.5;

fn configured_traces_per_kernel() -> usize {
    std::env::var("QSAG_DUDECT_SAMPLES")
        .ok()
        .and_then(|s| s.replace('_', "").parse::<usize>().ok())
        .filter(|&n| n >= CHUNK)
        .unwrap_or(DEFAULT_TRACES_PER_KERNEL)
}

/// Deterministic Keccak-f[1600] sponge stream for reproducible `dudect` input generation.
struct KeccakRng {
    state: KeccakState4x,
    pos: usize,
}

impl KeccakRng {
    fn new(domain: u64) -> Self {
        let mut state = KeccakState4x::default();
        state.0[0] = [
            domain,
            domain ^ 0x5153_4147_4455_4445,
            0x0123_4567_89AB_CDEF,
            0x1F,
        ];
        state.0[16] = [0x8000_0000_0000_0000; 4];
        qsag_asm::portable::keccak_f1600_4x_portable(&mut state);
        Self { state, pos: 0 }
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        if self.pos >= 68 {
            qsag_asm::portable::keccak_f1600_4x_portable(&mut self.state);
            self.pos = 0;
        }
        let lane = self.pos / 4;
        let inst = self.pos % 4;
        self.pos += 1;
        self.state.0[lane][inst]
    }

    #[inline]
    fn next_u128(&mut self) -> u128 {
        (self.next_u64() as u128) | ((self.next_u64() as u128) << 64)
    }

    fn fill_bytes(&mut self, buf: &mut [u8]) {
        let mut off = 0;
        while off < buf.len() {
            let w = self.next_u64().to_le_bytes();
            let take = (buf.len() - off).min(8);
            buf[off..off + take].copy_from_slice(&w[..take]);
            off += take;
        }
    }
}

#[inline(always)]
fn serialized_ticks_start() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        core::arch::x86_64::_mm_lfence();
        let t = core::arch::x86_64::_rdtsc();
        core::arch::x86_64::_mm_lfence();
        t
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        let t: u64;
        core::arch::asm!("isb", "mrs {0}, cntvct_el0", "isb", out(reg) t, options(nomem, nostack));
        t
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        0
    }
}

#[inline(always)]
fn serialized_ticks_end() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        let mut aux = 0u32;
        let t = core::arch::x86_64::__rdtscp(&mut aux);
        core::arch::x86_64::_mm_lfence();
        t
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        let t: u64;
        core::arch::asm!("isb", "mrs {0}, cntvct_el0", "isb", out(reg) t, options(nomem, nostack));
        t
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        0
    }
}

#[derive(Clone, Copy, Default)]
struct WelfordPair {
    n: [u64; 2],
    mean: [f64; 2],
    m2: [f64; 2],
}

impl WelfordPair {
    #[inline]
    fn push(&mut self, class: usize, x: f64) {
        self.n[class] += 1;
        let n = self.n[class] as f64;
        let delta = x - self.mean[class];
        self.mean[class] += delta / n;
        let delta2 = x - self.mean[class];
        self.m2[class] += delta * delta2;
    }

    fn welch_t(&self) -> f64 {
        if self.n[0] < 2 || self.n[1] < 2 {
            return f64::INFINITY;
        }
        let n0 = self.n[0] as f64;
        let n1 = self.n[1] as f64;
        let var0 = self.m2[0] / (n0 - 1.0);
        let var1 = self.m2[1] / (n1 - 1.0);
        let denom = (var0 / n0 + var1 / n1).sqrt();
        let diff = self.mean[0] - self.mean[1];
        if denom <= 1e-15 {
            if diff.abs() <= 1e-12 {
                0.0
            } else {
                diff.signum() * f64::INFINITY
            }
        } else {
            diff / denom
        }
    }
}

struct DudectResult {
    name: &'static str,
    traces: usize,
    t_raw: f64,
    t_p50: f64,
    t_p90: f64,
    t_p99: f64,
    max_abs_t: f64,
    mean_cycles_c0: f64,
    mean_cycles_c1: f64,
}

fn run_dudect_batched<S, Prep, Meas>(
    name: &'static str,
    min_traces: usize,
    state: &mut S,
    mut prepare_chunk: Prep,
    mut measure_slot: Meas,
) -> DudectResult
where
    Prep: FnMut(&mut S, &mut KeccakRng, &[u8; CHUNK]),
    Meas: FnMut(&mut S, usize) -> u64,
{
    let mut rng = KeccakRng::new(0xD0DE_C700_0000_0001 ^ (name.len() as u64));
    let mut classes = [0u8; CHUNK];
    let mut ticks = [0u64; CHUNK];

    let mut warmup_samples = Vec::with_capacity(WARMUP_CHUNKS * CHUNK);
    for _ in 0..WARMUP_CHUNKS {
        for c in &mut classes {
            *c = (rng.next_u64() & 1) as u8;
        }
        prepare_chunk(state, &mut rng, &classes);
        for (i, tick) in ticks.iter_mut().enumerate() {
            let t0 = serialized_ticks_start();
            black_box(measure_slot(state, i));
            let t1 = serialized_ticks_end();
            *tick = t1.wrapping_sub(t0);
        }
        warmup_samples.extend_from_slice(&ticks);
    }
    warmup_samples.sort_unstable();
    let wn = warmup_samples.len();
    let thresholds = [
        warmup_samples[(wn * 50) / 100].max(1) as f64,
        warmup_samples[(wn * 75) / 100].max(1) as f64,
        warmup_samples[(wn * 90) / 100].max(1) as f64,
        warmup_samples[(wn * 95) / 100].max(1) as f64,
        warmup_samples[(wn * 99) / 100].max(1) as f64,
    ];

    let n_chunks = min_traces.div_ceil(CHUNK);
    let total_traces = n_chunks * CHUNK;
    let mut raw_estimator = WelfordPair::default();
    let mut estimators = [WelfordPair::default(); 5];

    for _ in 0..n_chunks {
        for c in &mut classes {
            *c = (rng.next_u64() & 1) as u8;
        }
        prepare_chunk(state, &mut rng, &classes);
        for (i, tick) in ticks.iter_mut().enumerate() {
            let t0 = serialized_ticks_start();
            black_box(measure_slot(state, i));
            let t1 = serialized_ticks_end();
            *tick = t1.wrapping_sub(t0);
        }
        for i in 0..CHUNK {
            let cls = classes[i] as usize;
            let dt = ticks[i] as f64;
            raw_estimator.push(cls, dt);
            for (tier, &cap) in thresholds.iter().enumerate() {
                if dt <= cap {
                    estimators[tier].push(cls, dt);
                }
            }
        }
    }

    let t_raw = raw_estimator.welch_t();
    let t_p50 = estimators[0].welch_t();
    let t_p90 = estimators[2].welch_t();
    let t_p99 = estimators[4].welch_t();
    let max_abs_t = estimators
        .iter()
        .map(|e| e.welch_t().abs())
        .fold(t_raw.abs(), f64::max);

    DudectResult {
        name,
        traces: total_traces,
        t_raw,
        t_p50,
        t_p90,
        t_p99,
        max_abs_t,
        mean_cycles_c0: estimators[4].mean[0],
        mean_cycles_c1: estimators[4].mean[1],
    }
}

#[inline(never)]
fn leaky_early_exit_tag_control(a: &[u8; 64], b: &[u8; 64]) -> u64 {
    for i in 0..64 {
        if unsafe { core::ptr::read_volatile(&a[i]) != core::ptr::read_volatile(&b[i]) } {
            return 0;
        }
        core::hint::spin_loop();
    }
    1
}

fn main() {
    let caps = probe_capabilities();
    let active = detect_backend();
    let dit = enable_hardware_dit();
    let traces_per_kernel = configured_traces_per_kernel();

    println!("================================================================================");
    println!(" QSAG-ASM Constant-Time Empirical Verification (dudect 10^6 traces) & Benchmarks");
    println!("================================================================================");
    println!(" Detected Backend : {:?}", active);
    println!(" Hardware DIT/DOIT: {:?}", dit);
    println!(
        " CPU Capabilities : avx2={} bmi2={} adx={} pclmul={} gfni={} vpclmul={} arch_cap_msr={} doitm={}",
        caps.avx2,
        caps.bmi2,
        caps.adx,
        caps.pclmulqdq,
        caps.gfni,
        caps.vpclmulqdq,
        caps.x86_arch_capabilities_msr,
        caps.x86_doit_enumerated
    );
    println!(
        " Traces / Kernel  : {} (+ {} warmup; override via QSAG_DUDECT_SAMPLES)",
        traces_per_kernel.div_ceil(CHUNK) * CHUNK,
        WARMUP_CHUNKS * CHUNK
    );
    println!("--------------------------------------------------------------------------------");

    // 0. Negative Control (#tooth)
    let ref_tag64 = [0xAAu8; 64];
    let mut ctrl_tags = [[0xAAu8; 64]; CHUNK];
    let neg_ctrl = run_dudect_batched(
        "NEGATIVE_CONTROL_early_exit_tag",
        100_000,
        &mut ctrl_tags,
        |tags, _rng, classes| {
            for i in 0..CHUNK {
                let m = 0u8.wrapping_sub(classes[i]);
                tags[i] = [0xAAu8; 64];
                tags[i][0] ^= (!m) & 0x01;
                tags[i][63] ^= m & 0x01;
            }
        },
        |tags, i| leaky_early_exit_tag_control(black_box(&ref_tag64), black_box(&tags[i])),
    );
    println!(
        " [TOOTH] {:<34} | max|t| = {:>8.2} (c0={:>6.1} cyc, c1={:>6.1} cyc) -> LEAK DETECTED!",
        neg_ctrl.name, neg_ctrl.max_abs_t, neg_ctrl.mean_cycles_c0, neg_ctrl.mean_cycles_c1
    );
    assert!(
        neg_ctrl.max_abs_t > 10.0,
        "dudect negative control must exceed |t| > 10.0, got {}",
        neg_ctrl.max_abs_t
    );

    let mut results = Vec::new();

    // 1. Keccak-f[1600] 256-way / 4x SIMD
    let mut keccak_batch = vec![KeccakState4x::default(); CHUNK];
    results.push(run_dudect_batched(
        "qsag_asm_keccak_f1600_x4",
        traces_per_kernel,
        &mut keccak_batch,
        |batch, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u64.wrapping_sub(class as u64);
                for lane in &mut batch[i].0 {
                    for value in lane {
                        *value = rng.next_u64() & mask;
                    }
                }
            }
        },
        |batch, i| {
            keccak_f1600_x4_with_backend(black_box(&mut batch[i]), active);
            batch[i].0[0][0]
        },
    ));

    // 2. Keccak MPC Chi 256-way row
    struct ChiBenchState {
        s0: Vec<KeccakRow256>,
        s1: Vec<KeccakRow256>,
        mask: KeccakRow256,
        out: KeccakRow256,
    }
    let mut chi_st = ChiBenchState {
        s0: vec![KeccakRow256::default(); CHUNK],
        s1: vec![KeccakRow256::default(); CHUNK],
        mask: KeccakRow256::default(),
        out: KeccakRow256::default(),
    };
    results.push(run_dudect_batched(
        "qsag_asm_keccak_chi_mpc_row256",
        traces_per_kernel,
        &mut chi_st,
        |st, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u64.wrapping_sub(class as u64);
                for x in 0..5 {
                    for k in 0..4 {
                        st.s0[i].0[x][k] = rng.next_u64() & mask;
                        st.s1[i].0[x][k] = rng.next_u64() & mask;
                    }
                }
            }
        },
        |st, i| {
            for _ in 0..8 {
                keccak_chi_mpc_row256_with_backend(
                    black_box(&mut st.out),
                    black_box(&st.s0[i]),
                    black_box(&st.s1[i]),
                    black_box(&st.mask),
                    active,
                );
            }
            st.out.0[0][0]
        },
    ));

    // 3. GF(2^8) Shamir Mul & MAC
    struct GfBenchState {
        a: Vec<[u8; 256]>,
        b: Vec<[u8; 256]>,
        sc: [u8; CHUNK],
        dst: [u8; 256],
    }
    let mut gf_st = GfBenchState {
        a: vec![[0u8; 256]; CHUNK],
        b: vec![[0u8; 256]; CHUNK],
        sc: [0u8; CHUNK],
        dst: [0u8; 256],
    };
    results.push(run_dudect_batched(
        "qsag_asm_gf256_shamir_mul",
        traces_per_kernel,
        &mut gf_st,
        |st, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u8.wrapping_sub(class);
                rng.fill_bytes(&mut st.a[i]);
                rng.fill_bytes(&mut st.b[i]);
                for b in &mut st.a[i] {
                    *b &= mask;
                }
                for b in &mut st.b[i] {
                    *b &= mask;
                }
            }
        },
        |st, i| {
            for _ in 0..4 {
                gf256_shamir_mul_with_backend(
                    black_box(&mut st.dst),
                    black_box(&st.a[i]),
                    black_box(&st.b[i]),
                    active,
                );
            }
            st.dst[0] as u64
        },
    ));

    results.push(run_dudect_batched(
        "qsag_asm_gf256_shamir_mac",
        traces_per_kernel,
        &mut gf_st,
        |st, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u8.wrapping_sub(class);
                rng.fill_bytes(&mut st.a[i]);
                for b in &mut st.a[i] {
                    *b &= mask;
                }
                st.sc[i] = ((rng.next_u64() & 0xFF) as u8) & mask;
            }
        },
        |st, i| {
            for _ in 0..4 {
                gf256_shamir_mac_with_backend(
                    black_box(&mut st.dst),
                    black_box(&st.a[i]),
                    black_box(st.sc[i]),
                    active,
                );
            }
            st.dst[0] as u64
        },
    ));

    // 4. Tower128 2-lane BDOZ MAC
    struct T128BenchState {
        l: Vec<[[u128; 2]; 8]>,
        r: Vec<[[u128; 2]; 8]>,
    }
    let mut t128_st = T128BenchState {
        l: vec![[[0u128; 2]; 8]; CHUNK],
        r: vec![[[0u128; 2]; 8]; CHUNK],
    };
    results.push(run_dudect_batched(
        "qsag_asm_tower128_bdoz_poly_mac",
        traces_per_kernel,
        &mut t128_st,
        |st, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u128.wrapping_sub(class as u128);
                for j in 0..8 {
                    st.l[i][j] = [rng.next_u128() & mask, rng.next_u128() & mask];
                    st.r[i][j] = [rng.next_u128() & mask, rng.next_u128() & mask];
                }
            }
        },
        |st, i| {
            let mut acc = 0u64;
            for _ in 0..4 {
                let r = tower128_bdoz_2lane_poly_mac_with_backend(
                    black_box(&st.l[i]),
                    black_box(&st.r[i]),
                    active,
                );
                acc ^= r[0] as u64;
            }
            acc
        },
    ));

    results.push(run_dudect_batched(
        "qsag_asm_tower128_bdoz_t7_mac",
        traces_per_kernel,
        &mut t128_st,
        |st, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u128.wrapping_sub(class as u128);
                for j in 0..8 {
                    st.l[i][j] = [rng.next_u128() & mask, rng.next_u128() & mask];
                    st.r[i][j] = [rng.next_u128() & mask, rng.next_u128() & mask];
                }
            }
        },
        |st, i| {
            let r = tower128_bdoz_2lane_mac_with_backend(
                black_box(&st.l[i]),
                black_box(&st.r[i]),
                active,
            );
            (r[0] ^ r[1]) as u64
        },
    ));

    // 5. Goldilocks mul + pow7 + dot2_adx
    struct GlBenchState {
        x: [u64; CHUNK],
        y: [u64; CHUNK],
    }
    let mut gl_st = GlBenchState {
        x: [0u64; CHUNK],
        y: [0u64; CHUNK],
    };
    results.push(run_dudect_batched(
        "qsag_asm_goldilocks_mul_ct",
        traces_per_kernel,
        &mut gl_st,
        |st, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u64.wrapping_sub(class as u64);
                st.x[i] = rng.next_u64() & mask;
                st.y[i] = (rng.next_u64() & mask) | !mask;
            }
        },
        |st, i| {
            let mut acc = st.x[i];
            for _ in 0..8 {
                acc = goldilocks_mul_ct_with_backend(black_box(acc), black_box(st.y[i]), active);
            }
            acc
        },
    ));

    results.push(run_dudect_batched(
        "qsag_asm_goldilocks_pow7_ct",
        traces_per_kernel,
        &mut gl_st,
        |st, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u64.wrapping_sub(class as u64);
                st.x[i] = (rng.next_u64() % GOLDILOCKS_PRIME) & mask;
            }
        },
        |st, i| {
            let mut acc = st.x[i];
            for _ in 0..8 {
                acc = goldilocks_pow7_ct_with_backend(black_box(acc), active);
            }
            acc
        },
    ));

    results.push(run_dudect_batched(
        "qsag_asm_goldilocks_dot2_adx",
        traces_per_kernel,
        &mut gl_st,
        |st, rng, classes| {
            for (i, &class) in classes.iter().enumerate() {
                let mask = 0u64.wrapping_sub(class as u64);
                st.x[i] = (rng.next_u64() % GOLDILOCKS_PRIME) & mask;
                st.y[i] = ((rng.next_u64() % GOLDILOCKS_PRIME) & mask)
                    | ((!mask) & (GOLDILOCKS_PRIME - 1));
            }
        },
        |st, i| {
            let mut acc = 0u64;
            for _ in 0..8 {
                acc ^= goldilocks_dot2_ct(
                    black_box(st.x[i]),
                    black_box(st.y[i]),
                    black_box(st.y[i]),
                    black_box(st.x[i]),
                );
            }
            acc
        },
    ));

    // 6. Constant-time 32B tag verify
    let tag_ref32 = [0x5Au8; 32];
    let mut tag_batch = [[0x5Au8; 32]; CHUNK];
    results.push(run_dudect_batched(
        "qsag_asm_ct_eq_32",
        traces_per_kernel,
        &mut tag_batch,
        |tags, _rng, classes| {
            for i in 0..CHUNK {
                let m = 0u8.wrapping_sub(classes[i]);
                tags[i] = [0x5Au8; 32];
                tags[i][0] ^= (!m) & 0x01;
            }
        },
        |tags, i| {
            let mut r = 0u64;
            for _ in 0..16 {
                r ^= ct_eq_32(black_box(&tag_ref32), black_box(&tags[i])) as u64;
            }
            r
        },
    ));

    println!("----------------------------------------------------------------------------------------");
    println!(
        " {:<32} | {:>7} | {:>7} | {:>7} | {:>7} | {:>7} | {:>7} | {:>4}",
        "Kernel Symbol", "Traces", "t(raw)", "t(p50)", "t(p90)", "t(p99)", "max|t|", "Gate"
    );
    println!("----------------------------------------------------------------------------------------");
    let mut all_pass = true;
    for r in &results {
        let pass = r.max_abs_t < T_THRESHOLD;
        if !pass {
            all_pass = false;
        }
        println!(
            " {:<32} | {:>7} | {:>+7.2} | {:>+7.2} | {:>+7.2} | {:>+7.2} | {:>7.2} | {}",
            r.name,
            r.traces,
            r.t_raw,
            r.t_p50,
            r.t_p90,
            r.t_p99,
            r.max_abs_t,
            if pass { "PASS" } else { "FAIL" }
        );
    }
    println!("----------------------------------------------------------------------------------------");

    // Throughput Benchmarks
    println!(" Scalar Portable vs Platform SIMD Throughput Benchmarks (median of 9 × 4096 iters):");
    println!("--------------------------------------------------------------------------------");
    let bench_iters = 4096usize;
    let mut bench_rng = KeccakRng::new(0xBEEF_CAFE_1234_5678);

    let mut sample_keccak = KeccakState4x::default();
    for lane in &mut sample_keccak.0 {
        for value in lane {
            *value = bench_rng.next_u64();
        }
    }

    let cyc_keccak_port = median_cycles(9, || {
        let mut st = sample_keccak;
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            keccak_f1600_x4_with_backend(black_box(&mut st), SimdBackend::Portable);
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64 * 4.0)
    });
    let cyc_keccak_simd = median_cycles(9, || {
        let mut st = sample_keccak;
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            keccak_f1600_x4_with_backend(black_box(&mut st), active);
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64 * 4.0)
    });
    println!(
        " Keccak-f[1600] (cyc / sponge)      : Portable = {:>8.2} | SIMD = {:>8.2} ({:>5.2}x)",
        cyc_keccak_port,
        cyc_keccak_simd,
        cyc_keccak_port / cyc_keccak_simd.max(0.01)
    );

    let mut gf_buf_a = [0x37u8; 1024];
    let mut gf_buf_b = [0x9Du8; 1024];
    let mut gf_buf_o = [0u8; 1024];
    bench_rng.fill_bytes(&mut gf_buf_a);
    bench_rng.fill_bytes(&mut gf_buf_b);

    let cyc_gf_mul_port = median_cycles(9, || {
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            gf256_shamir_mul_with_backend(
                black_box(&mut gf_buf_o),
                black_box(&gf_buf_a),
                black_box(&gf_buf_b),
                SimdBackend::Portable,
            );
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64 * 1024.0)
    });
    let cyc_gf_mul_simd = median_cycles(9, || {
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            gf256_shamir_mul_with_backend(
                black_box(&mut gf_buf_o),
                black_box(&gf_buf_a),
                black_box(&gf_buf_b),
                active,
            );
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64 * 1024.0)
    });
    println!(
        " GF(2^8) T_3 Shamir Mul (cyc / B)   : Portable = {:>8.3} | SIMD = {:>8.3} ({:>5.1}x)",
        cyc_gf_mul_port,
        cyc_gf_mul_simd,
        cyc_gf_mul_port / cyc_gf_mul_simd.max(0.0001)
    );

    let cyc_gf_mac_port = median_cycles(9, || {
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            gf256_shamir_mac_with_backend(
                black_box(&mut gf_buf_o),
                black_box(&gf_buf_a),
                black_box(0x7B),
                SimdBackend::Portable,
            );
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64 * 1024.0)
    });
    let cyc_gf_mac_simd = median_cycles(9, || {
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            gf256_shamir_mac_with_backend(
                black_box(&mut gf_buf_o),
                black_box(&gf_buf_a),
                black_box(0x7B),
                active,
            );
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64 * 1024.0)
    });
    println!(
        " GF(2^8) T_3 Shamir MAC (cyc / B)   : Portable = {:>8.3} | SIMD = {:>8.3} ({:>5.1}x)",
        cyc_gf_mac_port,
        cyc_gf_mac_simd,
        cyc_gf_mac_port / cyc_gf_mac_simd.max(0.0001)
    );

    let t128_l = [[0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3211u128; 2]; 16];
    let t128_r = [[0x89AB_CDEF_0123_4567_1357_9BDF_2468_ACE1u128; 2]; 16];
    let cyc_bdoz_port = median_cycles(9, || {
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            black_box(tower128_bdoz_2lane_poly_mac_with_backend(
                black_box(&t128_l),
                black_box(&t128_r),
                SimdBackend::Portable,
            ));
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64 * 16.0)
    });
    let cyc_bdoz_simd = median_cycles(9, || {
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            black_box(tower128_bdoz_2lane_poly_mac_with_backend(
                black_box(&t128_l),
                black_box(&t128_r),
                active,
            ));
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64 * 16.0)
    });
    println!(
        " Tower128 2-Lane BDOZ MAC (cyc/pair): Portable = {:>8.2} | SIMD = {:>8.2} ({:>5.1}x)",
        cyc_bdoz_port,
        cyc_bdoz_simd,
        cyc_bdoz_port / cyc_bdoz_simd.max(0.01)
    );

    let cyc_bdoz_t7_port = median_cycles(9, || {
        let t0 = serialized_ticks_start();
        for _ in 0..(bench_iters / 4) {
            black_box(tower128_bdoz_2lane_mac_with_backend(
                black_box(&t128_l),
                black_box(&t128_r),
                SimdBackend::Portable,
            ));
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / ((bench_iters / 4) as f64 * 16.0)
    });
    let cyc_bdoz_t7_simd = median_cycles(9, || {
        let t0 = serialized_ticks_start();
        for _ in 0..(bench_iters / 4) {
            black_box(tower128_bdoz_2lane_mac_with_backend(
                black_box(&t128_l),
                black_box(&t128_r),
                active,
            ));
        }
        serialized_ticks_end().wrapping_sub(t0) as f64 / ((bench_iters / 4) as f64 * 16.0)
    });
    println!(
        " Tower128 Wiedemann T_7 MAC (cyc/pr): Portable = {:>8.2} | SIMD = {:>8.2} ({:>5.1}x)",
        cyc_bdoz_t7_port,
        cyc_bdoz_t7_simd,
        cyc_bdoz_t7_port / cyc_bdoz_t7_simd.max(0.01)
    );

    let cyc_gl_port = median_cycles(9, || {
        let mut x = 0xFFFF_FFFE_1234_5678u64;
        let y = 0x7654_3210_FEDC_BA98u64;
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            x = goldilocks_mul_ct_with_backend(black_box(x), black_box(y), SimdBackend::Portable);
        }
        black_box(x);
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64)
    });
    let cyc_gl_simd = median_cycles(9, || {
        let mut x = 0xFFFF_FFFE_1234_5678u64;
        let y = 0x7654_3210_FEDC_BA98u64;
        let t0 = serialized_ticks_start();
        for _ in 0..bench_iters {
            x = goldilocks_mul_ct_with_backend(black_box(x), black_box(y), active);
        }
        black_box(x);
        serialized_ticks_end().wrapping_sub(t0) as f64 / (bench_iters as f64)
    });
    println!(
        " Goldilocks Mul (cyc / mul)         : Portable = {:>8.2} | ASM  = {:>8.2} ({:>5.2}x)",
        cyc_gl_port,
        cyc_gl_simd,
        cyc_gl_port / cyc_gl_simd.max(0.01)
    );
    println!("================================================================================");

    assert!(
        all_pass,
        "One or more qsag-asm kernels exceeded |t| >= {} threshold!",
        T_THRESHOLD
    );
}

fn median_cycles<F: FnMut() -> f64>(trials: usize, mut f: F) -> f64 {
    let mut vals = Vec::with_capacity(trials);
    for _ in 0..trials {
        vals.push(f());
    }
    vals.sort_by(|a, b| a.partial_cmp(b).unwrap());
    vals[trials / 2]
}
