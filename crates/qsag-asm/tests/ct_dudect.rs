//! Fast statistical constant-time integration gate (`dudect` Welch's $t$-test) for `qsag-asm`.
//!
//! Defaults to `25_600` traces per kernel (`< 2s` in `cargo test --release`) and honors
//! `QSAG_DUDECT_SAMPLES` (e.g. `QSAG_DUDECT_SAMPLES=1000000`) for deep saturation runs.
//! Reports and enforces `|t| < 5.5` across BOTH uncropped (`raw`) and cropped (`p50..p99`)
//! Welch-$t$ estimators over all 9 cryptographic assembly kernels (including
//! `tower128_bdoz_2lane_mac_with_backend`), paired with a `#tooth` negative-control leak check.

use core::hint::black_box;
use qsag_asm::{
    GOLDILOCKS_PRIME, KeccakRow256, KeccakState4x, ct_eq_32, detect_backend, enable_hardware_dit,
    gf256_shamir_mac_with_backend, gf256_shamir_mul_with_backend, goldilocks_dot2_ct,
    goldilocks_mul_ct_with_backend, goldilocks_pow7_ct_with_backend,
    keccak_chi_mpc_row256_with_backend, keccak_f1600_x4_with_backend,
    tower128_bdoz_2lane_mac_with_backend, tower128_bdoz_2lane_poly_mac_with_backend,
};

const CHUNK: usize = 256;
#[cfg(not(debug_assertions))]
const DEFAULT_TEST_TRACES: usize = 25_600;
#[cfg(debug_assertions)]
const DEFAULT_TEST_TRACES: usize = 4_096;
const WARMUP_CHUNKS: usize = 16;
#[cfg(not(debug_assertions))]
const T_GATE_THRESHOLD: f64 = 5.5;
#[cfg(debug_assertions)]
const T_GATE_THRESHOLD: f64 = 7.5;

fn configured_samples() -> usize {
    std::env::var("QSAG_DUDECT_SAMPLES")
        .ok()
        .and_then(|s| s.replace('_', "").parse::<usize>().ok())
        .filter(|&n| n >= CHUNK)
        .unwrap_or(DEFAULT_TEST_TRACES)
}

struct KeccakRng {
    state: KeccakState4x,
    pos: usize,
}

impl KeccakRng {
    fn new(domain: u64) -> Self {
        let mut state = KeccakState4x::default();
        state.0[0] = [
            domain,
            domain ^ 0x5153_4147_5445_5354,
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

struct GateStat {
    name: &'static str,
    t_raw: f64,
    t_cropped_max: f64,
    max_abs_t: f64,
}

fn measure_dudect<S, Prep, Meas>(
    name: &'static str,
    min_traces: usize,
    state: &mut S,
    mut prepare_chunk: Prep,
    mut measure_slot: Meas,
) -> GateStat
where
    Prep: FnMut(&mut S, &mut KeccakRng, &[u8; CHUNK]),
    Meas: FnMut(&mut S, usize) -> u64,
{
    let mut rng = KeccakRng::new(0xD0DE_C755_0000_0001 ^ (name.len() as u64));
    let mut classes = [0u8; CHUNK];
    let mut ticks = [0u64; CHUNK];

    let mut warmup = Vec::with_capacity(WARMUP_CHUNKS * CHUNK);
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
        warmup.extend_from_slice(&ticks);
    }
    warmup.sort_unstable();
    let wn = warmup.len();
    let thresholds = [
        warmup[(wn * 50) / 100].max(1) as f64,
        warmup[(wn * 75) / 100].max(1) as f64,
        warmup[(wn * 90) / 100].max(1) as f64,
        warmup[(wn * 95) / 100].max(1) as f64,
        warmup[(wn * 99) / 100].max(1) as f64,
    ];

    let n_chunks = min_traces.div_ceil(CHUNK);
    let mut raw_est = WelfordPair::default();
    let mut cropped = [WelfordPair::default(); 5];

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
            raw_est.push(cls, dt);
            for (tier, &cap) in thresholds.iter().enumerate() {
                if dt <= cap {
                    cropped[tier].push(cls, dt);
                }
            }
        }
    }

    let t_raw = raw_est.welch_t();
    let t_cropped_max = cropped
        .iter()
        .map(|e| e.welch_t().abs())
        .fold(0.0f64, f64::max);
    let max_abs_t = t_raw.abs().max(t_cropped_max);
    GateStat {
        name,
        t_raw,
        t_cropped_max,
        max_abs_t,
    }
}

#[inline(never)]
fn leaky_early_exit_tag(a: &[u8; 64], b: &[u8; 64]) -> u64 {
    for i in 0..64 {
        if unsafe { core::ptr::read_volatile(&a[i]) != core::ptr::read_volatile(&b[i]) } {
            return 0;
        }
        core::hint::spin_loop();
    }
    1
}

#[test]
fn dudect_constant_time_statistical_gate() {
    let active = detect_backend();
    let _ = enable_hardware_dit();
    let samples = configured_samples();

    // 0. Negative #tooth control must trip Welch's t-test decisively
    let ref64 = [0xAAu8; 64];
    let mut ctrl_tags = [[0xAAu8; 64]; CHUNK];
    let neg = measure_dudect(
        "NEGATIVE_CONTROL_early_exit_tag",
        samples.min(25_600),
        &mut ctrl_tags,
        |tags, _rng, classes| {
            for i in 0..CHUNK {
                let m = 0u8.wrapping_sub(classes[i]);
                tags[i] = [0xAAu8; 64];
                tags[i][0] ^= (!m) & 0x01;
                tags[i][63] ^= m & 0x01;
            }
        },
        |tags, i| leaky_early_exit_tag(black_box(&ref64), black_box(&tags[i])),
    );
    assert!(
        neg.max_abs_t > 8.0,
        "dudect negative control must detect timing leak (got max|t| = {:.2})",
        neg.max_abs_t
    );

    let mut stats = Vec::new();

    // 1. Keccak-f[1600] x4
    let mut k_batch = vec![KeccakState4x::default(); CHUNK];
    stats.push(measure_dudect(
        "qsag_asm_keccak_f1600_x4",
        samples,
        &mut k_batch,
        |batch, rng, classes| {
            for i in 0..CHUNK {
                let mask = 0u64.wrapping_sub(classes[i] as u64);
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

    // 2. Keccak MPC Chi row256
    let mut chi_s0 = vec![KeccakRow256::default(); CHUNK];
    let mut chi_s1 = vec![KeccakRow256::default(); CHUNK];
    let chi_mask = KeccakRow256::default();
    let mut chi_out = KeccakRow256::default();
    stats.push(measure_dudect(
        "qsag_asm_keccak_chi_mpc_row256",
        samples,
        &mut (&mut chi_s0, &mut chi_s1, &mut chi_out),
        |(s0, s1, _), rng, classes| {
            for i in 0..CHUNK {
                let mask = 0u64.wrapping_sub(classes[i] as u64);
                for x in 0..5 {
                    for k in 0..4 {
                        s0[i].0[x][k] = rng.next_u64() & mask;
                        s1[i].0[x][k] = rng.next_u64() & mask;
                    }
                }
            }
        },
        |(s0, s1, out), i| {
            keccak_chi_mpc_row256_with_backend(
                black_box(*out),
                black_box(&s0[i]),
                black_box(&s1[i]),
                black_box(&chi_mask),
                active,
            );
            out.0[0][0]
        },
    ));

    // 3 & 4. GF(2^8) Shamir Mul & MAC
    let mut gf_a = vec![[0u8; 256]; CHUNK];
    let mut gf_b = vec![[0u8; 256]; CHUNK];
    let mut gf_sc = [0u8; CHUNK];
    let mut gf_dst = [0u8; 256];
    stats.push(measure_dudect(
        "qsag_asm_gf256_shamir_mul",
        samples,
        &mut (&mut gf_a, &mut gf_b, &mut gf_dst),
        |(a, b, _), rng, classes| {
            for i in 0..CHUNK {
                let m = 0u8.wrapping_sub(classes[i]);
                rng.fill_bytes(&mut a[i]);
                rng.fill_bytes(&mut b[i]);
                for v in &mut a[i] {
                    *v &= m;
                }
                for v in &mut b[i] {
                    *v &= m;
                }
            }
        },
        |(a, b, dst), i| {
            gf256_shamir_mul_with_backend(black_box(*dst), black_box(&a[i]), black_box(&b[i]), active);
            dst[0] as u64
        },
    ));
    stats.push(measure_dudect(
        "qsag_asm_gf256_shamir_mac",
        samples,
        &mut (&mut gf_a, &mut gf_sc, &mut gf_dst),
        |(a, sc, _), rng, classes| {
            for i in 0..CHUNK {
                let m = 0u8.wrapping_sub(classes[i]);
                rng.fill_bytes(&mut a[i]);
                for v in &mut a[i] {
                    *v &= m;
                }
                sc[i] = ((rng.next_u64() & 0xFF) as u8) & m;
            }
        },
        |(a, sc, dst), i| {
            gf256_shamir_mac_with_backend(black_box(*dst), black_box(&a[i]), black_box(sc[i]), active);
            dst[0] as u64
        },
    ));

    // 5 & 6. Tower128 BDOZ Poly MAC & Wiedemann T_7 MAC
    let mut t_l = vec![[[0u128; 2]; 8]; CHUNK];
    let mut t_r = vec![[[0u128; 2]; 8]; CHUNK];
    stats.push(measure_dudect(
        "qsag_asm_tower128_bdoz_poly_mac",
        samples,
        &mut (&mut t_l, &mut t_r),
        |(l, r), rng, classes| {
            for i in 0..CHUNK {
                let m = 0u128.wrapping_sub(classes[i] as u128);
                for j in 0..8 {
                    l[i][j] = [rng.next_u128() & m, rng.next_u128() & m];
                    r[i][j] = [rng.next_u128() & m, rng.next_u128() & m];
                }
            }
        },
        |(l, r), i| {
            let out =
                tower128_bdoz_2lane_poly_mac_with_backend(black_box(&l[i]), black_box(&r[i]), active);
            (out[0] ^ out[1]) as u64
        },
    ));
    stats.push(measure_dudect(
        "qsag_asm_tower128_bdoz_t7_mac",
        samples,
        &mut (&mut t_l, &mut t_r),
        |(l, r), rng, classes| {
            for i in 0..CHUNK {
                let m = 0u128.wrapping_sub(classes[i] as u128);
                for j in 0..8 {
                    l[i][j] = [rng.next_u128() & m, rng.next_u128() & m];
                    r[i][j] = [rng.next_u128() & m, rng.next_u128() & m];
                }
            }
        },
        |(l, r), i| {
            let out =
                tower128_bdoz_2lane_mac_with_backend(black_box(&l[i]), black_box(&r[i]), active);
            (out[0] ^ out[1]) as u64
        },
    ));

    // 7, 8 & 9. Goldilocks mul, pow7 & dot2_adx
    let mut gl_x = [0u64; CHUNK];
    let mut gl_y = [0u64; CHUNK];
    stats.push(measure_dudect(
        "qsag_asm_goldilocks_mul_ct",
        samples,
        &mut (&mut gl_x, &mut gl_y),
        |(x, y), rng, classes| {
            for i in 0..CHUNK {
                let m = 0u64.wrapping_sub(classes[i] as u64);
                x[i] = rng.next_u64() & m;
                y[i] = (rng.next_u64() & m) | !m;
            }
        },
        |(x, y), i| goldilocks_mul_ct_with_backend(black_box(x[i]), black_box(y[i]), active),
    ));
    stats.push(measure_dudect(
        "qsag_asm_goldilocks_pow7_ct",
        samples,
        &mut gl_x,
        |x, rng, classes| {
            for i in 0..CHUNK {
                let m = 0u64.wrapping_sub(classes[i] as u64);
                x[i] = (rng.next_u64() % GOLDILOCKS_PRIME) & m;
            }
        },
        |x, i| goldilocks_pow7_ct_with_backend(black_box(x[i]), active),
    ));
    stats.push(measure_dudect(
        "qsag_asm_goldilocks_dot2_adx",
        samples,
        &mut (&mut gl_x, &mut gl_y),
        |(x, y), rng, classes| {
            for i in 0..CHUNK {
                let m = 0u64.wrapping_sub(classes[i] as u64);
                x[i] = (rng.next_u64() % GOLDILOCKS_PRIME) & m;
                y[i] = ((rng.next_u64() % GOLDILOCKS_PRIME) & m)
                    | ((!m) & (GOLDILOCKS_PRIME - 1));
            }
        },
        |(x, y), i| {
            goldilocks_dot2_ct(
                black_box(x[i]),
                black_box(y[i]),
                black_box(y[i]),
                black_box(x[i]),
            )
        },
    ));

    // 9. Constant-time 32B tag equality
    let ref32 = [0x5Au8; 32];
    let mut tags32 = [[0x5Au8; 32]; CHUNK];
    stats.push(measure_dudect(
        "qsag_asm_ct_eq_32",
        samples,
        &mut tags32,
        |tags, _rng, classes| {
            for i in 0..CHUNK {
                let m = 0u8.wrapping_sub(classes[i]);
                tags[i] = [0x5Au8; 32];
                tags[i][0] ^= (!m) & 0x01;
            }
        },
        |tags, i| ct_eq_32(black_box(&ref32), black_box(&tags[i])) as u64,
    ));

    for st in &stats {
        assert!(
            st.max_abs_t < T_GATE_THRESHOLD,
            "Constant-time Welch-t gate exceeded for {}: t_raw={:+.2}, t_cropped_max={:.2} (limit {})",
            st.name,
            st.t_raw,
            st.t_cropped_max,
            T_GATE_THRESHOLD
        );
    }
}

/// Fixed versus random operands for each exported x86 bitslice kernel, including
/// both multiplication implementations even when dispatch would prefer VPCLMUL.
#[cfg(target_arch = "x86_64")]
#[test]
fn dudect_bitslice_exported_kernels() {
    unsafe extern "C" {
        fn qsag_asm_transpose64x256_avx2(rows: *mut u8);
        fn qsag_asm_gf2_128_mul_acc_pclmul(acc: *mut u8, a: *const u8, b: *const u8, n: usize);
        fn qsag_asm_gf2_128_mul_acc_vpclmul(acc: *mut u8, a: *const u8, b: *const u8, pairs: usize);
    }
    // Reference the crate so the assembly object is linked even with LTO.
    black_box(qsag_asm::detect_backend());
    let samples = configured_samples();
    let mut stats = Vec::new();
    if std::is_x86_feature_detected!("avx2") {
        let mut rows = vec![[[0u64; 4]; 64]; CHUNK];
        stats.push(measure_dudect("transpose64x256_avx2", samples, &mut rows,
            |rows, rng, classes| {
                for (row, class) in rows.iter_mut().zip(classes) {
                    let mask = 0u64.wrapping_sub(*class as u64);
                    for word in row.iter_mut().flatten() { *word = rng.next_u64() & mask; }
                }
            },
            |rows, i| {
                // SAFETY: AVX2 checked above; exactly 64 contiguous 256-bit rows.
                unsafe { qsag_asm_transpose64x256_avx2(black_box(rows[i].as_mut_ptr().cast())); }
                black_box(rows[i][0][0])
            }));
    }
    for vector in [false, true] {
        if !std::is_x86_feature_detected!("pclmulqdq") ||
            (vector && !(std::is_x86_feature_detected!("avx2") && std::is_x86_feature_detected!("vpclmulqdq"))) { continue; }
        let mut operands = vec![([[0u64; 2]; 16], [[0u64; 2]; 16], [0u64; 2]); CHUNK];
        stats.push(measure_dudect(if vector { "gf2_128_mul_acc_vpclmul" } else { "gf2_128_mul_acc_pclmul" }, samples, &mut operands,
            |ops, rng, classes| {
                for ((a, b, acc), class) in ops.iter_mut().zip(classes) {
                    let mask = 0u64.wrapping_sub(*class as u64);
                    for word in a.iter_mut().chain(b.iter_mut()).flatten().chain(acc.iter_mut()) { *word = rng.next_u64() & mask; }
                }
            },
            |ops, i| {
                let (a, b, acc) = &mut ops[i];
                // SAFETY: CPU features checked; buffers hold sixteen 128-bit operands.
                unsafe {
                    if vector { qsag_asm_gf2_128_mul_acc_vpclmul(black_box(acc.as_mut_ptr().cast()), black_box(a.as_ptr().cast()), black_box(b.as_ptr().cast()), 8); }
                    else { qsag_asm_gf2_128_mul_acc_pclmul(black_box(acc.as_mut_ptr().cast()), black_box(a.as_ptr().cast()), black_box(b.as_ptr().cast()), 16); }
                }
                black_box(acc[0])
            }));
    }
    for stat in stats {
        eprintln!("{}: raw t={:+.3}, cropped max |t|={:.3}", stat.name, stat.t_raw, stat.t_cropped_max);
        assert!(stat.max_abs_t < 4.5, "{}: max |t|={} >= 4.5", stat.name, stat.max_abs_t);
    }
}
