//! Fast statistical constant-time integration gate (`dudect` Welch's $t$-test) for `qsag-asm`.
//!
//! Defaults to `25_600` traces per kernel (`< 2s` in `cargo test --release`) and honors
//! `QSAG_DUDECT_SAMPLES` (e.g. `QSAG_DUDECT_SAMPLES=1000000`) for deep saturation runs.
//! Reports and enforces `|t| < 5.5` across BOTH uncropped (`raw`) and cropped (`p50..p99`)
//! Welch-$t$ estimators over the cryptographic assembly kernels (including
//! `tower128_bdoz_2lane_mac_with_backend`) and, in a second gate, the remaining runtime-dispatched
//! entry points, paired with a `#tooth` negative-control leak check.

// Machine timing and rdtsc have no interpretation under Miri.
#![cfg(not(miri))]

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

/// Minimum counter ticks per recorded sample before inner batching kicks in.
///
/// `rdtsc` counts at core-clock granularity, so x86 keeps one call per sample. AArch64
/// `cntvct_el0` runs at a fixed `CNTFRQ_EL0` (24 MHz on Apple cores, 25-1000 MHz on Neoverse),
/// so a single nanosecond-scale call quantizes to `0`/`1` ticks and the Welch statistic
/// degenerates. There each sample instead times `reps` back-to-back calls on the same slot,
/// where `reps` is calibrated once per kernel from warmup chunks (independently of class) so
/// that a sample spans at least this many ticks. Override with `QSAG_DUDECT_MIN_SAMPLE_TICKS`.
#[cfg(target_arch = "aarch64")]
const DEFAULT_MIN_SAMPLE_TICKS: u64 = 256;
#[cfg(not(target_arch = "aarch64"))]
const DEFAULT_MIN_SAMPLE_TICKS: u64 = 1;
const MAX_INNER_REPS: u64 = 1 << 16;

fn configured_samples() -> usize {
    std::env::var("QSAG_DUDECT_SAMPLES")
        .ok()
        .and_then(|s| s.replace('_', "").parse::<usize>().ok())
        .filter(|&n| n >= CHUNK)
        .unwrap_or(DEFAULT_TEST_TRACES)
}

fn configured_min_sample_ticks() -> u64 {
    std::env::var("QSAG_DUDECT_MIN_SAMPLE_TICKS")
        .ok()
        .and_then(|s| s.replace('_', "").parse::<u64>().ok())
        .filter(|&n| n >= 1)
        .unwrap_or(DEFAULT_MIN_SAMPLE_TICKS)
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

    /// Bulk masked fill for multi-kilobyte operands: one Keccak-derived seed per call expanded
    /// with SplitMix64, so the random class stays full-entropy per slot without spending a
    /// portable Keccak permutation per 544 bytes. `mask = 0` yields the fixed (all-zero) class.
    fn fill_masked_u64(&mut self, words: &mut [u64], mask: u64) {
        let mut s = self.next_u64();
        for w in words {
            s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            *w = (z ^ (z >> 31)) & mask;
        }
    }

    fn fill_masked_bytes(&mut self, buf: &mut [u8], mask: u8) {
        let mut s = self.next_u64();
        for chunk in buf.chunks_mut(8) {
            s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            let w = (z ^ (z >> 31)).to_le_bytes();
            for (dst, src) in chunk.iter_mut().zip(w) {
                *dst = src & mask;
            }
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
    reps: u64,
}

/// Time `reps` back-to-back evaluations of slot `i` as one sample.
#[inline(always)]
fn time_slot<S, Meas>(state: &mut S, measure_slot: &mut Meas, i: usize, reps: u64) -> u64
where
    Meas: FnMut(&mut S, usize) -> u64,
{
    let t0 = serialized_ticks_start();
    for _ in 0..reps {
        black_box(measure_slot(state, i));
    }
    let t1 = serialized_ticks_end();
    t1.wrapping_sub(t0)
}

/// Every `measure_slot` must be idempotent per slot (in-place kernels copy their prepared
/// input into a work buffer inside the closure), so a batched sample re-runs the kernel on
/// the same class-`c` operand `reps` times rather than on its own output.
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

    // Warmup doubles as class-blind calibration of the inner batch size: the whole chunk
    // (both classes, random order) is timed with single calls, and `reps` is chosen from the
    // mean so that one sample spans at least `min_sample_ticks` counter ticks.
    let min_sample_ticks = configured_min_sample_ticks();
    let mut warm_total = 0u64;
    for _ in 0..WARMUP_CHUNKS {
        for c in &mut classes {
            *c = (rng.next_u64() & 1) as u8;
        }
        prepare_chunk(state, &mut rng, &classes);
        let w0 = serialized_ticks_start();
        for (i, tick) in ticks.iter_mut().enumerate() {
            *tick = time_slot(state, &mut measure_slot, i, 1);
        }
        let w1 = serialized_ticks_end();
        warm_total = warm_total.saturating_add(w1.wrapping_sub(w0));
    }
    let warm_calls = (WARMUP_CHUNKS * CHUNK) as u64;
    let reps = if min_sample_ticks <= 1 {
        1
    } else {
        // ceil(min_sample_ticks * calls / total), with a zero-tick total mapped to the cap.
        (min_sample_ticks.saturating_mul(warm_calls))
            .div_ceil(warm_total.max(1))
            .clamp(1, MAX_INNER_REPS)
    };

    let n_chunks = min_traces.div_ceil(CHUNK);
    let mut raw_est = WelfordPair::default();
    let mut cropped = [WelfordPair::default(); 5];
    let mut measured = Vec::with_capacity(n_chunks * CHUNK);

    for _ in 0..n_chunks {
        for c in &mut classes {
            *c = (rng.next_u64() & 1) as u8;
        }
        prepare_chunk(state, &mut rng, &classes);
        for (i, tick) in ticks.iter_mut().enumerate() {
            *tick = time_slot(state, &mut measure_slot, i, reps);
        }
        for i in 0..CHUNK {
            raw_est.push(classes[i] as usize, ticks[i] as f64);
            measured.push((classes[i], ticks[i]));
        }
    }

    // Crop at percentiles of the measured ticks themselves so DVFS frequency steps between
    // warmup and measurement cannot leave a crop tier empty (`n = 0`).
    let mut sorted: Vec<u64> = measured.iter().map(|&(_, dt)| dt).collect();
    sorted.sort_unstable();
    let thresholds = [50, 75, 90, 95, 99].map(|p| sorted[(sorted.len() * p) / 100]);
    for &(class, dt) in &measured {
        for (tier, &cap) in thresholds.iter().enumerate() {
            if dt <= cap {
                cropped[tier].push(class as usize, dt as f64);
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
        reps,
    }
}

fn report_and_gate(stats: &[GateStat], limit: f64) {
    for st in stats {
        eprintln!(
            "{}: raw t={:+.3}, cropped max |t|={:.3}, max |t|={:.3}, reps/sample={}",
            st.name, st.t_raw, st.t_cropped_max, st.max_abs_t, st.reps
        );
    }
    for st in stats {
        assert!(
            st.max_abs_t < limit,
            "Constant-time Welch-t gate exceeded for {}: t_raw={:+.2}, t_cropped_max={:.2} (limit {})",
            st.name,
            st.t_raw,
            st.t_cropped_max,
            limit
        );
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
    eprintln!(
        "{}: max |t|={:.3}, reps/sample={} (must exceed 8.0)",
        neg.name, neg.max_abs_t, neg.reps
    );

    let mut stats = Vec::new();

    // 1. Keccak-f[1600] x4 (prepared input copied into a work state so batched reps stay
    //    on the class operand instead of iterating the permutation on its own output)
    let mut k_batch = vec![KeccakState4x::default(); CHUNK];
    let mut k_work = KeccakState4x::default();
    stats.push(measure_dudect(
        "qsag_asm_keccak_f1600_x4",
        samples,
        &mut (&mut k_batch, &mut k_work),
        |(batch, _), rng, classes| {
            for i in 0..CHUNK {
                let mask = 0u64.wrapping_sub(classes[i] as u64);
                for lane in &mut batch[i].0 {
                    for value in lane {
                        *value = rng.next_u64() & mask;
                    }
                }
            }
        },
        |(batch, work), i| {
            **work = batch[i];
            keccak_f1600_x4_with_backend(black_box(&mut **work), active);
            work.0[0][0]
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
            gf256_shamir_mul_with_backend(
                black_box(*dst),
                black_box(&a[i]),
                black_box(&b[i]),
                active,
            );
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
            gf256_shamir_mac_with_backend(
                black_box(*dst),
                black_box(&a[i]),
                black_box(sc[i]),
                active,
            );
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
            let out = tower128_bdoz_2lane_poly_mac_with_backend(
                black_box(&l[i]),
                black_box(&r[i]),
                active,
            );
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
                y[i] = ((rng.next_u64() % GOLDILOCKS_PRIME) & m) | ((!m) & (GOLDILOCKS_PRIME - 1));
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

    report_and_gate(&stats, T_GATE_THRESHOLD);
}

/// Fixed versus random secret operands for the runtime-dispatched entry points the main gate
/// does not reach: the ML-DSA transforms, SHA-256 compression, the GF(2) accumulate, combine
/// and scale kernels, the bitslice pack and unpack, the tower basis maps, the scalar Goldilocks
/// add and sub, the byte comparison and erasure, the 8-way Keccak, and the AVX2
/// Russian-peasant Shamir pair. Each one runs on whatever backend this CPU dispatches to.
#[test]
fn dudect_dispatched_kernels_outside_the_main_gate() {
    use qsag_asm::bitslice::gf2_128_scale_xor;
    use qsag_asm::ntt_simd::{MLDSA_N, MLDSA_Q};
    use qsag_asm::{
        BITSLICE_LANES, BitPlane256, KECCAK_STATE_BITS, KECCAK_STATE_BYTES, KeccakState8x,
        XorCombinePattern, ct_eq_bytes, ct_memzero, gf2_64x128_clmul_acc, gf2_xor_combine_planes,
        gf256_shamir_mac_avx2_russian_peasant, gf256_shamir_mul_avx2_russian_peasant,
        goldilocks_add_ct, goldilocks_sub_ct, keccak_f1600_x8, mldsa_inv_ntt, mldsa_ntt,
        mldsa_pointwise_mul, pack_256x200_bitslice, poly128_to_tower128_ct, sha256_compress_blocks,
        tower128_to_poly128_ct, unpack_256x200_bitslice,
    };

    let _ = enable_hardware_dit();
    let samples = configured_samples();
    let mut stats = Vec::new();

    // ML-DSA forward and inverse transforms and the pointwise product, coefficients below q.
    type Poly = [u32; MLDSA_N];
    fn fill_polys(polys: &mut [Poly], rng: &mut KeccakRng, classes: &[u8; CHUNK]) {
        for (poly, class) in polys.iter_mut().zip(classes) {
            let mask = 0u32.wrapping_sub(u32::from(*class));
            for c in poly.iter_mut() {
                *c = ((rng.next_u64() % u64::from(MLDSA_Q)) as u32) & mask;
            }
        }
    }
    let mut polys = vec![[0u32; MLDSA_N]; CHUNK];
    let mut poly_work = [0u32; MLDSA_N];
    for (name, transform) in [
        ("mldsa_ntt", mldsa_ntt as fn(&mut Poly)),
        ("mldsa_inv_ntt", mldsa_inv_ntt as fn(&mut Poly)),
    ] {
        stats.push(measure_dudect(
            name,
            samples,
            &mut (&mut polys, &mut poly_work),
            |(polys, _), rng, classes| fill_polys(polys, rng, classes),
            |(polys, work), i| {
                **work = polys[i];
                transform(black_box(&mut **work));
                u64::from(work[0])
            },
        ));
    }
    let mut polys_rhs = vec![[0u32; MLDSA_N]; CHUNK];
    stats.push(measure_dudect(
        "mldsa_pointwise_mul",
        samples,
        &mut (&mut polys, &mut polys_rhs, &mut poly_work),
        |(lhs, rhs, _), rng, classes| {
            fill_polys(lhs, rng, classes);
            fill_polys(rhs, rng, classes);
        },
        |(lhs, rhs, out), i| {
            mldsa_pointwise_mul(
                black_box(&mut **out),
                black_box(&lhs[i]),
                black_box(&rhs[i]),
            );
            u64::from(out[0])
        },
    ));

    // SHA-256 compression: secret chaining value and four secret blocks.
    let mut sha_in = vec![([0u32; 8], [[0u8; 64]; 4]); CHUNK];
    let mut sha_state = [0u32; 8];
    stats.push(measure_dudect(
        "sha256_compress_blocks",
        samples,
        &mut (&mut sha_in, &mut sha_state),
        |(inputs, _), rng, classes| {
            for ((state, blocks), class) in inputs.iter_mut().zip(classes) {
                let mask = 0u8.wrapping_sub(*class);
                for word in state.iter_mut() {
                    *word = (rng.next_u64() as u32) & 0u32.wrapping_sub(u32::from(*class));
                }
                for block in blocks.iter_mut() {
                    rng.fill_masked_bytes(block, mask);
                }
            }
        },
        |(inputs, state), i| {
            **state = inputs[i].0;
            sha256_compress_blocks(black_box(&mut **state), black_box(&inputs[i].1));
            u64::from(state[0])
        },
    ));

    // Unreduced 64x128 carryless multiply-accumulate: secret words and a secret scalar.
    let mut clmul_in = vec![([0u64; 16], 0u128); CHUNK];
    let mut clmul_acc = [[0u128; 2]; 16];
    stats.push(measure_dudect(
        "gf2_64x128_clmul_acc",
        samples,
        &mut (&mut clmul_in, &mut clmul_acc),
        |(inputs, _), rng, classes| {
            for ((words, scalar), class) in inputs.iter_mut().zip(classes) {
                let mask = 0u64.wrapping_sub(u64::from(*class));
                rng.fill_masked_u64(words, mask);
                *scalar = rng.next_u128() & (u128::from(mask) | (u128::from(mask) << 64));
            }
        },
        |(inputs, acc), i| {
            **acc = [[0; 2]; 16];
            gf2_64x128_clmul_acc(
                black_box(&mut acc[..]),
                black_box(&inputs[i].0),
                black_box(inputs[i].1),
            );
            acc[0][0] as u64
        },
    ));

    // Elementwise scale-XOR in the polynomial field: secret source and scalar.
    let mut scale_in = vec![([0u128; 16], 0u128); CHUNK];
    let mut scale_dst = [0u128; 16];
    stats.push(measure_dudect(
        "gf2_128_scale_xor",
        samples,
        &mut (&mut scale_in, &mut scale_dst),
        |(inputs, _), rng, classes| {
            for ((src, scalar), class) in inputs.iter_mut().zip(classes) {
                let mask = 0u128.wrapping_sub(u128::from(*class));
                for value in src.iter_mut() {
                    *value = rng.next_u128() & mask;
                }
                *scalar = rng.next_u128() & mask;
            }
        },
        |(inputs, dst), i| {
            **dst = [0; 16];
            gf2_128_scale_xor(
                black_box(&mut dst[..]),
                black_box(&inputs[i].0),
                black_box(inputs[i].1),
            );
            dst[0] as u64
        },
    ));

    // Subset-XOR combination: secret rows under one fixed public pattern.
    let mut pattern_rng = KeccakRng::new(0x5EED_0000_0000_0A77);
    let mut pattern: XorCombinePattern = [[0; 16]; 128];
    for row in pattern.iter_mut() {
        pattern_rng.fill_bytes(row);
    }
    let mut combine_rows = vec![[[0u64; 4]; 64]; CHUNK];
    let mut combine_out = Box::new([[[0u64; 4]; 64]; 2]);
    stats.push(measure_dudect(
        "gf2_xor_combine_planes",
        samples,
        &mut (&mut combine_rows, &mut combine_out),
        |(rows, _), rng, classes| {
            for (row, class) in rows.iter_mut().zip(classes) {
                let mask = 0u64.wrapping_sub(u64::from(*class));
                for plane in row.iter_mut() {
                    rng.fill_masked_u64(plane, mask);
                }
            }
        },
        |(rows, out), i| {
            gf2_xor_combine_planes(
                black_box(&rows[i]),
                black_box(&pattern),
                black_box(&mut **out),
            );
            out[0][0][0]
        },
    ));

    // Bitslice pack and unpack of 256 Keccak states. Both are pure functions of their input,
    // so no work copy is needed.
    let mut states = vec![[[0u8; KECCAK_STATE_BYTES]; BITSLICE_LANES]; CHUNK];
    let mut planes_out = vec![[0u64; 4]; KECCAK_STATE_BITS];
    stats.push(measure_dudect(
        "pack_256x200_bitslice",
        samples,
        &mut (&mut states, &mut planes_out),
        |(states, _), rng, classes| {
            for (state, class) in states.iter_mut().zip(classes) {
                let mask = 0u8.wrapping_sub(*class);
                for lane in state.iter_mut() {
                    rng.fill_masked_bytes(lane, mask);
                }
            }
        },
        |(states, planes), i| {
            let planes: &mut [BitPlane256; KECCAK_STATE_BITS] =
                (&mut planes[..]).try_into().unwrap();
            pack_256x200_bitslice(black_box(&states[i]), black_box(planes));
            planes[0][0]
        },
    ));
    drop(states);
    let mut planes_in = vec![[[0u64; 4]; KECCAK_STATE_BITS]; CHUNK];
    let mut states_out = vec![[0u8; KECCAK_STATE_BYTES]; BITSLICE_LANES];
    stats.push(measure_dudect(
        "unpack_256x200_bitslice",
        samples,
        &mut (&mut planes_in, &mut states_out),
        |(planes, _), rng, classes| {
            for (plane_set, class) in planes.iter_mut().zip(classes) {
                let mask = 0u64.wrapping_sub(u64::from(*class));
                for plane in plane_set.iter_mut() {
                    rng.fill_masked_u64(plane, mask);
                }
            }
        },
        |(planes, states), i| {
            let states: &mut [[u8; KECCAK_STATE_BYTES]; BITSLICE_LANES] =
                (&mut states[..]).try_into().unwrap();
            unpack_256x200_bitslice(black_box(&planes[i]), black_box(states));
            u64::from(states[0][0])
        },
    ));
    drop(planes_in);

    // Tower <-> polynomial basis maps (`linear_map`).
    let mut field = [0u128; CHUNK];
    for (name, map) in [
        (
            "tower128_to_poly128_ct",
            tower128_to_poly128_ct as fn(u128) -> u128,
        ),
        (
            "poly128_to_tower128_ct",
            poly128_to_tower128_ct as fn(u128) -> u128,
        ),
    ] {
        stats.push(measure_dudect(
            name,
            samples,
            &mut field,
            |values, rng, classes| {
                for (value, class) in values.iter_mut().zip(classes) {
                    *value = rng.next_u128() & 0u128.wrapping_sub(u128::from(*class));
                }
            },
            |values, i| map(black_box(values[i])) as u64,
        ));
    }

    // Scalar Goldilocks add and sub on canonical operands.
    let mut gl = [(0u64, 0u64); CHUNK];
    for (name, op) in [
        (
            "goldilocks_add_ct",
            goldilocks_add_ct as fn(u64, u64) -> u64,
        ),
        (
            "goldilocks_sub_ct",
            goldilocks_sub_ct as fn(u64, u64) -> u64,
        ),
    ] {
        stats.push(measure_dudect(
            name,
            samples,
            &mut gl,
            |pairs, rng, classes| {
                for (pair, class) in pairs.iter_mut().zip(classes) {
                    let mask = 0u64.wrapping_sub(u64::from(*class));
                    // Fixed class: the operands whose sum and difference both wrap.
                    *pair = (
                        ((rng.next_u64() % GOLDILOCKS_PRIME) & mask) | (!mask & 1),
                        ((rng.next_u64() % GOLDILOCKS_PRIME) & mask)
                            | (!mask & (GOLDILOCKS_PRIME - 1)),
                    );
                }
            },
            |pairs, i| op(black_box(pairs[i].0), black_box(pairs[i].1)),
        ));
    }

    // Variable-length comparison: equal against a difference in the first byte.
    let eq_ref = [0x5Au8; 96];
    let mut eq_in = [[0x5Au8; 96]; CHUNK];
    stats.push(measure_dudect(
        "ct_eq_bytes",
        samples,
        &mut eq_in,
        |tags, _rng, classes| {
            for (tag, class) in tags.iter_mut().zip(classes) {
                *tag = [0x5A; 96];
                tag[0] ^= (*class ^ 1) & 1;
            }
        },
        |tags, i| u64::from(ct_eq_bytes(black_box(&eq_ref), black_box(&tags[i]))),
    ));

    // Erasure must not depend on what is erased.
    let mut zero_in = [[0u8; 96]; CHUNK];
    let mut zero_work = [0u8; 96];
    stats.push(measure_dudect(
        "ct_memzero",
        samples,
        &mut (&mut zero_in, &mut zero_work),
        |(inputs, _), rng, classes| {
            for (input, class) in inputs.iter_mut().zip(classes) {
                rng.fill_masked_bytes(input, 0u8.wrapping_sub(*class));
            }
        },
        |(inputs, work), i| {
            **work = inputs[i];
            ct_memzero(black_box(&mut work[..]));
            u64::from(work[0])
        },
    ));

    // Eight-way Keccak-f[1600].
    let mut k8 = vec![KeccakState8x::default(); CHUNK];
    let mut k8_work = KeccakState8x::default();
    stats.push(measure_dudect(
        "keccak_f1600_x8",
        samples,
        &mut (&mut k8, &mut k8_work),
        |(batch, _), rng, classes| {
            for (state, class) in batch.iter_mut().zip(classes) {
                let mask = 0u64.wrapping_sub(u64::from(*class));
                for lane in state.0.iter_mut() {
                    rng.fill_masked_u64(lane, mask);
                }
            }
        },
        |(batch, work), i| {
            **work = batch[i];
            keccak_f1600_x8(black_box(&mut **work));
            work.0[0][0]
        },
    ));

    // AVX2 Russian-peasant Shamir multiply and multiply-accumulate (portable elsewhere),
    // at a length with both whole blocks and a tail.
    const SHAMIR_LEN: usize = 80;
    let mut sh = vec![([0u8; SHAMIR_LEN], [0u8; SHAMIR_LEN], 0u8); CHUNK];
    let mut sh_out = [0u8; SHAMIR_LEN];
    fn fill_shamir(
        inputs: &mut [([u8; SHAMIR_LEN], [u8; SHAMIR_LEN], u8)],
        rng: &mut KeccakRng,
        classes: &[u8; CHUNK],
    ) {
        for ((a, b, scalar), class) in inputs.iter_mut().zip(classes) {
            let mask = 0u8.wrapping_sub(*class);
            rng.fill_masked_bytes(a, mask);
            rng.fill_masked_bytes(b, mask);
            *scalar = (rng.next_u64() as u8) & mask;
        }
    }
    stats.push(measure_dudect(
        "gf256_shamir_mul_avx2_russian_peasant",
        samples,
        &mut (&mut sh, &mut sh_out),
        |(inputs, _), rng, classes| fill_shamir(inputs, rng, classes),
        |(inputs, out), i| {
            gf256_shamir_mul_avx2_russian_peasant(
                black_box(&mut out[..]),
                black_box(&inputs[i].0),
                black_box(&inputs[i].1),
            );
            u64::from(out[0])
        },
    ));
    stats.push(measure_dudect(
        "gf256_shamir_mac_avx2_russian_peasant",
        samples,
        &mut (&mut sh, &mut sh_out),
        |(inputs, _), rng, classes| fill_shamir(inputs, rng, classes),
        |(inputs, out), i| {
            **out = inputs[i].1;
            gf256_shamir_mac_avx2_russian_peasant(
                black_box(&mut out[..]),
                black_box(&inputs[i].0),
                black_box(inputs[i].2),
            );
            u64::from(out[0])
        },
    ));

    report_and_gate(&stats, T_GATE_THRESHOLD);
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
        stats.push(measure_dudect(
            "transpose64x256_avx2",
            samples,
            &mut rows,
            |rows, rng, classes| {
                for (row, class) in rows.iter_mut().zip(classes) {
                    let mask = 0u64.wrapping_sub(*class as u64);
                    for word in row.iter_mut().flatten() {
                        *word = rng.next_u64() & mask;
                    }
                }
            },
            |rows, i| {
                // SAFETY: AVX2 checked above; exactly 64 contiguous 256-bit rows.
                unsafe {
                    qsag_asm_transpose64x256_avx2(black_box(rows[i].as_mut_ptr().cast()));
                }
                black_box(rows[i][0][0])
            },
        ));
    }
    for vector in [false, true] {
        if !std::is_x86_feature_detected!("pclmulqdq")
            || (vector
                && !(std::is_x86_feature_detected!("avx2")
                    && std::is_x86_feature_detected!("vpclmulqdq")))
        {
            continue;
        }
        let mut operands = vec![([[0u64; 2]; 16], [[0u64; 2]; 16], [0u64; 2]); CHUNK];
        stats.push(measure_dudect(
            if vector {
                "gf2_128_mul_acc_vpclmul"
            } else {
                "gf2_128_mul_acc_pclmul"
            },
            samples,
            &mut operands,
            |ops, rng, classes| {
                for ((a, b, acc), class) in ops.iter_mut().zip(classes) {
                    let mask = 0u64.wrapping_sub(*class as u64);
                    for word in a
                        .iter_mut()
                        .chain(b.iter_mut())
                        .flatten()
                        .chain(acc.iter_mut())
                    {
                        *word = rng.next_u64() & mask;
                    }
                }
            },
            |ops, i| {
                let (a, b, acc) = &mut ops[i];
                // SAFETY: CPU features checked; buffers hold sixteen 128-bit operands.
                unsafe {
                    if vector {
                        qsag_asm_gf2_128_mul_acc_vpclmul(
                            black_box(acc.as_mut_ptr().cast()),
                            black_box(a.as_ptr().cast()),
                            black_box(b.as_ptr().cast()),
                            8,
                        );
                    } else {
                        qsag_asm_gf2_128_mul_acc_pclmul(
                            black_box(acc.as_mut_ptr().cast()),
                            black_box(a.as_ptr().cast()),
                            black_box(b.as_ptr().cast()),
                            16,
                        );
                    }
                }
                black_box(acc[0])
            },
        ));
    }
    for stat in stats {
        eprintln!(
            "{}: raw t={:+.3}, cropped max |t|={:.3}, reps/sample={}",
            stat.name, stat.t_raw, stat.t_cropped_max, stat.reps
        );
        assert!(
            stat.max_abs_t < 4.5,
            "{}: max |t|={} >= 4.5",
            stat.name,
            stat.max_abs_t
        );
    }
}
