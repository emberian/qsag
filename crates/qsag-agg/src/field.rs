//! Hem field layer. The base field `Goldilocks` ($\mathbb{F}_p, p = 2^{64} - 2^{32} + 1$) and the
//! quadratic extension `GoldilocksExt2` ($\mathbb{F}_p\[u\]/(u^2 - 7)$) are the `qsag-core` types,
//! re-exported here. This module adds what only the aggregation prover needs on top of them:
//! shift/fold helpers, batch inversion, 2-adic roots of unity, and Radix-2 / Radix-4
//! Cooley–Tukey NTT/INTT and coset Reed–Solomon encoding (paired with Quintic `Fp5` in
//! [`crate::zk_hem::v2::field5`]).

use alloc::vec;
use alloc::vec::Vec;
use qsag_core::field::goldilocks::GOLDILOCKS_ROOT_2_32;
pub use qsag_core::field::goldilocks::{GOLDILOCKS_PRIME, Goldilocks, GoldilocksExt2};

/// Primitive $2^{32}$-th root of unity $\omega_{2^{32}} = 7^{2^{32} - 1} \bmod p$.
pub const TWO_ADIC_ROOT_OF_UNITY_32: u64 = GOLDILOCKS_ROOT_2_32;

/// `2^S * x` for `1 <= S <= 31` using shifts and one $\epsilon$ fold.
#[inline(always)]
pub(crate) const fn gl_shl_small<const S: u32>(x: Goldilocks) -> Goldilocks {
    const { assert!(S >= 1 && S <= 31) };
    let v = x.to_canonical_u64();
    Goldilocks::reduce96(v << S, v >> (64 - S))
}

/// Primitive $2^k$-th root of unity for $k \le 32$.
#[inline]
pub(crate) const fn gl_two_adic_generator(log_n: usize) -> Goldilocks {
    assert!(log_n <= 32, "Goldilocks 2-adicity is 32");
    let mut w = Goldilocks::from_u64_reduced(TWO_ADIC_ROOT_OF_UNITY_32);
    let mut steps = 32 - log_n;
    while steps > 0 {
        w = w.square();
        steps -= 1;
    }
    w
}

/// `(c_0 + c_1 u) * u = 7 c_1 + c_0 u`.
#[inline(always)]
pub(crate) const fn ext2_mul_by_u(x: GoldilocksExt2) -> GoldilocksExt2 {
    GoldilocksExt2::new(x.c1.mul_by_7(), x.c0)
}

#[inline(always)]
pub(crate) const fn ext2_shl_small<const S: u32>(x: GoldilocksExt2) -> GoldilocksExt2 {
    GoldilocksExt2::new(gl_shl_small::<S>(x.c0), gl_shl_small::<S>(x.c1))
}

/// Fixed-work inverse `conj(x) / N(x)`, mapping zero to zero.
#[inline]
pub(crate) const fn ext2_inv_or_zero(x: GoldilocksExt2) -> GoldilocksExt2 {
    x.conj().mul_base(x.norm().inv_or_zero())
}

#[inline(always)]
pub(crate) const fn ext2_is_zero(x: GoldilocksExt2) -> bool {
    x.c0.to_canonical_u64() == 0 && x.c1.to_canonical_u64() == 0
}

/// Prover-side helpers on the `qsag-core` base field.
pub trait GoldilocksOps: Copy {
    /// Strict canonical constructor: `None` if `v >= GOLDILOCKS_PRIME`.
    fn from_canonical_u64(v: u64) -> Option<Self>;
    fn is_zero(self) -> bool;
    /// Multiply by $2^S$ (`1 <= S <= 31`) without a multiplication.
    fn shl_small<const S: u32>(self) -> Self;
    /// Montgomery prefix-product batch inversion in place (`1` inversion + $3(N - 1)$
    /// multiplications), mapping `0 -> 0` without poisoning nonzero entries.
    fn batch_inv(values: &mut [Self]);
    /// Primitive $2^k$-th root of unity for $k \le 32$.
    fn two_adic_generator(log_n: usize) -> Self;
}

impl GoldilocksOps for Goldilocks {
    #[inline]
    fn from_canonical_u64(v: u64) -> Option<Self> {
        qsag_whir_verified::decode_canonical_u64(v).map(Goldilocks::from_u64_reduced)
    }

    #[inline(always)]
    fn is_zero(self) -> bool {
        self.to_canonical_u64() == 0
    }

    #[inline(always)]
    fn shl_small<const S: u32>(self) -> Self {
        gl_shl_small::<S>(self)
    }

    fn batch_inv(values: &mut [Self]) {
        const STACK_CAP: usize = 512;
        if values.len() <= 1 {
            if let [x] = values {
                *x = x.inv();
            }
            return;
        }
        if values.len() <= STACK_CAP {
            let mut scratch = [Self::ONE; STACK_CAP];
            batch_inv_with_scratch(values, &mut scratch[..values.len()]);
        } else {
            let mut scratch = vec![Self::ONE; values.len()];
            batch_inv_with_scratch(values, &mut scratch);
        }
    }

    #[inline]
    fn two_adic_generator(log_n: usize) -> Self {
        gl_two_adic_generator(log_n)
    }
}

#[inline]
fn batch_inv_with_scratch(values: &mut [Goldilocks], prefix: &mut [Goldilocks]) {
    debug_assert_eq!(values.len(), prefix.len());
    let mut acc = Goldilocks::ONE;
    for (slot, &v) in prefix.iter_mut().zip(values.iter()) {
        *slot = acc;
        if !v.is_zero() {
            acc = acc.const_mul(v);
        }
    }
    let mut inv_acc = acc.inv();
    for (v, &pref) in values.iter_mut().zip(prefix.iter()).rev() {
        if !v.is_zero() {
            let orig = *v;
            *v = pref.const_mul(inv_acc);
            inv_acc = inv_acc.const_mul(orig);
        }
    }
}

/// Prover-side helpers on the `qsag-core` quadratic extension.
pub trait GoldilocksExt2Ops: Copy {
    /// The adjoined root `u` (`u^2 = 7`).
    const U: Self;
    fn is_zero(self) -> bool;
    fn from_u64(v: u64) -> Self;
    fn to_le_bytes(self) -> [u8; 16];
    fn from_le_bytes_canonical(bytes: [u8; 16]) -> Option<Self>;
    /// Multiply by `u`.
    fn mul_by_u(self) -> Self;
    /// Frobenius endomorphism $x \mapsto x^p = c_0 - c_1 u$.
    fn frobenius(self) -> Self;
    /// Norm $c_0^2 - 7 c_1^2 \in \mathbb{F}_p$.
    fn norm_to_base(self) -> Goldilocks;
    /// Fixed-work inverse, mapping zero to zero.
    fn inv_or_zero(self) -> Self;
    fn pow(self, exp: u64) -> Self;
    fn shl_small<const S: u32>(self) -> Self;
}

impl GoldilocksExt2Ops for GoldilocksExt2 {
    const U: Self = GoldilocksExt2::U_BASIS;

    #[inline(always)]
    fn is_zero(self) -> bool {
        ext2_is_zero(self)
    }

    #[inline]
    fn from_u64(v: u64) -> Self {
        Self::from_base(Goldilocks::from_u64_reduced(v))
    }

    #[inline]
    fn to_le_bytes(self) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&self.c0.to_le_bytes());
        out[8..].copy_from_slice(&self.c1.to_le_bytes());
        out
    }

    #[inline]
    fn from_le_bytes_canonical(bytes: [u8; 16]) -> Option<Self> {
        let (lo, hi) = bytes.split_at(8);
        let c0 = Goldilocks::from_canonical_u64(u64::from_le_bytes(lo.try_into().ok()?))?;
        let c1 = Goldilocks::from_canonical_u64(u64::from_le_bytes(hi.try_into().ok()?))?;
        Some(Self::new(c0, c1))
    }

    #[inline(always)]
    fn mul_by_u(self) -> Self {
        ext2_mul_by_u(self)
    }

    #[inline(always)]
    fn frobenius(self) -> Self {
        self.conj()
    }

    #[inline(always)]
    fn norm_to_base(self) -> Goldilocks {
        self.norm()
    }

    #[inline]
    fn inv_or_zero(self) -> Self {
        ext2_inv_or_zero(self)
    }

    #[inline]
    fn pow(self, mut exp: u64) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        while exp > 0 {
            if (exp & 1) == 1 {
                acc = acc.const_mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }

    #[inline(always)]
    fn shl_small<const S: u32>(self) -> Self {
        ext2_shl_small::<S>(self)
    }
}

/// Bit-reversal permutation in place for power-of-two slice.
#[inline]
fn bit_reverse_permute<T: Copy>(a: &mut [T]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros() as usize;
    if log_n == 0 {
        return;
    }
    for i in 0..n {
        let rev = i.reverse_bits() >> (usize::BITS as usize - log_n);
        if i < rev {
            a.swap(i, rev);
        }
    }
}

/// 4-way unrolled Cooley–Tukey butterfly block breaking serial twiddle dependency chains.
#[inline(always)]
fn butterfly_block_goldilocks(
    lo: &mut [Goldilocks],
    hi: &mut [Goldilocks],
    w_init: Goldilocks,
    w_len: Goldilocks,
) {
    let m = lo.len();
    debug_assert_eq!(m, hi.len());
    if m >= 4 {
        let w2 = w_len.const_mul(w_len);
        let fourth_power = w2.const_mul(w2);
        let mut wk0 = w_init;
        let mut wk1 = wk0.const_mul(w_len);
        let mut wk2 = wk0.const_mul(w2);
        let mut wk3 = wk1.const_mul(w2);
        let mut j = 0usize;
        while j + 4 <= m {
            let u0 = lo[j];
            let v0 = hi[j].const_mul(wk0);
            let u1 = lo[j + 1];
            let v1 = hi[j + 1].const_mul(wk1);
            let u2 = lo[j + 2];
            let v2 = hi[j + 2].const_mul(wk2);
            let u3 = lo[j + 3];
            let v3 = hi[j + 3].const_mul(wk3);
            lo[j] = u0 + v0;
            hi[j] = u0 - v0;
            lo[j + 1] = u1 + v1;
            hi[j + 1] = u1 - v1;
            lo[j + 2] = u2 + v2;
            hi[j + 2] = u2 - v2;
            lo[j + 3] = u3 + v3;
            hi[j + 3] = u3 - v3;
            wk0 = wk0.const_mul(fourth_power);
            wk1 = wk1.const_mul(fourth_power);
            wk2 = wk2.const_mul(fourth_power);
            wk3 = wk3.const_mul(fourth_power);
            j += 4;
        }
        while j < m {
            let u = lo[j];
            let v = hi[j].const_mul(wk0);
            lo[j] = u + v;
            hi[j] = u - v;
            wk0 = wk0.const_mul(w_len);
            j += 1;
        }
    } else {
        let mut w = w_init;
        for j in 0..m {
            let u = lo[j];
            let v = hi[j].const_mul(w);
            lo[j] = u + v;
            hi[j] = u - v;
            w = w.const_mul(w_len);
        }
    }
}

/// Stages whose blocks fit in `2^NTT_CACHE_BLOCK_LOG` elements (128 KiB of base-field words)
/// are completed block by block, so the low stages never leave the L2 cache.
const NTT_CACHE_BLOCK_LOG: usize = 14;

/// One pass applying Cooley–Tukey stages `stage` and `stage + 1` together. It performs exactly
/// the butterflies of the two radix-2 stages, so the result is identical word for word.
#[inline]
fn radix4_stage_pair_goldilocks(a: &mut [Goldilocks], stage: usize, inverse: bool) {
    let root = |s: usize| {
        let g = Goldilocks::two_adic_generator(s);
        if inverse { g.inv() } else { g }
    };
    let w_hi = root(stage + 1);
    let quarter_turn = root(2);
    let quarter = 1usize << (stage - 1);
    for block in a.chunks_exact_mut(4 * quarter) {
        let (lo, hi) = block.split_at_mut(2 * quarter);
        let (a0, a1) = lo.split_at_mut(quarter);
        let (a2, a3) = hi.split_at_mut(quarter);
        let mut t = Goldilocks::ONE;
        for j in 0..quarter {
            let u = t.square();
            let b1 = a1[j].const_mul(u);
            let b3 = a3[j].const_mul(u);
            let (x0, x1) = (a0[j] + b1, a0[j] - b1);
            let (x2, x3) = (a2[j] + b3, a2[j] - b3);
            let c2 = x2.const_mul(t);
            let c3 = x3.const_mul(t.const_mul(quarter_turn));
            a0[j] = x0 + c2;
            a2[j] = x0 - c2;
            a1[j] = x1 + c3;
            a3[j] = x1 - c3;
            t = t.const_mul(w_hi);
        }
    }
}

/// Cooley–Tukey stages `1..=stages` on bit-reversed input: cache-resident blocks first, then the
/// remaining stages two per pass.
fn ntt_goldilocks_stages_blocked(a: &mut [Goldilocks], stages: usize, inverse: bool) {
    let radix2 = |a: &mut [Goldilocks], stage: usize| {
        let g = Goldilocks::two_adic_generator(stage);
        let w_len = if inverse { g.inv() } else { g };
        let half = 1usize << (stage - 1);
        for block in a.chunks_exact_mut(2 * half) {
            let (lo, hi) = block.split_at_mut(half);
            butterfly_block_goldilocks(lo, hi, Goldilocks::ONE, w_len);
        }
    };
    let low = stages.min(NTT_CACHE_BLOCK_LOG);
    for block in a.chunks_exact_mut(1usize << low) {
        for stage in 1..=low {
            radix2(block, stage);
        }
    }
    let mut stage = low + 1;
    while stage < stages {
        radix4_stage_pair_goldilocks(a, stage, inverse);
        stage += 2;
    }
    if stage == stages {
        radix2(a, stage);
    }
}

fn ntt_goldilocks_serial(a: &mut [Goldilocks]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    bit_reverse_permute(a);
    ntt_goldilocks_stages_blocked(a, n.trailing_zeros() as usize, false);
}

/// In-place Radix-2 Cooley–Tukey NTT over `Goldilocks` in natural evaluation order
/// ($f(\omega^0), f(\omega^1), \dots, f(\omega^{N-1})$).
pub fn ntt_goldilocks(a: &mut [Goldilocks]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    if n <= 1 {
        return;
    }

    ntt_goldilocks_cpu(a);
}

pub(crate) fn ntt_goldilocks_cpu(a: &mut [Goldilocks]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    if n <= 1 {
        return;
    }
    #[cfg(feature = "std")]
    if n >= 16_384 {
        let threads = crate::parallel_pow2_workers(n / 2);
        if threads > 1 {
            bit_reverse_permute(a);
            ntt_goldilocks_parallel_stages(a, threads, false);
            return;
        }
    }

    ntt_goldilocks_serial(a);
}

#[cfg(feature = "std")]
fn ntt_goldilocks_parallel_stages(a: &mut [Goldilocks], threads: usize, inverse: bool) {
    debug_assert!(threads.is_power_of_two() && a.len() >= threads * 2);
    let n = a.len();
    let chunk_n = n / threads;
    let chunk_stages = chunk_n.trailing_zeros() as usize;
    std::thread::scope(|scope| {
        for sub in a.chunks_mut(chunk_n) {
            crate::spawn_bounded(scope, move || {
                ntt_goldilocks_stages_blocked(sub, chunk_stages, inverse);
            });
        }
    });

    let log_n = n.trailing_zeros() as usize;
    for stage in (chunk_stages + 1)..=log_n {
        let len = 1usize << stage;
        let half = len / 2;
        let g = Goldilocks::two_adic_generator(stage);
        let w_len = if inverse { g.inv() } else { g };
        for block in a.chunks_mut(len) {
            let (lo, hi) = block.split_at_mut(half);
            let sub_j = (half / threads).max(1);
            std::thread::scope(|scope| {
                for (t_idx, (lo_c, hi_c)) in
                    lo.chunks_mut(sub_j).zip(hi.chunks_mut(sub_j)).enumerate()
                {
                    let w_init = w_len.pow((t_idx * sub_j) as u64);
                    crate::spawn_bounded(scope, move || {
                        butterfly_block_goldilocks(lo_c, hi_c, w_init, w_len);
                    });
                }
            });
        }
    }
}

/// In-place Radix-2 Inverse NTT over `Goldilocks`.
pub fn intt_goldilocks(a: &mut [Goldilocks]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    if n <= 1 {
        return;
    }
    bit_reverse_permute(a);
    #[cfg(feature = "std")]
    if n >= 16_384 {
        let threads = crate::parallel_pow2_workers(n / 2);
        if threads > 1 {
            ntt_goldilocks_parallel_stages(a, threads, true);
            let n_inv = Goldilocks::from_u64_reduced(n as u64).inv();
            let chunk = (n / threads).max(1);
            std::thread::scope(|scope| {
                for sub in a.chunks_mut(chunk) {
                    crate::spawn_bounded(scope, move || {
                        for x in sub.iter_mut() {
                            *x = x.const_mul(n_inv);
                        }
                    });
                }
            });
            return;
        }
    }
    let mut len = 2;
    let mut stage = 1;
    while len <= n {
        let w_len = Goldilocks::two_adic_generator(stage).inv();
        let half = len / 2;
        for block in a.chunks_exact_mut(len) {
            let (lo, hi) = block.split_at_mut(half);
            butterfly_block_goldilocks(lo, hi, Goldilocks::ONE, w_len);
        }
        len <<= 1;
        stage += 1;
    }
    let n_inv = Goldilocks::from_u64_reduced(n as u64).inv();
    for x in a.iter_mut() {
        *x = x.const_mul(n_inv);
    }
}

/// Coset Reed–Solomon encoding of polynomial coefficients `coeffs` (length $N = 2^k$) onto
/// shifted multiplicative subgroup $g \cdot H$ of size $|H| = N \cdot \text{blowup}$ (`g = 7`).
pub fn encode_rs_coset_goldilocks(coeffs: &[Goldilocks], blowup: usize) -> Vec<Goldilocks> {
    encode_rs_coset_goldilocks_with_secret(coeffs, blowup, false)
}

/// [`encode_rs_coset_goldilocks`] with optional zeroization of intermediate coset buffers for
/// hiding commitments (`secret == true`); `secret == false` incurs zero overhead.
pub(crate) fn encode_rs_coset_goldilocks_with_secret(
    coeffs: &[Goldilocks],
    blowup: usize,
    secret: bool,
) -> Vec<Goldilocks> {
    let _phase = crate::profile::span("encode_rs_coset_goldilocks");
    let n_c = coeffs.len();
    assert!(n_c.is_power_of_two());
    assert!(blowup.is_power_of_two() && blowup >= 2);
    let domain_len = n_c.checked_mul(blowup).expect("RS domain size overflow");
    assert!(
        domain_len.trailing_zeros() <= 32,
        "RS domain exceeds Goldilocks two-adicity"
    );

    encode_rs_coset_goldilocks_cpu_inner(coeffs, blowup, secret)
}

/// [`encode_rs_coset_goldilocks`] on the host only.
#[cfg(test)]
pub(crate) fn encode_rs_coset_goldilocks_cpu(
    coeffs: &[Goldilocks],
    blowup: usize,
) -> Vec<Goldilocks> {
    encode_rs_coset_goldilocks_cpu_inner(coeffs, blowup, false)
}

fn encode_rs_coset_goldilocks_cpu_inner(
    coeffs: &[Goldilocks],
    blowup: usize,
    #[cfg_attr(not(feature = "std"), allow(unused_variables))] secret: bool,
) -> Vec<Goldilocks> {
    let n_c = coeffs.len();
    let domain_len = n_c * blowup;

    // Coset decomposition: `B = blowup` independent size-`N` shifted NTTs (`out[q * B + r] = NTT_N(c_i * (g * w_D^r)^i)[q]`),
    // keeping each sub-NTT L2/L3-cache resident with zero cross-coset synchronization.
    #[cfg(feature = "std")]
    if domain_len >= 32_768 && n_c >= 64 && blowup >= 4 {
        let workers = crate::parallel_pow2_workers(domain_len / 64);
        let log_d = domain_len.trailing_zeros() as usize;
        let log_c = n_c.trailing_zeros() as usize;
        let rev_shift_c = usize::BITS as usize - log_c;
        let omega_d = Goldilocks::two_adic_generator(log_d);

        let mut cosets = vec![Goldilocks::ZERO; domain_len];
        if blowup >= workers {
            let outer_threads = workers.min(blowup);
            let r_per_thread = blowup / outer_threads;
            std::thread::scope(|scope| {
                for (t_idx, coset_chunk) in cosets.chunks_mut(r_per_thread * n_c).enumerate() {
                    let base_r = t_idx * r_per_thread;
                    crate::spawn_bounded(scope, move || {
                        for (off_r, row) in coset_chunk.chunks_exact_mut(n_c).enumerate() {
                            let r = base_r + off_r;
                            let s_r = Goldilocks::NON_RESIDUE * omega_d.pow(r as u64);
                            let mut sp = Goldilocks::ONE;
                            for (i, &c) in coeffs.iter().enumerate() {
                                let dst = i.reverse_bits() >> rev_shift_c;
                                row[dst] = c.const_mul(sp);
                                sp = sp.const_mul(s_r);
                            }
                            ntt_goldilocks_stages_blocked(row, log_c, false);
                        }
                    });
                }
            });
        } else {
            let inner_threads = (workers / blowup).max(1).min(n_c / 2).max(1);
            std::thread::scope(|scope| {
                for (r, row) in cosets.chunks_exact_mut(n_c).enumerate() {
                    let s_r = Goldilocks::NON_RESIDUE * omega_d.pow(r as u64);
                    crate::spawn_bounded(scope, move || {
                        // Precompute a 24 KiB L1-resident 3x1024 Kronecker power table for `s_r^k`
                        // (`k < 2^30`), writing `row[j] = coeffs[rev(j)] * s_r^{rev(j)}` directly
                        // in ONE contiguous pass with ZERO auxiliary `shifted` heap allocation!
                        let mut t0 = [Goldilocks::ONE; 1024];
                        let mut t1 = [Goldilocks::ONE; 1024];
                        let mut t2 = [Goldilocks::ONE; 1024];
                        for i in 1..1024 {
                            t0[i] = t0[i - 1].const_mul(s_r);
                        }
                        let s_10 = t0[1023].const_mul(s_r);
                        for i in 1..1024 {
                            t1[i] = t1[i - 1].const_mul(s_10);
                        }
                        let s_20 = t1[1023].const_mul(s_10);
                        for i in 1..1024 {
                            t2[i] = t2[i - 1].const_mul(s_20);
                        }
                        let sub_c = n_c / inner_threads;
                        let t0_ref = &t0;
                        let t1_ref = &t1;
                        let t2_ref = &t2;
                        std::thread::scope(|inner| {
                            for (ti, dst_s) in row.chunks_mut(sub_c).enumerate() {
                                let base_j = ti * sub_c;
                                crate::spawn_bounded(inner, move || {
                                    for (off, slot) in dst_s.iter_mut().enumerate() {
                                        let rev = (base_j + off).reverse_bits() >> rev_shift_c;
                                        let sp = t0_ref[rev & 0x3FF]
                                            .const_mul(t1_ref[(rev >> 10) & 0x3FF])
                                            .const_mul(t2_ref[(rev >> 20) & 0x3FF]);
                                        *slot = coeffs[rev].const_mul(sp);
                                    }
                                });
                            }
                        });
                        if inner_threads > 1 && n_c >= inner_threads * 2 {
                            ntt_goldilocks_parallel_stages(row, inner_threads, false);
                        } else {
                            ntt_goldilocks_stages_blocked(row, log_c, false);
                        }
                    });
                }
            });
        }

        let mut out = vec![Goldilocks::ZERO; domain_len];
        let t_threads = crate::parallel_pow2_workers(n_c);
        let q_chunk = (n_c / t_threads).max(1);
        let cosets_ref = &cosets;
        std::thread::scope(|scope| {
            for (ti, out_sub) in out.chunks_mut(q_chunk * blowup).enumerate() {
                let base_q = ti * q_chunk;
                crate::spawn_bounded(scope, move || {
                    const TILE_Q: usize = 64;
                    let mut off_q = 0usize;
                    while off_q + TILE_Q <= q_chunk {
                        let q0 = base_q + off_q;
                        let dst_tile = &mut out_sub[off_q * blowup..(off_q + TILE_Q) * blowup];
                        for r in 0..blowup {
                            let src = &cosets_ref[r * n_c + q0..r * n_c + q0 + TILE_Q];
                            for (dq, &val) in src.iter().enumerate() {
                                dst_tile[dq * blowup + r] = val;
                            }
                        }
                        off_q += TILE_Q;
                    }
                    for dq in off_q..q_chunk {
                        let q = base_q + dq;
                        let dst_row = &mut out_sub[dq * blowup..(dq + 1) * blowup];
                        for (r, slot) in dst_row.iter_mut().enumerate() {
                            *slot = cosets_ref[r * n_c + q];
                        }
                    }
                });
            }
        });
        if secret {
            qsag_asm::volatile_fill(&mut cosets, Goldilocks::ZERO);
        }
        return out;
    }

    let mut buf = vec![Goldilocks::ZERO; domain_len];
    let shift = Goldilocks::NON_RESIDUE;
    let mut shift_pow = Goldilocks::ONE;
    for (i, &c) in coeffs.iter().enumerate() {
        buf[i] = c.const_mul(shift_pow);
        shift_pow = shift_pow.const_mul(shift);
    }
    ntt_goldilocks_cpu(&mut buf);
    buf
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "RS domain size overflow")]
    fn encode_rs_coset_goldilocks_rejects_domain_overflow() {
        let _ = encode_rs_coset_goldilocks(&[Goldilocks::ONE; 4], 1usize << 62);
    }

    #[test]
    #[should_panic(expected = "RS domain exceeds Goldilocks two-adicity")]
    fn encode_rs_coset_goldilocks_rejects_excessive_two_adicity() {
        let _ = encode_rs_coset_goldilocks(&[Goldilocks::ONE; 4], 1usize << 31);
    }

    #[test]
    fn goldilocks_addition_chain_inv_and_batch_inv_match_pow() {
        let edge_cases = [
            0u64,
            1,
            2,
            3,
            7,
            (1u64 << 32) - 1,
            1u64 << 32,
            (1u64 << 32) + 1,
            GOLDILOCKS_PRIME - 3,
            GOLDILOCKS_PRIME - 2,
            GOLDILOCKS_PRIME - 1,
            TWO_ADIC_ROOT_OF_UNITY_32,
        ];
        for &raw in &edge_cases {
            let x = Goldilocks::from_canonical_u64(raw).unwrap();
            let got = x.inv();
            let want = x.pow(GOLDILOCKS_PRIME - 2);
            assert_eq!(got, want, "inv mismatch on edge limb {raw:#x}");
            if !x.is_zero() {
                assert_eq!(x * got, Goldilocks::ONE);
            } else {
                assert_eq!(got, Goldilocks::ZERO);
            }
        }
        assert!(Goldilocks::from_canonical_u64(GOLDILOCKS_PRIME).is_none());

        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut random_vec = Vec::with_capacity(600);
        for idx in 0..600usize {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let x = if idx.is_multiple_of(29) {
                Goldilocks::ZERO
            } else {
                Goldilocks::from_u64_reduced(state)
            };
            assert_eq!(x.inv(), x.pow(GOLDILOCKS_PRIME - 2));
            random_vec.push(x);
        }

        let mut empty: [Goldilocks; 0] = [];
        Goldilocks::batch_inv(&mut empty);

        for mut single in [[Goldilocks::ZERO], [Goldilocks::NON_RESIDUE]] {
            let expected = single[0].inv();
            Goldilocks::batch_inv(&mut single);
            assert_eq!(single[0], expected);
        }

        let mut all_zeros = [Goldilocks::ZERO; 17];
        Goldilocks::batch_inv(&mut all_zeros);
        assert_eq!(all_zeros, [Goldilocks::ZERO; 17]);

        for len in [2usize, 7, 64, 258, 512, 600] {
            let expected: Vec<Goldilocks> = random_vec[..len].iter().map(|x| x.inv()).collect();
            let mut actual = random_vec[..len].to_vec();
            Goldilocks::batch_inv(&mut actual);
            assert_eq!(actual, expected, "batch_inv mismatch at len={len}");
        }
    }
}

#[cfg(test)]
mod base_ntt_tests {
    use super::*;

    fn radix2_reference(a: &mut [Goldilocks], inverse: bool) {
        bit_reverse_permute(a);
        for stage in 1..=a.len().trailing_zeros() as usize {
            let g = Goldilocks::two_adic_generator(stage);
            let w_len = if inverse { g.inv() } else { g };
            let half = 1usize << (stage - 1);
            for block in a.chunks_exact_mut(2 * half) {
                let mut w = Goldilocks::ONE;
                for j in 0..half {
                    let u = block[j];
                    let v = block[j + half].const_mul(w);
                    block[j] = u + v;
                    block[j + half] = u - v;
                    w = w.const_mul(w_len);
                }
            }
        }
    }

    fn sample(n: usize, seed: u64) -> Vec<Goldilocks> {
        let mut x = seed;
        (0..n)
            .map(|_| {
                x = x
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                Goldilocks::from_u64_reduced(x ^ (x >> 29))
            })
            .collect()
    }

    #[test]
    fn blocked_stages_match_radix2_reference_forward_and_inverse() {
        for log_n in [1usize, 2, 5, 13, 14, 15, 16, 17, 18] {
            for inverse in [false, true] {
                let input = sample(1 << log_n, 0x51ed_270b ^ log_n as u64);
                let mut expected = input.clone();
                radix2_reference(&mut expected, inverse);
                let mut got = input;
                bit_reverse_permute(&mut got);
                ntt_goldilocks_stages_blocked(&mut got, log_n, inverse);
                assert_eq!(got, expected, "log_n {log_n}, inverse {inverse}");
            }
        }
    }

    #[test]
    fn public_ntt_roundtrips_and_matches_reference() {
        for log_n in [10usize, 15, 17] {
            let input = sample(1 << log_n, 7 + log_n as u64);
            let mut expected = input.clone();
            radix2_reference(&mut expected, false);
            let mut got = input.clone();
            ntt_goldilocks(&mut got);
            assert_eq!(got, expected);
            intt_goldilocks(&mut got);
            assert_eq!(got, input);
        }
    }

    #[test]
    fn cpu_coset_encoding_matches_public_encoder() {
        for (log_c, blowup) in [(3, 2), (13, 4), (15, 8), (10, 32)] {
            let coeffs = sample(1 << log_c, 481 + log_c as u64);
            assert_eq!(
                encode_rs_coset_goldilocks_cpu(&coeffs, blowup),
                encode_rs_coset_goldilocks(&coeffs, blowup)
            );
        }
    }

    #[test]
    fn coset_encoding_matches_horner_at_sampled_points() {
        for (log_c, blowup) in [(14usize, 4usize), (15, 4), (13, 32), (16, 8)] {
            let coeffs = sample(1 << log_c, 99 + log_c as u64);
            let code = encode_rs_coset_goldilocks(&coeffs, blowup);
            let domain = coeffs.len() * blowup;
            assert_eq!(code.len(), domain);
            let omega = Goldilocks::two_adic_generator(domain.trailing_zeros() as usize);
            for idx in [0usize, 1, 2, blowup, domain / 3, domain / 2 + 5, domain - 1] {
                let x = Goldilocks::NON_RESIDUE.const_mul(omega.pow(idx as u64));
                let mut acc = Goldilocks::ZERO;
                for &c in coeffs.iter().rev() {
                    acc = acc.const_mul(x) + c;
                }
                assert_eq!(
                    code[idx], acc,
                    "log_c {log_c}, blowup {blowup}, index {idx}"
                );
            }
        }
    }
}
