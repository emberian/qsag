//! Hem field layer. The base field `Goldilocks` ($\mathbb{F}_p, p = 2^{64} - 2^{32} + 1$) and the
//! quadratic extension `GoldilocksExt2` ($\mathbb{F}_p[u]/(u^2 - 7)$) are the `qsag-core` types,
//! re-exported here. This module adds what only the aggregation prover needs on top of them:
//! shift/fold helpers, batch inversion, 2-adic roots of unity, the quartic extension
//! `GoldilocksExt4` ($\mathbb{F}_{p^2}[v]/(v^2 - u) \cong \mathbb{F}_p[v]/(v^4 - 7)$), Radix-2
//! NTT/INTT, univariate round-polynomial interpolation, and multilinear folding/evaluation.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use qsag_core::field::goldilocks::{GOLDILOCKS_EPSILON as EPSILON, GOLDILOCKS_ROOT_2_32};
pub use qsag_core::field::goldilocks::{GOLDILOCKS_PRIME, Goldilocks, GoldilocksExt2};

// The Aeneas-extracted WHIR verifier core and `qsag-core` must agree on the modulus.
const _: () = assert!(GOLDILOCKS_PRIME == qsag_whir_verified::GOLDILOCKS_P);

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

/// Reduce `lo + 2^64 * hi` (`lo, hi < 2^70`) to a canonical element, using
/// $2^{64} \equiv 2^{32} - 1 \pmod p$ three times.
#[inline(always)]
const fn reduce_lo_hi(lo: u128, hi: u128) -> Goldilocks {
    debug_assert!(lo >> 70 == 0 && hi >> 70 == 0);
    // `x < 2^70 + 2^102`.
    let x = lo + hi * EPSILON as u128;
    // `y < 2^64 + 2^38 * 2^32`.
    let y = (x as u64) as u128 + (x >> 64) * EPSILON as u128;
    Goldilocks::reduce96(y as u64, (y >> 64) as u64)
}

/// Sum of base-field products as separate low-word and high-word accumulators, so several
/// 128-bit products are added exactly and reduced once.
#[derive(Clone, Copy)]
struct WideAcc {
    lo: u128,
    hi: u128,
}

impl WideAcc {
    const ZERO: Self = Self { lo: 0, hi: 0 };

    /// Add `weight * a * b` for a small weight; at most `2^6` weighted products fit.
    #[inline(always)]
    const fn add_mul(self, a: Goldilocks, b: Goldilocks, weight: u128) -> Self {
        let prod = (a.to_canonical_u64() as u128) * (b.to_canonical_u64() as u128);
        Self {
            lo: self.lo + weight * ((prod as u64) as u128),
            hi: self.hi + weight * (prod >> 64),
        }
    }

    /// Add a single field element.
    #[inline(always)]
    const fn add_elem(self, x: Goldilocks) -> Self {
        Self {
            lo: self.lo + x.to_canonical_u64() as u128,
            hi: self.hi,
        }
    }

    #[inline(always)]
    const fn reduce(self) -> Goldilocks {
        reduce_lo_hi(self.lo, self.hi)
    }
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

    #[cfg(feature = "vulkan")]
    if crate::acceleration::ntt(a, false) {
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
    #[cfg(feature = "vulkan")]
    if crate::acceleration::ntt(a, true) {
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
    let _phase = crate::profile::span("encode_rs_coset_goldilocks");
    let n_c = coeffs.len();
    assert!(n_c.is_power_of_two());
    assert!(blowup.is_power_of_two() && blowup >= 2);
    let domain_len = n_c.checked_mul(blowup).expect("RS domain size overflow");
    assert!(
        domain_len.trailing_zeros() <= 32,
        "RS domain exceeds Goldilocks two-adicity"
    );

    #[cfg(feature = "vulkan")]
    if let Some(values) = crate::acceleration::encode(coeffs, domain_len) {
        return values;
    }
    encode_rs_coset_goldilocks_cpu(coeffs, blowup)
}

/// [`encode_rs_coset_goldilocks`] on the host only.
pub(crate) fn encode_rs_coset_goldilocks_cpu(coeffs: &[Goldilocks], blowup: usize) -> Vec<Goldilocks> {
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
                        let sub_c = n_c / inner_threads;
                        let mut shifted = vec![Goldilocks::ZERO; n_c];
                        std::thread::scope(|inner| {
                            for (ti, dst_s) in shifted.chunks_mut(sub_c).enumerate() {
                                let src_s = &coeffs[ti * sub_c..(ti + 1) * sub_c];
                                let mut sp = s_r.pow((ti * sub_c) as u64);
                                crate::spawn_bounded(inner, move || {
                                    for (d, &c) in dst_s.iter_mut().zip(src_s.iter()) {
                                        *d = c.const_mul(sp);
                                        sp = sp.const_mul(s_r);
                                    }
                                });
                            }
                        });
                        let shifted_ref = &shifted;
                        std::thread::scope(|inner| {
                            for (ti, dst_s) in row.chunks_mut(sub_c).enumerate() {
                                let base_i = ti * sub_c;
                                crate::spawn_bounded(inner, move || {
                                    for (off, slot) in dst_s.iter_mut().enumerate() {
                                        let rev = (base_i + off).reverse_bits() >> rev_shift_c;
                                        *slot = shifted_ref[rev];
                                    }
                                });
                            }
                        });
                        drop(shifted);
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
                    for (off_q, dst_row) in out_sub.chunks_exact_mut(blowup).enumerate() {
                        let q = base_q + off_q;
                        for (r, slot) in dst_row.iter_mut().enumerate() {
                            *slot = cosets_ref[r * n_c + q];
                        }
                    }
                });
            }
        });
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

// ============================================================================
// Quartic Extension `GoldilocksExt4` (`F_{p^4} = F_{p^2}[v]/(v^2 - u) ~= F_p[v]/(v^4 - 7)`)
// ============================================================================

/// Primitive 4-th root of unity $\zeta_4 = 7^{(p-1)/4} \in \mathbb{F}_p$ ($\zeta_4^2 \equiv -1 \pmod p$),
/// governing the Frobenius action $v^p = v \cdot (v^4)^{(p-1)/4} = \zeta_4 v$ on $\mathbb{F}_{p^4}$.
pub const FROBENIUS_ZETA4: Goldilocks = Goldilocks::NON_RESIDUE.pow((GOLDILOCKS_PRIME - 1) / 4);

/// Quartic extension $\mathbb{F}_{p^4} = \mathbb{F}_{p^2}[v] / (v^2 - u) \cong \mathbb{F}_p[v] / (v^4 - 7)$,
/// $|\mathbb{F}_{p^4}| > 2^{255.99}$.
///
/// Irreducibility proof: $p = 2^{64} - 2^{32} + 1 \equiv 1 \pmod 4$ and $p \equiv 6 \pmod 7$, so by
/// quadratic reciprocity $7^{(p-1)/2} \equiv -1 \pmod p$. Consequently $u^p = -u$ in $\mathbb{F}_{p^2}$,
/// $u^{p+1} = -u^2 = -7$, and since $(p - 1)/2 = 2^{31}(2^{32} - 1)$ is even,
/// $u^{(p^2 - 1)/2} = (-7)^{(p-1)/2} = (+1)\cdot(-1) = -1 \ne 1$. Thus $u$ is a quadratic non-residue
/// in $\mathbb{F}_{p^2}$ and $v^2 - u$ is irreducible over $\mathbb{F}_{p^2}$.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct GoldilocksExt4 {
    pub c0: GoldilocksExt2,
    pub c1: GoldilocksExt2,
}

impl GoldilocksExt4 {
    pub const ZERO: Self = Self {
        c0: GoldilocksExt2::ZERO,
        c1: GoldilocksExt2::ZERO,
    };
    pub const ONE: Self = Self {
        c0: GoldilocksExt2::ONE,
        c1: GoldilocksExt2::ZERO,
    };
    pub const V: Self = Self {
        c0: GoldilocksExt2::ZERO,
        c1: GoldilocksExt2::ONE,
    };

    #[inline(always)]
    pub const fn new(c0: GoldilocksExt2, c1: GoldilocksExt2) -> Self {
        Self { c0, c1 }
    }

    #[inline(always)]
    pub const fn from_limbs(limbs: [Goldilocks; 4]) -> Self {
        Self {
            c0: GoldilocksExt2::new(limbs[0], limbs[1]),
            c1: GoldilocksExt2::new(limbs[2], limbs[3]),
        }
    }

    #[inline(always)]
    pub const fn to_limbs(self) -> [Goldilocks; 4] {
        [self.c0.c0, self.c0.c1, self.c1.c0, self.c1.c1]
    }

    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        ext2_is_zero(self.c0) && ext2_is_zero(self.c1)
    }

    #[inline(always)]
    pub const fn from_ext2(c0: GoldilocksExt2) -> Self {
        Self {
            c0,
            c1: GoldilocksExt2::ZERO,
        }
    }

    #[inline(always)]
    pub const fn from_base(c0: Goldilocks) -> Self {
        Self {
            c0: GoldilocksExt2::from_base(c0),
            c1: GoldilocksExt2::ZERO,
        }
    }

    #[inline(always)]
    pub const fn from_u64(v: u64) -> Self {
        Self::from_base(Goldilocks::from_u64_reduced(v))
    }

    #[inline]
    pub const fn to_le_bytes(self) -> [u8; 32] {
        let limbs = [self.c0.c0, self.c0.c1, self.c1.c0, self.c1.c1];
        let mut out = [0u8; 32];
        let mut i = 0;
        while i < 4 {
            let w = limbs[i].to_le_bytes();
            let mut k = 0;
            while k < 8 {
                out[8 * i + k] = w[k];
                k += 1;
            }
            i += 1;
        }
        out
    }

    #[inline]
    pub fn from_le_bytes_canonical(bytes: [u8; 32]) -> Option<Self> {
        let mut b0 = [0u8; 8];
        let mut b1 = [0u8; 8];
        let mut b2 = [0u8; 8];
        let mut b3 = [0u8; 8];
        b0.copy_from_slice(&bytes[0..8]);
        b1.copy_from_slice(&bytes[8..16]);
        b2.copy_from_slice(&bytes[16..24]);
        b3.copy_from_slice(&bytes[24..32]);
        let ext = qsag_whir_verified::decode_canonical_ext4(
            u64::from_le_bytes(b0),
            u64::from_le_bytes(b2),
            u64::from_le_bytes(b1),
            u64::from_le_bytes(b3),
        )?;
        Some(Self::from_limbs([
            Goldilocks::from_u64_reduced(ext.a),
            Goldilocks::from_u64_reduced(ext.c),
            Goldilocks::from_u64_reduced(ext.b),
            Goldilocks::from_u64_reduced(ext.d),
        ]))
    }

    #[inline(always)]
    pub const fn mul_base(self, s: Goldilocks) -> Self {
        let z = WideAcc::ZERO;
        Self {
            c0: GoldilocksExt2::new(
                z.add_mul(self.c0.c0, s, 1).reduce(),
                z.add_mul(self.c0.c1, s, 1).reduce(),
            ),
            c1: GoldilocksExt2::new(
                z.add_mul(self.c1.c0, s, 1).reduce(),
                z.add_mul(self.c1.c1, s, 1).reduce(),
            ),
        }
    }

    #[inline(always)]
    pub const fn mul_ext2(self, s: GoldilocksExt2) -> Self {
        Self {
            c0: self.c0.const_mul(s),
            c1: self.c1.const_mul(s),
        }
    }

    #[inline(always)]
    pub const fn const_add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0.const_add(rhs.c0),
            c1: self.c1.const_add(rhs.c1),
        }
    }

    #[inline(always)]
    pub const fn const_sub(self, rhs: Self) -> Self {
        Self {
            c0: self.c0.const_sub(rhs.c0),
            c1: self.c1.const_sub(rhs.c1),
        }
    }

    #[inline(always)]
    pub const fn const_neg(self) -> Self {
        Self::ZERO.const_sub(self)
    }

    #[inline(always)]
    pub const fn shl_small<const S: u32>(self) -> Self {
        Self {
            c0: ext2_shl_small::<S>(self.c0),
            c1: ext2_shl_small::<S>(self.c1),
        }
    }

    /// Product in $\mathbb{F}_p[v]/(v^4 - 7)$. With polynomial-basis coefficients
    /// `p = [c0.c0, c1.c0, c0.c1, c1.c1]` (powers `v^0..v^3`, since `u = v^2`), coefficient `k`
    /// is `sum_{i+j=k} a_i b_j + 7 sum_{i+j=k+4} a_i b_j`. The sixteen 128-bit products are
    /// accumulated exactly and each coefficient is reduced once.
    #[inline(always)]
    pub const fn const_mul(self, rhs: Self) -> Self {
        self.mul_add(rhs, Self::ZERO)
    }

    /// `self * rhs + addend` with one reduction per coefficient.
    #[inline(always)]
    pub const fn mul_add(self, rhs: Self, addend: Self) -> Self {
        let a = [self.c0.c0, self.c1.c0, self.c0.c1, self.c1.c1];
        let b = [rhs.c0.c0, rhs.c1.c0, rhs.c0.c1, rhs.c1.c1];
        let c = [addend.c0.c0, addend.c1.c0, addend.c0.c1, addend.c1.c1];
        let mut out = [Goldilocks::ZERO; 4];
        let mut k = 0;
        while k < 4 {
            let mut acc = WideAcc::ZERO.add_elem(c[k]);
            let mut i = 0;
            while i < 4 {
                // `j = k - i` when that is in range, otherwise `j = k + 4 - i` with weight 7.
                acc = if i <= k {
                    acc.add_mul(a[i], b[k - i], 1)
                } else {
                    acc.add_mul(a[i], b[k + 4 - i], 7)
                };
                i += 1;
            }
            out[k] = acc.reduce();
            k += 1;
        }
        Self {
            c0: GoldilocksExt2::new(out[0], out[2]),
            c1: GoldilocksExt2::new(out[1], out[3]),
        }
    }

    /// Limb-wise sum and negation through the `qsag-core` base field; test references.
    #[cfg(test)]
    pub(crate) const fn tower_add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0.const_add(rhs.c0),
            c1: self.c1.const_add(rhs.c1),
        }
    }

    #[cfg(test)]
    pub(crate) const fn tower_neg(self) -> Self {
        Self {
            c0: self.c0.const_neg(),
            c1: self.c1.const_neg(),
        }
    }

    /// Karatsuba product over $\mathbb{F}_{p^2}[v]/(v^2 - u)$; the tower-form definition that
    /// [`Self::const_mul`] is tested against.
    #[cfg(test)]
    pub(crate) const fn const_mul_tower(self, rhs: Self) -> Self {
        let v0 = self.c0.const_mul(rhs.c0);
        let v1 = self.c1.const_mul(rhs.c1);
        let mid = self
            .c0
            .const_add(self.c1)
            .const_mul(rhs.c0.const_add(rhs.c1))
            .const_sub(v0)
            .const_sub(v1);
        Self {
            c0: v0.const_add(ext2_mul_by_u(v1)),
            c1: mid,
        }
    }

    /// Square in $\mathbb{F}_p[v]/(v^4 - 7)$: the ten distinct products of the polynomial-basis
    /// coefficients, cross terms doubled, one reduction per coefficient.
    #[inline(always)]
    pub const fn square(self) -> Self {
        let [a0, a1, a2, a3] = [self.c0.c0, self.c1.c0, self.c0.c1, self.c1.c1];
        let z = WideAcc::ZERO;
        let p0 = z.add_mul(a0, a0, 1).add_mul(a1, a3, 14).add_mul(a2, a2, 7);
        let p1 = z.add_mul(a0, a1, 2).add_mul(a2, a3, 14);
        let p2 = z.add_mul(a0, a2, 2).add_mul(a1, a1, 1).add_mul(a3, a3, 7);
        let p3 = z.add_mul(a0, a3, 2).add_mul(a1, a2, 2);
        Self {
            c0: GoldilocksExt2::new(p0.reduce(), p2.reduce()),
            c1: GoldilocksExt2::new(p1.reduce(), p3.reduce()),
        }
    }

    /// Relative norm $\mathrm{N}_{\mathbb{F}_{p^4}/\mathbb{F}_{p^2}}(c_0 + c_1 v) = c_0^2 - u c_1^2 \in \mathbb{F}_{p^2}$.
    #[inline(always)]
    pub const fn norm_to_ext2(self) -> GoldilocksExt2 {
        self.c0.square().const_sub(ext2_mul_by_u(self.c1.square()))
    }

    /// Absolute norm $\mathrm{N}_{\mathbb{F}_{p^4}/\mathbb{F}_p}(x) \in \mathbb{F}_p$.
    #[inline(always)]
    pub const fn norm_to_base(self) -> Goldilocks {
        self.norm_to_ext2().norm()
    }

    /// Branchless constant-time multiplicative inverse $(c_0 - c_1 v) / (c_0^2 - u c_1^2)$ (`0 -> 0`).
    #[inline]
    pub const fn inv(self) -> Self {
        let norm_inv = ext2_inv_or_zero(self.norm_to_ext2());
        Self {
            c0: self.c0.const_mul(norm_inv),
            c1: self.c1.const_neg().const_mul(norm_inv),
        }
    }

    #[inline]
    pub const fn pow(self, mut exp: u64) -> Self {
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

    /// Frobenius endomorphism $\phi(c_0 + c_1 v) = (c_0 + c_1 v)^p = c_0^p + \zeta_4 c_1^p v$.
    #[inline(always)]
    pub const fn frobenius(self) -> Self {
        Self {
            c0: self.c0.conj(),
            c1: self.c1.conj().mul_base(FROBENIUS_ZETA4),
        }
    }

    /// Squared Frobenius $\phi^2(c_0 + c_1 v) = (c_0 + c_1 v)^{p^2} = c_0 - c_1 v$.
    #[inline(always)]
    pub const fn frobenius_sq(self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c1.const_neg(),
        }
    }
}

impl Add for GoldilocksExt4 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}

impl AddAssign for GoldilocksExt4 {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}

impl Sub for GoldilocksExt4 {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}

impl SubAssign for GoldilocksExt4 {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}

impl Neg for GoldilocksExt4 {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        self.const_neg()
    }
}

impl Mul for GoldilocksExt4 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}

impl MulAssign for GoldilocksExt4 {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.const_mul(rhs);
    }
}

/// 4-way unrolled Cooley–Tukey butterfly block over `GoldilocksExt4` using base-field twiddles.
#[inline(always)]
fn butterfly_block_ext4(
    lo: &mut [GoldilocksExt4],
    hi: &mut [GoldilocksExt4],
    w_init: Goldilocks,
    w_len: Goldilocks,
) {
    let m = lo.len();
    debug_assert_eq!(m, hi.len());
    if m >= 4 {
        let w2 = w_len * w_len;
        let fourth_power = w2 * w2;
        let mut wk0 = w_init;
        let mut wk1 = wk0 * w_len;
        let mut wk2 = wk0 * w2;
        let mut wk3 = wk1 * w2;
        let mut j = 0usize;
        while j + 4 <= m {
            let u0 = lo[j];
            let v0 = hi[j].mul_base(wk0);
            let u1 = lo[j + 1];
            let v1 = hi[j + 1].mul_base(wk1);
            let u2 = lo[j + 2];
            let v2 = hi[j + 2].mul_base(wk2);
            let u3 = lo[j + 3];
            let v3 = hi[j + 3].mul_base(wk3);
            lo[j] = u0 + v0;
            hi[j] = u0 - v0;
            lo[j + 1] = u1 + v1;
            hi[j + 1] = u1 - v1;
            lo[j + 2] = u2 + v2;
            hi[j + 2] = u2 - v2;
            lo[j + 3] = u3 + v3;
            hi[j + 3] = u3 - v3;
            wk0 *= fourth_power;
            wk1 *= fourth_power;
            wk2 *= fourth_power;
            wk3 *= fourth_power;
            j += 4;
        }
        while j < m {
            let u = lo[j];
            let v = hi[j].mul_base(wk0);
            lo[j] = u + v;
            hi[j] = u - v;
            wk0 *= w_len;
            j += 1;
        }
    } else {
        let mut w = w_init;
        for j in 0..m {
            let u = lo[j];
            let v = hi[j].mul_base(w);
            lo[j] = u + v;
            hi[j] = u - v;
            w *= w_len;
        }
    }
}

/// In-place Radix-2 Cooley–Tukey NTT over `GoldilocksExt4` using 2-adic roots in `Goldilocks`.
pub fn ntt_ext4(a: &mut [GoldilocksExt4]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    if n <= 1 {
        return;
    }
    bit_reverse_permute(a);

    #[cfg(feature = "std")]
    if n >= 8_192 {
        let threads = crate::parallel_pow2_workers(n / 2);
        if threads > 1 {
            ntt_ext4_parallel_stages(a, threads);
            return;
        }
    }

    let mut len = 2;
    let mut stage = 1;
    while len <= n {
        let w_len = Goldilocks::two_adic_generator(stage);
        let half = len / 2;
        for block in a.chunks_exact_mut(len) {
            let (lo, hi) = block.split_at_mut(half);
            butterfly_block_ext4(lo, hi, Goldilocks::ONE, w_len);
        }
        len <<= 1;
        stage += 1;
    }
}

#[cfg(feature = "std")]
fn ntt_ext4_parallel_stages(a: &mut [GoldilocksExt4], threads: usize) {
    debug_assert!(threads.is_power_of_two() && a.len() >= threads * 2);
    let n = a.len();
    let chunk_n = n / threads;
    let chunk_stages = chunk_n.trailing_zeros() as usize;
    std::thread::scope(|scope| {
        for sub in a.chunks_mut(chunk_n) {
            crate::spawn_bounded(scope, move || {
                let mut len = 2;
                let mut stage = 1;
                while stage <= chunk_stages {
                    let w_len = Goldilocks::two_adic_generator(stage);
                    let half = len / 2;
                    for block in sub.chunks_exact_mut(len) {
                        let (lo, hi) = block.split_at_mut(half);
                        butterfly_block_ext4(lo, hi, Goldilocks::ONE, w_len);
                    }
                    len <<= 1;
                    stage += 1;
                }
            });
        }
    });

    let log_n = n.trailing_zeros() as usize;
    for stage in (chunk_stages + 1)..=log_n {
        let len = 1usize << stage;
        let half = len / 2;
        let w_len = Goldilocks::two_adic_generator(stage);
        for block in a.chunks_mut(len) {
            let (lo, hi) = block.split_at_mut(half);
            let sub_j = (half / threads).max(1);
            std::thread::scope(|scope| {
                for (t_idx, (lo_c, hi_c)) in
                    lo.chunks_mut(sub_j).zip(hi.chunks_mut(sub_j)).enumerate()
                {
                    let w_init = w_len.pow((t_idx * sub_j) as u64);
                    crate::spawn_bounded(scope, move || {
                        butterfly_block_ext4(lo_c, hi_c, w_init, w_len);
                    });
                }
            });
        }
    }
}

/// Coset Reed–Solomon encoding over `GoldilocksExt4` onto shifted subgroup $g \cdot H$ (`g = 7`).
pub fn encode_rs_coset_ext4(coeffs: &[GoldilocksExt4], blowup: usize) -> Vec<GoldilocksExt4> {
    let _phase = crate::profile::span("encode_rs_coset_ext4");
    let n_c = coeffs.len();
    assert!(n_c.is_power_of_two());
    assert!(blowup.is_power_of_two() && blowup >= 2);
    let domain_len = n_c.checked_mul(blowup).expect("RS domain size overflow");
    assert!(
        domain_len.trailing_zeros() <= 32,
        "RS domain exceeds Goldilocks two-adicity"
    );

    // Coset decomposition across hardware worker threads: `blowup` independent L1/L2-resident size-`n_c` NTTs!
    #[cfg(feature = "std")]
    if domain_len >= 8_192 && n_c >= 32 && blowup >= 4 {
        let workers = crate::parallel_pow2_workers(domain_len / 32);
        let log_d = domain_len.trailing_zeros() as usize;
        let log_c = n_c.trailing_zeros() as usize;
        let rev_shift_c = usize::BITS as usize - log_c;
        let omega_d = Goldilocks::two_adic_generator(log_d);

        let mut cosets = vec![GoldilocksExt4::ZERO; domain_len];
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
                                row[dst] = c.mul_base(sp);
                                sp *= s_r;
                            }
                            let mut len = 2;
                            let mut stage = 1;
                            while len <= n_c {
                                let w_len = Goldilocks::two_adic_generator(stage);
                                let half = len / 2;
                                for block in row.chunks_exact_mut(len) {
                                    let (lo, hi) = block.split_at_mut(half);
                                    butterfly_block_ext4(lo, hi, Goldilocks::ONE, w_len);
                                }
                                len <<= 1;
                                stage += 1;
                            }
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
                        let sub_c = n_c / inner_threads;
                        let mut shifted = vec![GoldilocksExt4::ZERO; n_c];
                        std::thread::scope(|inner| {
                            for (ti, dst_s) in shifted.chunks_mut(sub_c).enumerate() {
                                let src_s = &coeffs[ti * sub_c..(ti + 1) * sub_c];
                                let mut sp = s_r.pow((ti * sub_c) as u64);
                                crate::spawn_bounded(inner, move || {
                                    for (d, &c) in dst_s.iter_mut().zip(src_s.iter()) {
                                        *d = c.mul_base(sp);
                                        sp *= s_r;
                                    }
                                });
                            }
                        });
                        let shifted_ref = &shifted;
                        std::thread::scope(|inner| {
                            for (ti, dst_s) in row.chunks_mut(sub_c).enumerate() {
                                let base_i = ti * sub_c;
                                crate::spawn_bounded(inner, move || {
                                    for (off, slot) in dst_s.iter_mut().enumerate() {
                                        let rev = (base_i + off).reverse_bits() >> rev_shift_c;
                                        *slot = shifted_ref[rev];
                                    }
                                });
                            }
                        });
                        drop(shifted);
                        if inner_threads > 1 && n_c >= inner_threads * 2 {
                            ntt_ext4_parallel_stages(row, inner_threads);
                        } else {
                            let mut len = 2;
                            let mut stage = 1;
                            while len <= n_c {
                                let w_len = Goldilocks::two_adic_generator(stage);
                                let half = len / 2;
                                for block in row.chunks_exact_mut(len) {
                                    let (lo, hi) = block.split_at_mut(half);
                                    butterfly_block_ext4(lo, hi, Goldilocks::ONE, w_len);
                                }
                                len <<= 1;
                                stage += 1;
                            }
                        }
                    });
                }
            });
        }

        let mut out = vec![GoldilocksExt4::ZERO; domain_len];
        let t_threads = crate::parallel_pow2_workers(n_c);
        let q_chunk = (n_c / t_threads).max(1);
        let cosets_ref = &cosets;
        std::thread::scope(|scope| {
            for (ti, out_sub) in out.chunks_mut(q_chunk * blowup).enumerate() {
                let base_q = ti * q_chunk;
                crate::spawn_bounded(scope, move || {
                    for (off_q, dst_row) in out_sub.chunks_exact_mut(blowup).enumerate() {
                        let q = base_q + off_q;
                        for (r, slot) in dst_row.iter_mut().enumerate() {
                            *slot = cosets_ref[r * n_c + q];
                        }
                    }
                });
            }
        });
        return out;
    }

    let mut buf = vec![GoldilocksExt4::ZERO; domain_len];
    let shift = Goldilocks::NON_RESIDUE;
    let mut shift_pow = Goldilocks::ONE;
    for (i, &c) in coeffs.iter().enumerate() {
        buf[i] = c.mul_base(shift_pow);
        shift_pow *= shift;
    }
    ntt_ext4(&mut buf);
    buf
}

/// Evaluate univariate polynomial $\sum_k c_k z^k$ (`coeffs` in ascending degree) at `z: Goldilocks`.
#[inline]
pub fn eval_univariate_ext4_at_base(coeffs: &[GoldilocksExt4], z: Goldilocks) -> GoldilocksExt4 {
    let mut acc = GoldilocksExt4::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul_base(z) + c;
    }
    acc
}

/// Four independent Horner chains expose instruction-level parallelism without changing
/// coefficient order: lane `j` contains the coefficients of powers congruent to `j mod 4`.
#[inline]
fn horner_ext4_interleaved(coeffs: &[GoldilocksExt4], z: GoldilocksExt4) -> GoldilocksExt4 {
    if coeffs.len() < 32 {
        return coeffs
            .iter()
            .rev()
            .fold(GoldilocksExt4::ZERO, |acc, &c| acc * z + c);
    }
    let (blocks, rem) = coeffs.as_chunks::<4>();
    let mut lanes = [GoldilocksExt4::ZERO; 4];
    lanes[..rem.len()].copy_from_slice(rem);
    let z4 = z.square().square();
    for block in blocks.iter().rev() {
        for lane in 0..4 {
            lanes[lane] = lanes[lane].mul_add(z4, block[lane]);
        }
    }
    ((lanes[3] * z + lanes[2]) * z + lanes[1]) * z + lanes[0]
}

/// Evaluate univariate polynomial $\sum_k c_k z^k$ (`coeffs` in ascending degree) at `z: GoldilocksExt4`.
#[inline]
pub fn eval_univariate_ext4(coeffs: &[GoldilocksExt4], z: GoldilocksExt4) -> GoldilocksExt4 {
    #[cfg(feature = "std")]
    if coeffs.len() >= 16_384 {
        let workers = crate::parallel_workers().min(8);
        let chunk = coeffs.len().div_ceil(workers);
        return std::thread::scope(|scope| {
            let parts: Vec<_> = coeffs
                .chunks(chunk)
                .enumerate()
                .map(|(i, sub)| {
                    crate::spawn_bounded(scope, move || {
                        horner_ext4_interleaved(sub, z) * z.pow((i * chunk) as u64)
                    })
                })
                .collect();
            parts
                .into_iter()
                .map(crate::join_worker)
                .fold(GoldilocksExt4::ZERO, |a, b| a + b)
        });
    }
    horner_ext4_interleaved(coeffs, z)
}

/// Univariate polynomial over `GoldilocksExt4` in monomial basis $c_0 + c_1 X + \dots + c_d X^d$.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoundPolyExt4 {
    pub coeffs: Vec<GoldilocksExt4>,
}

impl RoundPolyExt4 {
    #[inline]
    pub fn evaluate(&self, x: GoldilocksExt4) -> GoldilocksExt4 {
        eval_univariate_ext4(&self.coeffs, x)
    }

    #[inline]
    pub fn degree_bound(&self) -> usize {
        self.coeffs.len().saturating_sub(1)
    }

    /// Interpolate unique polynomial of degree `< evals.len()` from values at $X = 0, 1, \dots, m-1$.
    pub fn interpolate_from_small_ints(evals: &[GoldilocksExt4]) -> Self {
        let m = evals.len();
        if m == 0 {
            return Self { coeffs: Vec::new() };
        }
        let mut coeffs = vec![GoldilocksExt4::ZERO; m];
        for (i, &eval) in evals.iter().enumerate().take(m) {
            let mut numer = vec![Goldilocks::ZERO; m];
            numer[0] = Goldilocks::ONE;
            let mut deg = 0usize;
            let mut denom = Goldilocks::ONE;
            for j in 0..m {
                if i == j {
                    continue;
                }
                let neg_j = Goldilocks::from_u64_reduced(j as u64).const_neg();
                for k in (1..=deg + 1).rev() {
                    numer[k] = numer[k - 1] + numer[k] * neg_j;
                }
                numer[0] *= neg_j;
                deg += 1;

                let diff = if i >= j {
                    Goldilocks::from_u64_reduced((i - j) as u64)
                } else {
                    Goldilocks::from_u64_reduced((j - i) as u64).const_neg()
                };
                denom *= diff;
            }
            let scale = eval.mul_base(denom.inv());
            for k in 0..m {
                coeffs[k] += scale.mul_base(numer[k]);
            }
        }
        Self { coeffs }
    }
}

/// Multilinear equality kernel $\widetilde{\text{eq}}(a, b)$ over `GoldilocksExt4`.
pub fn eq_poly_ext4(a: &[GoldilocksExt4], b: &[GoldilocksExt4]) -> GoldilocksExt4 {
    assert_eq!(a.len(), b.len());
    let mut acc = GoldilocksExt4::ONE;
    for (&ai, &bi) in a.iter().zip(b.iter()) {
        let prod = ai * bi;
        let term = GoldilocksExt4::ONE - ai - bi + prod + prod;
        acc *= term;
    }
    acc
}

/// Multilinear equality kernel $\widetilde{\text{eq}}(a_{\text{base}}, b_{\text{ext4}})$.
pub fn eq_poly_base_ext4(a_base: &[Goldilocks], b_ext4: &[GoldilocksExt4]) -> GoldilocksExt4 {
    assert_eq!(a_base.len(), b_ext4.len());
    let mut acc = GoldilocksExt4::ONE;
    for (&ai, &bi) in a_base.iter().zip(b_ext4.iter()) {
        let prod = bi.mul_base(ai);
        let term = GoldilocksExt4::from_base(Goldilocks::ONE - ai) - bi + prod + prod;
        acc *= term;
    }
    acc
}

/// Expand the $2^\ell$-element table `T[x] = eq(r, bits(x))` over `GoldilocksExt4`.
pub fn build_eq_table_ext4(r: &[GoldilocksExt4]) -> Vec<GoldilocksExt4> {
    let mut table = Vec::with_capacity(1usize << r.len());
    table.push(GoldilocksExt4::ONE);
    for &ri in r.iter().rev() {
        let cur_len = table.len();
        table.resize(cur_len * 2, GoldilocksExt4::ZERO);
        for idx in (0..cur_len).rev() {
            let v = table[idx];
            let vr = v * ri;
            table[2 * idx] = v - vr;
            table[2 * idx + 1] = vr;
        }
    }
    table
}

/// Expand the $2^\ell$-element table `T[x] = eq(r, bits(x))` over base-field `Goldilocks`.
pub fn build_eq_table_base(r: &[Goldilocks]) -> Vec<Goldilocks> {
    let mut table = Vec::with_capacity(1usize << r.len());
    table.push(Goldilocks::ONE);
    for &ri in r.iter().rev() {
        let cur_len = table.len();
        table.resize(cur_len * 2, Goldilocks::ZERO);
        for idx in (0..cur_len).rev() {
            let v = table[idx];
            let vr = v * ri;
            table[2 * idx] = v - vr;
            table[2 * idx + 1] = vr;
        }
    }
    table
}

/// Univariate-to-multilinear Kronecker point $\text{pow2}(z) = (z, z^2, z^4, \dots, z^{2^{\ell-1}})$
/// over `GoldilocksExt4`, satisfying $W(\text{pow2}(z)) = f_{\text{uni}}(z)$.
pub fn pow2_point_ext4(mut z: GoldilocksExt4, num_vars: usize) -> Vec<GoldilocksExt4> {
    let mut out = Vec::with_capacity(num_vars);
    for _ in 0..num_vars {
        out.push(z);
        z = z.square();
    }
    out
}

/// Univariate-to-multilinear Kronecker point $\text{pow2}(z) = (z, z^2, z^4, \dots, z^{2^{\ell-1}})$
/// over base-field `Goldilocks`.
pub fn pow2_point_base(mut z: Goldilocks, num_vars: usize) -> Vec<Goldilocks> {
    let mut out = Vec::with_capacity(num_vars);
    for _ in 0..num_vars {
        out.push(z);
        z = z.square();
    }
    out
}

/// Evaluate multilinear extension of `table` ($2^\ell$ base-field elements) at `point` ($\ell$ `Ext4` coords).
pub fn mle_eval_base_at_ext4(table: &[Goldilocks], point: &[GoldilocksExt4]) -> GoldilocksExt4 {
    assert_eq!(table.len(), 1usize << point.len());
    let eq_tab = build_eq_table_ext4(point);
    let mut acc = GoldilocksExt4::ZERO;
    for (&w, &e) in table.iter().zip(eq_tab.iter()) {
        acc += e.mul_base(w);
    }
    acc
}

/// Evaluate multilinear extension of `table` ($2^\ell$ `Ext4` elements) at `point` ($\ell$ `Ext4` coords).
pub fn mle_eval_ext4(table: &[GoldilocksExt4], point: &[GoldilocksExt4]) -> GoldilocksExt4 {
    assert_eq!(table.len(), 1usize << point.len());
    let eq_tab = build_eq_table_ext4(point);
    let mut acc = GoldilocksExt4::ZERO;
    for (&w, &e) in table.iter().zip(eq_tab.iter()) {
        acc += e * w;
    }
    acc
}

/// Fold first variable $X_0 \leftarrow r$ of an `Ext4` multilinear hypercube table.
pub fn fold_first_var_ext4(table: &[GoldilocksExt4], r: GoldilocksExt4) -> Vec<GoldilocksExt4> {
    assert!(table.len() >= 2 && table.len().is_power_of_two());
    let half = table.len() / 2;
    let mut out = Vec::with_capacity(half);
    for k in 0..half {
        let a = table[2 * k];
        out.push(a + r * (table[2 * k + 1] - a));
    }
    out
}

/// In-place variant of [`fold_first_var_ext4`]: halves `table` without allocating.
pub fn fold_first_var_in_place_ext4(table: &mut Vec<GoldilocksExt4>, r: GoldilocksExt4) {
    assert!(table.len() >= 2 && table.len().is_power_of_two());
    let half = table.len() / 2;
    for k in 0..half {
        let a = table[2 * k];
        table[k] = a + r * (table[2 * k + 1] - a);
    }
    table.truncate(half);
}

#[cfg(test)]
mod ext4_tests {
    #[test]
    fn interleaved_horner_matches_scalar() {
        let coeffs: Vec<_> = (0..16_389)
            .map(|i| {
                GoldilocksExt4::from_limbs(core::array::from_fn(|j| {
                    Goldilocks::from_u64_reduced(
                        (i as u64 + 1).wrapping_mul(u64::MAX - 17 * j as u64),
                    )
                }))
            })
            .collect();
        for z in [GoldilocksExt4::ZERO, GoldilocksExt4::ONE, coeffs[13]] {
            for len in (0..20).chain([31, 32, 33, 63, 64, 65, 16_383, 16_384, 16_389]) {
                let expected = coeffs[..len]
                    .iter()
                    .rev()
                    .fold(GoldilocksExt4::ZERO, |acc, &c| acc * z + c);
                assert_eq!(eval_univariate_ext4(&coeffs[..len], z), expected);
            }
        }
    }

    use super::*;

    fn sample_ext4(seed: u64) -> GoldilocksExt4 {
        let m = |k: u64| {
            Goldilocks::from_u64_reduced(
                seed.wrapping_mul(
                    0x9E37_79B9_7F4A_7C15_u64.wrapping_add(k.wrapping_mul(6364136223846793005)),
                )
                .wrapping_add(0xD1B5_4A32_D192_ED03_u64 ^ (k << 19)),
            )
        };
        GoldilocksExt4::from_limbs([m(1), m(2), m(3), m(4)])
    }

    #[test]
    fn parallel_horner_matches_serial_with_nondivisible_chunks() {
        let coeffs: Vec<_> = (0..16_387)
            .map(|i| {
                GoldilocksExt4::from_limbs(core::array::from_fn(|j| {
                    Goldilocks::from_u64_reduced((i * 7919 + j * 31) as u64)
                }))
            })
            .collect();
        for z in [
            GoldilocksExt4::ZERO,
            GoldilocksExt4::ONE,
            GoldilocksExt4::V + GoldilocksExt4::from_u64(17),
        ] {
            let expected = coeffs
                .iter()
                .rev()
                .fold(GoldilocksExt4::ZERO, |a, &c| a * z + c);
            assert_eq!(eval_univariate_ext4(&coeffs, z), expected);
        }
    }

    #[test]
    fn ext4_polynomial_irreducibility_over_ext2_and_base() {
        let minus_one_base = Goldilocks::ONE.const_neg();
        // 7 is a quadratic non-residue in F_p: 7^((p-1)/2) == -1.
        assert_eq!(
            Goldilocks::NON_RESIDUE.pow((GOLDILOCKS_PRIME - 1) / 2),
            minus_one_base
        );
        // FROBENIUS_ZETA4^2 == -1 in F_p.
        assert_eq!(FROBENIUS_ZETA4.square(), minus_one_base);

        // u in F_{p^2} satisfies u^((p^2 - 1)/2) = (u^(p + 1))^((p - 1)/2) == -1 in F_{p^2},
        // proving X^2 - u is irreducible over F_{p^2}.
        let u = GoldilocksExt2::U;
        let u_pow_p_plus_1 = u.pow(GOLDILOCKS_PRIME) * u;
        assert_eq!(
            u_pow_p_plus_1,
            GoldilocksExt2::from_base(Goldilocks::NON_RESIDUE.const_neg())
        );
        let euler_crit_u = u_pow_p_plus_1.pow((GOLDILOCKS_PRIME - 1) / 2);
        assert_eq!(euler_crit_u, GoldilocksExt2::ONE.const_neg());

        // Generator v satisfies v^2 == u and v^4 == 7.
        let v = GoldilocksExt4::V;
        assert_eq!(v.square(), GoldilocksExt4::from_ext2(u));
        assert_eq!(
            v.square().square(),
            GoldilocksExt4::from_base(Goldilocks::NON_RESIDUE)
        );
    }

    #[test]
    fn ext4_field_axioms_inversion_and_canonical_bytes() {
        assert_eq!(GoldilocksExt4::ZERO.inv(), GoldilocksExt4::ZERO);
        assert_eq!(GoldilocksExt4::ONE.inv(), GoldilocksExt4::ONE);

        let specials = [
            GoldilocksExt4::V,
            GoldilocksExt4::from_ext2(GoldilocksExt2::U),
            GoldilocksExt4::new(GoldilocksExt2::ZERO, GoldilocksExt2::U),
            GoldilocksExt4::from_limbs([
                Goldilocks::from_canonical_u64(GOLDILOCKS_PRIME - 1).unwrap(),
                Goldilocks::from_canonical_u64(GOLDILOCKS_PRIME - 2).unwrap(),
                Goldilocks::from_canonical_u64(GOLDILOCKS_PRIME - 3).unwrap(),
                Goldilocks::from_canonical_u64(GOLDILOCKS_PRIME - 4).unwrap(),
            ]),
        ];
        for &x in &specials {
            assert!(!x.is_zero());
            assert_eq!(x * x.inv(), GoldilocksExt4::ONE);
            assert_eq!(x.inv() * x, GoldilocksExt4::ONE);
            assert_eq!(x.square(), x * x);
        }

        for s in 1..=64u64 {
            let a = sample_ext4(s);
            let b = sample_ext4(s + 1_000);
            let c = sample_ext4(s + 2_000);

            assert_eq!(a + b, b + a);
            assert_eq!((a + b) + c, a + (b + c));
            assert_eq!(a + (-a), GoldilocksExt4::ZERO);
            assert_eq!(a * b, b * a);
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!(a.square(), a * a);
            assert_eq!(a.mul_base(b.c0.c0), a * GoldilocksExt4::from_base(b.c0.c0));
            assert_eq!(a.mul_ext2(b.c0), a * GoldilocksExt4::from_ext2(b.c0));
            if !a.is_zero() {
                assert_eq!(a * a.inv(), GoldilocksExt4::ONE);
            }

            let enc = a.to_le_bytes();
            assert_eq!(GoldilocksExt4::from_le_bytes_canonical(enc), Some(a));
        }

        // Non-canonical limb (>= GOLDILOCKS_PRIME) must be rejected on every 8-byte slot.
        for slot in 0..4 {
            let mut bad = GoldilocksExt4::ONE.to_le_bytes();
            bad[slot * 8..(slot + 1) * 8].copy_from_slice(&GOLDILOCKS_PRIME.to_le_bytes());
            assert_eq!(GoldilocksExt4::from_le_bytes_canonical(bad), None);
        }
    }

    #[test]
    fn ext4_frobenius_endomorphism_and_galois_norm() {
        for s in 1..=32u64 {
            let x = sample_ext4(s * 17);
            let y = sample_ext4(s * 31 + 9);
            let phi_x = x.frobenius();
            let phi_y = y.frobenius();

            // Direct definition: phi(x) == x^p.
            assert_eq!(phi_x, x.pow(GOLDILOCKS_PRIME));
            // Ring homomorphism: phi(x + y) == phi(x) + phi(y), phi(x * y) == phi(x) * phi(y).
            assert_eq!((x + y).frobenius(), phi_x + phi_y);
            assert_eq!((x * y).frobenius(), phi_x * phi_y);
            // Involution on F_{p^4}/F_{p^2} and order 4 over F_p.
            let phi2_x = phi_x.frobenius();
            let phi3_x = phi2_x.frobenius();
            let phi4_x = phi3_x.frobenius();
            assert_eq!(phi2_x, x.frobenius_sq());
            assert_eq!(phi4_x, x);
            // Galois norm x * phi(x) * phi^2(x) * phi^3(x) lies in F_p and matches norm_to_base.
            let galois_prod = x * phi_x * phi2_x * phi3_x;
            assert_eq!(galois_prod, GoldilocksExt4::from_base(x.norm_to_base()));
        }
    }

    #[test]
    fn ext4_coset_ntt_matches_direct_horner_evaluation() {
        let coeffs: Vec<GoldilocksExt4> = (0..16).map(|i| sample_ext4(i + 500)).collect();
        let blowup = 4usize;
        let cw = encode_rs_coset_ext4(&coeffs, blowup);
        let domain_len = coeffs.len() * blowup;
        let omega = Goldilocks::two_adic_generator(domain_len.trailing_zeros() as usize);
        let mut x = Goldilocks::NON_RESIDUE;
        for &got in &cw {
            assert_eq!(got, eval_univariate_ext4_at_base(&coeffs, x));
            x *= omega;
        }
    }

    #[test]
    #[should_panic(expected = "RS domain size overflow")]
    fn encode_rs_coset_goldilocks_rejects_domain_overflow() {
        let _ = encode_rs_coset_goldilocks(&[Goldilocks::ONE; 4], 1usize << 62);
    }

    #[test]
    #[should_panic(expected = "RS domain exceeds Goldilocks two-adicity")]
    fn encode_rs_coset_ext4_rejects_excessive_two_adicity() {
        let _ = encode_rs_coset_ext4(&[GoldilocksExt4::ONE; 4], 1usize << 31);
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

        // Empty, singleton, zero-only, stack-path (<= 512), and heap-path (> 512) batch_inv.
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

    /// Sizes below, at and above the cache block, with both parities of remaining stages.
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

    /// The single-reduction quartic product against the tower Karatsuba definition, including
    /// operands whose every limb is `p - 1` (the largest accumulators).
    #[test]
    fn ext4_product_equals_tower_karatsuba() {
        let top = Goldilocks::from_u64_reduced(GOLDILOCKS_PRIME - 1);
        let v = sample(4 * 512, 0xE4);
        let mut elems: Vec<GoldilocksExt4> = v
            .as_chunks::<4>()
            .0
            .iter()
            .map(|l| GoldilocksExt4::from_limbs(*l))
            .collect();
        elems.push(GoldilocksExt4::from_limbs([top; 4]));
        elems.push(GoldilocksExt4::from_limbs([
            top,
            Goldilocks::ZERO,
            top,
            Goldilocks::ONE,
        ]));
        elems.push(GoldilocksExt4::ZERO);
        elems.push(GoldilocksExt4::ONE);
        elems.push(GoldilocksExt4::V);
        for (i, &x) in elems.iter().enumerate() {
            for &y in &elems[i.saturating_sub(3)..] {
                assert_eq!(
                    x.mul_base(y.c0.c0),
                    x.const_mul_tower(GoldilocksExt4::from_base(y.c0.c0))
                );
                assert_eq!(
                    x.mul_ext2(y.c1),
                    x.const_mul_tower(GoldilocksExt4::from_ext2(y.c1))
                );
                assert_eq!(x.const_mul(y), x.const_mul_tower(y));
                assert_eq!(y.const_mul(x), x.const_mul_tower(y));
                assert_eq!(x.mul_add(y, x), x.const_mul_tower(y).tower_add(x));
                assert_eq!(x + y, x.tower_add(y));
                assert_eq!(x - y, x.tower_add(y.tower_neg()));
                assert_eq!(-y, y.tower_neg());
            }
            assert_eq!(x.square(), x.const_mul_tower(x));
        }
    }

    /// The wide accumulator against the `qsag-core` operations, on random words and on
    /// every pair from the boundary set (carry, borrow and `2^32` limb edges).
    #[test]
    fn wide_accumulator_equals_core_operations() {
        let p = GOLDILOCKS_PRIME;
        let mut xs: Vec<Goldilocks> = [
            0,
            1,
            2,
            0xFFFF_FFFF,
            0x1_0000_0000,
            0x1_0000_0001,
            p / 2,
            p / 2 + 1,
            0xFFFF_FFFE_FFFF_FFFF,
            p - 0x1_0000_0000,
            p - 2,
            p - 1,
        ]
        .into_iter()
        .map(Goldilocks::from_u64_reduced)
        .collect();
        xs.extend(sample(200, 0xBA5E));
        for &a in &xs {
            for &b in &xs {
                assert_eq!(
                    WideAcc::ZERO
                        .add_mul(a, b, 14)
                        .add_mul(b, b, 7)
                        .add_elem(a)
                        .reduce(),
                    a.const_mul(b).const_mul(Goldilocks::from_u64_reduced(14))
                        + b.const_mul(b).const_mul(Goldilocks::from_u64_reduced(7))
                        + a
                );
            }
        }
    }

    #[test]
    #[ignore = "timing probe: run with --ignored --nocapture"]
    fn bench_field_kernels() {
        let n = 1usize << 22;
        let base = sample(4 * n, 0xBE);
        let coeffs: Vec<GoldilocksExt4> = base
            .as_chunks::<4>()
            .0
            .iter()
            .map(|l| GoldilocksExt4::from_limbs(*l))
            .collect();
        let z = coeffs[17];
        let ns = |t: std::time::Instant, count: usize| t.elapsed().as_nanos() as f64 / count as f64;

        let t = std::time::Instant::now();
        let mut acc = z;
        for c in &coeffs[..1 << 20] {
            acc *= *c;
        }
        let chain_ns = ns(t, 1 << 20);

        let t = std::time::Instant::now();
        let mut sum = GoldilocksExt4::ZERO;
        for c in &coeffs {
            sum += *c * z;
        }
        let indep_ns = ns(t, n);

        let t = std::time::Instant::now();
        let h = horner_ext4_interleaved(&coeffs, z);
        let horner_ns = ns(t, n);

        for log_n in [14usize, 20, 24] {
            let mut data = sample(1 << log_n, 5);
            let t = std::time::Instant::now();
            ntt_goldilocks_stages_blocked(&mut data, log_n, false);
            let per = t.elapsed().as_nanos() as f64 / ((log_n << log_n) as f64 / 2.0);
            std::println!(
                "FIELD ntt_blocked log_n={log_n} ns_per_butterfly={per:.2} ({:?})",
                data[1]
            );
        }

        let t = std::time::Instant::now();
        let mut sq = z;
        for _ in 0..1 << 20 {
            sq = sq.square();
        }
        let square_ns = ns(t, 1 << 20);
        let t = std::time::Instant::now();
        let mut mb = z;
        for x in &base[..1 << 20] {
            mb = mb.mul_base(*x);
        }
        let mul_base_ns = ns(t, 1 << 20);
        std::println!(
            "FIELD ext4_square_chain_ns={square_ns:.1} ext4_mul_base_chain_ns={mul_base_ns:.1} \
             (checks {:?} {:?})",
            sq.to_limbs()[0],
            mb.to_limbs()[0]
        );

        let t = std::time::Instant::now();
        let mut b = Goldilocks::ONE;
        for x in &base[..1 << 22] {
            b = b.const_mul(*x);
        }
        let base_chain_ns = ns(t, 1 << 22);
        std::println!(
            "FIELD ext4_mul_chain_ns={chain_ns:.1} ext4_mul_indep_ns={indep_ns:.1} \
             horner_ns_per_coeff={horner_ns:.1} base_mul_chain_ns={base_chain_ns:.2} \
             (checks {:?} {:?} {:?} {:?})",
            acc.to_limbs()[0],
            sum.to_limbs()[0],
            h.to_limbs()[0],
            b
        );
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
