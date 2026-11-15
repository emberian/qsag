//! Hem field layer. The base field `Goldilocks` ($\mathbb{F}_p, p = 2^{64} - 2^{32} + 1$) and the
//! quadratic extension `GoldilocksExt2` ($\mathbb{F}_p[u]/(u^2 - 7)$) are the `qsag-core` types,
//! re-exported here. This module adds what only the aggregation prover needs on top of them:
//! shift/fold helpers, batch inversion, 2-adic roots of unity, the quartic extension
//! `GoldilocksExt4` ($\mathbb{F}_{p^2}[v]/(v^2 - u) \cong \mathbb{F}_p[v]/(v^4 - 7)$), Radix-2
//! NTT/INTT, univariate round-polynomial interpolation, and multilinear folding/evaluation.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

pub use qsag_core::field::goldilocks::{GOLDILOCKS_PRIME, Goldilocks, GoldilocksExt2};
use qsag_core::field::goldilocks::{GOLDILOCKS_EPSILON as EPSILON, GOLDILOCKS_ROOT_2_32};

// The Aeneas-extracted WHIR verifier core and `qsag-core` must agree on the modulus.
const _: () = assert!(GOLDILOCKS_PRIME == qsag_whir_verified::GOLDILOCKS_P);

/// Primitive $2^{32}$-th root of unity $\omega_{2^{32}} = 7^{2^{32} - 1} \bmod p$.
pub const TWO_ADIC_ROOT_OF_UNITY_32: u64 = GOLDILOCKS_ROOT_2_32;

/// Reduce `lo + 2^64 * hi` for `hi < 2^32` using $2^{64} \equiv 2^{32} - 1 \pmod p$.
#[inline(always)]
const fn fold_small_carry(lo: u64, hi: u64) -> Goldilocks {
    let adj = (hi << 32).wrapping_sub(hi);
    let (s, c) = lo.overflowing_add(adj);
    let s2 = s.wrapping_add((0u64.wrapping_sub(c as u64)) & EPSILON);
    Goldilocks::from_u64_reduced(s2)
}

/// `7 * x` without a 64x64 multiplication.
#[inline(always)]
pub(crate) const fn gl_mul_by_7(x: Goldilocks) -> Goldilocks {
    let v = x.to_canonical_u64() as u128;
    let prod = (v << 3) - v;
    fold_small_carry(prod as u64, (prod >> 64) as u64)
}

/// `2^S * x` for `1 <= S <= 31` using shifts and one $\epsilon$ fold.
#[inline(always)]
pub(crate) const fn gl_shl_small<const S: u32>(x: Goldilocks) -> Goldilocks {
    const { assert!(S >= 1 && S <= 31) };
    let v = x.to_canonical_u64();
    fold_small_carry(v << S, v >> (64 - S))
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
    GoldilocksExt2::new(gl_mul_by_7(x.c1), x.c0)
}

#[inline(always)]
pub(crate) const fn ext2_shl_small<const S: u32>(x: GoldilocksExt2) -> GoldilocksExt2 {
    GoldilocksExt2::new(gl_shl_small::<S>(x.c0), gl_shl_small::<S>(x.c1))
}

/// `x^2 = (c_0^2 + 7 c_1^2) + 2 c_0 c_1 u` with two base squarings and one base product.
#[inline(always)]
pub(crate) const fn ext2_square(x: GoldilocksExt2) -> GoldilocksExt2 {
    let ab = x.c0.const_mul(x.c1);
    GoldilocksExt2::new(
        x.c0.square().const_add(gl_mul_by_7(x.c1.square())),
        ab.const_add(ab),
    )
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
    /// Multiply by the quadratic non-residue `7` without a 64x64 multiplication.
    fn mul_by_7(self) -> Self;
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
    fn mul_by_7(self) -> Self {
        gl_mul_by_7(self)
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
            base = ext2_square(base);
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

fn ntt_goldilocks_serial(a: &mut [Goldilocks]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    bit_reverse_permute(a);
    let mut len = 2;
    let mut stage = 1;
    while len <= n {
        let w_len = Goldilocks::two_adic_generator(stage);
        let half = len / 2;
        for block in a.chunks_exact_mut(len) {
            let (lo, hi) = block.split_at_mut(half);
            butterfly_block_goldilocks(lo, hi, Goldilocks::ONE, w_len);
        }
        len <<= 1;
        stage += 1;
    }
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
    if crate::acceleration::ntt(a) {
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
                let mut len = 2;
                let mut stage = 1;
                while stage <= chunk_stages {
                    let g = Goldilocks::two_adic_generator(stage);
                    let w_len = if inverse { g.inv() } else { g };
                    let half = len / 2;
                    for block in sub.chunks_exact_mut(len) {
                        let (lo, hi) = block.split_at_mut(half);
                        butterfly_block_goldilocks(lo, hi, Goldilocks::ONE, w_len);
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
                            *x *= n_inv;
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
        *x *= n_inv;
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
                                row[dst] = c * sp;
                                sp *= s_r;
                            }
                            let mut len = 2;
                            let mut stage = 1;
                            while len <= n_c {
                                let w_len = Goldilocks::two_adic_generator(stage);
                                let half = len / 2;
                                for block in row.chunks_exact_mut(len) {
                                    let (lo, hi) = block.split_at_mut(half);
                                    butterfly_block_goldilocks(lo, hi, Goldilocks::ONE, w_len);
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
                        let mut shifted = vec![Goldilocks::ZERO; n_c];
                        std::thread::scope(|inner| {
                            for (ti, dst_s) in shifted.chunks_mut(sub_c).enumerate() {
                                let src_s = &coeffs[ti * sub_c..(ti + 1) * sub_c];
                                let mut sp = s_r.pow((ti * sub_c) as u64);
                                crate::spawn_bounded(inner, move || {
                                    for (d, &c) in dst_s.iter_mut().zip(src_s.iter()) {
                                        *d = c * sp;
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
                            ntt_goldilocks_parallel_stages(row, inner_threads, false);
                        } else {
                            let mut len = 2;
                            let mut stage = 1;
                            while len <= n_c {
                                let w_len = Goldilocks::two_adic_generator(stage);
                                let half = len / 2;
                                for block in row.chunks_exact_mut(len) {
                                    let (lo, hi) = block.split_at_mut(half);
                                    butterfly_block_goldilocks(lo, hi, Goldilocks::ONE, w_len);
                                }
                                len <<= 1;
                                stage += 1;
                            }
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
        buf[i] = c * shift_pow;
        shift_pow *= shift;
    }
    ntt_goldilocks(&mut buf);
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
        Self {
            c0: self.c0.mul_base(s),
            c1: self.c1.mul_base(s),
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
        Self {
            c0: self.c0.const_neg(),
            c1: self.c1.const_neg(),
        }
    }

    #[inline(always)]
    pub const fn shl_small<const S: u32>(self) -> Self {
        Self {
            c0: ext2_shl_small::<S>(self.c0),
            c1: ext2_shl_small::<S>(self.c1),
        }
    }

    /// Karatsuba multiplication over $\mathbb{F}_{p^2}[v]/(v^2 - u)$ (`3` $\mathbb{F}_{p^2}$ muls = `9` base muls).
    #[inline(always)]
    pub const fn const_mul(self, rhs: Self) -> Self {
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

    /// Complex-style squaring over $\mathbb{F}_{p^2}[v]/(v^2 - u)$ (`2` $\mathbb{F}_{p^2}$ muls = `6` base muls):
    /// $(c_0 + c_1)(c_0 + u c_1) - c_0 c_1 - u(c_0 c_1) = c_0^2 + u c_1^2$.
    #[inline(always)]
    pub const fn square(self) -> Self {
        let p0 = self.c0.const_mul(self.c1);
        let up0 = ext2_mul_by_u(p0);
        let t = self
            .c0
            .const_add(self.c1)
            .const_mul(self.c0.const_add(ext2_mul_by_u(self.c1)));
        Self {
            c0: t.const_sub(p0).const_sub(up0),
            c1: p0.const_add(p0),
        }
    }

    /// Relative norm $\mathrm{N}_{\mathbb{F}_{p^4}/\mathbb{F}_{p^2}}(c_0 + c_1 v) = c_0^2 - u c_1^2 \in \mathbb{F}_{p^2}$.
    #[inline(always)]
    pub const fn norm_to_ext2(self) -> GoldilocksExt2 {
        ext2_square(self.c0).const_sub(ext2_mul_by_u(ext2_square(self.c1)))
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
            lanes[lane] = lanes[lane] * z4 + block[lane];
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
