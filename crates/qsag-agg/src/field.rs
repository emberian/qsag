//! Canonical `Goldilocks` ($\mathbb{F}_p, p = 2^{64} - 2^{32} + 1$), quadratic extension
//! `GoldilocksExt2` ($\mathbb{F}_p[u]/(u^2 - 7)$), quartic extension `GoldilocksExt4`
//! ($\mathbb{F}_{p^2}[v]/(v^2 - u) \cong \mathbb{F}_p[v]/(v^4 - 7)$), 2-adic roots of unity,
//! Radix-2 NTT/INTT, univariate round-polynomial interpolation, and multilinear folding/evaluation.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// Goldilocks prime $p = 2^{64} - 2^{32} + 1$.
pub const GOLDILOCKS_PRIME: u64 = 0xFFFF_FFFF_0000_0001;

/// $\epsilon = 2^{32} - 1$ such that $2^{64} \equiv \epsilon \pmod p$.
const EPSILON: u64 = 0xFFFF_FFFF;

/// Primitive $2^{32}$-th root of unity $\omega_{2^{32}} = 7^{2^{32} - 1} \bmod p$.
pub const TWO_ADIC_ROOT_OF_UNITY_32: u64 = 1_753_635_133_440_165_772;

/// Canonical element of $\mathbb{F}_p$ ($0 \le \text{val} < p$).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Goldilocks(u64);

impl Goldilocks {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    pub const TWO: Self = Self(2);
    pub const NON_RESIDUE: Self = Self(7);

    /// Strict canonical constructor: returns `None` if `v >= GOLDILOCKS_PRIME`.
    #[inline]
    pub const fn from_canonical_u64(v: u64) -> Option<Self> {
        if v < GOLDILOCKS_PRIME {
            Some(Self(v))
        } else {
            None
        }
    }

    /// Reduce an arbitrary `u64` into `[0, p)` in constant time (branchless borrow mask).
    #[inline(always)]
    pub const fn from_u64_reduced(v: u64) -> Self {
        let (diff, borrow) = v.overflowing_sub(GOLDILOCKS_PRIME);
        let mask = 0u64.wrapping_sub(borrow as u64);
        Self((v & mask) | (diff & !mask))
    }

    /// Reduce an arbitrary `u128` modulo $p$ via $2^{96} \equiv -1, 2^{64} \equiv 2^{32} - 1 \pmod p$
    /// in 10 branchless constant-time integer instructions (exact across all `0..=u128::MAX`).
    #[inline(always)]
    pub const fn reduce128(x: u128) -> Self {
        let x_lo = x as u64;
        let x_hi = (x >> 64) as u64;
        let x_hi_hi = x_hi >> 32;
        let x_hi_lo = x_hi & EPSILON;

        let (t0_raw, brw0) = x_lo.overflowing_sub(x_hi_hi);
        let t0 = t0_raw.wrapping_sub((0u64.wrapping_sub(brw0 as u64)) & EPSILON);

        let t1 = (x_hi_lo << 32).wrapping_sub(x_hi_lo);
        let (res_raw, over1) = t0.overflowing_add(t1);
        let res = res_raw.wrapping_add((0u64.wrapping_sub(over1 as u64)) & EPSILON);

        Self::from_u64_reduced(res)
    }

    /// Canonical branchless modular addition for `a, b < GOLDILOCKS_PRIME`.
    #[inline(always)]
    const fn add_canonical(a: u64, b: u64) -> u64 {
        let (s, c1) = a.overflowing_add(b);
        let (d, brw) = s.overflowing_sub(GOLDILOCKS_PRIME);
        let keep_s = (brw as u64) & ((!c1) as u64);
        let mask = 0u64.wrapping_sub(keep_s);
        (s & mask) | (d & !mask)
    }

    /// Canonical branchless modular subtraction for `a, b < GOLDILOCKS_PRIME`.
    #[inline(always)]
    const fn sub_canonical(a: u64, b: u64) -> u64 {
        let (diff, brw) = a.overflowing_sub(b);
        diff.wrapping_sub((0u64.wrapping_sub(brw as u64)) & EPSILON)
    }

    /// Multiply canonical `self` (`self.0 < p`) by `NON_RESIDUE = 7` without 64x64 `mulq`.
    #[inline(always)]
    pub const fn mul_by_7(self) -> Self {
        let prod = ((self.0 as u128) << 3) - (self.0 as u128);
        let lo = prod as u64;
        let hi = (prod >> 64) as u64;
        let adj = (hi << 32).wrapping_sub(hi);
        let (s, c) = lo.overflowing_add(adj);
        let s2 = s.wrapping_add((0u64.wrapping_sub(c as u64)) & EPSILON);
        Self::from_u64_reduced(s2)
    }

    #[inline(always)]
    pub const fn to_canonical_u64(self) -> u64 {
        self.0
    }

    #[inline(always)]
    pub const fn to_le_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    #[inline]
    pub const fn from_le_bytes_canonical(bytes: [u8; 8]) -> Option<Self> {
        Self::from_canonical_u64(u64::from_le_bytes(bytes))
    }

    #[inline(always)]
    pub const fn const_add(self, rhs: Self) -> Self {
        Self(Self::add_canonical(self.0, rhs.0))
    }

    #[inline(always)]
    pub const fn const_sub(self, rhs: Self) -> Self {
        Self(Self::sub_canonical(self.0, rhs.0))
    }

    /// Branchless constant-time negation in $\mathbb{F}_p$.
    #[inline(always)]
    pub const fn const_neg(self) -> Self {
        // nonzero_mask is 0xFFFF..FF when self.0 != 0, 0 when self.0 == 0.
        let nz = (self.0 | self.0.wrapping_neg()) >> 63;
        let mask = 0u64.wrapping_sub(nz);
        Self(GOLDILOCKS_PRIME.wrapping_sub(self.0) & mask)
    }

    #[inline(always)]
    pub const fn const_mul(self, rhs: Self) -> Self {
        Self::reduce128((self.0 as u128) * (rhs.0 as u128))
    }

    #[inline(always)]
    pub const fn square(self) -> Self {
        self.const_mul(self)
    }

    /// Binary exponentiation `self^exp mod p`.
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

    /// Branchless constant-time multiplicative inverse $x^{p - 2} \bmod p$ (`0 -> 0`).
    #[inline]
    pub const fn inv(self) -> Self {
        self.pow(GOLDILOCKS_PRIME - 2)
    }

    /// Primitive $2^k$-th root of unity for $k \le 32$.
    #[inline]
    pub const fn two_adic_generator(log_n: usize) -> Self {
        assert!(log_n <= 32, "Goldilocks 2-adicity is 32");
        let mut w = Self(TWO_ADIC_ROOT_OF_UNITY_32);
        let mut steps = 32 - log_n;
        while steps > 0 {
            w = w.square();
            steps -= 1;
        }
        w
    }
}

impl Add for Goldilocks {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}

impl AddAssign for Goldilocks {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}

impl Sub for Goldilocks {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}

impl SubAssign for Goldilocks {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}

impl Neg for Goldilocks {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.const_neg()
    }
}

impl Mul for Goldilocks {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}

impl MulAssign for Goldilocks {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.const_mul(rhs);
    }
}

/// Quadratic extension $\mathbb{F}_{p^2} = \mathbb{F}_p[u] / (u^2 - 7)$, $|\mathbb{F}_{p^2}| > 2^{127.99}$.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct GoldilocksExt2 {
    pub c0: Goldilocks,
    pub c1: Goldilocks,
}

impl GoldilocksExt2 {
    pub const ZERO: Self = Self {
        c0: Goldilocks::ZERO,
        c1: Goldilocks::ZERO,
    };
    pub const ONE: Self = Self {
        c0: Goldilocks::ONE,
        c1: Goldilocks::ZERO,
    };
    pub const U: Self = Self {
        c0: Goldilocks::ZERO,
        c1: Goldilocks::ONE,
    };

    #[inline]
    pub const fn new(c0: Goldilocks, c1: Goldilocks) -> Self {
        Self { c0, c1 }
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.c0.0 == 0 && self.c1.0 == 0
    }

    #[inline]
    pub const fn from_base(c0: Goldilocks) -> Self {
        Self {
            c0,
            c1: Goldilocks::ZERO,
        }
    }

    #[inline]
    pub const fn from_u64(v: u64) -> Self {
        Self::from_base(Goldilocks::from_u64_reduced(v))
    }

    #[inline]
    pub const fn to_le_bytes(self) -> [u8; 16] {
        let b0 = self.c0.to_le_bytes();
        let b1 = self.c1.to_le_bytes();
        [
            b0[0], b0[1], b0[2], b0[3], b0[4], b0[5], b0[6], b0[7], b1[0], b1[1], b1[2], b1[3],
            b1[4], b1[5], b1[6], b1[7],
        ]
    }

    #[inline]
    pub fn from_le_bytes_canonical(bytes: [u8; 16]) -> Option<Self> {
        let mut lo = [0u8; 8];
        let mut hi = [0u8; 8];
        lo.copy_from_slice(&bytes[0..8]);
        hi.copy_from_slice(&bytes[8..16]);
        let c0 = Goldilocks::from_le_bytes_canonical(lo)?;
        let c1 = Goldilocks::from_le_bytes_canonical(hi)?;
        Some(Self { c0, c1 })
    }

    #[inline(always)]
    pub const fn mul_base(self, s: Goldilocks) -> Self {
        Self {
            c0: self.c0.const_mul(s),
            c1: self.c1.const_mul(s),
        }
    }

    /// Multiply by quadratic non-residue root $u$ ($u^2 = 7$): $(c_0 + c_1 u) \cdot u = 7 c_1 + c_0 u$.
    #[inline(always)]
    pub const fn mul_by_u(self) -> Self {
        Self {
            c0: self.c1.mul_by_7(),
            c1: self.c0,
        }
    }

    /// Frobenius endomorphism $x \mapsto x^p = c_0 - c_1 u$ (since $7^{(p-1)/2} \equiv -1 \pmod p$).
    #[inline(always)]
    pub const fn frobenius(self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c1.const_neg(),
        }
    }

    /// Norm $\mathrm{N}_{\mathbb{F}_{p^2}/\mathbb{F}_p}(c_0 + c_1 u) = c_0^2 - 7 c_1^2 \in \mathbb{F}_p$.
    #[inline(always)]
    pub const fn norm_to_base(self) -> Goldilocks {
        self.c0.square().const_sub(self.c1.square().mul_by_7())
    }

    #[inline(always)]
    pub const fn square(self) -> Self {
        let a = self.c0;
        let b = self.c1;
        let ab = a.const_mul(b);
        Self {
            c0: a.square().const_add(b.square().mul_by_7()),
            c1: ab.const_add(ab),
        }
    }

    /// Branchless constant-time multiplicative inverse $(c_0 - c_1 u) / (c_0^2 - 7 c_1^2)$ (`0 -> 0`).
    #[inline]
    pub const fn inv(self) -> Self {
        let norm_inv = self.norm_to_base().inv();
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
    pub const fn const_mul(self, rhs: Self) -> Self {
        let a0b0 = self.c0.const_mul(rhs.c0);
        let a1b1 = self.c1.const_mul(rhs.c1);
        let mid = self
            .c0
            .const_add(self.c1)
            .const_mul(rhs.c0.const_add(rhs.c1))
            .const_sub(a0b0)
            .const_sub(a1b1);
        Self {
            c0: a0b0.const_add(a1b1.mul_by_7()),
            c1: mid,
        }
    }
}

impl Add for GoldilocksExt2 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}

impl AddAssign for GoldilocksExt2 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}

impl Sub for GoldilocksExt2 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}

impl SubAssign for GoldilocksExt2 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}

impl Neg for GoldilocksExt2 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.const_neg()
    }
}

impl Mul for GoldilocksExt2 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}

impl MulAssign for GoldilocksExt2 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.const_mul(rhs)
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
        let w2 = w_len * w_len;
        let w4 = w2 * w2;
        let mut wk0 = w_init;
        let mut wk1 = wk0 * w_len;
        let mut wk2 = wk0 * w2;
        let mut wk3 = wk1 * w2;
        let mut j = 0usize;
        while j + 4 <= m {
            let u0 = lo[j];
            let v0 = hi[j] * wk0;
            let u1 = lo[j + 1];
            let v1 = hi[j + 1] * wk1;
            let u2 = lo[j + 2];
            let v2 = hi[j + 2] * wk2;
            let u3 = lo[j + 3];
            let v3 = hi[j + 3] * wk3;
            lo[j] = u0 + v0;
            hi[j] = u0 - v0;
            lo[j + 1] = u1 + v1;
            hi[j + 1] = u1 - v1;
            lo[j + 2] = u2 + v2;
            hi[j + 2] = u2 - v2;
            lo[j + 3] = u3 + v3;
            hi[j + 3] = u3 - v3;
            wk0 *= w4;
            wk1 *= w4;
            wk2 *= w4;
            wk3 *= w4;
            j += 4;
        }
        while j < m {
            let u = lo[j];
            let v = hi[j] * wk0;
            lo[j] = u + v;
            hi[j] = u - v;
            wk0 *= w_len;
            j += 1;
        }
    } else {
        let mut w = w_init;
        for j in 0..m {
            let u = lo[j];
            let v = hi[j] * w;
            lo[j] = u + v;
            hi[j] = u - v;
            w *= w_len;
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

    #[cfg(feature = "std")]
    if n >= 32_768 {
        bit_reverse_permute(a);
        ntt_goldilocks_parallel_stages(a, 16);
        return;
    }

    ntt_goldilocks_serial(a);
}

#[cfg(feature = "std")]
fn ntt_goldilocks_parallel_stages(a: &mut [Goldilocks], threads: usize) {
    debug_assert!(threads.is_power_of_two() && a.len() >= threads * 2);
    let n = a.len();
    let chunk_n = n / threads;
    let chunk_stages = chunk_n.trailing_zeros() as usize;
    std::thread::scope(|scope| {
        for sub in a.chunks_mut(chunk_n) {
            scope.spawn(move || {
                let mut len = 2;
                let mut stage = 1;
                while stage <= chunk_stages {
                    let w_len = Goldilocks::two_adic_generator(stage);
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
        let w_len = Goldilocks::two_adic_generator(stage);
        for block in a.chunks_mut(len) {
            let (lo, hi) = block.split_at_mut(half);
            let sub_j = (half / threads).max(1);
            std::thread::scope(|scope| {
                for (t_idx, (lo_c, hi_c)) in
                    lo.chunks_mut(sub_j).zip(hi.chunks_mut(sub_j)).enumerate()
                {
                    let w_init = w_len.pow((t_idx * sub_j) as u64);
                    scope.spawn(move || {
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
    let n_c = coeffs.len();
    assert!(n_c.is_power_of_two());
    assert!(blowup.is_power_of_two() && blowup >= 2);
    let domain_len = n_c * blowup;

    // Coset decomposition: `B = blowup` independent size-`N` shifted NTTs (`out[q * B + r] = NTT_N(c_i * (g * w_D^r)^i)[q]`),
    // keeping each sub-NTT L2/L3-cache resident with zero cross-coset synchronization.
    #[cfg(feature = "std")]
    if domain_len >= 65_536 && n_c >= 64 && blowup >= 4 {
        let log_d = domain_len.trailing_zeros() as usize;
        let log_c = n_c.trailing_zeros() as usize;
        let rev_shift_c = usize::BITS as usize - log_c;
        let omega_d = Goldilocks::two_adic_generator(log_d);

        let mut cosets = vec![Goldilocks::ZERO; domain_len];
        if blowup >= 16 {
            let outer_threads = 16usize.min(blowup);
            let r_per_thread = blowup / outer_threads;
            std::thread::scope(|scope| {
                for (t_idx, coset_chunk) in cosets.chunks_mut(r_per_thread * n_c).enumerate() {
                    let base_r = t_idx * r_per_thread;
                    scope.spawn(move || {
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
            let inner_threads = (16 / blowup).max(1);
            std::thread::scope(|scope| {
                for (r, row) in cosets.chunks_exact_mut(n_c).enumerate() {
                    let s_r = Goldilocks::NON_RESIDUE * omega_d.pow(r as u64);
                    scope.spawn(move || {
                        let sub_c = n_c / inner_threads;
                        let mut shifted = vec![Goldilocks::ZERO; n_c];
                        std::thread::scope(|inner| {
                            for (ti, dst_s) in shifted.chunks_mut(sub_c).enumerate() {
                                let src_s = &coeffs[ti * sub_c..(ti + 1) * sub_c];
                                let mut sp = s_r.pow((ti * sub_c) as u64);
                                inner.spawn(move || {
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
                                inner.spawn(move || {
                                    for (off, slot) in dst_s.iter_mut().enumerate() {
                                        let rev = (base_i + off).reverse_bits() >> rev_shift_c;
                                        *slot = shifted_ref[rev];
                                    }
                                });
                            }
                        });
                        drop(shifted);
                        if inner_threads > 1 && n_c >= inner_threads * 2 {
                            ntt_goldilocks_parallel_stages(row, inner_threads);
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
        const T_THREADS: usize = 16;
        let q_chunk = (n_c / T_THREADS).max(1);
        let cosets_ref = &cosets;
        std::thread::scope(|scope| {
            for (ti, out_sub) in out.chunks_mut(q_chunk * blowup).enumerate() {
                let base_q = ti * q_chunk;
                scope.spawn(move || {
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
