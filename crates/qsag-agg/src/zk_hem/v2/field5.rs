//! Quintic extension of Goldilocks, $\mathbb{F}_{p^5} = \mathbb{F}_p[X]/(X^5 - 3)$ with
//! $p = 2^{64} - 2^{32} + 1$: the challenge field of zk-Hem v2 ($|\mathbb{F}_{p^5}| > 2^{319.99}$).
//!
//! Irreducibility: $5 \mid p - 1$ and $3^{(p-1)/5} = \zeta_5 \ne 1$, so `3` is not a fifth power in
//! $\mathbb{F}_p$; a binomial $X^\ell - c$ of prime degree $\ell \mid p - 1$ is irreducible exactly
//! when `c` is not an $\ell$-th power. Consequently $X^p = X \cdot (X^5)^{(p-1)/5} = \zeta_5 X$ and
//! the Frobenius endomorphism scales coefficient `i` by $\zeta_5^i$.
//!
//! [`Fp5`] is a flat array of five canonical base-field limbs in the power basis (there is no
//! intermediate tower, unlike `GoldilocksExt4`, whose limb order interleaves its quadratic
//! tower). The method names follow `GoldilocksExt4`; `inverse`/`norm` are additional aliases
//! of `inv`/`norm_to_base`.
//!
//! Constant-time conventions are those of `GoldilocksExt4`: products are accumulated as exact
//! 128-bit sums and reduced once per coefficient with the branchless base-field reductions,
//! inversion is fixed-work and maps zero to zero, and the only data-dependent control flow is
//! on public values (exponents, Frobenius powers, decoding of public bytes).

use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use qsag_core::field::goldilocks::GOLDILOCKS_EPSILON as EPSILON;

use crate::field::{GOLDILOCKS_PRIME, Goldilocks, GoldilocksOps};

/// The constant `3` of the defining binomial $X^5 - 3$.
pub const FP5_W: Goldilocks = Goldilocks::from_u64_reduced(3);

/// Primitive fifth root of unity $\zeta_5 = 3^{(p-1)/5} \in \mathbb{F}_p$, governing the Frobenius
/// action $X^p = \zeta_5 X$.
pub const FROBENIUS_ZETA5: Goldilocks = FP5_W.pow((GOLDILOCKS_PRIME - 1) / 5);

const _: () = assert!(FROBENIUS_ZETA5.to_canonical_u64() == 1_041_288_259_238_279_555);
const _: () = assert!(FROBENIUS_ZETA5.pow(5).to_canonical_u64() == 1);

/// `FROBENIUS_COEFFS[k][i] = zeta_5^(i * k)`: the scaling of coefficient `i` under $\phi^k$.
const FROBENIUS_COEFFS: [[Goldilocks; 5]; 5] = {
    let mut table = [[Goldilocks::ONE; 5]; 5];
    let mut k = 0;
    while k < 5 {
        let mut i = 0;
        while i < 5 {
            table[k][i] = FROBENIUS_ZETA5.pow(((i * k) % 5) as u64);
            i += 1;
        }
        k += 1;
    }
    table
};

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

/// Sum of weighted base-field products as separate low-word and high-word accumulators, so the
/// products of one output coefficient are added exactly and reduced once. The weights of one
/// accumulator may sum to at most `2^6`; a quintic coefficient uses at most `1 + 4 * 3 = 13`.
#[derive(Clone, Copy)]
struct WideAcc {
    lo: u128,
    hi: u128,
}

impl WideAcc {
    const ZERO: Self = Self { lo: 0, hi: 0 };

    #[inline(always)]
    const fn add_mul(self, a: Goldilocks, b: Goldilocks, weight: u128) -> Self {
        let prod = (a.to_canonical_u64() as u128) * (b.to_canonical_u64() as u128);
        Self {
            lo: self.lo + weight * ((prod as u64) as u128),
            hi: self.hi + weight * (prod >> 64),
        }
    }

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

/// `a * b + c` in $\mathbb{F}_p[X]/(X^5 - w)$ for a small public `w` (`1 + 4 w <= 2^6 - 1`):
/// coefficient `k` is `sum_{i+j=k} a_i b_j + w * sum_{i+j=k+5} a_i b_j`. The field uses `w = 3`;
/// the tests run the same code with `w = 2` to exhibit a zero divisor.
#[inline(always)]
const fn mul_add_binomial(
    a: [Goldilocks; 5],
    b: [Goldilocks; 5],
    c: [Goldilocks; 5],
    w: u128,
) -> [Goldilocks; 5] {
    debug_assert!(w <= 15);
    let mut out = [Goldilocks::ZERO; 5];
    let mut k = 0;
    while k < 5 {
        let mut acc = WideAcc::ZERO.add_elem(c[k]);
        let mut i = 0;
        while i < 5 {
            acc = if i <= k {
                acc.add_mul(a[i], b[k - i], 1)
            } else {
                acc.add_mul(a[i], b[k + 5 - i], w)
            };
            i += 1;
        }
        out[k] = acc.reduce();
        k += 1;
    }
    out
}

/// Element $c_0 + c_1 X + c_2 X^2 + c_3 X^3 + c_4 X^4$ of $\mathbb{F}_p[X]/(X^5 - 3)$, limbs
/// `[c0, c1, c2, c3, c4]`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Fp5(pub [Goldilocks; 5]);

impl Fp5 {
    pub const ZERO: Self = Self([Goldilocks::ZERO; 5]);
    pub const ONE: Self = Self([
        Goldilocks::ONE,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
    ]);
    /// The adjoined root `X` (`X^5 = 3`).
    pub const X: Self = Self([
        Goldilocks::ZERO,
        Goldilocks::ONE,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::ZERO,
    ]);

    /// Serialized length: five little-endian canonical `u64` limbs.
    pub const BYTES: usize = 40;
    /// Input length of [`Self::from_uniform_bytes`].
    pub const UNIFORM_BYTES: usize = 120;

    #[inline(always)]
    pub const fn from_limbs(limbs: [Goldilocks; 5]) -> Self {
        Self(limbs)
    }

    #[inline(always)]
    pub const fn to_limbs(self) -> [Goldilocks; 5] {
        self.0
    }

    #[inline(always)]
    pub const fn from_base(c0: Goldilocks) -> Self {
        Self([
            c0,
            Goldilocks::ZERO,
            Goldilocks::ZERO,
            Goldilocks::ZERO,
            Goldilocks::ZERO,
        ])
    }

    #[inline(always)]
    pub const fn from_u64(v: u64) -> Self {
        Self::from_base(Goldilocks::from_u64_reduced(v))
    }

    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        let [c0, c1, c2, c3, c4] = self.0;
        (c0.to_canonical_u64()
            | c1.to_canonical_u64()
            | c2.to_canonical_u64()
            | c3.to_canonical_u64()
            | c4.to_canonical_u64())
            == 0
    }

    /// Whether the element lies in the base field (`c1 = c2 = c3 = c4 = 0`), equivalently
    /// whether it is fixed by [`Self::frobenius`].
    #[inline(always)]
    pub const fn is_base(self) -> bool {
        let [_, c1, c2, c3, c4] = self.0;
        (c1.to_canonical_u64()
            | c2.to_canonical_u64()
            | c3.to_canonical_u64()
            | c4.to_canonical_u64())
            == 0
    }

    #[inline]
    pub const fn to_le_bytes(self) -> [u8; 40] {
        let mut out = [0u8; 40];
        let mut i = 0;
        while i < 5 {
            let w = self.0[i].to_le_bytes();
            let mut k = 0;
            while k < 8 {
                out[8 * i + k] = w[k];
                k += 1;
            }
            i += 1;
        }
        out
    }

    /// Strict decoding: `None` if any of the five little-endian limbs is `>= p`.
    ///
    /// Applied to 40 uniform bytes this is the per-limb rejection rule of the v1 transcript and
    /// seed streams: an accepted element is exactly uniform, and a draw is rejected with
    /// probability $1 - (p / 2^{64})^5 < 2^{-29.6}$.
    #[inline]
    pub fn from_le_bytes_canonical(bytes: [u8; 40]) -> Option<Self> {
        let mut limbs = [Goldilocks::ZERO; 5];
        for (limb, word) in limbs.iter_mut().zip(bytes.as_chunks::<8>().0) {
            *limb = Goldilocks::from_canonical_u64(u64::from_le_bytes(*word))?;
        }
        Some(Self(limbs))
    }

    /// Rejection-free sampling from 120 uniform bytes: limb `i` is the 192-bit little-endian
    /// integer `bytes[24 i .. 24 i + 24]` reduced modulo `p`.
    ///
    /// Since $2^{192} \equiv 1 \pmod p$, each limb is within statistical distance
    /// $(p - 1) / (p \cdot 2^{192}) < 2^{-192}$ of uniform, and the element within
    /// $5 \cdot 2^{-192} < 2^{-189}$ of uniform on $\mathbb{F}_{p^5}$. Fixed work, no branches.
    #[inline]
    pub fn from_uniform_bytes(bytes: &[u8; 120]) -> Self {
        let mut limbs = [Goldilocks::ZERO; 5];
        for (limb, wide) in limbs.iter_mut().zip(bytes.as_chunks::<24>().0) {
            *limb = Goldilocks::from_bytes24_unbiased(wide);
        }
        Self(limbs)
    }

    #[inline(always)]
    pub const fn mul_base(self, s: Goldilocks) -> Self {
        let z = WideAcc::ZERO;
        let [c0, c1, c2, c3, c4] = self.0;
        Self([
            z.add_mul(c0, s, 1).reduce(),
            z.add_mul(c1, s, 1).reduce(),
            z.add_mul(c2, s, 1).reduce(),
            z.add_mul(c3, s, 1).reduce(),
            z.add_mul(c4, s, 1).reduce(),
        ])
    }

    #[inline(always)]
    pub const fn const_add(self, rhs: Self) -> Self {
        let (a, b) = (self.0, rhs.0);
        Self([
            a[0].const_add(b[0]),
            a[1].const_add(b[1]),
            a[2].const_add(b[2]),
            a[3].const_add(b[3]),
            a[4].const_add(b[4]),
        ])
    }

    #[inline(always)]
    pub const fn const_sub(self, rhs: Self) -> Self {
        let (a, b) = (self.0, rhs.0);
        Self([
            a[0].const_sub(b[0]),
            a[1].const_sub(b[1]),
            a[2].const_sub(b[2]),
            a[3].const_sub(b[3]),
            a[4].const_sub(b[4]),
        ])
    }

    #[inline(always)]
    pub const fn const_neg(self) -> Self {
        Self::ZERO.const_sub(self)
    }

    #[inline(always)]
    pub const fn double(self) -> Self {
        self.const_add(self)
    }

    /// Product in $\mathbb{F}_p[X]/(X^5 - 3)$: the twenty-five 128-bit products are accumulated
    /// exactly and each coefficient is reduced once.
    #[inline(always)]
    pub const fn const_mul(self, rhs: Self) -> Self {
        self.mul_add(rhs, Self::ZERO)
    }

    /// `self * rhs + addend` with one reduction per coefficient.
    #[inline(always)]
    pub const fn mul_add(self, rhs: Self, addend: Self) -> Self {
        Self(mul_add_binomial(self.0, rhs.0, addend.0, 3))
    }

    /// Square: the fifteen distinct products, cross terms doubled, one reduction per coefficient.
    #[inline(always)]
    pub const fn square(self) -> Self {
        let [a0, a1, a2, a3, a4] = self.0;
        let z = WideAcc::ZERO;
        let p0 = z.add_mul(a0, a0, 1).add_mul(a1, a4, 6).add_mul(a2, a3, 6);
        let p1 = z.add_mul(a0, a1, 2).add_mul(a2, a4, 6).add_mul(a3, a3, 3);
        let p2 = z.add_mul(a0, a2, 2).add_mul(a1, a1, 1).add_mul(a3, a4, 6);
        let p3 = z.add_mul(a0, a3, 2).add_mul(a1, a2, 2).add_mul(a4, a4, 3);
        let p4 = z.add_mul(a0, a4, 2).add_mul(a1, a3, 2).add_mul(a2, a2, 1);
        Self([
            p0.reduce(),
            p1.reduce(),
            p2.reduce(),
            p3.reduce(),
            p4.reduce(),
        ])
    }

    /// Frobenius endomorphism $\phi(x) = x^p$: $c_i \mapsto \zeta_5^i c_i$.
    #[inline(always)]
    pub const fn frobenius(self) -> Self {
        self.frobenius_pow(1)
    }

    /// $\phi^k(x) = x^{p^k}$ for a public `k` (taken modulo 5): $c_i \mapsto \zeta_5^{i k} c_i$.
    #[inline(always)]
    pub const fn frobenius_pow(self, k: usize) -> Self {
        let z = WideAcc::ZERO;
        let t = &FROBENIUS_COEFFS[k % 5];
        let [c0, c1, c2, c3, c4] = self.0;
        Self([
            c0,
            z.add_mul(c1, t[1], 1).reduce(),
            z.add_mul(c2, t[2], 1).reduce(),
            z.add_mul(c3, t[3], 1).reduce(),
            z.add_mul(c4, t[4], 1).reduce(),
        ])
    }

    /// $x^{p + p^2 + p^3 + p^4} = \phi(x) \phi^2(x) \phi^3(x) \phi^4(x)$ in two multiplications:
    /// with $t = \phi(x) \cdot \phi^2(x)$ it is $t \cdot \phi^2(t)$.
    #[inline(always)]
    const fn conjugate_product(self) -> Self {
        let f1 = self.frobenius_pow(1);
        let t = f1.const_mul(f1.frobenius_pow(1));
        t.const_mul(t.frobenius_pow(2))
    }

    /// `c0` coordinate of `self * rhs`.
    #[inline(always)]
    const fn mul_c0(self, rhs: Self) -> Goldilocks {
        let (a, b) = (self.0, rhs.0);
        WideAcc::ZERO
            .add_mul(a[0], b[0], 1)
            .add_mul(a[1], b[4], 3)
            .add_mul(a[2], b[3], 3)
            .add_mul(a[3], b[2], 3)
            .add_mul(a[4], b[1], 3)
            .reduce()
    }

    /// Absolute norm $\mathrm{N}(x) = x^{1 + p + p^2 + p^3 + p^4} \in \mathbb{F}_p$.
    #[inline(always)]
    pub const fn norm_to_base(self) -> Goldilocks {
        self.mul_c0(self.conjugate_product())
    }

    /// Alias of [`Self::norm_to_base`].
    #[inline(always)]
    pub const fn norm(self) -> Goldilocks {
        self.norm_to_base()
    }

    /// Branchless fixed-work Itoh-Tsujii inverse $x^{p + p^2 + p^3 + p^4} / \mathrm{N}(x)$
    /// (`0 -> 0`): two extension multiplications, one base-field inversion, one scaling.
    #[inline]
    pub const fn inv(self) -> Self {
        let conj = self.conjugate_product();
        conj.mul_base(self.mul_c0(conj).inv_or_zero())
    }

    /// Alias of [`Self::inv`].
    #[inline]
    pub const fn inverse(self) -> Self {
        self.inv()
    }

    /// Public-exponent binary exponentiation.
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

    /// Public-exponent binary exponentiation for an exponent given as little-endian `u64` limbs.
    #[inline]
    pub const fn pow_limbs(self, exp: &[u64]) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        let mut i = 0;
        while i < exp.len() {
            let mut word = exp[i];
            let mut bit = 0;
            while bit < 64 {
                if (word & 1) == 1 {
                    acc = acc.const_mul(base);
                }
                base = base.square();
                word >>= 1;
                bit += 1;
            }
            i += 1;
        }
        acc
    }
}

impl Add for Fp5 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}

impl AddAssign for Fp5 {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}

impl Sub for Fp5 {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}

impl SubAssign for Fp5 {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}

impl Neg for Fp5 {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        self.const_neg()
    }
}

impl Mul for Fp5 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}

impl MulAssign for Fp5 {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.const_mul(rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::GoldilocksExt4;

    const P: u64 = GOLDILOCKS_PRIME;

    /// SplitMix64.
    struct Rng(u64);

    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn base(&mut self) -> Goldilocks {
            Goldilocks::from_u64_reduced(self.next_u64())
        }

        fn fp5(&mut self) -> Fp5 {
            Fp5(core::array::from_fn(|_| self.base()))
        }
    }

    fn el(limbs: [u64; 5]) -> Fp5 {
        Fp5(limbs.map(|v| Goldilocks::from_canonical(v).expect("canonical test limb")))
    }

    fn g(v: u64) -> Goldilocks {
        Goldilocks::from_u64_reduced(v)
    }

    /// Schoolbook product through the base-field operators: 25 reduced products, the wrapped
    /// ones scaled by `w`.
    fn mul_reference(a: Fp5, b: Fp5, w: Goldilocks) -> Fp5 {
        let mut out = [Goldilocks::ZERO; 5];
        for i in 0..5 {
            for j in 0..5 {
                let prod = a.0[i] * b.0[j];
                if i + j < 5 {
                    out[i + j] += prod;
                } else {
                    out[i + j - 5] += prod * w;
                }
            }
        }
        Fp5(out)
    }

    const KAT_A: [u64; 5] = [1, 2, 3, 4, 5];
    const KAT_B: [u64; 5] = [6, 7, 8, 9, 10];

    #[test]
    fn known_answers_match_independent_python() {
        let (a, b) = (el(KAT_A), el(KAT_B));
        assert_eq!(a * b, el([348, 337, 295, 220, 110]));
        assert_eq!(a.square(), el([133, 142, 130, 95, 35]));
        assert_eq!(
            a.frobenius(),
            el([
                1,
                2_082_576_518_476_559_110,
                10_568_986_813_412_808_496,
                846_350_220_555_798_788,
                6_865_216_354_783_480_110,
            ])
        );
        assert_eq!(
            a.inverse(),
            el([
                16_227_807_958_868_272_813,
                4_552_730_750_487_813_724,
                11_612_833_514_307_017_418,
                9_161_515_214_422_980_997,
                13_509_202_856_671_625_680,
            ])
        );
        assert_eq!(a.norm(), g(214_567));
    }

    #[test]
    fn generator_fifth_power_is_three() {
        assert_eq!(Fp5::X.pow(5), Fp5::from_u64(3));
        assert_eq!(Fp5::X.pow(5), Fp5::from_base(FP5_W));
        assert_eq!(Fp5::X * Fp5::X, el([0, 0, 1, 0, 0]));
        assert_ne!(Fp5::X.pow(4), Fp5::from_u64(3));
    }

    #[test]
    fn ring_laws_on_random_elements() {
        let mut rng = Rng(0x5eed_0001);
        for _ in 0..200 {
            let (a, b, c) = (rng.fp5(), rng.fp5(), rng.fp5());
            assert_eq!((a * b) * c, a * (b * c));
            assert_eq!(a * b, b * a);
            assert_eq!(a * (b + c), a * b + a * c);
            assert_eq!((a + b) + c, a + (b + c));
            assert_eq!(a + b, b + a);
            assert_eq!(a - b, a + (-b));
            assert_eq!(a + (-a), Fp5::ZERO);
            assert_eq!(a * Fp5::ONE, a);
            assert_eq!(a * Fp5::ZERO, Fp5::ZERO);
            assert_eq!(a.double(), a + a);
            assert_eq!(a.mul_add(b, c), a * b + c);
        }
    }

    #[test]
    fn lazy_product_and_square_match_schoolbook_reference() {
        let mut rng = Rng(0x5eed_0002);
        let top = el([P - 1; 5]);
        assert_eq!(top * top, mul_reference(top, top, FP5_W));
        assert_eq!(top.square(), mul_reference(top, top, FP5_W));
        assert_eq!(top.mul_add(top, top), mul_reference(top, top, FP5_W) + top);
        for _ in 0..2000 {
            let (a, b) = (rng.fp5(), rng.fp5());
            assert_eq!(a * b, mul_reference(a, b, FP5_W));
            assert_eq!(a.square(), mul_reference(a, a, FP5_W));
        }
    }

    #[test]
    fn assign_operators_match_binary_operators() {
        let mut rng = Rng(0x5eed_0003);
        let (a, b) = (rng.fp5(), rng.fp5());
        let mut x = a;
        x += b;
        assert_eq!(x, a + b);
        x = a;
        x -= b;
        assert_eq!(x, a - b);
        x = a;
        x *= b;
        assert_eq!(x, a * b);
    }

    #[test]
    fn mul_base_matches_embedding() {
        let mut rng = Rng(0x5eed_0004);
        for _ in 0..200 {
            let (a, s) = (rng.fp5(), rng.base());
            assert_eq!(a.mul_base(s), a * Fp5::from_base(s));
        }
        let top = el([P - 1; 5]);
        assert_eq!(top.mul_base(g(P - 1)), top * Fp5::from_base(g(P - 1)));
    }

    #[test]
    fn frobenius_is_pth_power() {
        let mut rng = Rng(0x5eed_0005);
        for _ in 0..32 {
            let a = rng.fp5();
            assert_eq!(a.frobenius(), a.pow(P));
        }
    }

    #[test]
    fn frobenius_powers_compose_and_have_order_five() {
        let mut rng = Rng(0x5eed_0006);
        for _ in 0..64 {
            let a = rng.fp5();
            let mut acc = a;
            for k in 0..=7usize {
                assert_eq!(a.frobenius_pow(k), acc, "k = {k}");
                acc = acc.frobenius();
            }
            assert_eq!(a.frobenius_pow(5), a);
            // A generic element is moved by every nontrivial power.
            if !a.is_base() {
                for k in 1..5 {
                    assert_ne!(a.frobenius_pow(k), a);
                }
            }
            let b = rng.fp5();
            assert_eq!((a * b).frobenius(), a.frobenius() * b.frobenius());
        }
    }

    #[test]
    fn inverse_of_random_nonzero_elements() {
        let mut rng = Rng(0x5eed_0007);
        let mut checked = 0;
        for _ in 0..500 {
            let a = rng.fp5();
            if a.is_zero() {
                continue;
            }
            assert_eq!(a * a.inverse(), Fp5::ONE);
            assert_eq!(a.inverse(), a.inv());
            checked += 1;
        }
        assert_eq!(checked, 500);
        for k in 0..5 {
            let mut limbs = [0u64; 5];
            limbs[k] = 1 + k as u64;
            let a = el(limbs);
            assert_eq!(a * a.inverse(), Fp5::ONE);
        }
        assert_eq!(Fp5::ZERO.inverse(), Fp5::ZERO);
        assert_eq!(Fp5::ONE.inverse(), Fp5::ONE);
    }

    /// The same multiplication code with reduction constant `2` is not a field: `2 = t^5` in
    /// `F_p`, so `X - t` divides `X^5 - 2` and is a zero divisor there. With constant `3` the same
    /// pair multiplies to `X^5 - t^5 = 3 - 2 = 1`.
    #[test]
    fn reduction_constant_two_has_a_zero_divisor() {
        let t = g(35_184_372_080_640);
        assert_eq!(t.pow(5), g(2));
        let lin = Fp5([-t, Goldilocks::ONE, g(0), g(0), g(0)]);
        let cofactor = Fp5([t.pow(4), t.pow(3), t.pow(2), t, Goldilocks::ONE]);
        assert!(!lin.is_zero() && !cofactor.is_zero());

        let with_two = Fp5(mul_add_binomial(lin.0, cofactor.0, Fp5::ZERO.0, 2));
        assert_eq!(with_two, Fp5::ZERO);
        assert_eq!(with_two, mul_reference(lin, cofactor, g(2)));

        assert_eq!(lin * cofactor, Fp5::ONE);
        assert_eq!(lin.inverse(), cofactor);
    }

    #[test]
    fn norm_is_multiplicative_and_matches_power() {
        let mut rng = Rng(0x5eed_0008);
        for _ in 0..64 {
            let (a, b) = (rng.fp5(), rng.fp5());
            assert_eq!((a * b).norm(), a.norm() * b.norm());
            let product = a
                * a.frobenius_pow(1)
                * a.frobenius_pow(2)
                * a.frobenius_pow(3)
                * a.frobenius_pow(4);
            assert!(product.is_base());
            assert_eq!(product, Fp5::from_base(a.norm()));
            assert_eq!(a.norm(), a.norm_to_base());
            let s = rng.base();
            assert_eq!(Fp5::from_base(s).norm(), s.pow(5));
        }
        assert_eq!(Fp5::ZERO.norm(), Goldilocks::ZERO);
        assert_eq!(Fp5::X.norm(), g(3));
    }

    #[test]
    fn is_base_iff_fixed_by_frobenius() {
        let mut rng = Rng(0x5eed_0009);
        let mut samples = alloc::vec![Fp5::ZERO, Fp5::ONE, Fp5::X, Fp5::from_u64(P - 1)];
        for k in 1..5 {
            let mut limbs = [7u64, 0, 0, 0, 0];
            limbs[k] = 1;
            samples.push(el(limbs));
        }
        for _ in 0..64 {
            samples.push(Fp5::from_base(rng.base()));
            samples.push(rng.fp5());
        }
        let mut seen = [0usize; 2];
        for a in samples {
            assert_eq!(a.is_base(), a.frobenius() == a, "{a:?}");
            seen[a.is_base() as usize] += 1;
        }
        assert!(seen[0] >= 64 && seen[1] >= 64);
    }

    #[test]
    fn pow_agrees_with_repeated_multiplication_and_fermat() {
        let mut rng = Rng(0x5eed_000a);
        let a = rng.fp5();
        let mut acc = Fp5::ONE;
        for e in 0..40u64 {
            assert_eq!(a.pow(e), acc);
            assert_eq!(a.pow_limbs(&[e]), acc);
            acc *= a;
        }
        assert_eq!(a.pow_limbs(&[]), Fp5::ONE);
        assert_eq!(a.pow_limbs(&[0, 1]), a.pow(1 << 32).pow(1 << 32));
        // `p^5 - 1`, little-endian limbs.
        let order = [
            0xffff_fffb_0000_0000u64,
            0xffff_ffe2_0000_000e,
            0xffff_ffcd_0000_002c,
            0xffff_ffe2_0000_002c,
            0xffff_fffb_0000_000e,
        ];
        assert_eq!(a.pow_limbs(&order), Fp5::ONE);
        let mut short = order;
        short[4] -= 1;
        assert_ne!(a.pow_limbs(&short), Fp5::ONE);
    }

    #[test]
    fn byte_round_trip_and_canonical_decoding() {
        let mut rng = Rng(0x5eed_000b);
        for _ in 0..200 {
            let a = rng.fp5();
            assert_eq!(Fp5::from_le_bytes_canonical(a.to_le_bytes()), Some(a));
        }
        let a = el([1, 2, 3, 4, 0x0102_0304_0506_0708]);
        let bytes = a.to_le_bytes();
        assert_eq!(&bytes[..9], &[1, 0, 0, 0, 0, 0, 0, 0, 2]);
        assert_eq!(&bytes[32..], &[8, 7, 6, 5, 4, 3, 2, 1]);

        for k in 0..5 {
            let mut raw = [0u8; 40];
            let slot = 8 * k..8 * k + 8;
            raw[slot.clone()].copy_from_slice(&(P - 1).to_le_bytes());
            let top = Fp5::from_le_bytes_canonical(raw).expect("p - 1 is canonical");
            assert_eq!(top.0[k], g(P - 1));
            raw[slot.clone()].copy_from_slice(&P.to_le_bytes());
            assert_eq!(Fp5::from_le_bytes_canonical(raw), None);
            raw[slot.clone()].copy_from_slice(&(P + 1).to_le_bytes());
            assert_eq!(Fp5::from_le_bytes_canonical(raw), None);
            raw[slot].copy_from_slice(&u64::MAX.to_le_bytes());
            assert_eq!(Fp5::from_le_bytes_canonical(raw), None);
        }
    }

    #[test]
    fn uniform_bytes_reduce_each_192_bit_limb() {
        // Python: `int.from_bytes(bs[24 i : 24 i + 24], "little") % p`, `bs[i] = (7 i + 3) & 0xff`.
        let bytes: [u8; 120] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        assert_eq!(
            Fp5::from_uniform_bytes(&bytes),
            el([
                6_293_595_035_447_328_769,
                6_438_275_381_089_795_839,
                6_293_595_035_447_328_769,
                6_293_595_035_447_329_025,
                6_438_275_381_089_730_303,
            ])
        );
        // `2^192 - 1 = 0 mod p` in every limb, and `2^96 = -1 mod p` in limb 2.
        assert_eq!(Fp5::from_uniform_bytes(&[0xff; 120]), Fp5::ZERO);
        let mut bytes = [0u8; 120];
        bytes[2 * 24 + 12] = 1;
        assert_eq!(Fp5::from_uniform_bytes(&bytes), el([0, 0, P - 1, 0, 0]));
    }

    #[test]
    fn default_constants_and_wiping() {
        assert_eq!(Fp5::default(), Fp5::ZERO);
        assert!(Fp5::ZERO.is_zero() && !Fp5::ONE.is_zero() && !Fp5::X.is_zero());
        for k in 0..5 {
            let mut limbs = [0u64; 5];
            limbs[k] = 1;
            assert!(!el(limbs).is_zero());
        }
        assert_eq!(Fp5::from_limbs(el(KAT_A).to_limbs()), el(KAT_A));
        assert_eq!(Fp5::from_u64(P + 4), Fp5::from_base(g(4)));

        let mut rng = Rng(0x5eed_000c);
        let mut secret = [rng.fp5(), rng.fp5(), rng.fp5()];
        assert!(secret.iter().all(|x| !x.is_zero()));
        qsag_asm::volatile_fill(&mut secret, Fp5::ZERO);
        assert!(secret.iter().all(|x| x.is_zero()));
    }

    /// Dependent-chain multiplication timing: `Fp5` lazy product, the schoolbook reference and
    /// `GoldilocksExt4`. Run with `--release -- --ignored --nocapture`.
    #[test]
    #[ignore = "micro-benchmark"]
    fn bench_mul_against_reference_and_ext4() {
        use std::hint::black_box;
        use std::time::Instant;

        const ITERS: u32 = 4_000_000;
        let mut rng = Rng(0x5eed_00be);
        let (a5, b5) = (rng.fp5(), rng.fp5());
        let a4 = GoldilocksExt4::from_limbs(core::array::from_fn(|_| rng.base()));
        let b4 = GoldilocksExt4::from_limbs(core::array::from_fn(|_| rng.base()));

        let time = |f: &mut dyn FnMut()| {
            let mut best = f64::INFINITY;
            for _ in 0..5 {
                let t = Instant::now();
                f();
                best = best.min(t.elapsed().as_secs_f64());
            }
            best * 1e9 / f64::from(ITERS)
        };

        let mut lazy = Fp5::ZERO;
        let lazy_ns = time(&mut || {
            let (mut x, y) = (black_box(a5), black_box(b5));
            for _ in 0..ITERS {
                x *= y;
            }
            lazy = black_box(x);
        });
        let mut reference = Fp5::ZERO;
        let reference_ns = time(&mut || {
            let (mut x, y) = (black_box(a5), black_box(b5));
            for _ in 0..ITERS {
                x = mul_reference(x, y, FP5_W);
            }
            reference = black_box(x);
        });
        let square_ns = time(&mut || {
            let mut x = black_box(a5);
            for _ in 0..ITERS {
                x = x.square();
            }
            black_box(x);
        });
        let ext4_ns = time(&mut || {
            let (mut x, y) = (black_box(a4), black_box(b4));
            for _ in 0..ITERS {
                x *= y;
            }
            black_box(x);
        });
        let inv_ns = time(&mut || {
            let mut x = black_box(a5);
            for _ in 0..ITERS / 100 {
                x = x.inv() + a5;
            }
            black_box(x);
        }) * 100.0;

        assert_eq!(lazy, reference);
        std::println!(
            "fp5 mul {lazy_ns:.2} ns | fp5 schoolbook reference {reference_ns:.2} ns | \
             fp5 square {square_ns:.2} ns | ext4 mul {ext4_ns:.2} ns | fp5 inv {inv_ns:.1} ns"
        );
    }
}
