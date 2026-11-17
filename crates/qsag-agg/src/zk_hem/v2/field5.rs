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
