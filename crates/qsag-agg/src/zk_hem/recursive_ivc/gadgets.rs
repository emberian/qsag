//! Shared R1CS and native Goldilocks wire gadgets for [`super`] (`recursive_ivc`).
//!
//! Every comparison and bit-decomposition gadget synthesizes a fixed constraint shape
//! independent of witness values; values choose only wire assignments.

use alloc::vec::Vec;

use crate::field::{GOLDILOCKS_PRIME, Goldilocks as F};
use crate::zk_hem::relation::{ConstraintSystem, Lc};

#[inline]
pub(crate) fn f(v: u64) -> F {
    F::from_u64_reduced(v)
}

pub(crate) trait Base: Clone {
    fn constant(v: F) -> Self;
    fn plus(&self, rhs: &Self) -> Self;
    fn minus(&self, rhs: &Self) -> Self;
    fn scale(&self, k: F) -> Self;
}

impl Base for F {
    fn constant(v: F) -> Self {
        v
    }
    fn plus(&self, rhs: &Self) -> Self {
        *self + *rhs
    }
    fn minus(&self, rhs: &Self) -> Self {
        *self - *rhs
    }
    fn scale(&self, k: F) -> Self {
        self.const_mul(k)
    }
}

impl Base for Lc {
    fn constant(v: F) -> Self {
        Lc::constant(v)
    }
    fn plus(&self, rhs: &Self) -> Self {
        self.plus(rhs)
    }
    fn minus(&self, rhs: &Self) -> Self {
        self.minus(rhs)
    }
    fn scale(&self, k: F) -> Self {
        self.scaled(k)
    }
}

pub(crate) trait Backend {
    type W: Base;
    fn alloc(&mut self, v: F) -> Self::W;
    fn value(&self, v: &Self::W) -> F;
    fn mul(&mut self, a: &Self::W, b: &Self::W) -> Self::W;
    fn equal(&mut self, a: &Self::W, b: &Self::W);
    /// One row `a * b = c` without a fresh product variable.
    fn product(&mut self, a: &Self::W, b: &Self::W, c: &Self::W);
    fn pin(&mut self, v: Self::W) -> Self::W {
        let out = self.alloc(self.value(&v));
        self.equal(&out, &v);
        out
    }
}

#[derive(Default)]
pub(crate) struct Native {
    pub(crate) failed: bool,
}

impl Backend for Native {
    type W = F;
    fn alloc(&mut self, v: F) -> F {
        v
    }
    fn value(&self, v: &F) -> F {
        *v
    }
    fn mul(&mut self, a: &F, b: &F) -> F {
        a.const_mul(*b)
    }
    fn equal(&mut self, a: &F, b: &F) {
        self.failed |= a != b;
    }
    fn product(&mut self, a: &F, b: &F, c: &F) {
        self.failed |= a.const_mul(*b) != *c;
    }
    fn pin(&mut self, v: F) -> F {
        v
    }
}

impl Backend for ConstraintSystem {
    type W = Lc;
    fn alloc(&mut self, v: F) -> Lc {
        ConstraintSystem::alloc(self, v).into()
    }
    fn value(&self, v: &Lc) -> F {
        self.eval(v)
    }
    fn mul(&mut self, a: &Lc, b: &Lc) -> Lc {
        ConstraintSystem::mul(self, a, b).into()
    }
    fn equal(&mut self, a: &Lc, b: &Lc) {
        self.enforce_equal(a, b);
    }
    fn product(&mut self, a: &Lc, b: &Lc, c: &Lc) {
        self.enforce_mul(a.clone(), b.clone(), c.clone());
    }
}

/// Little-endian Boolean decomposition. Below 64 bits the integer sum cannot reach `p`;
/// at 64 bits the alias `x + p` is excluded explicitly (`!(hi32 == 0xFFFF_FFFF && lo32 != 0)`).
pub(crate) fn bits<B: Backend>(b: &mut B, value: &B::W, n: usize) -> Vec<B::W> {
    assert!(n <= 64);
    let raw = b.value(value).to_canonical_u64();
    let zero = B::W::constant(F::ZERO);
    let one = B::W::constant(F::ONE);
    let out: Vec<_> = (0..n)
        .map(|i| {
            let v = b.alloc(f((raw >> i) & 1));
            b.product(&v, &one.minus(&v), &zero);
            v
        })
        .collect();
    let weighted = |bits: &[B::W]| {
        bits.iter()
            .enumerate()
            .fold(zero.clone(), |a, (i, bit)| a.plus(&bit.scale(f(1u64 << i))))
    };
    b.equal(value, &weighted(&out));
    if n == 64 {
        // p = 2^64 - 2^32 + 1: when the high 32 bits are all one, the low 32 must be zero.
        let mut high = out[32].clone();
        for v in &out[33..] {
            high = b.mul(&high, v);
        }
        b.product(&high, &weighted(&out[..32]), &zero);
    }
    out
}

/// Canonical 64-bit little-endian Boolean decomposition strictly below `GOLDILOCKS_PRIME`
/// (`!(hi32 == 0xFFFF_FFFF && lo32 != 0)`), preventing `x + p` field-to-byte aliasing.
pub(crate) fn bits_canonical_u64<B: Backend>(b: &mut B, value: &B::W) -> [B::W; 64] {
    bits(b, value, 64)
        .try_into()
        .unwrap_or_else(|_| unreachable!("bits(..., 64) always returns 64 wires"))
}

pub(crate) fn equal_bit<B: Backend>(b: &mut B, a: &B::W, c: &B::W) -> B::W {
    let d = a.minus(c);
    let v = b.value(&d);
    let eq = b.alloc(if v == F::ZERO { F::ONE } else { F::ZERO });
    let inv = b.alloc(v.inv_or_zero());
    b.product(&d, &eq, &B::W::constant(F::ZERO));
    b.product(&d, &inv, &B::W::constant(F::ONE).minus(&eq));
    eq
}

/// `0 <= v <= max` as integers, with a bitwise comparison to the public bound.
fn bounded<B: Backend>(b: &mut B, v: &B::W, max: u64) {
    let n = (64 - max.leading_zeros()) as usize;
    assert!(n < 64);
    let binary = bits(b, v, n);
    let mut prefix = B::W::constant(F::ONE);
    let mut first = true;
    for i in (0..n).rev() {
        if max & ((1u64 << (i + 1)) - 1) == (1u64 << (i + 1)) - 1 {
            break;
        }
        if (max >> i) & 1 == 1 {
            prefix = if first {
                binary[i].clone()
            } else {
                b.mul(&prefix, &binary[i])
            };
            first = false;
        } else {
            b.product(&prefix, &binary[i], &B::W::constant(F::ZERO));
        }
    }
}

pub(crate) fn select<B: Backend>(b: &mut B, bit: &B::W, yes: &B::W, no: &B::W) -> B::W {
    let delta = yes.minus(no);
    let out = b.alloc(b.value(no) + b.value(bit).const_mul(b.value(&delta)));
    b.product(bit, &delta, &out.minus(no));
    out
}

/// Canonical integer remainder of a uniform field challenge; quotient and remainder bounds
/// exclude modular wrap (`<= ceil(p / divisor)` preimages per remainder).
pub(super) fn remainder<B: Backend>(b: &mut B, word: &B::W, divisor: u64) -> B::W {
    if divisor.is_power_of_two() {
        let binary = bits(b, word, 64);
        return binary[..divisor.trailing_zeros() as usize]
            .iter()
            .enumerate()
            .fold(B::W::constant(F::ZERO), |a, (i, bit)| {
                a.plus(&bit.scale(f(1u64 << i)))
            });
    }
    let raw = b.value(word).to_canonical_u64();
    let q = b.alloc(f(raw / divisor));
    let r = b.alloc(f(raw % divisor));
    let max = (GOLDILOCKS_PRIME - 1) / divisor;
    bounded(b, &q, max);
    let n = (64 - (divisor - 1).leading_zeros()) as usize;
    bits(b, &r, n);
    let at_max = equal_bit(b, &q, &B::W::constant(f(max)));
    let tail = (GOLDILOCKS_PRIME - 1) % divisor;
    let bound = B::W::constant(f(divisor - 1)).minus(&at_max.scale(f(divisor - 1 - tail)));
    let slack = b.alloc(f(b
        .value(&bound)
        .to_canonical_u64()
        .saturating_sub(raw % divisor)));
    bits(b, &slack, n);
    b.equal(&r.plus(&slack), &bound);
    b.equal(word, &q.scale(f(divisor)).plus(&r));
    r
}
