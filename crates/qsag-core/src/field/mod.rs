//! Finite field arithmetic for `qsag-core`:
//! - [`goldilocks`]: Canonical 64-bit Goldilocks prime field ($\mathbb{F}_p, p = 2^{64} - 2^{32} + 1$)
//!   and 128-bit quadratic challenge/MAC extension `GoldilocksExt2` ($\mathbb{F}_p\[u\]/(u^2 - 7)$).
//! - [`tower`]: Wiedemann binary tower $\mathcal{T}_0 \dots \mathcal{T}_7$ (`TowerGf256` = $\mathbb{F}_{2^8}$,
//!   `Tower128` = $\mathbb{F}_{2^{128}}$), `PublicGf256Matrix` Four-Russians public-scalar bitslice
//!   multiplier, and constant-time secret-scalar multiplier.

pub mod goldilocks;
pub mod tower;
