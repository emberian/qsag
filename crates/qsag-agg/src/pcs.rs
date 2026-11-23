//! Shared Quintic `Fp5` WHIR stage-folding geometry, multilinear Möbius transforms, and
//! bounded parallel slice fill helpers used by [`crate::hem_quintic`], [`crate::zk_hem::v2`],
//! and [`crate::zk_hem::recursive_ivc`].

use alloc::vec;
use alloc::vec::Vec;

use crate::field::Goldilocks;

/// Maximum multilinear polynomial dimension (`2^28` cells, unlocked by `[DKT26]` Theorem 5.12).
pub const MAX_PCS_NUM_VARS: usize = 28;

/// Maximum terminal polynomial variables sent in full (`2^8 = 256` coefficients).
pub const EARLY_STOP_VARS: usize = 8;

/// Maximum multilinear variables folded in a single WHIR stage (`<= 6`).
pub const MAX_FOLD_STEP_VARS: usize = 6;

/// Canonical WHIR stage-folding geometry `(early_stop_vars, vec![(blowup, step_vars), ...])`
/// for a `num_vars`-variable multilinear polynomial (`2 <= num_vars <= MAX_PCS_NUM_VARS`).
pub(crate) fn stage_geometry(num_vars: usize) -> (usize, Vec<(usize, usize)>) {
    assert!(
        (2..=MAX_PCS_NUM_VARS).contains(&num_vars),
        "unsupported PCS num_vars={num_vars}"
    );
    if num_vars <= 6 {
        let es = if num_vars <= 3 { 1 } else { 2 };
        return (es, vec![(16, num_vars - es)]);
    }
    if num_vars <= 11 {
        let es = if num_vars <= 8 { 3 } else { 4 };
        let rem = num_vars - es;
        let s0 = rem.div_ceil(2);
        let s1 = rem - s0;
        return (es, vec![(4, s0), (16, s1)]);
    }
    if num_vars <= 16 {
        let es = if num_vars <= 13 {
            4
        } else if num_vars <= 15 {
            5
        } else {
            6
        };
        let rem = num_vars - es;
        let s0 = 4usize.min(rem - 4);
        let s1 = (rem - s0) / 2;
        let s2 = rem - s0 - s1;
        return (es, vec![(4, s0), (16, s1), (64, s2)]);
    }
    if num_vars <= 20 {
        let es = num_vars - 12;
        return (es, vec![(4, 5), (16, 3), (64, 4)]);
    }
    match num_vars {
        21 => (8, vec![(4, 6), (16, 3), (64, 4)]),
        22 => (8, vec![(4, 6), (16, 4), (64, 4)]),
        23 => (7, vec![(4, 6), (16, 4), (64, 3), (256, 3)]),
        24 => (8, vec![(4, 6), (16, 4), (64, 3), (256, 3)]),
        25 => (8, vec![(4, 6), (16, 4), (64, 4), (256, 3)]),
        26 => (8, vec![(4, 6), (16, 5), (64, 4), (256, 3)]),
        27 => (8, vec![(4, 6), (16, 5), (64, 4), (256, 4)]),
        28 => (8, vec![(4, 6), (16, 6), (64, 4), (256, 4)]),
        _ => unreachable!(),
    }
}

/// Blocks of `2^MOBIUS_CACHE_BLOCK_LOG` cells complete their low variables while cache-resident.
const MOBIUS_CACHE_BLOCK_LOG: usize = 13;

/// Möbius steps for variables `0..bits` of `a` (`a.len()` a multiple of `2^bits`): cache-resident
/// blocks first, then the remaining variables two per pass. Each step is the exact subtraction
/// `hi -= lo`, so the result does not depend on the blocking.
fn mobius_steps_blocked<T>(a: &mut [T], bits: usize)
where
    T: Copy + core::ops::SubAssign,
{
    let step = |a: &mut [T], bit: usize| {
        let stride = 1usize << bit;
        for block in a.chunks_exact_mut(2 * stride) {
            let (lo, hi) = block.split_at_mut(stride);
            for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                *h -= l;
            }
        }
    };
    let low = bits.min(MOBIUS_CACHE_BLOCK_LOG);
    for block in a.chunks_exact_mut(1usize << low) {
        for bit in 0..low {
            step(block, bit);
        }
    }
    let mut bit = low;
    while bit + 1 < bits {
        let stride = 1usize << bit;
        for block in a.chunks_exact_mut(4 * stride) {
            let (lo, hi) = block.split_at_mut(2 * stride);
            let (q0, q1) = lo.split_at_mut(stride);
            let (q2, q3) = hi.split_at_mut(stride);
            for k in 0..stride {
                q1[k] -= q0[k];
                q3[k] -= q2[k];
                q2[k] -= q0[k];
                q3[k] -= q1[k];
            }
        }
        bit += 2;
    }
    if bit < bits {
        step(a, bit);
    }
}

/// In-place multilinear Möbius transform over `[0, 1]^\ell` (`coeffs.len() == 2^\ell`),
/// parallelized when `std` is enabled and `coeffs.len() >= parallel_min_len`.
pub fn hypercube_to_monomial_in_place<T>(coeffs: &mut [T], parallel_min_len: usize)
where
    T: Copy + Send + Sync + core::ops::SubAssign,
{
    let ell = coeffs.len().trailing_zeros() as usize;
    #[cfg(feature = "std")]
    if coeffs.len() >= parallel_min_len {
        let threads = crate::parallel_pow2_workers(coeffs.len() / 2);
        let chunk_n = coeffs.len() / threads;
        let chunk_bits = chunk_n.trailing_zeros() as usize;
        std::thread::scope(|scope| {
            for sub in coeffs.chunks_mut(chunk_n) {
                crate::spawn_bounded(scope, move || mobius_steps_blocked(sub, chunk_bits));
            }
        });
        for bit in chunk_bits..ell {
            let stride = 1usize << bit;
            for block in coeffs.chunks_mut(stride * 2) {
                let (lo, hi) = block.split_at_mut(stride);
                let sub_len = (stride / threads).max(1);
                std::thread::scope(|scope| {
                    for (lo_c, hi_c) in lo.chunks(sub_len).zip(hi.chunks_mut(sub_len)) {
                        crate::spawn_bounded(scope, move || {
                            for (h, &l) in hi_c.iter_mut().zip(lo_c.iter()) {
                                *h -= l;
                            }
                        });
                    }
                });
            }
        }
        return;
    }
    #[cfg(not(feature = "std"))]
    let _ = parallel_min_len;
    mobius_steps_blocked(coeffs, ell);
}

/// Convert boolean-hypercube evaluations `evals[0..2^\ell]` into multilinear monomial coefficients.
pub fn hypercube_to_monomial_coeffs(evals: &[Goldilocks]) -> Vec<Goldilocks> {
    assert!(evals.len().is_power_of_two() && evals.len() >= 2);
    let mut coeffs = evals.to_vec();
    hypercube_to_monomial_in_place(&mut coeffs, 32_768);
    coeffs
}

pub(crate) fn fill_indexed<T, F>(out: &mut [T], f: F)
where
    T: Send,
    F: Fn(usize) -> T + Sync,
{
    #[cfg(feature = "std")]
    if out.len() >= 8_192 {
        let threads = crate::parallel_workers().min(out.len());
        let chunk = out.len().div_ceil(threads);
        let f_ref = &f;
        std::thread::scope(|scope| {
            for (t_idx, sub) in out.chunks_mut(chunk).enumerate() {
                crate::spawn_bounded(scope, move || {
                    for (off, dst) in sub.iter_mut().enumerate() {
                        *dst = f_ref(t_idx * chunk + off);
                    }
                });
            }
        });
        return;
    }
    for (i, dst) in out.iter_mut().enumerate() {
        *dst = f(i);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stage_geometry_partitions_all_supported_dimensions() {
        for nv in 2..=MAX_PCS_NUM_VARS {
            let (es, stages) = stage_geometry(nv);
            assert!((1..=EARLY_STOP_VARS).contains(&es));
            assert!(!stages.is_empty() && stages.len() <= 4);
            let mut rem = nv;
            for &(blowup, step_vars) in &stages {
                assert!(matches!(blowup, 4 | 16 | 64 | 256));
                assert!((1..=MAX_FOLD_STEP_VARS).contains(&step_vars));
                assert!(step_vars < rem);
                let domain_u64 = (1u64 << rem) * (blowup as u64);
                assert!(domain_u64 <= (1u64 << 31));
                rem -= step_vars;
            }
            assert_eq!(rem, es);
        }
    }

    #[test]
    fn mobius_transform_recovers_boolean_hypercube_evaluations() {
        for ell in [2usize, 5, 13, 15] {
            let n = 1usize << ell;
            let evals: Vec<Goldilocks> = (0..n as u64)
                .map(|i| Goldilocks::from_u64_reduced(i.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 17))
                .collect();
            let coeffs = hypercube_to_monomial_coeffs(&evals);
            for mask in [0usize, 1, n / 3, n / 2 + 1, n - 1] {
                let mut sum = Goldilocks::ZERO;
                let mut sub = mask;
                loop {
                    sum += coeffs[sub];
                    if sub == 0 {
                        break;
                    }
                    sub = (sub - 1) & mask;
                }
                assert_eq!(sum, evals[mask], "ell={ell} mask={mask}");
            }
        }
    }
}
