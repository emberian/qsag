//! Monomial affine folds and their dual linear-functional bridge.
use super::*;

type E = GoldilocksExt4;

fn monomial_table_core(point: &[E]) -> Vec<E> {
    let mut out = Vec::with_capacity(1usize << point.len());
    out.push(E::ONE);
    for &r in point {
        let n = out.len();
        for i in 0..n {
            out.push(out[i] * r);
        }
    }
    out
}

pub(super) fn monomial_table(point: &[E]) -> Vec<E> {
    #[cfg(feature = "std")]
    if point.len() >= 14 {
        let workers = crate::parallel_pow2_workers(1usize << (point.len() - 10));
        let top_bits = workers.trailing_zeros() as usize;
        if top_bits > 0 && top_bits < point.len() {
            let split = point.len() - top_bits;
            let top = monomial_table_core(&point[split..]);
            let bot = &point[..split];
            let total = 1usize << point.len();
            let sub_len = 1usize << split;
            let mut out = vec![E::ZERO; total + 2];
            std::thread::scope(|scope| {
                for (t_idx, sub) in out[..total].chunks_mut(sub_len).enumerate() {
                    let init = top[t_idx];
                    crate::spawn_bounded(scope, move || {
                        sub[0] = init;
                        for (bit, &r) in bot.iter().enumerate() {
                            let n = 1usize << bit;
                            for i in 0..n {
                                sub[n + i] = sub[i] * r;
                            }
                        }
                    });
                }
            });
            return out;
        }
    }
    let mut out = monomial_table_core(point);
    out.resize(out.len() + 2, E::ZERO);
    out
}

#[cfg(test)]
pub(super) fn geometric(z: E, len: usize) -> Vec<E> {
    powers_of_ext4(z, len)
}

/// Accumulate four independent geometric progressions to shorten the multiplication
/// dependency chain. The tail continues lane zero at the next multiple of four.
fn add_geometric_chunk(dst: &mut [E], initial: E, z: E) {
    let z2 = z.square();
    let z4 = z2.square();
    let mut powers = [initial, initial * z, initial * z2, initial * z2 * z];
    let mut chunks = dst.chunks_exact_mut(4);
    for chunk in chunks.by_ref() {
        for lane in 0..4 {
            chunk[lane] += powers[lane];
            powers[lane] *= z4;
        }
    }
    for (slot, power) in chunks.into_remainder().iter_mut().zip(powers) {
        *slot += power;
    }
}

/// Zero-allocation streaming accumulation `dst[i] += xi * z^i` for `i in 0..dst.len()`.
pub(super) fn add_geometric_scaled_in_place(dst: &mut [E], xi: E, z: E) {
    let _phase = crate::profile::span("add_geometric_scaled");
    if dst.is_empty() {
        return;
    }
    #[cfg(feature = "std")]
    if dst.len() >= 8_192 {
        let workers = crate::parallel_workers().min(dst.len().div_ceil(2_048));
        let chunk = dst.len().div_ceil(workers);
        std::thread::scope(|scope| {
            for (t_idx, sub) in dst.chunks_mut(chunk).enumerate() {
                let initial = xi * z.pow((t_idx * chunk) as u64);
                crate::spawn_bounded(scope, move || add_geometric_chunk(sub, initial, z));
            }
        });
        return;
    }
    add_geometric_chunk(dst, xi, z);
}

/// Reusable-buffer dual fold (`pairs + 1` slots; trailing slot is zero so overflow never wraps).
pub(super) fn fold_kernel_into(k: &[E], phi: E, out: &mut Vec<E>) {
    let pairs = k.len() / 2;
    out.resize(pairs + 1, E::ZERO);
    fill_indexed(&mut out[..pairs], |i| k[2 * i] + phi * k[2 * i + 1]);
    out[pairs] = E::ZERO;
}

/// Reusable-buffer primal monomial affine fold (`c.len() / 2 + 1` slots, zero per-round alloc).
pub(super) fn fold_coeffs_into(c: &[E], [theta, alpha, beta]: [E; 3], out: &mut Vec<E>) {
    let m = c.len() / 2;
    if m == 0 {
        out.clear();
        out.push(E::ZERO);
        return;
    }
    out.resize(m + 1, E::ZERO);
    let mix0 = c[0] + theta * c[1];
    out[0] = c[1] + alpha * mix0;
    let fill = |start: usize, dst: &mut [E]| {
        let mut prev_mix = c[2 * (start - 1)] + theta * c[2 * (start - 1) + 1];
        for (offset, slot) in dst.iter_mut().enumerate() {
            let i = start + offset;
            let cur_mix = c[2 * i] + theta * c[2 * i + 1];
            *slot = beta * prev_mix + (c[2 * i + 1] + alpha * cur_mix);
            prev_mix = cur_mix;
        }
    };
    #[cfg(feature = "std")]
    if m >= 8_192 {
        let workers = crate::parallel_workers().min(m.div_ceil(2_048));
        let chunk = (m - 1).div_ceil(workers);
        std::thread::scope(|scope| {
            for (index, dst) in out[1..m].chunks_mut(chunk).enumerate() {
                let fill = &fill;
                crate::spawn_bounded(scope, move || fill(1 + index * chunk, dst));
            }
        });
    } else {
        fill(1, &mut out[1..m]);
    }
    #[cfg(not(feature = "std"))]
    fill(1, &mut out[1..m]);
    let last_mix = c[2 * (m - 1)] + theta * c[2 * (m - 1) + 1];
    out[m] = beta * last_mix;
}

#[cfg(test)]
pub(super) fn fold_coeffs(c: &[E], chals: [E; 3]) -> Vec<E> {
    let mut out = Vec::with_capacity(c.len() / 2 + 1);
    fold_coeffs_into(c, chals, &mut out);
    out
}

pub(super) fn bridge_prefix(wire: &[E; 5], tr: &mut FiatShamirTranscript<InstanceBound>) -> E {
    for &v in &wire[..3] {
        tr.absorb_ext4(b"WHIR_AFFINE_CROSS", v);
    }
    tr.squeeze_ext4(b"WHIR_AFFINE_PHI")
}

pub(super) fn bridge_finish(
    wire: &[E; 5],
    claim: E,
    phi: E,
    tr: &mut FiatShamirTranscript<InstanceBound>,
) -> (E, [E; 3]) {
    for &v in &wire[3..] {
        tr.absorb_ext4(b"WHIR_AFFINE_SHIFT", v);
    }
    let theta = tr.squeeze_ext4(b"WHIR_AFFINE_THETA");
    let alpha = tr.squeeze_ext4(b"WHIR_AFFINE_ALPHA");
    let beta = tr.squeeze_ext4(b"WHIR_AFFINE_BETA");
    let next = from_verified_ext4(qsag_whir_verified::cwyz_bridge_claim_step(
        to_verified_ext4(wire[0]),
        to_verified_ext4(wire[1]),
        to_verified_ext4(wire[2]),
        to_verified_ext4(wire[3]),
        to_verified_ext4(wire[4]),
        to_verified_ext4(claim),
        to_verified_ext4(phi),
        to_verified_ext4(theta),
        to_verified_ext4(alpha),
        to_verified_ext4(beta),
    ));
    (next, [theta, alpha, beta])
}

pub(super) fn prove_fold_in_place(
    c: &mut Vec<E>,
    k: &mut Vec<E>,
    c_scratch: &mut Vec<E>,
    k_scratch: &mut Vec<E>,
    claim: &mut E,
    tr: &mut FiatShamirTranscript<InstanceBound>,
) -> ([E; 5], [E; 3]) {
    let _phase = crate::profile::span("prove_affine_fold");
    let mut wire = [E::ZERO; 5];
    let pairs_ck = (c.len() / 2).min(k.len() / 2);
    let cross_range = |c_ref: &[E], k_ref: &[E], i0: usize, i1: usize| -> [E; 3] {
        let mut acc = [E::ZERO; 3];
        for i in i0..i1 {
            let a0 = c_ref[2 * i];
            let a1 = c_ref[2 * i + 1];
            let b0 = k_ref[2 * i];
            let b1 = k_ref[2 * i + 1];
            acc[0] += a0 * b0;
            acc[1] += a0 * b1;
            acc[2] += a1 * b0;
        }
        acc
    };
    #[cfg(feature = "std")]
    if pairs_ck >= 4_096 {
        let workers = crate::parallel_workers().min(pairs_ck);
        let chunk = pairs_ck.div_ceil(workers);
        let c_ref = c.as_slice();
        let k_ref = k.as_slice();
        let cross_fn = &cross_range;
        let parts: Vec<[E; 3]> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers)
                .filter_map(|t_idx| {
                    let i0 = t_idx * chunk;
                    (i0 < pairs_ck).then(|| {
                        let i1 = (i0 + chunk).min(pairs_ck);
                        crate::spawn_bounded(scope, move || cross_fn(c_ref, k_ref, i0, i1))
                    })
                })
                .collect();
            handles.into_iter().map(crate::join_worker).collect()
        });
        for p in parts {
            wire[0] += p[0];
            wire[1] += p[1];
            wire[2] += p[2];
        }
    } else {
        let p = cross_range(c, k, 0, pairs_ck);
        wire[0] = p[0];
        wire[1] = p[1];
        wire[2] = p[2];
    }
    #[cfg(not(feature = "std"))]
    {
        let p = cross_range(c, k, 0, pairs_ck);
        wire[0] = p[0];
        wire[1] = p[1];
        wire[2] = p[2];
    }

    let phi = bridge_prefix(&wire, tr);
    fold_kernel_into(k, phi, k_scratch);
    core::mem::swap(k, k_scratch);

    let pairs_c = c.len() / 2;
    let shift_range = |c_ref: &[E], k_ref: &[E], i0: usize, i1: usize| -> [E; 2] {
        let mut acc = [E::ZERO; 2];
        for i in i0..i1 {
            let ki1 = k_ref[i + 1];
            acc[0] += c_ref[2 * i] * ki1;
            acc[1] += c_ref[2 * i + 1] * ki1;
        }
        acc
    };
    #[cfg(feature = "std")]
    if pairs_c >= 4_096 {
        let workers = crate::parallel_workers().min(pairs_c);
        let chunk = pairs_c.div_ceil(workers);
        let c_ref = c.as_slice();
        let k_ref = k.as_slice();
        let shift_fn = &shift_range;
        let parts: Vec<[E; 2]> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers)
                .filter_map(|t_idx| {
                    let i0 = t_idx * chunk;
                    (i0 < pairs_c).then(|| {
                        let i1 = (i0 + chunk).min(pairs_c);
                        crate::spawn_bounded(scope, move || shift_fn(c_ref, k_ref, i0, i1))
                    })
                })
                .collect();
            handles.into_iter().map(crate::join_worker).collect()
        });
        for p in parts {
            wire[3] += p[0];
            wire[4] += p[1];
        }
    } else {
        let p = shift_range(c, k, 0, pairs_c);
        wire[3] = p[0];
        wire[4] = p[1];
    }
    #[cfg(not(feature = "std"))]
    {
        let p = shift_range(c, k, 0, pairs_c);
        wire[3] = p[0];
        wire[4] = p[1];
    }

    let (next, chals) = bridge_finish(&wire, *claim, phi, tr);
    *claim = next;
    fold_coeffs_into(c, chals, c_scratch);
    core::mem::swap(c, c_scratch);
    debug_assert_eq!(dot_ext4_fast(c, k), next);
    (wire, chals)
}

#[cfg(test)]
pub(super) fn prove_fold(
    c: &mut Vec<E>,
    k: &mut Vec<E>,
    claim: &mut E,
    tr: &mut FiatShamirTranscript<InstanceBound>,
) -> ([E; 5], [E; 3]) {
    let mut c_scratch = Vec::new();
    let mut k_scratch = Vec::new();
    prove_fold_in_place(c, k, &mut c_scratch, &mut k_scratch, claim, tr)
}

/// Encode the power-of-two core using the existing fast NTT, then add the
/// two overflow monomials on exactly the same coset (no domain enlargement).
pub(super) fn encode_overflow(c: &[E], blowup: usize) -> Vec<E> {
    let n = c.len() - 2;
    let mut cw = encode_rs_coset_ext4(&c[..n], blowup);
    let omega = Goldilocks::two_adic_generator(cw.len().trailing_zeros() as usize);
    let shift_n = Goldilocks::NON_RESIDUE.pow(n as u64);
    let omega_n = omega.pow(n as u64);
    let add = |start: usize, chunk: &mut [E]| {
        let mut x = Goldilocks::NON_RESIDUE * omega.pow(start as u64);
        let mut xn = shift_n * omega_n.pow(start as u64);
        for value in chunk {
            *value += (c[n] + c[n + 1].mul_base(x)).mul_base(xn);
            x *= omega;
            xn *= omega_n;
        }
    };
    #[cfg(feature = "std")]
    if cw.len() >= 8_192 {
        let workers = crate::parallel_workers();
        let chunk = cw.len().div_ceil(workers);
        std::thread::scope(|scope| {
            for (i, part) in cw.chunks_mut(chunk).enumerate() {
                let add = &add;
                crate::spawn_bounded(scope, move || add(i * chunk, part));
            }
        });
        return cw;
    }
    add(0, &mut cw);
    cw
}

/// Each input has an affine weight a + b X. The first pair uses the
/// equal-degree combiner; subsequent inputs enter the asymmetric cascade.
pub(super) fn cascade_weights(
    count: usize,
    tr: &mut FiatShamirTranscript<InstanceBound>,
) -> Vec<[E; 2]> {
    let theta = tr.squeeze_ext4(b"PCS_BATCH_AFFINE_THETA");
    let a = tr.squeeze_ext4(b"PCS_BATCH_AFFINE_ALPHA");
    let b = tr.squeeze_ext4(b"PCS_BATCH_AFFINE_BETA");
    let mut out = vec![[a, b], [E::ONE + theta * a, theta * b]];
    for _ in 2..count {
        out.push([
            tr.squeeze_ext4(b"PCS_BATCH_AFFINE_ALPHA"),
            tr.squeeze_ext4(b"PCS_BATCH_AFFINE_BETA"),
        ]);
    }
    out
}

pub(super) fn combine_claims(weights: &[[E; 2]], evals: &[E], shifts: &[E]) -> E {
    weights
        .iter()
        .zip(evals)
        .zip(shifts)
        .fold(E::ZERO, |acc, ((w, &e), &s)| {
            from_verified_ext4(qsag_whir_verified::affine_cascade_claim_step(
                to_verified_ext4(acc),
                to_verified_ext4(w[0]),
                to_verified_ext4(w[1]),
                to_verified_ext4(e),
                to_verified_ext4(s),
            ))
        })
}

/// Deferred tensor kernel, including the two explicit overflow weights.
#[derive(Clone)]
pub(super) struct KernelClaim {
    pub offset: usize,
    pub weight: E,
    pub point: Vec<E>,
    pub overflow: [E; 2],
}
impl KernelClaim {
    pub fn evaluation(offset: usize, weight: E, z: E, vars: usize) -> Self {
        let point = pow2_point_ext4(z, vars);
        let zn = point.last().copied().unwrap_or(z).square();
        Self {
            offset,
            weight,
            point,
            overflow: [zn, zn * z],
        }
    }
}

/// Claims contracted per pool work item in [`terminal_sum`].
#[cfg(feature = "std")]
const TERMINAL_CLAIM_CHUNK: usize = 16;

pub(super) fn terminal_sum(phis: &[E], early: usize, claims: &[KernelClaim], c: &[E]) -> E {
    let _phase = crate::profile::span("verify_terminal_sum");
    #[cfg(feature = "std")]
    if claims.len() >= 4 * TERMINAL_CLAIM_CHUNK {
        // The contraction is linear in the claims, so chunks are summed independently.
        let phis: alloc::sync::Arc<[E]> = phis.into();
        let claims: alloc::sync::Arc<[KernelClaim]> = claims.into();
        let c: alloc::sync::Arc<[E]> = c.into();
        let chunks = claims.len().div_ceil(TERMINAL_CLAIM_CHUNK);
        return crate::pool::map_indices(chunks, 1, move |i| {
            let start = i * TERMINAL_CLAIM_CHUNK;
            let end = (start + TERMINAL_CLAIM_CHUNK).min(claims.len());
            terminal_sum_serial(&phis, early, &claims[start..end], &c)
        })
        .into_iter()
        .fold(E::ZERO, |a, b| a + b);
    }
    terminal_sum_serial(phis, early, claims, c)
}

/// `sum_i c[i] * k[i]` for the deferred kernel `k` of `claims`, one claim at a time.
///
/// A claim's kernel restricted to the `2^early` core coefficients is
/// `scale * prod_{bit in i} tail[bit]`, so its contribution is `scale` times the multilinear
/// monomial evaluation of `c` at `tail`, computed by halving folds from the top variable.
fn terminal_sum_serial(phis: &[E], early: usize, claims: &[KernelClaim], c: &[E]) -> E {
    let n = 1usize << early;
    assert!(c.len() == n + 2);
    let half_n = n / 2;
    let mut buf = vec![E::ZERO; half_n.max(1)];
    let mut total = E::ZERO;
    for claim in claims {
        let prefix = phis.len() - claim.offset;
        assert!(claim.point.len() == prefix + early);
        let (head, tail) = claim.point.split_at(prefix);
        let mut scale = claim.weight;
        // Shift queries lie in the base field. Preserve that representation through
        // contraction rather than paying for general quartic multiplication by zero limbs.
        let base_point = claim
            .point
            .iter()
            .all(|r| r.c0.c1 == Goldilocks::ZERO && r.c1 == crate::field::GoldilocksExt2::ZERO);
        let core = if base_point {
            for (&r, &phi) in head.iter().zip(&phis[claim.offset..]) {
                scale *= E::ONE + phi.mul_base(r.c0.c0);
            }
            if early == 0 {
                c[0]
            } else {
                let top = tail[early - 1].c0.c0;
                for (i, slot) in buf[..half_n].iter_mut().enumerate() {
                    *slot = c[i] + c[i + half_n].mul_base(top);
                }
                let mut width = half_n;
                for r in tail[..early - 1].iter().rev() {
                    width /= 2;
                    let r = r.c0.c0;
                    let (lo, hi) = buf[..2 * width].split_at_mut(width);
                    for (l, &h) in lo.iter_mut().zip(hi.iter()) {
                        *l += h.mul_base(r);
                    }
                }
                buf[0]
            }
        } else {
            for (&r, &phi) in head.iter().zip(&phis[claim.offset..]) {
                scale *= E::ONE + phi * r;
            }
            if early == 0 {
                c[0]
            } else {
                let top = tail[early - 1];
                for (i, slot) in buf[..half_n].iter_mut().enumerate() {
                    *slot = c[i] + c[i + half_n] * top;
                }
                let mut width = half_n;
                for &r in tail[..early - 1].iter().rev() {
                    width /= 2;
                    let (lo, hi) = buf[..2 * width].split_at_mut(width);
                    for (l, &h) in lo.iter_mut().zip(hi.iter()) {
                        *l += h * r;
                    }
                }
                buf[0]
            }
        };
        total += scale * core;
        if prefix == 0 {
            total += claim.weight * (claim.overflow[0] * c[n] + claim.overflow[1] * c[n + 1]);
        } else {
            total +=
                claim.weight * (claim.overflow[0] + phis[claim.offset] * claim.overflow[1]) * c[n];
        }
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;
    fn sample(i: usize) -> E {
        E::from_limbs(core::array::from_fn(|j| {
            Goldilocks::from_u64_reduced((i * 7919 + j * 313 + 17) as u64)
        }))
    }
    #[test]
    fn geometric_and_primal_chunks_match_scalar() {
        for len in [0, 1, 2, 3, 4, 5, 17, 8191, 8192, 8193, 16386] {
            let z = sample(11);
            let xi = sample(23);
            let mut got: Vec<_> = (0..len).map(sample).collect();
            let mut expected = got.clone();
            let mut power = xi;
            for slot in &mut expected {
                *slot += power;
                power *= z;
            }
            add_geometric_scaled_in_place(&mut got, xi, z);
            assert_eq!(got, expected);
            if len < 2 {
                continue;
            }
            let chals = [sample(31), sample(32), sample(33)];
            let [theta, alpha, beta] = chals;
            let m = got.len() / 2;
            let mut expected = vec![E::ZERO; m + 1];
            for i in 0..m {
                let mix = got[2 * i] + theta * got[2 * i + 1];
                expected[i] += got[2 * i + 1] + alpha * mix;
                expected[i + 1] += beta * mix;
            }
            assert_eq!(fold_coeffs(&got, chals), expected);
        }
    }

    #[test]
    fn terminal_base_field_specialization_matches_generic_contraction() {
        let phis: Vec<_> = (1..5).map(sample).collect();
        let early = 4;
        let n = 1 << early;
        let c: Vec<_> = (0..n + 2).map(sample).collect();
        let mut claims = Vec::new();
        for offset in 0..=phis.len() {
            for z in [E::from_base(Goldilocks::from_u64_reduced(7919)), sample(37)] {
                claims.push(KernelClaim::evaluation(
                    offset,
                    sample(offset + 11),
                    z,
                    early + phis.len() - offset,
                ));
            }
        }
        let mut k = vec![E::ZERO; n + 2];
        for claim in &claims {
            let prefix = phis.len() - claim.offset;
            let mut scale = claim.weight;
            for (&r, &phi) in claim.point.iter().zip(&phis[claim.offset..]) {
                scale *= E::ONE + phi * r;
            }
            let suffix = monomial_table(&claim.point[prefix..]);
            for (v, &w) in k[..n].iter_mut().zip(&suffix) {
                *v += scale * w;
            }
            if prefix == 0 {
                k[n] += claim.weight * claim.overflow[0];
                k[n + 1] += claim.weight * claim.overflow[1];
            } else {
                k[n] += claim.weight * (claim.overflow[0] + phis[claim.offset] * claim.overflow[1]);
            }
        }
        assert_eq!(
            terminal_sum(&phis, early, &claims, &c),
            dot_ext4_fast(&c, &k)
        );
    }

    fn transcript() -> FiatShamirTranscript<InstanceBound> {
        FiatShamirTranscript::new()
            .bind_relation(b"AFFINE_TEST", b"v1", &whir_stage_schedule(8))
            .bind_instance(&[b"instance"])
    }

    #[test]
    fn monomial_fold_matches_coset_and_degree_fixed_point() {
        for nv in 2..=10 {
            let n = 1usize << nv;
            let mut c: Vec<_> = (0..n + 2).map(sample).collect();
            // Include both nonzero overflow coefficients to exercise later stages.
            let original = c.clone();
            let mut chals = Vec::new();
            for step in 1..=nv.min(MAX_FOLD_STEP_VARS) {
                let chal = [sample(step * 3), sample(step * 3 + 1), sample(step * 3 + 2)];
                c = fold_coeffs(&c, chal);
                chals.push(chal);
                assert_eq!(c.len(), (n >> step) + 2);
                let arity = 1usize << step;
                let zeta = Goldilocks::two_adic_generator(step);
                let x = Goldilocks::NON_RESIDUE;
                let fiber: Vec<_> = (0..arity)
                    .map(|j| eval_univariate_ext4_at_base(&original, x * zeta.pow(j as u64)))
                    .collect();
                let folded = fold_coset_group_ext4(
                    &fiber,
                    x,
                    x.inv(),
                    Goldilocks::TWO.inv(),
                    &build_inv_zetas(),
                    &chals,
                );
                assert_eq!(
                    folded,
                    eval_univariate_ext4_at_base(&c, pow2_iter_base(x, step))
                );
            }
        }
        for nv in 2..=24 {
            for initial_degree in [(1usize << nv) - 1, 1usize << nv] {
                let mut degree = initial_degree;
                for step in 1..nv {
                    degree = degree / 2 + 1;
                    assert!(degree <= (1usize << (nv - step)) + 1);
                }
            }
        }
    }

    #[test]
    fn overflow_encoding_matches_horner_on_unchanged_domains() {
        for nv in 1..=5 {
            let c: Vec<_> = (0..(1usize << nv) + 2).map(sample).collect();
            for blowup in [4, 16, 64, 256] {
                let cw = encode_overflow(&c, blowup);
                assert_eq!(cw.len(), (1usize << nv) * blowup);
                let omega = Goldilocks::two_adic_generator(cw.len().trailing_zeros() as usize);
                let mut x = Goldilocks::NON_RESIDUE;
                for value in cw {
                    assert_eq!(value, eval_univariate_ext4_at_base(&c, x));
                    x *= omega;
                }
            }
        }
    }

    #[test]
    fn deferred_kernel_matches_dense_bridge_with_overflow() {
        let nv = 8;
        let point: Vec<_> = (0..nv).map(sample).collect();
        let mut k = monomial_table(&point);
        let mut c: Vec<_> = (0..k.len()).map(|i| sample(i + 10)).collect();
        let mut claim = dot_ext4_fast(&c, &k);
        let mut claims = vec![KernelClaim {
            offset: 0,
            weight: E::ONE,
            point,
            overflow: [E::ZERO; 2],
        }];
        let mut phis = Vec::new();
        let mut tr = transcript();
        let mut replay = transcript();
        for offset in 0..nv - 2 {
            for j in 0..2 {
                let z = sample(100 + offset * 2 + j);
                let weight = sample(200 + offset * 2 + j);
                axpy_ext4_fast(&mut k, weight, &geometric(z, c.len()));
                claim += weight * eval_univariate_ext4(&c, z);
                claims.push(KernelClaim::evaluation(offset, weight, z, nv - offset));
            }
            let previous_claim = claim;
            let (wire, _) = prove_fold(&mut c, &mut k, &mut claim, &mut tr);
            let phi = bridge_prefix(&wire, &mut replay);
            let (replayed, _) = bridge_finish(&wire, previous_claim, phi, &mut replay);
            assert_eq!(replayed, claim);
            phis.push(phi);
            assert_eq!(claim, terminal_sum(&phis, nv - offset - 1, &claims, &c));
        }
        // The parallel dot-product must include the two non-power-of-two tails.
        let mut a = vec![E::ZERO; 32_770];
        a[32_768] = sample(1);
        a[32_769] = sample(2);
        assert_eq!(
            dot_ext4_fast(&a, &a),
            a[32_768].square() + a[32_769].square()
        );
    }

    #[test]
    fn affine_batch_sizes_and_all_bridge_messages_are_bound() {
        for (nv, count) in [(2, 1), (3, 2), (7, 3), (8, 16)] {
            let polys: Vec<Vec<_>> = (0..count)
                .map(|j| {
                    (0..1usize << nv)
                        .map(|i| Goldilocks::from_u64_reduced((i * i + 7919 * j + 13) as u64))
                        .collect()
                })
                .collect();
            let points: Vec<Vec<_>> = (0..count)
                .map(|j| (0..nv).map(|i| sample(i + j * 13)).collect())
                .collect();
            let evals: Vec<_> = polys
                .iter()
                .zip(&points)
                .map(|(c, p)| crate::field::mle_eval_base_at_ext4(c, p))
                .collect();
            let points: Vec<_> = points.iter().map(Vec::as_slice).collect();
            let (comm, state) = whir_commit_batch_owned(polys, &[7; 32]);
            let proof = whir_open_batch(&state, &points, &evals, &mut transcript());
            let check = |p: &HemWhirBatchOpeningProof| {
                whir_verify_batch(&comm, nv, &points, &evals, p, &mut transcript())
            };
            assert!(check(&proof), "nv={nv} count={count}");
            let mut bytes = Vec::new();
            proof.push_bytes(&mut bytes);
            assert_eq!(
                HemWhirBatchOpeningProof::from_bytes_canonical(&bytes),
                Some((proof.clone(), bytes.len()))
            );
            for i in 0..proof.shifted_evals.len() {
                let mut bad = proof.clone();
                bad.shifted_evals[i] += E::ONE;
                assert!(!check(&bad));
            }
            for round in 0..proof.opening.fold_sumcheck_polys.len() {
                for i in 0..5 {
                    let mut bad = proof.clone();
                    bad.opening.fold_sumcheck_polys[round][i] += E::V;
                    assert!(!check(&bad));
                }
            }
            for i in 0..2 {
                let mut bad = proof.clone();
                bad.opening.stage0_ood_evals[i] += E::ONE;
                assert!(!check(&bad));
                for stage in 0..proof.opening.folded_layers.len() {
                    let mut bad = proof.clone();
                    bad.opening.folded_layers[stage].stage_ood_evals[i] += E::ONE;
                    assert!(!check(&bad));
                }
                let mut bad = proof.clone();
                let n = bad.opening.final_coeffs.len();
                bad.opening.final_coeffs[n - 2 + i] += E::ONE;
                assert!(!check(&bad));
            }
            let mut bad = proof.clone();
            bad.opening.final_coeffs.pop();
            assert!(!check(&bad));
        }
    }
}
