//! Monomial affine folds and their dual linear-functional bridge.
use super::*;

type E = GoldilocksExt4;

pub(super) fn monomial_table(point: &[E]) -> Vec<E> {
    let mut out = vec![E::ONE];
    for &r in point {
        let n = out.len();
        for i in 0..n {
            out.push(out[i] * r);
        }
    }
    out.resize(out.len() + 2, E::ZERO);
    out
}

pub(super) fn geometric(z: E, len: usize) -> Vec<E> {
    powers_of_ext4(z, len)
}

/// The dual fold has one extra zero slot; overflow never wraps into the core.
pub(super) fn fold_kernel(k: &[E], phi: E) -> Vec<E> {
    let mut out: Vec<_> = k.chunks_exact(2).map(|v| v[0] + phi * v[1]).collect();
    out.push(E::ZERO);
    out
}

pub(super) fn fold_coeffs(c: &[E], [theta, alpha, beta]: [E; 3]) -> Vec<E> {
    let mut out = vec![E::ZERO; c.len() / 2 + 1];
    for (i, pair) in c.chunks_exact(2).enumerate() {
        let mix = pair[0] + theta * pair[1];
        out[i] += pair[1] + alpha * mix;
        out[i + 1] += beta * mix;
    }
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
    let f = wire[0] + phi * wire[1];
    let g = wire[2] + phi * (claim - wire[0]);
    (
        g + alpha * (f + theta * g) + beta * (wire[3] + theta * wire[4]),
        [theta, alpha, beta],
    )
}

pub(super) fn prove_fold(
    c: &mut Vec<E>,
    k: &mut Vec<E>,
    claim: &mut E,
    tr: &mut FiatShamirTranscript<InstanceBound>,
) -> ([E; 5], [E; 3]) {
    let mut wire = [E::ZERO; 5];
    for (a, b) in c.chunks_exact(2).zip(k.chunks_exact(2)) {
        wire[0] += a[0] * b[0];
        wire[1] += a[0] * b[1];
        wire[2] += a[1] * b[0];
    }
    let phi = bridge_prefix(&wire, tr);
    *k = fold_kernel(k, phi);
    for (i, a) in c.chunks_exact(2).enumerate() {
        wire[3] += a[0] * k[i + 1];
        wire[4] += a[1] * k[i + 1];
    }
    let (next, chals) = bridge_finish(&wire, *claim, phi, tr);
    *claim = next;
    *c = fold_coeffs(c, chals);
    debug_assert_eq!(dot_ext4_fast(c, k), next);
    (wire, chals)
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
    if cw.len() >= 16_384 {
        let chunk = cw.len().div_ceil(16);
        std::thread::scope(|scope| {
            for (i, part) in cw.chunks_mut(chunk).enumerate() {
                let add = &add;
                scope.spawn(move || add(i * chunk, part));
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
        .fold(E::ZERO, |acc, ((w, &e), &s)| acc + w[0] * e + w[1] * s)
}

/// Deferred tensor kernel, including the two explicit overflow weights.
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

pub(super) fn terminal_sum(phis: &[E], early: usize, claims: &[KernelClaim], c: &[E]) -> E {
    let n = 1usize << early;
    let mut k = vec![E::ZERO; n + 2];
    for claim in claims {
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
    dot_ext4_fast(c, &k)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn sample(i: usize) -> E {
        E::from_limbs(core::array::from_fn(|j| {
            Goldilocks::from_u64_reduced((i * 7919 + j * 313 + 17) as u64)
        }))
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
