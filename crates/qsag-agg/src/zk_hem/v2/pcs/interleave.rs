//! One authenticated vector of RS symbols at each fiber. Projection over
//! the instance variables commutes with encoding and with the fiber transform.
use super::*;

pub(in crate::zk_hem) const MAX_FIBER_WORDS: usize = 1 << 16;

pub(in crate::zk_hem) struct Interleaved {
    hasher: Hasher,
    dims: Vec<StageDims>,
    salt: SecretBuffer<[u8; 32]>,
    coefficients: SecretBuffer<Vec<Vec<Goldilocks>>>,
    codes: SecretBuffer<Vec<Vec<Goldilocks>>>,
    mask: SecretBuffer<Vec<Fp5>>,
    mask_code: SecretBuffer<Vec<Fp5>>,
    tree: MerkleTree,
}

fn symbols(codes: &[Vec<Goldilocks>], d: &StageDims, j: usize) -> Vec<Goldilocks> {
    let mut z = Vec::with_capacity(codes.len() * d.arity());
    for code in codes {
        for t in 0..d.arity() {
            z.push(code[j + t * d.fibers]);
        }
    }
    z
}

fn shifts(
    query: &Stage0Query,
    d: &StageDims,
    indices: &[usize],
    weights: &[Fp5],
    chals: &[[Fp5; 3]],
    beta: Fp5,
) -> Vec<(Goldilocks, Fp5)> {
    indices
        .iter()
        .zip(&query.leaves)
        .map(|(&j, leaf)| {
            let mut vals = vec![Fp5::ZERO; d.arity()];
            for (chunk, &w) in leaf.z.chunks_exact(d.arity()).zip(weights) {
                for (acc, &v) in vals.iter_mut().zip(chunk) {
                    *acc += w.mul_base(v);
                }
            }
            let v = fold_fiber(vals, d.fiber_base(j), chals);
            (d.fiber_image(j), v + beta * leaf.r)
        })
        .collect()
}

impl Interleaved {
    pub(in crate::zk_hem) fn commit(
        profile: Profile,
        log: usize,
        schedule: &Schedule,
        table: &[Goldilocks],
        mask: Vec<Fp5>,
        nonce: [u8; 32],
        salt: [u8; 32],
    ) -> Option<Self> {
        let dims = stage_dims(log, schedule)?;
        let d = &dims[0];
        let width = table.len().checked_shr(log as u32)?;
        if !table.len().is_power_of_two()
            || width < 2
            || width * d.arity() > MAX_FIBER_WORDS
            || mask.len() != mask_len(log, d.step_vars)
        {
            return None;
        }
        let hasher = Hasher::new(profile);
        let coefficients = SecretBuffer::new(
            table
                .chunks_exact(1 << log)
                .map(crate::pcs::hypercube_to_monomial_coeffs)
                .collect::<Vec<_>>(),
        );
        let codes = SecretBuffer::new(
            coefficients
                .iter()
                .map(|v| encode_base(v, d.log_domain))
                .collect::<Vec<_>>(),
        );
        let mask_code = SecretBuffer::new(encode_ext_folded(&mask, d.log_domain, d.step_vars));
        let mut hashes = vec![[0; DIGEST_BYTES]; d.fibers];
        crate::pcs::fill_indexed(&mut hashes, |j| {
            let words = SecretBuffer::new(symbols(&codes, d, j));
            hasher
                .leaf_interleaved(
                    &nonce,
                    j as u32,
                    &hasher.salt(&salt, j as u32),
                    d.arity(),
                    &words,
                    mask_code[j],
                )
                .expect("validated fiber width")
        });
        Some(Self {
            hasher,
            dims,
            salt: SecretBuffer::new(salt),
            coefficients,
            codes,
            mask: SecretBuffer::new(mask),
            mask_code,
            tree: MerkleTree::build(hasher, 0, hashes),
        })
    }
    pub(in crate::zk_hem) fn root(&self) -> Digest {
        self.tree.root()
    }

    pub(in crate::zk_hem) fn open(
        &self,
        weights: &[Fp5],
        kernel: Vec<Fp5>,
        value: Fp5,
        ch: &mut impl Channel,
    ) -> Option<Opening> {
        if weights.len() != self.codes.len() {
            return None;
        }
        let d = &self.dims[0];
        let mut poly = SecretBuffer::new(vec![Fp5::ZERO; self.coefficients[0].len()]);
        par_chunks_mut(&mut poly, |off, part| {
            for (cs, &w) in self.coefficients.iter().zip(weights) {
                for (out, &v) in part.iter_mut().zip(&cs[off..]) {
                    *out += w.mul_base(v);
                }
            }
        });
        let red = stage0_reduce(
            &poly,
            &self.mask,
            d.step_vars,
            MASK_POINTS,
            kernel,
            value,
            ch,
        )
        .ok()?;
        drop(poly);
        open_reduced(
            self.hasher,
            &self.dims,
            red,
            ch,
            cpu_oracle,
            &cpu_folds,
            |idx, chals, beta| {
                let query = Stage0Query {
                    leaves: idx
                        .iter()
                        .map(|&j| Stage0Leaf {
                            salt: self.hasher.salt(&self.salt, j as u32),
                            z: symbols(&self.codes, d, j),
                            r: self.mask_code[j],
                        })
                        .collect(),
                    siblings: self.tree.open(idx),
                };
                let result = shifts(&query, d, idx, weights, chals, beta);
                (query, result)
            },
        )
        .ok()
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::zk_hem) fn verify(
    profile: Profile,
    nonce: &[u8; 32],
    root: &Digest,
    log: usize,
    schedule: &Schedule,
    weights: &[Fp5],
    term: &TensorTerm,
    value: Fp5,
    p: &Opening,
    ch: &mut impl Channel,
) -> bool {
    verify_inner(
        profile,
        log,
        schedule,
        core::slice::from_ref(term),
        value,
        &p.mask_evals,
        &p.stage0_folds,
        p.mask_claim,
        |hasher, d, idx, chals, beta| {
            let q = &p.stage0_query;
            let words = weights.len().checked_mul(d.arity())?;
            if !weights.len().is_power_of_two()
                || weights.len() < 2
                || words > MAX_FIBER_WORDS
                || q.leaves.len() != idx.len()
            {
                return None;
            }
            let digests: Vec<_> = idx
                .iter()
                .zip(&q.leaves)
                .map(|(&j, leaf)| {
                    if leaf.z.len() != words {
                        return None;
                    }
                    Some((
                        j,
                        hasher.leaf_interleaved(
                            nonce,
                            j as u32,
                            &leaf.salt,
                            d.arity(),
                            &leaf.z,
                            leaf.r,
                        )?,
                    ))
                })
                .collect::<Option<_>>()?;
            verify_multiproof(hasher, 0, d.log_leaves(), root, &digests, &q.siblings)
                .then(|| shifts(q, d, idx, weights, chals, beta))
        },
        &p.stages,
        &p.final_coeffs,
        ch,
    )
}
