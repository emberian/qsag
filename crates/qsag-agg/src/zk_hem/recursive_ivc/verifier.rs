//! The verifier executes identically on field values, the constraint recorder,
//! and the row counter. Host decisions only supply witness assignments.
use super::super::relation::{ConstraintSystem, Lc};
use super::*;

struct Kernel<W: Base> {
    tensor_weight: Quint<W>,
    points: Vec<(Quint<W>, Quint<W>)>,
    shifted: Vec<(Quint<W>, W)>,
    consumed: usize,
}
impl<W: Base> Kernel<W> {
    fn fold<B: Wide<W = W>>(&mut self, b: &mut B, phi: &Quint<W>, point: &[Quint<W>]) {
        let one = Quint::constant(E::ONE);
        let factor = one.add(&phi.mul(b, &point[self.consumed]));
        self.tensor_weight = self.tensor_weight.mul(b, &factor);
        for (w, x) in &mut self.points {
            let factor = one.add(&phi.mul(b, x));
            *w = w.mul(b, &factor);
            *x = x.mul(b, x);
        }
        for (w, x) in &mut self.shifted {
            let factor = one.add(&phi.by_base(b, x));
            *w = w.mul(b, &factor);
            *x = b.mul(x, x);
        }
        self.consumed += 1;
    }
    fn tensor<B: Wide<W = W>>(&self, b: &mut B, poly: &[Quint<W>], point: &[Quint<W>]) -> Quint<W> {
        let suffix = &point[self.consumed..];
        let mut terms = poly[..1 << suffix.len()].to_vec();
        for x in suffix {
            terms = terms
                .chunks_exact(2)
                .map(|p| p[0].add(&p[1].mul(b, x)))
                .collect();
        }
        self.tensor_weight.mul(b, &terms[0])
    }
}
fn folds<B: Wide>(
    b: &mut B,
    tr: &mut Duplex<B::W>,
    k: &mut Kernel<B::W>,
    point: &[Quint<B::W>],
    claim: &mut Quint<B::W>,
    wires: &[[E; 5]],
) -> Vec<[Quint<B::W>; 3]> {
    wires
        .iter()
        .map(|wire| {
            let w = wire.map(|v| Quint::alloc(b, v));
            tr.exts(b, b"FOLD_A", &w[..3]);
            let phi = tr.challenge(b, b"FOLD_PHI");
            tr.exts(b, b"FOLD_B", &w[3..]);
            let [theta, alpha, beta] = [b"FOLD_THETA".as_slice(), b"FOLD_ALPHA", b"FOLD_BETA"]
                .map(|tag| tr.challenge(b, tag));
            let ff = w[0].add(&phi.mul(b, &w[1]));
            let gg = w[2].add(&phi.mul(b, &claim.sub(&w[0])));
            let mixed = ff.add(&theta.mul(b, &gg));
            let tail = w[3].add(&theta.mul(b, &w[4]));
            *claim = gg.add(&alpha.mul(b, &mixed)).add(&beta.mul(b, &tail));
            k.fold(b, &phi, point);
            [theta, alpha, beta]
        })
        .collect()
}
fn fiber_fold<B: Wide>(
    b: &mut B,
    mut vals: Vec<Quint<B::W>>,
    mut x: B::W,
    chals: &[[Quint<B::W>; 3]],
    base: bool,
) -> (B::W, Quint<B::W>) {
    let mut inv = b.alloc(b.value(&x).inv_or_zero());
    b.product(&x, &inv, &B::W::constant(F::ONE));
    let mut zeta = F::two_adic_generator(chals.len());
    for (j, [theta, alpha, beta]) in chals.iter().enumerate() {
        let n = vals.len() / 2;
        let x2 = b.mul(&x, &x);
        let beta_x2 = beta.by_base(b, &x2);
        let mut zi = F::ONE;
        let mut zi2 = F::ONE;
        let zeta_inv = zeta.inv();
        let zeta2 = zeta.square();
        for t in 0..n {
            let even = vals[t].add(&vals[t + n]).scale(F::TWO.inv());
            let d = vals[t].sub(&vals[t + n]);
            let factor = inv.scale(F::TWO.inv() * zi);
            let (odd, todd) = if base && j == 0 {
                let o = b.mul(&d.0[0], &factor);
                (Quint::base(o.clone()), theta.by_base(b, &o))
            } else {
                let o = d.by_base(b, &factor);
                let to = theta.mul(b, &o);
                (o, to)
            };
            let mix = even.add(&todd);
            vals[t] = odd.add(&alpha.add(&beta_x2.scale(zi2)).mul(b, &mix));
            zi *= zeta_inv;
            zi2 *= zeta2;
        }
        vals.truncate(n);
        x = x2;
        if j + 1 < chals.len() {
            inv = b.mul(&inv, &inv);
        }
        zeta = zeta2;
    }
    (x, vals.pop().unwrap())
}
fn queries<B: Wide>(
    b: &mut B,
    tr: &mut Duplex<B::W>,
    stage: usize,
    d: StageDims,
    s: &Stage,
    root: &[B::W; 7],
    nonce: &[B::W; 4],
    chals: &[[Quint<B::W>; 3]],
    beta: &Quint<B::W>,
) -> Vec<(B::W, Quint<B::W>)> {
    let idx = sample(b, tr, d);
    let mut hashes = Vec::with_capacity(idx.len());
    let shifts = idx
        .iter()
        .zip(&s.fibers)
        .map(|((index, binary), fiber)| {
            let words: Vec<_> = fiber.iter().map(|&v| b.alloc(v)).collect();
            hashes.push(leaf(b, stage, index.clone(), &words, nonce));
            let mut x = B::W::constant(F::NON_RESIDUE);
            let mut omega = F::two_adic_generator(d.log_domain);
            for bit in binary {
                x = b.mul(&x, &B::W::constant(F::ONE).plus(&bit.scale(omega - F::ONE)));
                omega = omega.square();
            }
            let vals = if stage == 0 {
                words[9..].iter().cloned().map(Quint::base).collect()
            } else {
                words
                    .as_chunks::<5>()
                    .0
                    .iter()
                    .cloned()
                    .map(Quint)
                    .collect()
            };
            let (y, mut folded) = fiber_fold(b, vals, x, chals, stage == 0);
            if stage == 0 {
                folded = folded
                    .add(&beta.mul(b, &Quint(core::array::from_fn(|i| words[4 + i].clone()))));
            }
            (y, folded)
        })
        .collect();
    octopus::verify(b, stage, d.fibers, &idx, hashes, &s.siblings, root);
    shifts
}
pub(super) fn check<B: Wide>(
    b: &mut B,
    cfg: &IvcStepConfig,
    ctx: &[B::W],
    nonce: &[B::W; 4],
    root: &[B::W; 7],
    point: &[Quint<B::W>],
    value: &Quint<B::W>,
    proof: &FixedPathWhirW24,
) {
    let mut tr = Duplex(cfg.transcript().0.map(B::W::constant));
    bind(b, &mut tr, ctx, nonce, root, point, value);
    let roots: Vec<_> = proof
        .stages
        .iter()
        .map(|s| s.root.map(|x| b.alloc(x)))
        .collect();
    for (x, y) in roots[0].iter().zip(root) {
        b.equal(x, y);
    }
    let dims = cfg.dims();
    let s = &proof.stages[0];
    let mut k = Kernel {
        tensor_weight: Quint::constant(E::ONE),
        points: Vec::new(),
        shifted: Vec::new(),
        consumed: 0,
    };
    let mut claim = value.clone();
    let xs: Vec<_> = (0..5).map(|_| tr.challenge(b, b"MASK_POINT")).collect();
    let evals: Vec<_> = s.ood.iter().map(|&e| Quint::alloc(b, e)).collect();
    tr.exts(b, b"MASK_EVAL", &evals);
    for (x, v) in xs.into_iter().zip(evals) {
        let w = tr.challenge(b, b"MASK_WEIGHT");
        claim = claim.add(&w.mul(b, &v));
        k.points.push((w, x));
    }
    let mut chals = folds(b, &mut tr, &mut k, point, &mut claim, &s.folds);
    let mask = Quint::alloc(b, proof.mask_claim);
    tr.exts(b, b"MASK_CLAIM", core::slice::from_ref(&mask));
    let beta = tr.challenge(b, b"MASK_BETA");
    let inv = E(core::array::from_fn(|i| b.value(&beta.0[i]))).inv();
    let inverse = Quint::alloc(b, inv);
    beta.mul(b, &inverse).equal(b, &Quint::constant(E::ONE));
    claim = claim.add(&beta.mul(b, &mask));
    for (i, s) in proof.stages.iter().enumerate().skip(1) {
        tr.frame(b, b"STAGE_ROOT", &roots[i]);
        let xs = [tr.challenge(b, b"OOD_POINT"), tr.challenge(b, b"OOD_POINT")];
        let vs: Vec<_> = s.ood.iter().map(|&x| Quint::alloc(b, x)).collect();
        tr.exts(b, b"OOD_EVAL", &vs);
        let shifts = queries(
            b,
            &mut tr,
            i - 1,
            dims[i - 1],
            &proof.stages[i - 1],
            &roots[i - 1],
            nonce,
            &chals,
            &beta,
        );
        let values: Vec<_> = shifts.iter().map(|(_, v)| v.clone()).collect();
        tr.exts(b, b"QUERY_VALUES", &values);
        for (x, v) in xs.into_iter().zip(vs) {
            let w = tr.challenge(b, b"OOD_WEIGHT");
            claim = claim.add(&w.mul(b, &v));
            k.points.push((w, x));
        }
        let gamma = tr.challenge(b, b"QUERY_GAMMA");
        let mut w = gamma.clone();
        for (y, v) in shifts {
            claim = claim.add(&w.mul(b, &v));
            k.shifted.push((w.clone(), y));
            w = w.mul(b, &gamma);
        }
        chals = folds(b, &mut tr, &mut k, point, &mut claim, &s.folds);
    }
    let poly: Vec<_> = proof
        .final_coeffs
        .iter()
        .map(|&x| Quint::alloc(b, x))
        .collect();
    tr.exts(b, b"FINAL_POLY", &poly);
    let i = dims.len() - 1;
    let shifts = queries(
        b,
        &mut tr,
        i,
        dims[i],
        &proof.stages[i],
        &roots[i],
        nonce,
        &chals,
        &beta,
    );
    let points: Vec<_> = k
        .points
        .iter()
        .map(|(_, x)| x.clone())
        .chain(k.shifted.iter().map(|(_, x)| Quint::base(x.clone())))
        .chain(shifts.iter().map(|(x, _)| Quint::base(x.clone())))
        .collect();
    let evals = terminal_evals(b, &mut tr, &poly, &points);
    let mut terminal = k.tensor(b, &poly, point);
    let weights = k
        .points
        .iter()
        .map(|(w, _)| w)
        .chain(k.shifted.iter().map(|(w, _)| w));
    let mut evaluations = evals.into_iter();
    for w in weights {
        terminal = terminal.add(&w.mul(b, &evaluations.next().unwrap()));
    }
    terminal.equal(b, &claim);
    for ((_, v), expected) in shifts.into_iter().zip(evaluations) {
        v.equal(b, &expected);
    }
}

// Batched quotient identity for all terminal evaluations. For every valid
// (x_i,y_i), (P(X)-y_i)/(X-x_i) is a polynomial of degree at most deg(P)-1.
// Bind all y_i before gamma, then bind the coefficients of their weighted
// quotient Q before t. A wrong evaluation gives a nonzero residue (repeated
// points are separated by gamma); a false rational identity has at most
// deg(P)+points.len() roots. t equal to a pole fails the inverse constraint.
// These auxiliary wires are reconstructed from the PCS witness on both paths.
fn terminal_evals<B: Wide>(
    b: &mut B,
    tr: &mut Duplex<B::W>,
    poly: &[Quint<B::W>],
    points: &[Quint<B::W>],
) -> Vec<Quint<B::W>> {
    let concrete = |x: &Quint<B::W>| E(core::array::from_fn(|i| b.value(&x.0[i])));
    let coeffs: Vec<_> = poly.iter().map(concrete).collect();
    let xs: Vec<_> = points.iter().map(concrete).collect();
    let ys: Vec<_> = xs
        .iter()
        .map(|&x| {
            let y = if x.is_base() {
                coeffs
                    .iter()
                    .rev()
                    .fold(E::ZERO, |a, c| a.mul_base(x.0[0]) + *c)
            } else {
                coeffs.iter().rev().fold(E::ZERO, |a, c| a * x + *c)
            };
            Quint::alloc(b, y)
        })
        .collect();
    tr.exts(b, b"TERMINAL_EVALS", &ys);
    let gamma = tr.challenge(b, b"TERMINAL_BATCH");
    let g = E(core::array::from_fn(|i| b.value(&gamma.0[i])));
    let mut quot = vec![E::ZERO; poly.len() - 1];
    let mut weight = E::ONE;
    for &x in &xs {
        let mut high = E::ZERO;
        for (q, &c) in quot.iter_mut().zip(&coeffs[1..]).rev() {
            high = c + if x.is_base() {
                high.mul_base(x.0[0])
            } else {
                high * x
            };
            *q += weight * high;
        }
        weight *= g;
    }
    let quotient: Vec<_> = quot.into_iter().map(|x| Quint::alloc(b, x)).collect();
    tr.exts(b, b"TERMINAL_QUOT", &quotient);
    let t = tr.challenge(b, b"TERMINAL_POINT");
    let at = |b: &mut B, coeffs: &[Quint<B::W>]| {
        coeffs
            .iter()
            .rev()
            .cloned()
            .reduce(|a, c| a.mul(b, &t).add(&c))
            .unwrap()
    };
    let pt = at(b, poly);
    let qt = at(b, &quotient);
    let mut sum = Quint::constant(E::ZERO);
    for (x, y) in points.iter().zip(&ys).rev() {
        let denom = t.sub(x);
        let dx = E(core::array::from_fn(|i| b.value(&denom.0[i])));
        let inverse = Quint::alloc(b, dx.inv());
        denom.mul(b, &inverse).equal(b, &Quint::constant(E::ONE));
        sum = sum.mul(b, &gamma).add(&pt.sub(y).mul(b, &inverse));
    }
    qt.equal(b, &sum);
    ys
}

impl FixedPathWhirW24 {
    /// Constrain a complete opening on caller-supplied wires. The caller binds
    /// those wires to its own statement and checks the enclosing relation.
    pub fn constrain(
        &self,
        cs: &mut ConstraintSystem,
        cfg: &IvcStepConfig,
        context: &[Lc],
        nonce: &[Lc; 4],
        root: &[Lc; 7],
        point: &[[Lc; 5]],
        value: &[Lc; 5],
    ) -> Option<()> {
        if !self.fits(cfg) || point.len() != cfg.log_cells {
            return None;
        }
        let point = point.iter().cloned().map(Quint).collect::<Vec<_>>();
        check(
            cs,
            cfg,
            context,
            nonce,
            root,
            &point,
            &Quint(value.clone()),
            self,
        );
        Some(())
    }
    pub fn verify(
        &self,
        cfg: &IvcStepConfig,
        context: &[F],
        nonce: [F; 4],
        root: Digest,
        point: &[E],
        value: E,
    ) -> bool {
        if !self.fits(cfg) || point.len() != cfg.log_cells {
            return false;
        }
        let mut b = Native::default();
        check(
            &mut b,
            cfg,
            context,
            &nonce,
            &root,
            &point
                .iter()
                .copied()
                .map(Quint::constant)
                .collect::<Vec<_>>(),
            &Quint::constant(value),
            self,
        );
        !b.failed
    }
}
