//! Batch four evaluations of one fixed multilinear polynomial into one.
//! F(row,col,u,v,kind) interpolates (A,B,C,0) and the leaf/step
//! matrices. The product F(x) * sum_j beta^j eq(x,p_j) has individual
//! degree two. Every round precedes its challenge. At the root the evaluator
//! computes F directly from locally compiled matrices.
use super::super::{
    relation::Shape,
    v2::protocol::{column_table, eq_table},
};
use super::r1cs::{Acc, Claim};
use super::*;

fn start<B: Wide>(b: &mut B, claims: &[Claim<B::W>]) -> (Duplex<B::W>, Vec<Quint<B::W>>) {
    let mut tr = Duplex::new();
    for x in claims {
        tr.frame(b, b"IVC-MAT-BATCH", &x.words());
    }
    let beta = tr.challenge(b, b"BATCH_WEIGHT");
    let mut w = Quint::constant(E::ONE);
    let weights = (0..claims.len())
        .map(|_| {
            let out = w.clone();
            w = w.mul(b, &beta);
            out
        })
        .collect();
    (tr, weights)
}
pub(super) fn check<B: Wide>(
    b: &mut B,
    claims: &[Claim<B::W>],
    rounds: &[Vec<E>],
    answer: E,
) -> Claim<B::W> {
    let (mut tr, weights) = start(b, claims);
    let mut value = Quint::constant(E::ZERO);
    for (c, w) in claims.iter().zip(&weights) {
        value = value.add(&c.value.mul(b, w));
    }
    let (last, point) = r1cs::sumcheck(b, &mut tr, b"MAT_ROUND", value, rounds);
    let mut q = Quint::constant(E::ZERO);
    for (c, w) in claims.iter().zip(weights) {
        let basis = r1cs::eq(b, &point, &c.point);
        q = q.add(&w.mul(b, &basis));
    }
    let value = Quint::alloc(b, answer);
    q.mul(b, &value).equal(b, &last);
    Claim { point, value }
}
fn coeffs(tags: &[E]) -> [E; 3] {
    let [u, v] = [tags[0], tags[1]];
    [
        (E::ONE - u) * (E::ONE - v),
        u * (E::ONE - v),
        (E::ONE - u) * v,
    ]
}
fn contract_rows(shapes: [&Shape; 2], log: usize, point: &[E]) -> Vec<E> {
    let n = 1 << log;
    let tags = &point[2 * log..];
    let cs = coeffs(tags);
    let mut out = vec![E::ZERO; n];
    if cs.iter().all(|x| x.is_zero()) {
        return out;
    }
    let eq = eq_table(&point[log..2 * log]);
    for (s, weight) in shapes.into_iter().zip([E::ONE - tags[2], tags[2]]) {
        if weight.is_zero() {
            continue;
        }
        let w = cs.map(|c| c * weight);
        super::super::v2::pcs::par_chunks_mut(&mut out[..s.num_rows()], |off, part| {
            for (j, y) in part.iter_mut().enumerate() {
                for (m, c) in [&s.a, &s.b, &s.c].into_iter().zip(&w) {
                    let sum = m
                        .row(off + j)
                        .fold(E::ZERO, |a, (col, k)| a + eq[col].mul_base(k));
                    *y += *c * sum;
                }
            }
        });
    }
    out
}
pub(super) fn evaluate(shapes: [&Shape; 2], log: usize, c: &Acc) -> bool {
    let row = contract_rows(shapes, log, &c.point);
    let eq = eq_table(&c.point[..log]);
    row.into_iter().zip(eq).fold(E::ZERO, |a, (v, w)| a + v * w) == c.value
}
type Tables = Vec<(Vec<E>, Vec<E>)>;
fn fold_table(v: &mut Vec<E>, r: E) {
    for j in 0..v.len() / 2 {
        v[j] = v[2 * j] + r * (v[2 * j + 1] - v[2 * j]);
    }
    v.truncate(v.len() / 2);
}
fn phase(
    tr: &mut Duplex<F>,
    tables: &mut Tables,
    rounds: &mut Vec<Vec<E>>,
    point: &mut Vec<E>,
    claim: &mut E,
) {
    while tables[0].0.len() > 1 {
        let (mut constant, mut quadratic) = (E::ZERO, E::ZERO);
        for (v, w) in tables.iter() {
            for (v, w) in v.as_chunks::<2>().0.iter().zip(w.as_chunks::<2>().0) {
                constant += v[0] * w[0];
                quadratic += (v[1] - v[0]) * (w[1] - w[0]);
            }
        }
        let linear = *claim - constant - constant - quadratic;
        let co = vec![constant, linear, quadratic];
        tr.absorb_fp5_slice(b"MAT_ROUND", &co);
        let r = tr.squeeze_fp5(b"MAT_ROUND");
        *claim = constant + r * (linear + r * quadratic);
        for (v, w) in tables.iter_mut() {
            fold_table(v, r);
            fold_table(w, r);
        }
        rounds.push(co);
        point.push(r);
    }
}
pub(super) fn prove(shapes: [&Shape; 2], log: usize, claims: &[Claim<F>]) -> (Vec<Vec<E>>, Acc) {
    let (mut tr, weights) = start(&mut Native::default(), claims);
    let n = 1 << log;
    let points: Vec<_> = claims.iter().map(Claim::native).collect();
    let mut claim = points
        .iter()
        .zip(&weights)
        .fold(E::ZERO, |a, (c, w)| a + c.value * E(w.0));
    let mut rounds = Vec::new();
    let mut point = Vec::new();
    let mut tables: Tables = points
        .iter()
        .zip(weights)
        .map(|(p, w)| {
            let mut e = eq_table(&p.point[..log]);
            for x in &mut e {
                *x *= E(w.0);
            }
            (contract_rows(shapes, log, &p.point), e)
        })
        .collect();
    phase(&mut tr, &mut tables, &mut rounds, &mut point, &mut claim);
    let eq = eq_table(&point);
    // After fixing the row coordinates, each matrix is a vector of columns.
    let mut cols = Vec::with_capacity(8);
    for s in shapes {
        for k in 0..3 {
            let mut w = [E::ZERO; 3];
            w[k] = E::ONE;
            cols.push(column_table(s, &eq[..s.num_rows()], &w, n));
        }
        cols.push(Vec::new());
    }
    for ((v, w), p) in tables.iter_mut().zip(&points) {
        let weight = w[0];
        *w = eq_table(&p.point[log..2 * log]);
        for x in w {
            *x *= weight;
        }
        let tags = eq_table(&p.point[2 * log..]);
        *v = vec![E::ZERO; n];
        for (col, t) in cols.iter().zip(tags) {
            if !t.is_zero() {
                for (x, y) in v.iter_mut().zip(col) {
                    *x += *y * t;
                }
            }
        }
    }
    phase(&mut tr, &mut tables, &mut rounds, &mut point, &mut claim);
    let eq = eq_table(&point[log..]);
    let mat: Vec<_> = cols
        .into_iter()
        .map(|col| {
            col.into_iter()
                .zip(&eq)
                .fold(E::ZERO, |a, (c, w)| a + c * *w)
        })
        .collect();
    for ((v, w), p) in tables.iter_mut().zip(&points) {
        let weight = w[0];
        *w = eq_table(&p.point[2 * log..]);
        for x in w {
            *x *= weight;
        }
        v.clone_from(&mat);
    }
    phase(&mut tr, &mut tables, &mut rounds, &mut point, &mut claim);
    (
        rounds,
        Acc {
            point,
            value: tables[0].0[0],
        },
    )
}
