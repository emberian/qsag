//! At a common row point each assignment has three matrix products A, B and C.
//! Reduce the seventh power with two auxiliary product checks on the instance
//! cube. All instance rounds then have individual degree at most three.
use super::*;
use protocol::{eq_eval, eq_table, eval_poly, evals_to_coeffs};

pub(super) struct Channel {
    pub profile: Profile,
    pub tr: Transcript,
}

impl Channel {
    /// The preimage is on the wire. Recomputing its commitment also checks the
    /// opening. Only the digest enters the challenge transcript.
    pub fn bind(&mut self, label: &[u8], values: &[E]) {
        let bytes: Vec<u8> = values.iter().flat_map(|v| v.to_le_bytes()).collect();
        let commitment = Transcript::new(self.profile, &[MAGIC, b"ROUND", label, &bytes]).digest();
        self.tr.absorb(label, &commitment);
    }
    pub fn round(&mut self, label: &[u8], co: &[E]) -> E {
        self.bind(label, co);
        self.tr.squeeze_fp5(label)
    }
    pub fn point(&mut self, label: &[u8], len: usize) -> Vec<E> {
        (0..len).map(|_| self.tr.squeeze_fp5(label)).collect()
    }
}

pub(super) fn check_rounds(
    ch: &mut Channel,
    label: &[u8],
    rounds: &[Vec<E>],
    mut value: E,
) -> Option<(Vec<E>, E)> {
    let mut point = Vec::with_capacity(rounds.len());
    for co in rounds {
        if co[0] + eval_poly(co, E::ONE) != value {
            return None;
        }
        let r = ch.round(label, co);
        point.push(r);
        value = eval_poly(co, r);
    }
    Some((point, value))
}

pub(super) fn sumcheck<const N: usize>(
    ch: &mut Channel,
    label: &[u8],
    degree: usize,
    columns: [Vec<E>; N],
    gate: impl Fn([E; N]) -> E,
) -> (Vec<Vec<E>>, Vec<E>, [E; N]) {
    let mut columns = SecretBuffer::new(columns);
    let mut rounds = Vec::new();
    let mut point = Vec::new();
    while columns[0].len() > 1 {
        let half = columns[0].len() / 2;
        let mut evals = vec![E::ZERO; degree + 1];
        for j in 0..half {
            let mut x = core::array::from_fn(|k| columns[k][2 * j]);
            let delta: [E; N] = core::array::from_fn(|k| columns[k][2 * j + 1] - x[k]);
            for y in &mut evals {
                *y += gate(x);
                for (v, d) in x.iter_mut().zip(delta) {
                    *v += d;
                }
            }
        }
        let co = evals_to_coeffs(&evals);
        let r = ch.round(label, &co);
        for col in columns.iter_mut() {
            for i in 0..half {
                let lo = col[2 * i];
                col[i] = lo + r * (col[2 * i + 1] - lo);
            }
            qsag_asm::volatile_fill(&mut col[half..], E::ZERO);
            col.truncate(half);
        }
        rounds.push(co);
        point.push(r);
    }
    (rounds, point, core::array::from_fn(|k| columns[k][0]))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Fold {
    pub product: Vec<Vec<E>>,
    pub at_product: [E; 5],
    pub powers: Vec<Vec<E>>,
    pub at_powers: [E; 2],
    pub square: Vec<Vec<E>>,
    pub at_square: E,
    pub reduce: Vec<Vec<E>>,
    pub abc: [E; 3],
}

fn gate(s: E, [a, b, c, a4, a3]: [E; 5]) -> E {
    let ab = a * b;
    ab + s * (a4 * a3 - ab) - c
}

fn weights(beta: E) -> [E; 5] {
    let b2 = beta.square();
    [E::ONE, beta, b2, b2 * beta, b2.square()]
}

pub(super) fn prove(ch: &mut Channel, t: &[E], s: E, mut abc: Vec<[E; 3]>) -> (Fold, Vec<E>) {
    abc.resize(1 << t.len(), [E::ZERO; 3]);
    let [a, b, c]: [Vec<E>; 3] = core::array::from_fn(|k| abc.iter().map(|v| v[k]).collect());
    let a2: Vec<_> = a.iter().map(|v| v.square()).collect();
    let a3 = a2.iter().zip(&a).map(|(&x, &y)| x * y).collect();
    let a4 = a2.iter().map(|v| v.square()).collect();
    let (product, r, [ar, br, cr, p4, p3, _]) = sumcheck(
        ch,
        b"PRODUCT",
        3,
        [a.clone(), b.clone(), c.clone(), a4, a3, eq_table(t)],
        |[a, b, c, p4, p3, w]| w * gate(s, [a, b, c, p4, p3]),
    );
    let at_product = [ar, br, cr, p4, p3];
    ch.bind(b"PRODUCT_VALUES", &at_product);
    let lambda = ch.tr.squeeze_fp5(b"POWER_BATCH");
    let (powers, v, [dv, av, _]) = sumcheck(
        ch,
        b"POWERS",
        3,
        [a2, a.clone(), eq_table(&r)],
        |[d, a, w]| w * d * (d + lambda * a),
    );
    let at_powers = [dv, av];
    ch.bind(b"POWER_VALUES", &at_powers);
    let (square, w, [at_square, _]) =
        sumcheck(ch, b"SQUARE", 3, [a.clone(), eq_table(&v)], |[a, e]| {
            e * a.square()
        });
    ch.bind(b"SQUARE_VALUE", &[at_square]);
    let weights = weights(ch.tr.squeeze_fp5(b"REDUCE_BATCH"));
    let er = eq_table(&r);
    let wa = er
        .iter()
        .zip(eq_table(&v))
        .zip(eq_table(&w))
        .map(|((&x, y), z)| x + weights[3] * y + weights[4] * z)
        .collect();
    let (reduce, u, [a, b, c, _, _]) =
        sumcheck(ch, b"REDUCE", 2, [a, b, c, wa, er], |[a, b, c, ea, er]| {
            a * ea + (weights[1] * b + weights[2] * c) * er
        });
    let abc = [a, b, c];
    ch.bind(b"FOLDED_VALUES", &abc);
    (
        Fold {
            product,
            at_product,
            powers,
            at_powers,
            square,
            at_square,
            reduce,
            abc,
        },
        u,
    )
}

impl Fold {
    pub fn check(
        &self,
        ch: &mut Channel,
        t: &[E],
        s: E,
        row_factor: E,
        row_claim: E,
    ) -> Option<Vec<E>> {
        // The row equality factor is public. Fail closed on its negligible zero event.
        if row_factor.is_zero() {
            return None;
        }
        let (r, end) = check_rounds(ch, b"PRODUCT", &self.product, row_claim * row_factor.inv())?;
        if end != eq_eval(t, &r) * gate(s, self.at_product) {
            return None;
        }
        ch.bind(b"PRODUCT_VALUES", &self.at_product);
        let lambda = ch.tr.squeeze_fp5(b"POWER_BATCH");
        let [ar, br, cr, p4, p3] = self.at_product;
        let (v, end) = check_rounds(ch, b"POWERS", &self.powers, p4 + lambda * p3)?;
        let [dv, av] = self.at_powers;
        if end != eq_eval(&r, &v) * dv * (dv + lambda * av) {
            return None;
        }
        ch.bind(b"POWER_VALUES", &self.at_powers);
        let (w, end) = check_rounds(ch, b"SQUARE", &self.square, dv)?;
        if end != eq_eval(&v, &w) * self.at_square.square() {
            return None;
        }
        ch.bind(b"SQUARE_VALUE", &[self.at_square]);
        let beta = weights(ch.tr.squeeze_fp5(b"REDUCE_BATCH"));
        let initial = ar + beta[1] * br + beta[2] * cr + beta[3] * av + beta[4] * self.at_square;
        let (u, end) = check_rounds(ch, b"REDUCE", &self.reduce, initial)?;
        let [a, b, c] = self.abc;
        let er = eq_eval(&u, &r);
        let ea = er + beta[3] * eq_eval(&u, &v) + beta[4] * eq_eval(&u, &w);
        if end != a * ea + (beta[1] * b + beta[2] * c) * er {
            return None;
        }
        ch.bind(b"FOLDED_VALUES", &self.abc);
        Some(u)
    }
}
