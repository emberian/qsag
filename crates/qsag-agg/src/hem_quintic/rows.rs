//! Degree-eight row sumcheck for the shared 256-column StepOp relation.
//! All coordinates (columns first, then steps, then signer slots) are little-endian.
use super::*;
use crate::sponge::{poseidon2_apply_me, poseidon2_apply_mi};
use crate::trace::{RowPublicEval, RowWeights, TraceField, eval_row_with_weights};
use crate::zk_hem::v2::protocol::{eq_table, evals_to_coeffs};

impl TraceField for E {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;
    fn from_base(x: F) -> Self {
        Self::from_base(x)
    }
    fn from_u64(x: u64) -> Self {
        Self::from_u64(x)
    }
    fn mul_base_f(self, x: F) -> Self {
        self.mul_base(x)
    }
    fn sbox7(self) -> Self {
        let x2 = self.square();
        x2.square() * x2 * self
    }
    fn apply_me(st: &mut [Self; 12]) {
        linear_layer(st, poseidon2_apply_me);
    }
    fn apply_mi(st: &mut [Self; 12]) {
        linear_layer(st, poseidon2_apply_mi);
    }
}

// The two Goldilocks-linear maps act independently on each power-basis coordinate.
fn linear_layer(st: &mut [E; 12], layer: fn(&mut [F; 12])) {
    for i in 0..5 {
        let mut limbs = st.map(|x| x.0[i]);
        layer(&mut limbs);
        for (x, limb) in st.iter_mut().zip(limbs) {
            x.0[i] = limb;
        }
    }
}

const SEED: usize = NUM_TRACE_COLS;
const ROOT: usize = SEED + 4;
const MU: usize = ROOT + 4;
const STEP: usize = MU + 5;
const FIRST: usize = STEP + 1;
const LAST: usize = FIRST + 1;
const EQ: usize = LAST + 1;
const NOT_LAST: usize = EQ + 1;
const SHIFT: usize = NOT_LAST + 1;
const SELECTORS: usize = SHIFT + 1;

fn eval(c: &ShardCircuit, r: &[E], gamma: E, weights: &RowWeights<E>) -> E {
    eval_row_with_weights(
        &c.unique_ops,
        r.first_chunk().unwrap(),
        &RowPublicEval {
            // Individual selectors in the packed table already include the active-slot factor.
            active_signer: E::ONE,
            pk_seed: *r[SEED..].first_chunk().unwrap(),
            pk_root: *r[ROOT..].first_chunk().unwrap(),
            mu: *r[MU..].first_chunk().unwrap(),
            gated_op_sels: &r[SELECTORS..],
            step_c0: r[STEP],
            is_row_first: r[FIRST],
            is_row_last: r[LAST],
            eq_tau: r[EQ],
            eq_not_last: r[NOT_LAST],
            shift_tau: r[SHIFT],
        },
        gamma,
        Some(weights),
    )
}

fn challenges(st: &mut Statement) -> (Vec<E>, E) {
    let tau = (0..st.circuit.log_rows())
        .map(|_| st.transcript.squeeze_fp5(b"TAU"))
        .collect();
    (tau, st.transcript.squeeze_fp5(b"GAMMA"))
}

fn step_round(tr: &mut Transcript, poly: &[E; 9], claim: &mut E) -> Option<E> {
    if poly[0] + poly[1] != *claim {
        return None;
    }
    tr.absorb_fp5_slice(b"ROW_VALUES", poly);
    let r = tr.squeeze_fp5(b"ROW_POINT");
    *claim = pcs::eval_poly(&evals_to_coeffs(poly), [r])[0];
    Some(r)
}

fn col_claim(tr: &mut Transcript, cols: &[E; NUM_TRACE_COLS], rx: Vec<E>) -> (Vec<E>, E) {
    tr.absorb_fp5_slice(b"COLUMNS", cols);
    let mut point: Vec<_> = (0..crate::trace::LOG_TRACE_COLS)
        .map(|_| tr.squeeze_fp5(b"COLUMN_POINT"))
        .collect();
    let value = eq_table(&point)
        .into_iter()
        .zip(cols)
        .fold(E::ZERO, |a, (w, &x)| a + w * x);
    point.extend(rx);
    (point, value)
}

pub(super) fn prove(
    st: &mut Statement,
    rows: Vec<[F; NUM_TRACE_COLS]>,
    out: &mut Vec<u8>,
) -> Option<(Vec<E>, E)> {
    let (tau, gamma) = challenges(st);
    let eq = eq_table(&tau);
    let c = &st.circuit;
    let weights = RowWeights::new(&c.unique_ops, gamma);
    if weights.count() > 1 << 20 {
        return None;
    }
    let width = SELECTORS + c.unique_ops.len();
    let mut table = vec![E::ZERO; rows.len() * width];
    for (i, (r, cols)) in table.chunks_exact_mut(width).zip(rows).enumerate() {
        let step = i % c.rows_per_signer();
        r[..NUM_TRACE_COLS].copy_from_slice(&cols.map(E::from_base));
        if let Some(s) = st.signers.get(i / c.rows_per_signer()) {
            r[SEED..ROOT].copy_from_slice(&s.pk.pk_seed.map(E::from_base));
            r[ROOT..MU].copy_from_slice(&s.pk.pk_root.map(E::from_base));
            r[MU..STEP].copy_from_slice(&s.mu.map(E::from_base));
            r[SELECTORS + c.step_to_uid[step]] = E::ONE;
        }
        r[STEP] = E::from_base(c.step_c0_base[step]);
        r[FIRST] = E::from_u64((step == 0) as u64);
        r[LAST] = E::from_u64((step + 1 == c.rows_per_signer()) as u64);
        r[EQ] = eq[i];
        if i + 1 < eq.len() {
            r[NOT_LAST] = eq[i];
        }
        if i > 0 {
            r[SHIFT] = eq[i - 1];
        }
    }
    let mut claim = E::ZERO;
    let mut rx = Vec::with_capacity(tau.len());
    let mut work = vec![E::ZERO; width];
    let mut delta = vec![E::ZERO; width];
    for _ in tau {
        let mut values = [E::ZERO; 9];
        for pair in table.chunks_exact(2 * width) {
            let (a, b) = pair.split_at(width);
            work.copy_from_slice(a);
            for ((d, &lo), &hi) in delta.iter_mut().zip(a).zip(b) {
                *d = hi - lo;
            }
            for v in &mut values {
                *v += eval(c, &work, gamma, &weights);
                for (x, &d) in work.iter_mut().zip(&delta) {
                    *x += d;
                }
            }
        }
        write_es(out, &values);
        let r = step_round(&mut st.transcript, &values, &mut claim)?;
        rx.push(r);
        for i in 0..table.len() / (2 * width) {
            for j in 0..width {
                let a = table[2 * i * width + j];
                let b = table[(2 * i + 1) * width + j];
                table[i * width + j] = a + r * (b - a);
            }
        }
        table.truncate(table.len() / 2);
    }
    if eval(c, &table, gamma, &weights) != claim {
        return None;
    }
    let cols = table.first_chunk()?;
    write_es(out, cols);
    Some(col_claim(&mut st.transcript, cols, rx))
}

pub(super) fn verify(st: &mut Statement, input: &mut &[u8]) -> Option<(Vec<E>, E)> {
    let (tau, gamma) = challenges(st);
    let c = &st.circuit;
    let weights = RowWeights::new(&c.unique_ops, gamma);
    if weights.count() > 1 << 20 {
        return None;
    }
    let mut claim = E::ZERO;
    let mut rx = Vec::with_capacity(tau.len());
    for _ in &tau {
        rx.push(step_round(
            &mut st.transcript,
            &read_es(input)?,
            &mut claim,
        )?);
    }
    let cols = read_es::<NUM_TRACE_COLS>(input)?;
    let mut row = vec![E::ZERO; SELECTORS + c.unique_ops.len()];
    row[..NUM_TRACE_COLS].copy_from_slice(&cols);
    let (local, slots) = rx.split_at(c.log_local());
    let steps = eq_table(local);
    row[FIRST] = steps[0];
    row[LAST] = *steps.last()?;
    let mut active = E::ZERO;
    for (s, w) in st.signers.iter().zip(eq_table(slots)) {
        active += w;
        for (j, &v) in
            s.pk.pk_seed
                .iter()
                .chain(&s.pk.pk_root)
                .chain(&s.mu)
                .enumerate()
        {
            row[SEED + j] += w.mul_base(v);
        }
    }
    for (i, w) in steps.into_iter().enumerate() {
        row[STEP] += w.mul_base(c.step_c0_base[i]);
        row[SELECTORS + c.step_to_uid[i]] += active * w;
    }
    // Simultaneously evaluate equality and the one-step carry bus. On the Boolean cube
    // shift(t,x) is eq(t,x-1) for x>0, and zero for x=0.
    let (mut eq, mut carry, mut shift, mut last) = (E::ONE, E::ONE, E::ZERO, E::ONE);
    for (&t, &x) in tau.iter().zip(&rx) {
        let same = t * x + (E::ONE - t) * (E::ONE - x);
        shift = shift * same + carry * (E::ONE - t) * x;
        carry *= t * (E::ONE - x);
        last *= t * x;
        eq *= same;
    }
    row[EQ] = eq;
    row[NOT_LAST] = eq - last;
    row[SHIFT] = shift;
    if eval(c, &row, gamma, &weights) != claim {
        return None;
    }
    Some(col_claim(&mut st.transcript, &cols, rx))
}
