//! One unmasked Stage-0 oracle and a sequence of affine-folded quintic oracles.
//! Query positions are drawn only after the next root and OOD values (or final
//! polynomial) have been absorbed. The transcript determines every payload length.
use super::tree::Hash;
use super::*;
use crate::field::GoldilocksOps as _;
use crate::zk_hem::v2::hash::{CanopyTree, multiproof_len, verify_canopy};

enum Codeword {
    Base(Vec<F>),
    Extension(Vec<E>),
}

impl Codeword {
    fn symbols(&self, dims: &pcs::StageDims, j: usize) -> Vec<u8> {
        let mut bytes = Vec::new();
        match self {
            Self::Base(v) => {
                for x in pcs::fiber(v, dims, j) {
                    bytes.extend_from_slice(&x.to_le_bytes());
                }
            }
            Self::Extension(v) => write_es(&mut bytes, &pcs::fiber(v, dims, j)),
        }
        bytes
    }
}

struct Oracle<const N: usize> {
    code: Codeword,
    tree: CanopyTree<N>,
}

fn commit<const N: usize>(
    hash: impl Hash<N>,
    stage: usize,
    d: &pcs::StageDims,
    code: Codeword,
) -> Oracle<N> {
    let mut leaves = vec![[0; N]; d.fibers];
    crate::pcs::fill_indexed(&mut leaves, |i| hash.leaf(stage, i, &code.symbols(d, i)));
    Oracle {
        code,
        tree: CanopyTree::build(hash, stage as u8, leaves),
    }
}

fn decode_fiber(stage: usize, mut raw: &[u8], arity: usize) -> Option<Vec<E>> {
    (0..arity)
        .map(|_| {
            if stage == 0 {
                F::from_canonical_u64(u64::from_le_bytes(take(&mut raw)?)).map(E::from_base)
            } else {
                read_e(&mut raw)
            }
        })
        .collect()
}

type Shifts = Vec<(F, E)>;

fn indices(ch: &mut Transcript, d: &pcs::StageDims) -> Vec<usize> {
    ch.squeeze_distinct_indices(b"QUERY", d.fibers, d.queries)
}

fn answer<const N: usize>(
    oracle: &Oracle<N>,
    stage: usize,
    d: &pcs::StageDims,
    chals: &[[E; 3]],
    ch: &mut Transcript,
    out: &mut Vec<u8>,
) -> Shifts {
    let idx = indices(ch, d);
    let mut shifts = Vec::with_capacity(idx.len());
    for &j in &idx {
        let bytes = oracle.code.symbols(d, j);
        let vals = decode_fiber(stage, &bytes, d.arity()).expect("encoded canonical symbols");
        shifts.push((
            d.fiber_image(j),
            pcs::fold_fiber(vals, d.fiber_base(j), chals),
        ));
        out.extend(bytes);
    }
    for sibling in oracle.tree.open(&idx) {
        out.extend_from_slice(&sibling);
    }
    shifts
}

fn check<const N: usize, H: Hash<N>>(
    h: H,
    root: &[u8; N],
    stage: usize,
    d: &pcs::StageDims,
    chals: &[[E; 3]],
    ch: &mut Transcript,
    input: &mut &[u8],
) -> Option<Shifts> {
    let idx = indices(ch, d);
    let mut leaves = Vec::with_capacity(idx.len());
    let mut shifts = Vec::with_capacity(idx.len());
    for &j in &idx {
        let bytes = input.split_off(..d.arity() * if stage == 0 { 8 } else { 40 })?;
        leaves.push((j, h.leaf(stage, j, bytes)));
        let vals = decode_fiber(stage, bytes, d.arity())?;
        shifts.push((
            d.fiber_image(j),
            pcs::fold_fiber(vals, d.fiber_base(j), chals),
        ));
    }
    let siblings = (0..multiproof_len(d.log_leaves(), &idx))
        .map(|_| take(input).filter(H::canonical))
        .collect::<Option<Vec<_>>>()?;
    verify_canopy(h, stage as u8, d.log_leaves(), root, &leaves, &siblings).then_some(shifts)
}

fn ood_points<const K: usize>(ch: &mut Transcript) -> [E; K] {
    core::array::from_fn(|_| ch.squeeze_fp5(b"OOD_POINT"))
}

fn first_claim(ch: &mut Transcript, points: [E; 5], values: &[E; 5], claim: &mut E) -> Vec<(E, E)> {
    ch.absorb_fp5_slice(b"FIRST_OOD", values);
    points
        .into_iter()
        .zip(values)
        .map(|(p, &v)| {
            let w = ch.squeeze_fp5(b"OOD_WEIGHT");
            *claim += w * v;
            (w, p)
        })
        .collect()
}

fn tensor(point: &[E]) -> Vec<E> {
    let mut kernel = vec![E::ONE; 1 << point.len()];
    for (i, &r) in point.iter().enumerate() {
        let (lo, hi) = kernel[..2 << i].split_at_mut(1 << i);
        for (&x, y) in lo.iter().zip(hi) {
            *y = x * r;
        }
    }
    kernel
}

fn fold<T: pcs::Coef>(
    coeffs: &[T],
    state: &mut pcs::Folding,
    step_vars: usize,
    ch: &mut Transcript,
    out: &mut Vec<u8>,
) -> (Vec<E>, Vec<[E; 3]>) {
    let mut poly = Vec::new();
    let mut challenges = Vec::with_capacity(step_vars);
    for i in 0..step_vars {
        let result = if i == 0 {
            pcs::prove_fold(coeffs, state, 0, ch)
        } else {
            pcs::prove_fold(&poly, state, 0, ch)
        };
        let (next, values, chal) = result.expect("public folds have no mask-rank guard");
        write_es(out, &values);
        challenges.push(chal);
        poly = next;
    }
    (poly, challenges)
}

pub(super) fn prove<const N: usize>(
    hash: impl Hash<N>,
    mut st: Statement,
    rows: Vec<[F; NUM_TRACE_COLS]>,
) -> Result<Vec<u8>, Error> {
    let coeffs = crate::pcs::hypercube_to_monomial_coeffs(rows.as_flattened());
    let d0 = st.dims[0];
    let mut oracle = commit(
        hash,
        0,
        &d0,
        Codeword::Base(pcs::encode_base(&coeffs, d0.log_domain)),
    );
    let root = oracle.tree.root();
    let mut out = root.to_vec();
    st.transcript.absorb(b"ROOT", &root);
    let (point, mut claim) =
        rows::prove(&mut st, rows, &mut out).ok_or(Error::InconsistentTrace)?;
    let ch = &mut st.transcript;
    let points = ood_points(ch);
    let values = pcs::eval_poly(&coeffs, points);
    write_es(&mut out, &values);
    let terms = first_claim(ch, points, &values, &mut claim);
    let mut kernel = tensor(&point);
    pcs::add_points(&mut kernel, &terms);
    let mut state = pcs::Folding {
        kernel,
        points: terms,
        claim,
    };
    let (mut poly, mut challenges) = fold(&coeffs, &mut state, d0.step_vars, ch, &mut out);
    drop(coeffs);
    for (i, d) in st.dims.iter().enumerate().skip(1) {
        let next = commit(
            hash,
            i,
            d,
            Codeword::Extension(pcs::encode_ext(&poly, d.log_domain)),
        );
        let root = next.tree.root();
        out.extend_from_slice(&root);
        ch.absorb(b"ROOT", &root);
        let points = ood_points(ch);
        let values = pcs::eval_poly(&poly, points);
        write_es(&mut out, &values);
        ch.absorb_fp5_slice(b"OOD_EVAL", &values);
        let shifts = answer(&oracle, i - 1, &st.dims[i - 1], &challenges, ch, &mut out);
        oracle = next;
        let (terms, delta) = pcs::stage_claims(points, &values, &shifts, ch);
        pcs::add_points(&mut state.kernel, &terms);
        state.points.extend(terms);
        state.claim += delta;
        (poly, challenges) = fold(&poly, &mut state, d.step_vars, ch, &mut out);
    }
    let last = st.dims.len() - 1;
    write_es(&mut out, &poly);
    ch.absorb_fp5_slice(b"FINAL_POLY", &poly);
    answer(&oracle, last, &st.dims[last], &challenges, ch, &mut out);
    if ch.exhausted() {
        return Err(Error::TranscriptLimit);
    }
    Ok(out)
}

pub(super) fn verify<const N: usize, H: Hash<N>>(
    hash: H,
    mut st: Statement,
    mut input: &[u8],
) -> Option<()> {
    let mut root = take(&mut input).filter(H::canonical)?;
    st.transcript.absorb(b"ROOT", &root);
    let (point, mut claim) = rows::verify(&mut st, &mut input)?;
    let terms = [pcs::TensorTerm {
        weight: E::ONE,
        point,
    }];
    let mut kernel = pcs::KernelTerms::new(&terms);
    let ch = &mut st.transcript;
    let points = ood_points(ch);
    kernel.points = first_claim(ch, points, &read_es(&mut input)?, &mut claim);
    let mut challenges = Vec::new();
    for (i, d) in st.dims.iter().enumerate() {
        if i > 0 {
            let next = take(&mut input).filter(H::canonical)?;
            ch.absorb(b"ROOT", &next);
            let points = ood_points(ch);
            let values = read_es(&mut input)?;
            ch.absorb_fp5_slice(b"OOD_EVAL", &values);
            let shifts = check(
                hash,
                &root,
                i - 1,
                &st.dims[i - 1],
                &challenges,
                ch,
                &mut input,
            )?;
            let (terms, delta) = pcs::stage_claims(points, &values, &shifts, ch);
            kernel.points.extend(terms);
            claim += delta;
            root = next;
        }
        challenges.clear();
        for _ in 0..d.step_vars {
            challenges.push(pcs::verify_fold(
                &read_es(&mut input)?,
                &mut claim,
                &mut kernel,
                ch,
            ));
        }
    }
    let last = st.dims.len() - 1;
    let d = &st.dims[last];
    let final_len = (1 << (d.vars - d.step_vars)) + 2;
    let poly = (0..final_len)
        .map(|_| read_e(&mut input))
        .collect::<Option<Vec<_>>>()?;
    if kernel.apply(&poly) != claim {
        return None;
    }
    ch.absorb_fp5_slice(b"FINAL_POLY", &poly);
    let shifts = check(hash, &root, last, d, &challenges, ch, &mut input)?;
    (!ch.exhausted()
        && input.is_empty()
        && shifts
            .iter()
            .all(|&(y, v)| pcs::eval_at_base(&poly, y) == v))
    .then_some(())
}
