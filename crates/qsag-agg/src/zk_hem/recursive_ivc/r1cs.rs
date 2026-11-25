//! Row and column sumchecks over the fixed-size assignment table. A verifier
//! returns its single evaluation of the two fixed public constraint matrices
//! (selected by kind, and by the A/B/C coordinates). The root checks it on the
//! compiled shapes. Internal nodes use the matrix sumcheck in matrix.rs.
use super::super::relation::Shape;
use super::super::v2::protocol::{self as v2, Mask};
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Acc {
    pub point: Vec<E>,
    pub value: E,
}
impl Acc {
    pub fn dummy(log: usize) -> Self {
        let mut point = vec![E::ZERO; 2 * log + 3];
        point[2 * log] = E::ONE;
        point[2 * log + 1] = E::ONE; // fourth plane is the zero matrix
        Self {
            point,
            value: E::ZERO,
        }
    }
}
#[derive(Clone)]
pub(super) struct Claim<W> {
    pub point: Vec<Quint<W>>,
    pub value: Quint<W>,
}
impl<W: Base> Claim<W> {
    pub fn alloc<B: Wide<W = W>>(b: &mut B, x: &Acc) -> Self {
        Self {
            point: x.point.iter().map(|&q| Quint::alloc(b, q)).collect(),
            value: Quint::alloc(b, x.value),
        }
    }
    pub fn words(&self) -> Vec<W> {
        self.point
            .iter()
            .chain(core::iter::once(&self.value))
            .flat_map(|x| x.0.clone())
            .collect()
    }
    pub fn digest<B: Wide<W = W>>(&self, b: &mut B) -> [W; 7] {
        let mut tr = Duplex::new();
        tr.frame(b, b"IVC-MATRIX-POINT", &self.words());
        core::array::from_fn(|i| tr.0[i].clone())
    }
}
impl Claim<F> {
    pub fn from_acc(x: &Acc) -> Self {
        Self::alloc(&mut Native::default(), x)
    }
    pub fn native(&self) -> Acc {
        Acc {
            point: self.point.iter().map(|x| E(x.0)).collect(),
            value: E(self.value.0),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Argument {
    pub acc: Acc,
    pub root: Digest,
    pub nonce: [F; 4],
    pub row: Vec<Vec<E>>,
    pub abc: [E; 3],
    pub col: Vec<Vec<E>>,
    pub matrix: E,
    pub z: E,
    pub opening: FixedPathWhirW24,
}
impl Argument {
    pub fn fits(&self, cfg: &IvcStepConfig) -> bool {
        self.acc.point.len() == 2 * cfg.log_cells + 3
            && self.row.len() == cfg.log_cells
            && self.row.iter().all(|r| r.len() == 10)
            && self.col.len() == cfg.log_cells
            && self.col.iter().all(|r| r.len() == 3)
            && self.opening.fits(cfg)
    }

    pub fn blank(cfg: &IvcStepConfig) -> Self {
        Self {
            acc: Acc::dummy(cfg.log_cells),
            root: [F::ZERO; 7],
            nonce: [F::ZERO; 4],
            row: vec![vec![E::ZERO; 10]; cfg.log_cells],
            abc: [E::ZERO; 3],
            col: vec![vec![E::ZERO; 3]; cfg.log_cells],
            matrix: E::ZERO,
            z: E::ZERO,
            opening: FixedPathWhirW24::blank(cfg),
        }
    }
}
fn start<B: Wide>(
    b: &mut B,
    cfg: &IvcStepConfig,
    kind: &B::W,
    public: &[B::W],
    nonce: &[B::W; 4],
    root: &[B::W; 7],
) -> Duplex<B::W> {
    let mut tr = Duplex(cfg.transcript().0.map(B::W::constant));
    tr.frame(b, b"IVC-R1CS-v1", core::slice::from_ref(kind));
    tr.frame(b, b"PUBLIC", public);
    tr.frame(b, b"TREE_NONCE", nonce);
    tr.frame(b, b"WITNESS", root);
    tr
}
pub(super) fn sumcheck<B: Wide>(
    b: &mut B,
    tr: &mut Duplex<B::W>,
    label: &[u8],
    mut claim: Quint<B::W>,
    rounds: &[Vec<E>],
) -> (Quint<B::W>, Vec<Quint<B::W>>) {
    let mut point = Vec::with_capacity(rounds.len());
    for co in rounds {
        let p: Vec<_> = co.iter().map(|&v| Quint::alloc(b, v)).collect();
        p.iter()
            .fold(p[0].clone(), |a, c| a.add(c))
            .equal(b, &claim);
        tr.exts(b, label, &p);
        let r = tr.challenge(b, label);
        claim = p
            .iter()
            .rev()
            .cloned()
            .reduce(|a, c| a.mul(b, &r).add(&c))
            .unwrap();
        point.push(r);
    }
    (claim, point)
}
pub(super) fn eq<B: Wide>(b: &mut B, p: &[Quint<B::W>], q: &[Quint<B::W>]) -> Quint<B::W> {
    let one = Quint::constant(E::ONE);
    p.iter().zip(q).fold(one.clone(), |acc, (x, y)| {
        let factor = one.sub(x).sub(y).add(&x.mul(b, y).scale(F::TWO));
        acc.mul(b, &factor)
    })
}
fn prefix<B: Wide>(b: &mut B, point: &[Quint<B::W>], k: usize) -> Quint<B::W> {
    let one = Quint::constant(E::ONE);
    // Fixed topology even if one of the counts has leading zeroes.
    point
        .iter()
        .enumerate()
        .fold(Quint::constant(E::ZERO), |v, (i, r)| {
            let bit = f(((k >> i) & 1) as u64);
            let a = one.sub(r);
            let factor = a.add(&r.scale(F::TWO).sub(&one).scale(bit));
            v.mul(b, &factor).add(&a.scale(bit))
        })
}
fn combine<B: Wide>(b: &mut B, u: &Quint<B::W>, v: &Quint<B::W>) -> [Quint<B::W>; 3] {
    let uv = u.mul(b, v);
    [
        Quint::constant(E::ONE).sub(u).sub(v).add(&uv),
        u.sub(&uv),
        v.sub(&uv),
    ]
}
// The extra column term binds assignment[0]=1 and every public input. Its
// coefficients are powers of lambda, fixed before the column challenge.
fn public_weights<B: Wide>(
    b: &mut B,
    l: &Quint<B::W>,
    public: &[B::W],
) -> (Vec<Quint<B::W>>, Quint<B::W>) {
    let mut weights = vec![l.clone()];
    let mut value = l.clone();
    for x in public {
        let w = weights.last().unwrap().mul(b, l);
        value = value.add(&w.by_base(b, x));
        weights.push(w);
    }
    (weights, value)
}
pub(super) fn verify<B: Wide>(
    b: &mut B,
    cfg: &IvcStepConfig,
    num_sbox: [usize; 2],
    kind: &B::W,
    stmt: &[B::W],
    proof: &Argument,
) -> (Claim<B::W>, Claim<B::W>) {
    let acc = Claim::alloc(b, &proof.acc);
    let mut public = stmt.to_vec();
    public.extend(acc.digest(b));
    let root = proof.root.map(|v| b.alloc(v));
    let nonce = proof.nonce.map(|v| b.alloc(v));
    let mut tr = start(b, cfg, kind, &public, &nonce, &root);
    let tau: Vec<_> = (0..cfg.log_cells)
        .map(|_| tr.challenge(b, b"TAU"))
        .collect();
    let (last, rx) = sumcheck(
        b,
        &mut tr,
        b"ROW_ROUND",
        Quint::constant(E::ZERO),
        &proof.row,
    );
    let abc = proof.abc.map(|v| Quint::alloc(b, v));
    let [a, bb, c] = &abc;
    let a2 = a.mul(b, a);
    let a4 = a2.mul(b, &a2);
    let a7 = a4.mul(b, &a2).mul(b, a);
    let ab = a.mul(b, bb);
    let sl = prefix(b, &rx, num_sbox[0]);
    let si = prefix(b, &rx, num_sbox[1]);
    let sel = sl.add(&si.sub(&sl).by_base(b, kind));
    let gate = sel.mul(b, &a7.sub(&ab)).add(&ab).sub(c);
    eq(b, &tau, &rx).mul(b, &gate).equal(b, &last);
    tr.exts(b, b"ROW_VALUES", &abc);
    let u = tr.challenge(b, b"SELECT_A");
    let v = tr.challenge(b, b"SELECT_B");
    let comb = combine(b, &u, &v);
    let lambda = tr.challenge(b, b"PUBLIC_BATCH");
    let (weights, mut col_claim) = public_weights(b, &lambda, &public);
    for (x, w) in abc.iter().zip(comb) {
        col_claim = col_claim.add(&x.mul(b, &w));
    }
    let (last, ry) = sumcheck(b, &mut tr, b"COL_ROUND", col_claim, &proof.col);
    let mut weights = weights;
    let l = weights.len().next_power_of_two().trailing_zeros() as usize;
    weights.resize(1 << l, Quint::constant(E::ZERO));
    let fold_vars = l.min(ry.len());
    for r in &ry[..fold_vars] {
        weights = weights
            .as_chunks::<2>()
            .0
            .iter()
            .map(|p| p[0].add(&r.mul(b, &p[1].sub(&p[0]))))
            .collect();
    }
    if weights.len() > 1 {
        // Witness domain `2^log_cells` is smaller than `1 + public.len()` (`ry.len() < l`):
        // emit an unsatisfiable constraint rather than panicking on `&ry[..l]`.
        b.equal(&B::W::constant(F::ONE), &B::W::constant(F::ZERO));
        weights.truncate(1);
    }
    let mut public_col = weights.pop().unwrap();
    for r in &ry[fold_vars..] {
        public_col = public_col.mul(b, &Quint::constant(E::ONE).sub(r));
    }
    let matrix = Quint::alloc(b, proof.matrix);
    let z = Quint::alloc(b, proof.z);
    matrix.add(&public_col).mul(b, &z).equal(b, &last);
    tr.exts(b, b"TERMINAL", &[matrix.clone(), z.clone()]);
    verifier::check(b, cfg, &tr.0[..7], &nonce, &root, &ry, &z, &proof.opening);
    let mut point = rx;
    point.extend(ry);
    point.extend([u, v, Quint::base(kind.clone())]);
    (
        acc,
        Claim {
            point,
            value: matrix,
        },
    )
}
#[allow(clippy::too_many_arguments)]
pub(super) fn prove(
    cfg: &IvcStepConfig,
    shape: &Shape,
    kind: bool,
    stmt: &IvcSubtreeStatement,
    acc: Acc,
    assignment: Vec<F>,
    seed: &[u8; 32],
    #[cfg(feature = "vulkan")] gpu: Option<&qsag_accel::vulkan::VulkanFp5Session<'_>>,
) -> Option<Argument> {
    use qsag_core::wipe::SecretBuffer;
    let mut z = SecretBuffer::new(assignment);
    let n = 1 << cfg.log_cells;
    if z.len() != shape.num_vars
        || z.len() > n
        || shape.num_rows() > n
        || z[0] != F::ONE
        || shape.lookups().is_some()
    {
        return None;
    }
    let mut public = stmt.public_inputs().to_vec();
    public.extend(Claim::from_acc(&acc).digest(&mut Native::default()));
    if z.get(1..1 + public.len())? != public.as_slice() {
        return None;
    }
    let mut base = v2::row_tables(shape, &z, true)?;
    for t in &mut base {
        t.resize(n, F::ZERO);
    }
    z.resize(n, F::ZERO);
    let committed = IvcTableCommitment::commit_inner(
        cfg,
        &z,
        seed,
        #[cfg(feature = "vulkan")]
        gpu,
    )?;
    let nonce = committed.nonce();
    let root = committed.root();
    let mut tr = start(
        &mut Native::default(),
        cfg,
        &f(kind as u64),
        &public,
        &nonce,
        &root,
    );
    let tau: Vec<_> = (0..cfg.log_cells).map(|_| tr.squeeze_fp5(b"TAU")).collect();
    let zero_mask = Mask::from_coeffs(vec![vec![E::ZERO]; cfg.log_cells]);
    let (row, rx, abc) = v2::row_sumcheck(&mut tr, &tau, shape.num_sbox, base, &zero_mask, E::ZERO);
    tr.absorb_fp5_slice(b"ROW_VALUES", &abc);
    let u = tr.squeeze_fp5(b"SELECT_A");
    let v = tr.squeeze_fp5(b"SELECT_B");
    let comb = [
        (E::ONE - u) * (E::ONE - v),
        u * (E::ONE - v),
        (E::ONE - u) * v,
    ];
    let l = tr.squeeze_fp5(b"PUBLIC_BATCH");
    let rx_table = v2::eq_table(&rx);
    let mut cm = v2::column_table(shape, &rx_table[..shape.num_rows()], &comb, n);
    let mut w = l;
    for m in &mut cm[..1 + public.len()] {
        *m += w;
        w *= l;
    }
    let (col, ry, total) = v2::column_sumcheck(&mut tr, cm, &z, &zero_mask, E::ZERO);
    let eqy = v2::eq_table(&ry);
    let mut matrix = total;
    let mut w = l;
    for e in &eqy[..1 + public.len()] {
        matrix -= w * *e;
        w *= l;
    }
    let val = eqy
        .iter()
        .zip(z.iter())
        .fold(E::ZERO, |a, (x, y)| a + x.mul_base(*y));
    tr.absorb_fp5_slice(b"TERMINAL", &[matrix, val]);
    let (value, opening) = committed.open_inner(
        &tr.0[..7],
        &ry,
        #[cfg(feature = "vulkan")]
        gpu,
    )?;
    (val == value).then_some(Argument {
        acc,
        root,
        nonce,
        row,
        abc,
        col,
        matrix,
        z: val,
        opening,
    })
}
