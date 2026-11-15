//! Distributed zero-knowledge check of AND gates between one prover and two verifiers, over
//! `GF(2^128)`.
//!
//! In the replicated three-party engine of `crate::party_node`, party `P` sends one masked
//! product share per AND gate. Whether those messages were computed correctly is a statement
//! about values split between the other two parties: verifier `V1 = P - 1` holds one operand
//! share pair and the received messages, verifier `V2 = P + 1` holds the other pair. Per gate
//! `k` the statement is
//!
//! ```text
//! x0_k * y0_k + x1_k * y1_k = z_k        (x, and part of z, at V1;  y, and the rest of z, at V2)
//! ```
//!
//! and the prover knows every term. This module reduces all gates of a barrier to one inner
//! product and checks it with a polynomial identity test (the fully linear proof technique
//! of Boneh, Boyle, Corrigan-Gibbs, Gilboa and Ishai, in its one-round square-root form).
//!
//! 1. **First challenge (weights).** After every gate message is fixed, a joint coin gives
//!    weights `beta_k = gamma_row(k) * delta_col(k)`. The claim becomes
//!    `sum_k beta_k (x0_k y0_k + x1_k y1_k) = sum_k beta_k z_k`. If any gate is wrong, the two
//!    sides differ except with probability `2^-127`.
//! 2. **Proof.** The `2 * gates` products are laid out in `m` rows of `m` columns. Row `i`
//!    defines polynomials `f_i` (the weighted `x` entries) and `g_i` (the `y` entries) of
//!    degree `m + 1`: their values at nodes `1..=m` are the row's entries and their values at
//!    nodes `0` and `m + 1` are random masks, known to the prover and to the verifier that
//!    holds the entries. The prover computes `h = sum_i gamma_i f_i g_i` at the `2m + 3`
//!    nodes and splits it additively between the verifiers.
//! 3. **Second challenge (points).** A second joint coin, opened only after the verifiers
//!    hold their shares of `h`, gives two points `r1, r2`. The verifiers exchange
//!    `f_i(r), g_i(r)` and their shares of `h(r)` and of `sum_{j=1..m} h(j)`, and check
//!    `sum_i gamma_i f_i(r) g_i(r) = h(r)` at both points and that the node sum equals the
//!    claim. A wrong `h` survives both points with probability at most
//!    `((2m + 2) / 2^128)^2`.
//!
//! What each verifier sees of the other's inputs is two evaluations of a polynomial with two
//! masks it does not know, which are uniformly random. The functions here are the local
//! computations of the three roles; `crate::party_node` moves the messages.

use alloc::vec;
use alloc::vec::Vec;

use crate::hash::expand;

/// An element of `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`: `[low 64, high 64]` coefficients.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gf128(pub [u64; 2]);

impl Gf128 {
    pub const ZERO: Self = Self([0, 0]);
    pub const ONE: Self = Self([1, 0]);

    /// The element whose coefficient bits are the bits of `index`. Distinct indices give
    /// distinct elements; these are the interpolation nodes.
    pub const fn from_index(index: usize) -> Self {
        Self([index as u64, 0])
    }

    #[inline]
    #[must_use]
    pub const fn add(self, rhs: Self) -> Self {
        Self([self.0[0] ^ rhs.0[0], self.0[1] ^ rhs.0[1]])
    }

    #[inline]
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, rhs: Self) -> Self {
        let mut acc = [0u64; 2];
        qsag_asm::gf2_128_mul_acc_batch(&mut acc, &[self.0], &[rhs.0]);
        Self(acc)
    }

    /// Multiplicative inverse (`None` for zero), by `x^(2^128 - 2)`.
    pub fn inv(self) -> Option<Self> {
        if self == Self::ZERO {
            return None;
        }
        let mut square = self;
        let mut acc = Self::ONE;
        for _ in 1..128 {
            square = square.mul(square);
            acc = acc.mul(square);
        }
        Some(acc)
    }

    pub fn to_bytes(self) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&self.0[0].to_le_bytes());
        out[8..].copy_from_slice(&self.0[1].to_le_bytes());
        out
    }

    /// Decode 16 little-endian bytes.
    pub fn from_bytes(raw: &[u8; 16]) -> Self {
        let (words, _) = raw.as_chunks::<8>();
        Self([u64::from_le_bytes(words[0]), u64::from_le_bytes(words[1])])
    }
}

fn elements_of(raw: &[u8]) -> Vec<Gf128> {
    raw.as_chunks::<16>()
        .0
        .iter()
        .map(Gf128::from_bytes)
        .collect()
}

/// Encode field elements back to back.
pub fn encode_elements(elements: &[Gf128]) -> Vec<u8> {
    elements.iter().flat_map(|e| e.to_bytes()).collect()
}

/// Decode exactly `count` field elements, or `None` if the length is wrong.
pub fn decode_elements(raw: &[u8], count: usize) -> Option<Vec<Gf128>> {
    (count.checked_mul(16) == Some(raw.len())).then(|| elements_of(raw))
}

/// `count` pseudorandom field elements from `SHAKE256` over `domain` and `parts`.
pub fn expand_elements(domain: &[u8], parts: &[&[u8]], count: usize) -> Vec<Gf128> {
    let mut raw = vec![0u8; 16 * count];
    expand(domain, parts, &mut raw);
    let out = elements_of(&raw);
    qsag_asm::ct_memzero(&mut raw);
    out
}

/// Invert every element in place with one field inversion. Returns `false` (leaving the
/// slice unspecified) if an element is zero.
fn batch_invert(values: &mut [Gf128]) -> bool {
    let mut prefix = Vec::with_capacity(values.len());
    let mut acc = Gf128::ONE;
    for v in values.iter() {
        prefix.push(acc);
        acc = acc.mul(*v);
    }
    let Some(mut inv) = acc.inv() else {
        return false;
    };
    for (v, p) in values.iter_mut().zip(prefix).rev() {
        let original = *v;
        *v = inv.mul(p);
        inv = inv.mul(original);
    }
    true
}

/// Lagrange basis over the nodes `0, 1, ..., n - 1` (as [`Gf128::from_index`]).
pub struct NodeBasis {
    /// Barycentric weights `1 / prod_{l != j} (j - l)`.
    weights: Vec<Gf128>,
}

impl NodeBasis {
    pub fn new(nodes: usize) -> Self {
        let mut weights: Vec<Gf128> = (0..nodes)
            .map(|j| {
                (0..nodes)
                    .filter(|&l| l != j)
                    .fold(Gf128::ONE, |acc, l| acc.mul(Gf128::from_index(j ^ l)))
            })
            .collect();
        let invertible = batch_invert(&mut weights);
        debug_assert!(invertible, "distinct nodes have non-zero differences");
        Self { weights }
    }

    pub fn nodes(&self) -> usize {
        self.weights.len()
    }

    /// True if `point` is one of the nodes.
    pub fn contains(&self, point: Gf128) -> bool {
        point.0[1] == 0 && point.0[0] < self.weights.len() as u64
    }

    /// The values `lambda_j(point)` of all basis polynomials: a polynomial of degree below
    /// `n` with node values `v` evaluates to `sum_j lambda_j(point) * v_j`.
    pub fn coeffs_at(&self, point: Gf128) -> Vec<Gf128> {
        let n = self.weights.len();
        let diffs: Vec<Gf128> = (0..n).map(|l| point.add(Gf128::from_index(l))).collect();
        let mut out = vec![Gf128::ONE; n];
        let mut acc = Gf128::ONE;
        for (o, d) in out.iter_mut().zip(&diffs) {
            *o = acc;
            acc = acc.mul(*d);
        }
        acc = Gf128::ONE;
        for ((o, d), w) in out.iter_mut().zip(&diffs).zip(&self.weights).rev() {
            *o = o.mul(acc).mul(*w);
            acc = acc.mul(*d);
        }
        out
    }
}

/// `sum_j a_j * b_j`.
pub fn dot(a: &[Gf128], b: &[Gf128]) -> Gf128 {
    let n = a.len().min(b.len());
    if n == 0 {
        return Gf128::ZERO;
    }
    let mut acc = [0u64; 2];
    let mut lhs = [[0u64; 2]; 128];
    let mut rhs = [[0u64; 2]; 128];
    for (ca, cb) in a[..n].chunks(128).zip(b[..n].chunks(128)) {
        for (i, (x, y)) in ca.iter().zip(cb).enumerate() {
            lhs[i] = x.0;
            rhs[i] = y.0;
        }
        qsag_asm::gf2_128_mul_acc_batch(&mut acc, &lhs[..ca.len()], &rhs[..ca.len()]);
    }
    qsag_asm::volatile_fill(lhs.as_flattened_mut(), 0);
    qsag_asm::volatile_fill(rhs.as_flattened_mut(), 0);
    Gf128(acc)
}

/// Layout of one proof: `gates` AND gates in `m` rows of `m / 2` gates (two products each).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DzkShape {
    pub gates: usize,
    /// Rows, and product columns per row. Even.
    pub m: usize,
}

impl DzkShape {
    /// The smallest even `m` with `m * m >= 2 * gates`.
    pub fn for_gates(gates: usize) -> Self {
        let mut m = 2usize;
        while m * m < 2 * gates {
            m += 2;
        }
        Self { gates, m }
    }

    /// Gates per row.
    pub const fn half(&self) -> usize {
        self.m / 2
    }

    /// Nodes of a row polynomial: the `m` entries and two masks.
    pub const fn row_nodes(&self) -> usize {
        self.m + 2
    }

    /// Nodes of the product polynomial `h`.
    pub const fn h_nodes(&self) -> usize {
        2 * self.m + 3
    }
}

/// Weights of the first challenge: gate `k` in row `i`, position `c` has weight
/// `gamma[i] * delta[c]`.
pub struct DzkWeights {
    pub gamma: Vec<Gf128>,
    pub delta: Vec<Gf128>,
}

/// Expand the weights of `prover`'s proof from the first coin.
pub fn derive_weights(seed: &[u8; 32], prover: usize, shape: &DzkShape) -> DzkWeights {
    let mut all = expand_elements(
        b"QSAG.QUORUM.DZK.WEIGHTS/v1",
        &[
            seed,
            &(prover as u64).to_be_bytes(),
            &(shape.gates as u64).to_be_bytes(),
        ],
        shape.m + shape.half(),
    );
    let delta = all.split_off(shape.m);
    DzkWeights { gamma: all, delta }
}

/// The two evaluation points of `prover`'s proof from the second coin, or `None` in the
/// negligible case that they coincide or hit a node.
pub fn challenge_points(seed: &[u8; 32], prover: usize, shape: &DzkShape) -> Option<[Gf128; 2]> {
    let points = expand_elements(
        b"QSAG.QUORUM.DZK.POINTS/v1",
        &[
            seed,
            &(prover as u64).to_be_bytes(),
            &(shape.gates as u64).to_be_bytes(),
        ],
        2,
    );
    let is_node = |p: Gf128| p.0[1] == 0 && p.0[0] < shape.h_nodes() as u64;
    (points[0] != points[1] && !is_node(points[0]) && !is_node(points[1]))
        .then_some([points[0], points[1]])
}

#[inline]
fn bit(words: &[u64], gate: usize) -> u64 {
    (words[gate / 64] >> (gate % 64)) & 1
}

#[inline]
fn selected(term: Gf128, bit: u64) -> Gf128 {
    let mask = core::hint::black_box(0u64.wrapping_sub(bit & 1));
    Gf128([term.0[0] & mask, term.0[1] & mask])
}

// The only branch and all indices depend on public circuit dimensions.
fn column_bit(shape: &DzkShape, v0: &[u64], v1: &[u64], row: usize, col: usize) -> u64 {
    let gate = row * shape.half() + col / 2;
    if gate >= shape.gates {
        return 0;
    }
    bit(if col.is_multiple_of(2) { v0 } else { v1 }, gate)
}

/// `sum_k beta_k * bits_k` over the gates of the shape.
pub fn weighted_sum(shape: &DzkShape, weights: &DzkWeights, bits: &[u64]) -> Gf128 {
    let half = shape.half();
    let mut total = Gf128::ZERO;
    for (row, gamma) in weights.gamma.iter().enumerate() {
        let mut acc = Gf128::ZERO;
        for (c, delta) in weights.delta.iter().enumerate() {
            let gate = row * half + c;
            if gate >= shape.gates {
                break;
            }
            acc = acc.add(selected(*delta, bit(bits, gate)));
        }
        total = total.add(gamma.mul(acc));
    }
    total
}

/// Prover: the values of `h = sum_i gamma_i f_i g_i` at its `2m + 3` nodes.
///
/// `x0, x1, y0, y1` are bit vectors over the gates (bit `k` of word `k / 64`). `masks_f` and
/// `masks_g` hold two masks per row (`[2i]` at node 0, `[2i + 1]` at node `m + 1`).
#[allow(clippy::too_many_arguments)]
pub fn prove(
    shape: &DzkShape,
    weights: &DzkWeights,
    row_basis: &NodeBasis,
    x0: &[u64],
    x1: &[u64],
    y0: &[u64],
    y1: &[u64],
    masks_f: &[Gf128],
    masks_g: &[Gf128],
) -> Vec<Gf128> {
    let m = shape.m;
    let mut h = vec![Gf128::ZERO; shape.h_nodes()];
    let mut column_acc = vec![Gf128::ZERO; m];
    for (i, gamma) in weights.gamma.iter().enumerate() {
        for (col, acc) in column_acc.iter_mut().enumerate() {
            let xy = column_bit(shape, x0, x1, i, col) & column_bit(shape, y0, y1, i, col);
            *acc = acc.add(selected(*gamma, xy));
        }
    }
    for (col, acc) in column_acc.iter().enumerate() {
        h[col + 1] = weights.delta[col / 2].mul(*acc);
    }

    // Nodes 0 and m + 1: the masks.
    for (i, gamma) in weights.gamma.iter().enumerate() {
        h[0] = h[0].add(gamma.mul(masks_f[2 * i]).mul(masks_g[2 * i]));
        h[m + 1] = h[m + 1].add(gamma.mul(masks_f[2 * i + 1]).mul(masks_g[2 * i + 1]));
    }

    // Nodes m + 2 ..= 2m + 2: evaluate every row polynomial there.
    for (node, h_node) in h.iter_mut().enumerate().skip(m + 2) {
        let lambda = row_basis.coeffs_at(Gf128::from_index(node));
        let weighted: Vec<Gf128> = (0..m)
            .map(|col| lambda[col + 1].mul(weights.delta[col / 2]))
            .collect();
        let mut acc = Gf128::ZERO;
        for (i, gamma) in weights.gamma.iter().enumerate() {
            let mut f = lambda[0]
                .mul(masks_f[2 * i])
                .add(lambda[m + 1].mul(masks_f[2 * i + 1]));
            for (col, term) in weighted.iter().enumerate() {
                f = f.add(selected(*term, column_bit(shape, x0, x1, i, col)));
            }
            let mut g = lambda[0]
                .mul(masks_g[2 * i])
                .add(lambda[m + 1].mul(masks_g[2 * i + 1]));
            for col in 0..m {
                g = g.add(selected(lambda[col + 1], column_bit(shape, y0, y1, i, col)));
            }
            acc = acc.add(gamma.mul(f).mul(g));
        }
        *h_node = acc;
    }
    h
}

/// Verifier holding the `x` side: `f_i(r)` for every row, given the row basis at `r`.
pub fn x_evals(
    shape: &DzkShape,
    weights: &DzkWeights,
    x0: &[u64],
    x1: &[u64],
    masks_f: &[Gf128],
    lambda: &[Gf128],
) -> Vec<Gf128> {
    let m = shape.m;
    let weighted: Vec<Gf128> = (0..m)
        .map(|col| lambda[col + 1].mul(weights.delta[col / 2]))
        .collect();
    (0..m)
        .map(|i| {
            let mut f = lambda[0]
                .mul(masks_f[2 * i])
                .add(lambda[m + 1].mul(masks_f[2 * i + 1]));
            for (col, term) in weighted.iter().enumerate() {
                f = f.add(selected(*term, column_bit(shape, x0, x1, i, col)));
            }
            f
        })
        .collect()
}

/// Verifier holding the `y` side: `g_i(r)` for every row, given the row basis at `r`.
pub fn y_evals(
    shape: &DzkShape,
    y0: &[u64],
    y1: &[u64],
    masks_g: &[Gf128],
    lambda: &[Gf128],
) -> Vec<Gf128> {
    let m = shape.m;
    (0..m)
        .map(|i| {
            let mut g = lambda[0]
                .mul(masks_g[2 * i])
                .add(lambda[m + 1].mul(masks_g[2 * i + 1]));
            for col in 0..m {
                g = g.add(selected(lambda[col + 1], column_bit(shape, y0, y1, i, col)));
            }
            g
        })
        .collect()
}

/// A verifier's share of `sum_{j=1..m} h(j)` from its share of `h`.
pub fn data_node_sum(shape: &DzkShape, h_share: &[Gf128]) -> Gf128 {
    h_share[1..=shape.m]
        .iter()
        .fold(Gf128::ZERO, |acc, v| acc.add(*v))
}

/// `sum_i gamma_i f_i(r) g_i(r)`: what `h(r)` must equal.
pub fn row_product_sum(weights: &DzkWeights, f_at_r: &[Gf128], g_at_r: &[Gf128]) -> Gf128 {
    weights
        .gamma
        .iter()
        .zip(f_at_r)
        .zip(g_at_r)
        .fold(Gf128::ZERO, |acc, ((gamma, f), g)| {
            acc.add(gamma.mul(*f).mul(*g))
        })
}

#[cfg(test)]
mod tests {
    #[test]
    fn hostile_element_count_cannot_wrap_to_a_valid_frame() {
        assert!(decode_elements(&[], usize::MAX / 16 + 1).is_none());
        assert!(decode_elements(&[0; 16], usize::MAX).is_none());
        assert!(decode_elements(&[0; 15], 1).is_none());
        assert_eq!(decode_elements(&[0; 16], 1), Some(vec![Gf128::ZERO]));
    }
    use super::*;
    use crate::hash::SeedRng;

    fn random_elements(rng: &mut SeedRng, n: usize) -> Vec<Gf128> {
        let mut raw = vec![0u8; 16 * n];
        rng.fill(&mut raw);
        elements_of(&raw)
    }

    fn random_words(rng: &mut SeedRng, n: usize) -> Vec<u64> {
        let mut raw = vec![0u8; 8 * n];
        rng.fill(&mut raw);
        raw.as_chunks::<8>()
            .0
            .iter()
            .map(|c| u64::from_le_bytes(*c))
            .collect()
    }

    #[test]
    fn field_arithmetic_is_a_field() {
        let mut rng = SeedRng::new(&[1; 32], b"field");
        let v = random_elements(&mut rng, 12);
        for &[a, b, c] in v.as_chunks::<3>().0 {
            assert_eq!(a.mul(b), b.mul(a));
            assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
            assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));
            assert_eq!(a.mul(Gf128::ONE), a);
            assert_eq!(a.mul(a.inv().unwrap()), Gf128::ONE);
            assert_eq!(a.mul(b).0, qsag_asm::gf2_128_mul_portable(a.0, b.0));
            assert_eq!(Gf128::from_bytes(&a.to_bytes()), a);
        }
        assert_eq!(Gf128::ZERO.inv(), None);
        // x * x^127 reduces to x^7 + x^2 + x + 1.
        let x = Gf128([2, 0]);
        let x127 = Gf128([0, 1 << 63]);
        assert_eq!(x.mul(x127), Gf128([0x87, 0]));
        let mut batch = v.clone();
        assert!(batch_invert(&mut batch));
        for (a, inv) in v.iter().zip(&batch) {
            assert_eq!(a.inv(), Some(*inv));
        }
        let mut with_zero = vec![v[0], Gf128::ZERO];
        assert!(!batch_invert(&mut with_zero));
    }

    #[test]
    fn node_basis_interpolates_polynomials() {
        let mut rng = SeedRng::new(&[2; 32], b"basis");
        for n in [1usize, 2, 5, 17] {
            let coeffs = random_elements(&mut rng, n);
            let eval = |x: Gf128| {
                coeffs
                    .iter()
                    .rev()
                    .fold(Gf128::ZERO, |acc, c| acc.mul(x).add(*c))
            };
            let basis = NodeBasis::new(n);
            let values: Vec<Gf128> = (0..n).map(|j| eval(Gf128::from_index(j))).collect();
            for point in random_elements(&mut rng, 3) {
                assert!(!basis.contains(point));
                assert_eq!(dot(&basis.coeffs_at(point), &values), eval(point));
            }
            // At a node the basis is the indicator of that node.
            for j in 0..n {
                assert!(basis.contains(Gf128::from_index(j)));
                let lambda = basis.coeffs_at(Gf128::from_index(j));
                for (l, value) in lambda.iter().enumerate() {
                    assert_eq!(*value, if l == j { Gf128::ONE } else { Gf128::ZERO });
                }
            }
            assert!(!basis.contains(Gf128::from_index(n)));
        }
    }

    #[test]
    fn shapes_cover_their_gates() {
        for gates in [1usize, 2, 3, 64, 100, 1600, 38_400, 76_800] {
            let shape = DzkShape::for_gates(gates);
            assert_eq!(shape.m % 2, 0);
            assert!(shape.m * shape.m >= 2 * gates);
            assert!(shape.m == 2 || (shape.m - 2) * (shape.m - 2) < 2 * gates);
            assert!(shape.m * shape.half() >= gates);
        }
        assert_eq!(DzkShape::for_gates(38_400).m, 278);
    }

    struct Instance {
        shape: DzkShape,
        x0: Vec<u64>,
        x1: Vec<u64>,
        y0: Vec<u64>,
        y1: Vec<u64>,
        /// `z_k = x0_k y0_k + x1_k y1_k`.
        z: Vec<u64>,
        masks_f: Vec<Gf128>,
        masks_g: Vec<Gf128>,
    }

    fn instance(gates: usize, tag: u8) -> Instance {
        let mut rng = SeedRng::new(&[tag; 32], b"instance");
        let shape = DzkShape::for_gates(gates);
        let words = gates.div_ceil(64);
        let x0 = random_words(&mut rng, words);
        let x1 = random_words(&mut rng, words);
        let y0 = random_words(&mut rng, words);
        let y1 = random_words(&mut rng, words);
        let z = (0..words)
            .map(|w| (x0[w] & y0[w]) ^ (x1[w] & y1[w]))
            .collect();
        Instance {
            shape,
            x0,
            x1,
            y0,
            y1,
            z,
            masks_f: random_elements(&mut rng, 2 * shape.m),
            masks_g: random_elements(&mut rng, 2 * shape.m),
        }
    }

    /// Run both verifier checks on a (possibly modified) `h` and claim.
    fn verify(inst: &Instance, weights: &DzkWeights, h: &[Gf128], claim: Gf128) -> (bool, bool) {
        let shape = &inst.shape;
        let row_basis = NodeBasis::new(shape.row_nodes());
        let h_basis = NodeBasis::new(shape.h_nodes());
        let sum_ok = data_node_sum(shape, h) == claim;
        let points = challenge_points(&[0x77; 32], 0, shape).unwrap();
        let point_ok = points.iter().all(|&r| {
            let lambda = row_basis.coeffs_at(r);
            let f = x_evals(shape, weights, &inst.x0, &inst.x1, &inst.masks_f, &lambda);
            let g = y_evals(shape, &inst.y0, &inst.y1, &inst.masks_g, &lambda);
            row_product_sum(weights, &f, &g) == dot(&h_basis.coeffs_at(r), h)
        });
        (sum_ok, point_ok)
    }

    fn honest_h(inst: &Instance, weights: &DzkWeights) -> Vec<Gf128> {
        let row_basis = NodeBasis::new(inst.shape.row_nodes());
        prove(
            &inst.shape,
            weights,
            &row_basis,
            &inst.x0,
            &inst.x1,
            &inst.y0,
            &inst.y1,
            &inst.masks_f,
            &inst.masks_g,
        )
    }

    #[test]
    fn honest_proofs_verify_for_full_and_ragged_shapes() {
        for (gates, tag) in [(1usize, 1u8), (7, 2), (64, 3), (200, 4), (1600, 5)] {
            let inst = instance(gates, tag);
            let weights = derive_weights(&[0x33; 32], 0, &inst.shape);
            let h = honest_h(&inst, &weights);
            assert_eq!(h.len(), inst.shape.h_nodes());
            let claim = weighted_sum(&inst.shape, &weights, &inst.z);
            assert_eq!(
                verify(&inst, &weights, &h, claim),
                (true, true),
                "{gates} gates"
            );
        }
    }

    #[test]
    fn a_wrong_gate_fails_the_sum_and_patching_the_proof_fails_the_points() {
        let inst = instance(1600, 9);
        let weights = derive_weights(&[0x33; 32], 0, &inst.shape);
        let h = honest_h(&inst, &weights);
        for gate in [0usize, 777, 1599] {
            // The verifiers' view of gate `gate` is one bit off.
            let mut z = inst.z.clone();
            z[gate / 64] ^= 1 << (gate % 64);
            let wrong_claim = weighted_sum(&inst.shape, &weights, &z);
            assert_eq!(verify(&inst, &weights, &h, wrong_claim), (false, true));

            // A prover that knows the weights moves the difference into one node of h: the
            // sum now matches, and h is no longer the product polynomial.
            let half = inst.shape.half();
            let beta = weights.gamma[gate / half].mul(weights.delta[gate % half]);
            assert_eq!(
                wrong_claim,
                weighted_sum(&inst.shape, &weights, &inst.z).add(beta)
            );
            for node in [1usize, inst.shape.m] {
                let mut patched = h.clone();
                patched[node] = patched[node].add(beta);
                assert_eq!(
                    verify(&inst, &weights, &patched, wrong_claim),
                    (true, false)
                );
            }
        }
        // Changing h outside the data nodes keeps the sum and fails the points.
        let claim = weighted_sum(&inst.shape, &weights, &inst.z);
        for node in [0usize, inst.shape.m + 1, inst.shape.h_nodes() - 1] {
            let mut patched = h.clone();
            patched[node] = patched[node].add(Gf128::ONE);
            assert_eq!(verify(&inst, &weights, &patched, claim), (true, false));
        }
    }

    #[test]
    fn opened_evaluations_are_masked_by_the_row_masks() {
        // Two instances with different inputs: for any evaluations of the first there are
        // masks of the second that give the same evaluations, because the 2x2 system in
        // the two masks is invertible. Checked by solving for the masks.
        let a = instance(200, 21);
        let b = instance(200, 22);
        let shape = a.shape;
        let weights = derive_weights(&[0x33; 32], 0, &shape);
        let basis = NodeBasis::new(shape.row_nodes());
        let points = challenge_points(&[0x44; 32], 0, &shape).unwrap();
        let lambdas = [basis.coeffs_at(points[0]), basis.coeffs_at(points[1])];
        let target: Vec<Vec<Gf128>> = lambdas
            .iter()
            .map(|l| x_evals(&shape, &weights, &a.x0, &a.x1, &a.masks_f, l))
            .collect();
        let zero_masks = vec![Gf128::ZERO; 2 * shape.m];
        let base: Vec<Vec<Gf128>> = lambdas
            .iter()
            .map(|l| x_evals(&shape, &weights, &b.x0, &b.x1, &zero_masks, l))
            .collect();
        let m = shape.m;
        let (a00, a01) = (lambdas[0][0], lambdas[0][m + 1]);
        let (a10, a11) = (lambdas[1][0], lambdas[1][m + 1]);
        let det_inv = a00.mul(a11).add(a01.mul(a10)).inv().expect("invertible");
        let mut masks = Vec::with_capacity(2 * m);
        for i in 0..m {
            let d0 = target[0][i].add(base[0][i]);
            let d1 = target[1][i].add(base[1][i]);
            masks.push(d0.mul(a11).add(d1.mul(a01)).mul(det_inv));
            masks.push(d0.mul(a10).add(d1.mul(a00)).mul(det_inv));
        }
        for (l, want) in lambdas.iter().zip(&target) {
            assert_eq!(&x_evals(&shape, &weights, &b.x0, &b.x1, &masks, l), want);
        }
    }
}
