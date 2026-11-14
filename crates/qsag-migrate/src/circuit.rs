//! Fixed-topology mixed-field ownership circuits and exact local conversions.
use crate::{
    scalar,
    secp256k1_ct::{Fp256, SECP_P},
};
use alloc::vec::Vec;
use core::cell::RefCell;
use qsag_accel::{
    ct::ct_zeroize_u64s,
    goldilocks::{GOLDILOCKS_PRIME, gl_add, gl_mul, gl_sub},
};

pub(crate) type Wire = usize;
pub(crate) type Value = [u64; 4];
pub(crate) const ZERO: Value = [0; 4];
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Domain {
    Bit,
    Gold,
    Secp,
    Ed,
}
impl Domain {
    pub(crate) fn inverse(self, a: Value) -> Value {
        let exp = scalar::sub(self.modulus(), [2, 0, 0, 0], self.modulus());
        let mut out = [1, 0, 0, 0];
        for i in (0..self.width()).rev() {
            out = self.mul(out, out);
            if (exp[i / 64] >> (i % 64)) & 1 != 0 {
                out = self.mul(out, a);
            }
        }
        out
    }
    pub(crate) fn modulus(self) -> Value {
        match self {
            Self::Bit => [2, 0, 0, 0],
            Self::Gold => [GOLDILOCKS_PRIME, 0, 0, 0],
            Self::Secp => SECP_P,
            Self::Ed => scalar::ED_PRIME,
        }
    }
    pub(crate) fn width(self) -> usize {
        match self {
            Self::Bit => 1,
            Self::Gold => 64,
            Self::Secp => 256,
            Self::Ed => 255,
        }
    }
    #[inline(always)]
    pub(crate) fn canonical(self, x: Value) -> bool {
        scalar::less(x, self.modulus())
    }
    #[inline(always)]
    pub(crate) fn add(self, a: Value, b: Value) -> Value {
        match self {
            Self::Bit => [a[0] ^ b[0], 0, 0, 0],
            Self::Gold => [gl_add(a[0], b[0]), 0, 0, 0],
            Self::Secp => (Fp256(a) + Fp256(b)).0,
            Self::Ed => scalar::add(a, b, scalar::ED_PRIME),
        }
    }
    #[inline(always)]
    pub(crate) fn sub(self, a: Value, b: Value) -> Value {
        match self {
            Self::Bit => self.add(a, b),
            Self::Gold => [gl_sub(a[0], b[0]), 0, 0, 0],
            Self::Secp => (Fp256(a) - Fp256(b)).0,
            Self::Ed => scalar::sub(a, b, scalar::ED_PRIME),
        }
    }
    #[inline(always)]
    pub(crate) fn mul(self, a: Value, b: Value) -> Value {
        match self {
            Self::Bit => [a[0] & b[0], 0, 0, 0],
            Self::Gold => [gl_mul(a[0], b[0]), 0, 0, 0],
            Self::Secp => (Fp256(a) * Fp256(b)).0,
            Self::Ed => crate::ed25519_ct::multiply_limbs(a, b),
        }
    }
}
#[derive(Clone, Copy)]
pub(crate) enum Op {
    Input,
    Constant(Value),
    Add(Wire, Wire),
    Sub(Wire, Wire),
    Scale(Wire, Value),
    Mul(Wire, Wire),
    Lift(Wire, usize),
    Digit(Wire, usize, usize),
}
pub(crate) struct Node {
    pub(crate) domain: Domain,
    pub(crate) op: Op,
    pub(crate) value: Value,
}
pub(crate) struct Circuit {
    pub(crate) nodes: Vec<Node>,
    pub(crate) outputs: Vec<Wire>,
}
impl Drop for Circuit {
    fn drop(&mut self) {
        for n in &mut self.nodes {
            ct_zeroize_u64s(&mut n.value);
        }
    }
}
#[derive(Default)]
pub(crate) struct Builder {
    nodes: RefCell<Vec<Node>>,
    outputs: RefCell<Vec<Wire>>,
}
impl Builder {
    fn push(&self, domain: Domain, op: Op, value: Value) -> Wire {
        let mut ns = self.nodes.borrow_mut();
        let w = ns.len();
        ns.push(Node { domain, op, value });
        w
    }
    pub(crate) fn finish(self) -> Circuit {
        Circuit {
            nodes: self.nodes.into_inner(),
            outputs: self.outputs.into_inner(),
        }
    }
    pub(crate) fn value(&self, w: Wire) -> Value {
        self.nodes.borrow()[w].value
    }
    pub(crate) fn domain(&self, w: Wire) -> Domain {
        self.nodes.borrow()[w].domain
    }
    pub(crate) fn constant(&self, d: Domain, x: Value) -> Wire {
        self.push(d, Op::Constant(x), x)
    }
    pub(crate) fn small(&self, d: Domain, x: u64) -> Wire {
        self.constant(d, [x, 0, 0, 0])
    }
    pub(crate) fn input(&self, x: u8) -> Wire {
        self.push(Domain::Bit, Op::Input, [u64::from(x), 0, 0, 0])
    }
    fn known(&self, w: Wire) -> Option<Value> {
        match self.nodes.borrow()[w].op {
            Op::Constant(v) => Some(v),
            _ => None,
        }
    }
    pub(crate) fn add(&self, a: Wire, b: Wire) -> Wire {
        let d = self.domain(a);
        assert_eq!(d, self.domain(b));
        match (self.known(a), self.known(b)) {
            (Some(x), Some(y)) => self.constant(d, d.add(x, y)),
            (Some(ZERO), _) => b,
            (_, Some(ZERO)) => a,
            _ => self.push(d, Op::Add(a, b), d.add(self.value(a), self.value(b))),
        }
    }
    pub(crate) fn sub(&self, a: Wire, b: Wire) -> Wire {
        let d = self.domain(a);
        assert_eq!(d, self.domain(b));
        if a == b {
            return self.constant(d, ZERO);
        }
        match (self.known(a), self.known(b)) {
            (Some(x), Some(y)) => self.constant(d, d.sub(x, y)),
            (_, Some(ZERO)) => a,
            _ => self.push(d, Op::Sub(a, b), d.sub(self.value(a), self.value(b))),
        }
    }
    pub(crate) fn mul(&self, a: Wire, b: Wire) -> Wire {
        let d = self.domain(a);
        assert_eq!(d, self.domain(b));
        match (self.known(a), self.known(b)) {
            (Some(x), Some(y)) => self.constant(d, d.mul(x, y)),
            (Some(x), _) => self.scale_value(b, x),
            (_, Some(y)) => self.scale_value(a, y),
            _ => self.push(d, Op::Mul(a, b), d.mul(self.value(a), self.value(b))),
        }
    }
    fn scale_value(&self, a: Wire, x: Value) -> Wire {
        let d = self.domain(a);
        if x == ZERO {
            return self.constant(d, ZERO);
        }
        if x == [1, 0, 0, 0] {
            return a;
        }
        let v = d.mul(self.value(a), x);
        if self.known(a).is_some() {
            self.constant(d, v)
        } else {
            self.push(d, Op::Scale(a, x), v)
        }
    }
    pub(crate) fn scale(&self, a: Wire, x: u64) -> Wire {
        self.scale_value(a, [x, 0, 0, 0])
    }
    pub(crate) fn not(&self, a: Wire) -> Wire {
        self.add(a, self.small(Domain::Bit, 1))
    }
    pub(crate) fn select(&self, b: Wire, t: Wire, f: Wire) -> Wire {
        self.add(f, self.mul(b, self.sub(t, f)))
    }
    pub(crate) fn output(&self, a: Wire) {
        self.outputs.borrow_mut().push(a);
    }
    pub(crate) fn equal(&self, a: Wire, b: Wire) {
        self.output(self.sub(a, b));
    }
    /// Each owner locally injects its own XOR share, then the arithmetic
    /// circuit reconstructs XOR using x+y-2xy. No cross-domain equality oracle.
    pub(crate) fn lift(&self, a: Wire, d: Domain) -> Wire {
        assert_eq!(self.domain(a), Domain::Bit);
        let parts: [Wire; 3] = core::array::from_fn(|p| {
            self.push(d, Op::Lift(a, p), if p == 0 { self.value(a) } else { ZERO })
        });
        let xor = |x, y| self.sub(self.add(x, y), self.scale(self.mul(x, y), 2));
        xor(xor(parts[0], parts[1]), parts[2])
    }
    pub(crate) fn pack(&self, bits: &[Wire], d: Domain) -> Wire {
        bits.iter().rev().fold(self.small(d, 0), |a, &bit| {
            self.add(self.scale(a, 2), self.lift(bit, d))
        })
    }
    pub(crate) fn add_bits(&self, a: &[Wire], b: &[Wire], carry: Wire) -> (Vec<Wire>, Wire) {
        let mut c = carry;
        let out = a
            .iter()
            .zip(b)
            .map(|(&x, &y)| {
                let xc = self.add(x, c);
                let yc = self.add(y, c);
                let s = self.add(xc, y);
                c = self.add(c, self.mul(xc, yc));
                s
            })
            .collect();
        (out, c)
    }
    pub(crate) fn constant_bits(&self, x: Value, width: usize) -> Vec<Wire> {
        (0..width)
            .map(|i| self.small(Domain::Bit, (x[i / 64] >> (i % 64)) & 1))
            .collect()
    }
    fn modular_add_bits(&self, a: &[Wire], b: &[Wire], d: Domain) -> Vec<Wire> {
        let (mut sum, carry) = self.add_bits(a, b, self.small(Domain::Bit, 0));
        sum.push(carry);
        let mut modulus = self.constant_bits(d.modulus(), a.len());
        modulus.push(self.small(Domain::Bit, 0));
        let complement: Vec<_> = modulus.iter().map(|&b| self.not(b)).collect();
        let (diff, no_borrow) = self.add_bits(&sum, &complement, self.small(Domain::Bit, 1));
        sum.iter()
            .zip(&diff)
            .take(a.len())
            .map(|(&s, &v)| self.select(no_borrow, v, s))
            .collect()
    }
    /// Canonically encode each local arithmetic share, then add and reduce
    /// the three encodings inside GF(2). Both opened owners are checked locally.
    pub(crate) fn bits(&self, a: Wire) -> Vec<Wire> {
        let d = self.domain(a);
        let width = d.width();
        let parts: [Vec<Wire>; 3] = core::array::from_fn(|p| {
            (0..width)
                .map(|i| {
                    let v = if p == 0 {
                        (self.value(a)[i / 64] >> (i % 64)) & 1
                    } else {
                        0
                    };
                    self.push(Domain::Bit, Op::Digit(a, p, i), [v, 0, 0, 0])
                })
                .collect()
        });
        self.modular_add_bits(
            &self.modular_add_bits(&parts[0], &parts[1], d),
            &parts[2],
            d,
        )
    }
    pub(crate) fn require_scalar(&self, bits: &[Wire], order: Value) {
        let complement: Vec<_> = self
            .constant_bits(order, 256)
            .iter()
            .map(|&b| self.not(b))
            .collect();
        let (_, ge) = self.add_bits(bits, &complement, self.small(Domain::Bit, 1));
        self.output(ge);
        let all_zero = bits
            .iter()
            .fold(self.small(Domain::Bit, 1), |a, &b| self.mul(a, self.not(b)));
        self.output(all_zero);
    }
    pub(crate) fn inverse(&self, a: Wire) -> Wire {
        let d = self.domain(a);
        // A private field input, independently shared just like the scalar bits.
        // Only the multiplication constraint defines its relation to a.
        let out = self.push(d, Op::Input, d.inverse(self.value(a)));
        self.equal(self.mul(out, a), self.small(d, 1));
        out
    }
}

#[inline(always)]
pub(crate) fn local(node: &Node, party: usize, wires: &[Value]) -> Value {
    let d = node.domain;
    match node.op {
        Op::Constant(v) => {
            if party == 0 {
                v
            } else {
                ZERO
            }
        }
        Op::Add(a, b) => d.add(wires[a], wires[b]),
        Op::Sub(a, b) => d.sub(wires[a], wires[b]),
        Op::Scale(a, v) => d.mul(wires[a], v),
        Op::Lift(a, owner) => {
            if party == owner {
                wires[a]
            } else {
                ZERO
            }
        }
        Op::Digit(a, owner, bit) => {
            if party == owner {
                [(wires[a][bit / 64] >> (bit % 64)) & 1, 0, 0, 0]
            } else {
                ZERO
            }
        }
        Op::Input | Op::Mul(_, _) => ZERO,
    }
}
