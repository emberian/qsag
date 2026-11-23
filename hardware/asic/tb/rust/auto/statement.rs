// Compile the Rust verifier's public row polynomial with symbolic TraceField inputs.
// SSA common subexpressions are shared. Last-use allocation packs three SRAM
// register numbers and an opcode into each 32-bit straight-line instruction.
use qsag_agg::sponge::{poseidon2_apply_me, poseidon2_apply_mi};
use qsag_agg::trace::{self, RowPublicEval, TraceField};
use qsag_agg::{SignerBitmap, ValidatorPublicKey, field::Goldilocks as F};
use std::{
    cell::RefCell,
    collections::HashMap,
    ops::{Add, AddAssign, Mul, Sub},
};
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
enum Node {
    Const(u64),
    Input(u32),
    Gate(u32, u32, u32),
}
#[derive(Default)]
struct Graph {
    nodes: Vec<Node>,
    ids: HashMap<Node, u32>,
}
thread_local! {static GRAPH:RefCell<Graph>=RefCell::new(Graph::default());}
#[derive(Clone, Copy, Default, Eq, PartialEq)]
struct Wire(u32);
fn node(n: Node) -> Wire {
    GRAPH.with_borrow_mut(|g| {
        let id = *g.ids.entry(n).or_insert_with(|| {
            let id = g.nodes.len() as u32;
            g.nodes.push(n);
            id
        });
        Wire(id)
    })
}
impl Wire {
    fn op(self, r: Self, op: u32) -> Self {
        if r == Self::ZERO && op <= 1 {
            return self;
        }
        if self == Self::ZERO && op == 0 {
            return r;
        }
        if op == 1 && self == r {
            return Self::ZERO;
        }
        if op == 2 {
            if self == Self::ZERO || r == Self::ZERO {
                return Self::ZERO;
            }
            if self == Self::ONE {
                return r;
            }
            if r == Self::ONE {
                return self;
            }
        }
        let result =
            GRAPH.with_borrow(
                |g| match (g.nodes[self.0 as usize], g.nodes[r.0 as usize]) {
                    (Node::Const(a), Node::Const(b)) => {
                        let (x, y) = (F::from_u64_reduced(a), F::from_u64_reduced(b));
                        Some(match op {
                            0 => x + y,
                            1 => x - y,
                            _ => x * y,
                        })
                    }
                    _ => None,
                },
            );
        if let Some(x) = result {
            return Self::from_base(x);
        }
        if op != 1 && self.0 > r.0 {
            node(Node::Gate(op, r.0, self.0))
        } else {
            node(Node::Gate(op, self.0, r.0))
        }
    }
    fn layer(st: &mut [Self; 12], f: fn(&mut [F; 12])) {
        let mut out = [Self::ZERO; 12];
        for (j, x) in st.iter().enumerate() {
            let mut col = [F::ZERO; 12];
            col[j] = F::ONE;
            f(&mut col);
            for (v, c) in out.iter_mut().zip(col) {
                *v += x.mul_base_f(c);
            }
        }
        *st = out;
    }
}
impl Add for Wire {
    type Output = Self;
    fn add(self, r: Self) -> Self {
        self.op(r, 0)
    }
}
impl Sub for Wire {
    type Output = Self;
    fn sub(self, r: Self) -> Self {
        self.op(r, 1)
    }
}
impl Mul for Wire {
    type Output = Self;
    fn mul(self, r: Self) -> Self {
        self.op(r, 2)
    }
}
impl AddAssign for Wire {
    fn add_assign(&mut self, r: Self) {
        *self = *self + r
    }
}
impl TraceField for Wire {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);
    fn from_base(x: F) -> Self {
        node(Node::Const(x.to_canonical_u64()))
    }
    fn from_u64(x: u64) -> Self {
        Self::from_base(F::from_u64_reduced(x))
    }
    fn mul_base_f(self, x: F) -> Self {
        self * Self::from_base(x)
    }
    fn sbox7(self) -> Self {
        let a = self * self;
        a * a * a * self
    }
    fn apply_me(st: &mut [Self; 12]) {
        Self::layer(st, poseidon2_apply_me)
    }
    fn apply_mi(st: &mut [Self; 12]) {
        Self::layer(st, poseidon2_apply_mi)
    }
}
fn put(out: &mut Vec<u8>, n: usize) {
    out.extend(u32::try_from(n).unwrap().to_le_bytes());
}
fn blob(out: &mut Vec<u8>, b: &[u8]) {
    put(out, b.len());
    out.extend(b);
}
fn compile(out: &mut Vec<u8>, g: &Graph, root: Wire, inputs: usize) {
    let mut uses = vec![0; g.nodes.len()];
    uses[root.0 as usize] = 1;
    for (i, n) in g.nodes.iter().enumerate().rev() {
        if uses[i] > 0
            && let Node::Gate(_, a, b) = *n
        {
            uses[a as usize] += 1;
            uses[b as usize] += 1;
        }
    }
    let mut free = Vec::new();
    let mut slots = vec![0u32; g.nodes.len()];
    let mut next = inputs as u32;
    let mut code = Vec::new();
    let mut constants = Vec::new();
    for (i, &n) in g.nodes.iter().enumerate() {
        if uses[i] == 0 {
            continue;
        }
        if let Node::Input(j) = n {
            slots[i] = j;
            continue;
        }
        let (op, a, b) = match n {
            Node::Gate(op, a, b) => {
                let ab = (op, slots[a as usize], slots[b as usize]);
                for v in [a, b] {
                    uses[v as usize] -= 1;
                    if uses[v as usize] == 0 && slots[v as usize] >= inputs as u32 {
                        free.push(slots[v as usize]);
                    }
                }
                ab
            }
            Node::Const(v) => {
                let j = constants.len() as u32;
                constants.push(v);
                (3, j >> 10, j & 1023)
            }
            _ => unreachable!(),
        };
        let dest = free.pop().unwrap_or_else(|| {
            next += 1;
            next - 1
        });
        assert!(next <= 1024 && a < 1024 && b < 1024);
        slots[i] = dest;
        code.push((op << 30) | (dest << 20) | (a << 10) | b);
    }
    put(out, next as usize);
    put(out, slots[root.0 as usize] as usize);
    put(out, constants.len());
    for c in constants {
        out.extend(c.to_le_bytes());
    }
    put(out, code.len());
    println!("HQM2 row program gates={} slots={}", code.len(), next);
    for op in code {
        out.extend(op.to_le_bytes());
    }
}
pub fn hqm(
    pks: &[ValidatorPublicKey],
    bm: &SignerBitmap,
    mode: &qsag_agg::SigningMode<'_>,
) -> Vec<u8> {
    use qsag_agg::SigningMode;
    let indices = bm.active_indices();
    let profile = pks[indices[0]].profile;
    assert!(qsag_agg::sig::validate_unique_active_committee(
        pks, bm, profile
    ));
    let program = trace::build_signer_program(profile);
    let (ops, uid, c0) = trace::index_unique_program_ops(&program);
    let mut out = vec![0; 4];
    out.extend(b"HQD1");
    blob(&mut out, &bm.to_bytes());
    let committee: Vec<u8> = pks.iter().flat_map(ValidatorPublicKey::to_bytes).collect();
    blob(&mut out, &committee);
    match mode {
        SigningMode::SharedMessage(msg) => {
            out.push(0);
            blob(&mut out, msg);
        }
        SigningMode::PerSignerMessages(ms) => {
            assert_eq!(ms.len(), indices.len());
            out.push(1);
            blob(&mut out, &qsag_agg::sponge::encode_multi_frame(ms));
        }
    }
    put(&mut out, program.len().ilog2() as usize);
    put(&mut out, indices.len());
    put(&mut out, ops.len());
    let mut table = Vec::new();
    let mut steps = Vec::new();
    for (id, c) in uid.iter().zip(c0) {
        let v = c.to_canonical_u64();
        let pos = table.iter().position(|&x| x == v).unwrap_or_else(|| {
            table.push(v);
            table.len() - 1
        });
        steps.extend(u16::try_from(*id).unwrap().to_le_bytes());
        steps.extend(u16::try_from(pos).unwrap().to_le_bytes());
    }
    put(&mut out, table.len());
    for c in table {
        out.extend(c.to_le_bytes());
    }
    out.extend(steps);
    GRAPH.with_borrow_mut(|g| *g = Graph::default());
    assert!(Wire::from_u64(0) == Wire::ZERO && Wire::from_u64(1) == Wire::ONE);
    let input = |j| node(Node::Input(j));
    let cols = std::array::from_fn(|i| input(1 + i as u32));
    let sels: Vec<_> = (0..ops.len()).map(|i| input(276 + i as u32)).collect();
    let public = RowPublicEval {
        active_signer: Wire::ONE,
        pk_seed: std::array::from_fn(|i| input(257 + i as u32)),
        pk_root: std::array::from_fn(|i| input(261 + i as u32)),
        mu: std::array::from_fn(|i| input(265 + i as u32)),
        step_c0: input(270),
        is_row_first: input(271),
        is_row_last: input(272),
        eq_tau: input(273),
        eq_not_last: input(274),
        shift_tau: input(275),
        gated_op_sels: &sels,
    };
    let root = trace::eval_batched_row_constraints_generic(&ops, &cols, &public, input(0));
    GRAPH.with_borrow(|g| compile(&mut out, g, root, 276 + ops.len()));
    let size = out.len() as u32;
    out[..4].copy_from_slice(&size.to_le_bytes());
    out
}
