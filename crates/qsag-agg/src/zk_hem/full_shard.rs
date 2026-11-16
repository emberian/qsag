//! Full-shard recursion: one committed relation that runs a `JortsPoseidon2` shard's whole
//! verifier, so a parent proof certifies signatures and not only openings.
//!
//! A child here is a *recursive shard proof*: the same 256-column trace and degree-8 row
//! sumcheck as a [`crate::arithmetize::ShardBatchProof`], but committed in the fixed-path
//! format of [`super::recursive_whir`] and driven by a field-native Poseidon2 transcript.
//! [`shard_gadget`] is the only definition of its verifier. Run on the native backend it
//! verifies a child; recorded as a relation it becomes the parent's constraint system; run
//! on the assignment backend it produces the parent's witness. For each child it enforces
//!
//! 1. the committee digest: the witnessed public keys hash to the public digest;
//! 2. the signer set: one Boolean per committee slot, set only on real members, summing to
//!    the public signer count (a member cannot be counted twice);
//! 3. each member's message representative `mu`, recomputed from its key and the public
//!    32-byte message exactly as [`crate::sig::compute_message_mu`] does;
//! 4. the Fiat-Shamir transcript: statement, signer bits and the witness commitment are
//!    absorbed before any challenge;
//! 5. every round of the row sumcheck, and the terminal check against the batched row
//!    constraints ([`crate::trace::eval_batched_row_constraints_generic`], the same function
//!    the native shard verifier calls) at the public inputs' multilinear evaluations;
//! 6. the multilinear evaluation of the 256 column values at the column point, and the
//!    fixed-path WHIR opening of the witness commitment at that claim.
//!
//! The parent's public statement per child is the committee digest, the message and the
//! signer count: no child proof, summary or locally verified evidence is an input of
//! [`verify_full_shard_merge`].
//!
//! Scope. Only `JortsPoseidon2` shards. The signer set is hidden; the count is public. The
//! verifier of a parent still evaluates the relation's matrices, so its time is linear in
//! the relation size, and a parent cannot be a child of another parent. The composed
//! soundness of this transcript has not been mechanized, and the regimes keep their
//! bounded-query assumptions. Recording the row constraints needs `std`.

use super::protocol::{self, HologramPublicProof, ShapeHologram, ShapeVerifierKey};
use super::recursive_whir::{
    Assignment, Backend, Base, ChildWhirStatement, Digest, Ext, FixedPathWhirParams,
    FixedPathWhirProof, Native, RecursiveWhirError, Transcript, bits, commit_for_recursion, f,
    open_for_recursion, verify_gadget,
};
use super::relation::{ConstraintSystem, Lc, Shape};
use crate::arithmetize::{
    ROW_SUMCHECK_WIRE_COEFFS, RowTranscript, ShardCircuit, ShardSigner, build_shard_witness,
    prove_shard_rows,
};
use crate::field::{Goldilocks as F, GoldilocksExt4 as E};
use crate::pcs::WhirSecurityRegime;
use crate::sig::{
    AggSigProfile, SignerBitmap, ValidatorPublicKey, ValidatorSignature, compute_message_mu,
    verify_individual_signature_with_mu,
};
use crate::sponge::{POSEIDON2_CONST_IV, poseidon2_apply_me, poseidon2_apply_mi, poseidon2_sbox7};
use crate::trace::{
    LOG_TRACE_COLS, NUM_TRACE_COLS, RowPublicEval, TraceField,
    eval_batched_row_constraints_generic,
};
use alloc::{vec, vec::Vec};
use core::cell::RefCell;

/// Bytes of the message every signer of a recursive shard signs.
pub const SHARD_MESSAGE_BYTES: usize = 32;
/// Public words of one child: committee digest, message bytes, signer count.
pub(crate) const PUBLIC_WORDS: usize = 4 + SHARD_MESSAGE_BYTES + 1;
const PROOF_LABEL: &[u8] = b"QSAG.FULL.SHARD.MERGE/v1";

// Transcript frame tags, disjoint from the opening transcript's (1..=31) and the leaf,
// node and merge domains of `recursive_whir`.
const VERSION: u64 = 0x4653_4852_4400_0001;
const T_COMMITTEE: u64 = 0x4653_434F_4D4D;
const T_PARAMS: u64 = 100;
const T_STATEMENT: u64 = 101;
const T_SIGNERS: u64 = 102;
const T_COMMITMENT: u64 = 103;
const T_TAU: u64 = 104;
const T_GAMMA: u64 = 105;
const T_ROUND: u64 = 106;
const T_ROUND_CHALLENGE: u64 = 107;
const T_COLUMNS: u64 = 108;
const T_COLUMN_POINT: u64 = 109;
/// Header of the opening statement. The opening is bound to the shard by its commitment,
/// point and value, which are wires of the same relation.
const OPENING_HEADER: [u8; 32] = *b"QSAG.FULL.SHARD.OPENING/v1\0\0\0\0\0\0";

// ============================================================================
// The row constraints as a recorded operation list
// ============================================================================

/// A value of the row-constraint evaluator while it is being recorded (`#![no_std]` + `alloc`).
#[derive(Clone, Copy)]
enum Sym<'a> {
    Const(F),
    Wire(&'a RefCell<Vec<Node>>, u32),
}

impl core::fmt::Debug for Sym<'_> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Const(c) => fmt.debug_tuple("Const").field(c).finish(),
            Self::Wire(_, i) => fmt.debug_tuple("Wire").field(i).finish(),
        }
    }
}

impl Default for Sym<'_> {
    fn default() -> Self {
        Self::Const(F::ZERO)
    }
}

impl PartialEq for Sym<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::Const(a), Self::Const(b)) => a == b,
            (Self::Wire(_, i), Self::Wire(_, j)) => i == j,
            _ => false,
        }
    }
}

impl Eq for Sym<'_> {}

#[derive(Clone, Debug)]
enum Node {
    Const(F),
    Input(u32),
    Add(u32, u32),
    Sub(u32, u32),
    Scale(u32, F),
    Lin(Vec<(F, u32)>),
    Mul(u32, u32),
    Sbox(u32),
}

fn push_to<'a>(tape: &'a RefCell<Vec<Node>>, node: Node) -> Sym<'a> {
    let mut t = tape.borrow_mut();
    t.push(node);
    Sym::Wire(
        tape,
        u32::try_from(t.len() - 1).expect("row-constraint tape length"),
    )
}

fn node_idx<'a>(tape: &'a RefCell<Vec<Node>>, s: Sym<'a>) -> u32 {
    match s {
        Sym::Wire(_, idx) => idx,
        Sym::Const(c) if c == F::ZERO => 0,
        Sym::Const(c) if c == F::ONE => 1,
        Sym::Const(c) => {
            let mut t = tape.borrow_mut();
            t.push(Node::Const(c));
            u32::try_from(t.len() - 1).expect("row-constraint tape length")
        }
    }
}

fn scaled(s: Sym<'_>, k: F) -> Sym<'_> {
    match s {
        Sym::Const(c) => Sym::Const(c * k),
        Sym::Wire(..) if k == F::ONE => s,
        Sym::Wire(..) if k == F::ZERO => Sym::Const(F::ZERO),
        Sym::Wire(tape, idx) => push_to(tape, Node::Scale(idx, k)),
    }
}

fn linear_layer(st: &mut [Sym<'_>; 12], layer: fn(&mut [F; 12])) {
    let Some(tape) = st.iter().find_map(|s| match *s {
        Sym::Wire(t, _) => Some(t),
        Sym::Const(_) => None,
    }) else {
        let mut vals: [F; 12] = st.map(|s| match s {
            Sym::Const(c) => c,
            Sym::Wire(..) => unreachable!(),
        });
        layer(&mut vals);
        *st = vals.map(Sym::Const);
        return;
    };
    // Column `j` of the layer's matrix is its image of the `j`-th unit vector.
    let columns: [[F; 12]; 12] = core::array::from_fn(|j| {
        let mut unit = [F::ZERO; 12];
        unit[j] = F::ONE;
        layer(&mut unit);
        unit
    });
    let input_indices: [u32; 12] = st.map(|s| node_idx(tape, s));
    for (i, out) in st.iter_mut().enumerate() {
        *out = push_to(
            tape,
            Node::Lin((0..12).map(|j| (columns[j][i], input_indices[j])).collect()),
        );
    }
}

impl<'a> core::ops::Add for Sym<'a> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Sym::Const(a), Sym::Const(b)) => Sym::Const(a + b),
            (Sym::Const(a), _) if a == F::ZERO => rhs,
            (_, Sym::Const(b)) if b == F::ZERO => self,
            (Sym::Wire(tape, i), _) => {
                let j = node_idx(tape, rhs);
                push_to(tape, Node::Add(i, j))
            }
            (_, Sym::Wire(tape, j)) => {
                let i = node_idx(tape, self);
                push_to(tape, Node::Add(i, j))
            }
        }
    }
}
impl<'a> core::ops::AddAssign for Sym<'a> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl<'a> core::ops::Sub for Sym<'a> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Sym::Const(a), Sym::Const(b)) => Sym::Const(a - b),
            (_, Sym::Const(b)) if b == F::ZERO => self,
            (Sym::Wire(tape, i), _) => {
                let j = node_idx(tape, rhs);
                push_to(tape, Node::Sub(i, j))
            }
            (_, Sym::Wire(tape, j)) => {
                let i = node_idx(tape, self);
                push_to(tape, Node::Sub(i, j))
            }
        }
    }
}
impl<'a> core::ops::Mul for Sym<'a> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Sym::Const(a), _) => scaled(rhs, a),
            (_, Sym::Const(b)) => scaled(self, b),
            (Sym::Wire(tape, i), Sym::Wire(_, j)) => push_to(tape, Node::Mul(i, j)),
        }
    }
}
impl TraceField for Sym<'_> {
    const ZERO: Self = Sym::Const(F::ZERO);
    const ONE: Self = Sym::Const(F::ONE);
    fn from_base(b: F) -> Self {
        Sym::Const(b)
    }
    fn from_u64(v: u64) -> Self {
        Sym::Const(f(v))
    }
    fn mul_base_f(self, s: F) -> Self {
        scaled(self, s)
    }
    fn sbox7(self) -> Self {
        match self {
            Sym::Const(c) => Sym::Const(poseidon2_sbox7(c)),
            Sym::Wire(tape, idx) => push_to(tape, Node::Sbox(idx)),
        }
    }
    fn apply_me(st: &mut [Self; 12]) {
        linear_layer(st, poseidon2_apply_me);
    }
    fn apply_mi(st: &mut [Self; 12]) {
        linear_layer(st, poseidon2_apply_mi);
    }
}

/// A linear form wider than this is replaced by one wire per limb before it is used.
const MAX_FORM_TERMS: usize = 24;

/// The batched row polynomial of one shard profile as straight-line code over extension
/// values: inputs are the 256 column evaluations, then the public inputs in the order of
/// [`AirTape::inputs`].
#[derive(Clone, Debug)]
struct AirTape {
    nodes: Vec<Node>,
    pinned: Vec<bool>,
    output: u32,
    unique_ops: usize,
}

impl AirTape {
    fn record(circuit: &ShardCircuit) -> Self {
        let unique_ops = circuit.unique_ops.len();
        let tape = RefCell::new(vec![Node::Const(F::ZERO), Node::Const(F::ONE)]);
        let mut next = 0u32;
        let mut input = || {
            next += 1;
            push_to(&tape, Node::Input(next - 1))
        };
        let cols: [Sym<'_>; NUM_TRACE_COLS] = core::array::from_fn(|_| input());
        let active_signer = input();
        let pk_seed = core::array::from_fn(|_| input());
        let pk_root = core::array::from_fn(|_| input());
        let mu = core::array::from_fn(|_| input());
        let step_c0 = input();
        let is_row_first = input();
        let is_row_last = input();
        let eq_tau = input();
        let eq_not_last = input();
        let shift_tau = input();
        let gamma = input();
        let gated_op_sels: Vec<Sym<'_>> = (0..unique_ops).map(|_| input()).collect();
        let out = eval_batched_row_constraints_generic(
            &circuit.unique_ops,
            &cols,
            &RowPublicEval {
                active_signer,
                pk_seed,
                pk_root,
                mu,
                gated_op_sels: &gated_op_sels,
                step_c0,
                is_row_first,
                is_row_last,
                eq_tau,
                eq_not_last,
                shift_tau,
            },
            gamma,
        );
        let output = node_idx(&tape, out);
        let nodes = tape.into_inner();
        let mut width = Vec::with_capacity(nodes.len());
        let mut pinned = Vec::with_capacity(nodes.len());
        for node in &nodes {
            let w = match node {
                Node::Const(_) => 0,
                Node::Input(_) => 1,
                Node::Add(a, b) | Node::Sub(a, b) => width[*a as usize] + width[*b as usize],
                Node::Scale(a, _) => width[*a as usize],
                Node::Lin(terms) => terms.iter().map(|&(_, a)| width[a as usize]).sum(),
                Node::Mul(..) | Node::Sbox(_) => 7,
            };
            pinned.push(w > MAX_FORM_TERMS);
            width.push(if w > MAX_FORM_TERMS { 1 } else { w });
        }
        Self {
            nodes,
            pinned,
            output,
            unique_ops,
        }
    }

    /// Input vector in recording order.
    #[allow(clippy::too_many_arguments)]
    fn inputs<W: Base>(
        &self,
        cols: &[Ext<W>],
        active: Ext<W>,
        pk_seed: [Ext<W>; 4],
        pk_root: [Ext<W>; 4],
        mu: [Ext<W>; 5],
        step_c0: Ext<W>,
        row_first: Ext<W>,
        row_last: Ext<W>,
        kernels: [Ext<W>; 3],
        gamma: Ext<W>,
        gated_op_sels: Vec<Ext<W>>,
    ) -> Vec<Ext<W>> {
        assert_eq!(cols.len(), NUM_TRACE_COLS);
        assert_eq!(gated_op_sels.len(), self.unique_ops);
        let mut out = cols.to_vec();
        out.push(active);
        out.extend(pk_seed);
        out.extend(pk_root);
        out.extend(mu);
        out.extend([step_c0, row_first, row_last]);
        out.extend(kernels);
        out.push(gamma);
        out.extend(gated_op_sels);
        out
    }

    fn run<B: Backend>(&self, b: &mut B, inputs: &[Ext<B::W>]) -> Ext<B::W> {
        let mut values: Vec<Ext<B::W>> = Vec::with_capacity(self.nodes.len());
        for (node, &pinned) in self.nodes.iter().zip(&self.pinned) {
            let v = match node {
                Node::Const(c) => Ext::base(B::W::constant(*c)),
                Node::Input(i) => inputs[*i as usize].clone(),
                Node::Add(x, y) => values[*x as usize].add(&values[*y as usize]),
                Node::Sub(x, y) => values[*x as usize].sub(&values[*y as usize]),
                Node::Scale(x, k) => values[*x as usize].scale(*k),
                Node::Lin(terms) => terms.iter().fold(Ext::zero(), |acc, &(k, x)| {
                    acc.add(&values[x as usize].scale(k))
                }),
                Node::Mul(x, y) => {
                    let (x, y) = (values[*x as usize].clone(), &values[*y as usize]);
                    x.mul(b, y)
                }
                Node::Sbox(x) => {
                    let x = pin_ext(b, values[*x as usize].clone());
                    let x2 = x.mul(b, &x);
                    let x3 = x2.mul(b, &x);
                    let x6 = x3.mul(b, &x3);
                    x6.mul(b, &x)
                }
            };
            values.push(if pinned { pin_ext(b, v) } else { v });
        }
        values[self.output as usize].clone()
    }
}

// ============================================================================
// Gadget helpers
// ============================================================================

fn pin_ext<B: Backend>(b: &mut B, v: Ext<B::W>) -> Ext<B::W> {
    Ext(v.0.map(|w| b.pin(w)))
}
/// `x * y` as four fresh wires.
fn mul_pin<B: Backend>(b: &mut B, x: &Ext<B::W>, y: &Ext<B::W>) -> Ext<B::W> {
    let product = x.mul(b, y);
    pin_ext(b, product)
}
fn boolean<B: Backend>(b: &mut B, value: bool) -> B::W {
    let v = b.alloc(f(u64::from(value)));
    b.product(
        &v,
        &B::W::constant(F::ONE).minus(&v),
        &B::W::constant(F::ZERO),
    );
    v
}
/// Balanced sum, so that a sum of `n` forms copies `O(n log n)` terms.
fn sum_exts<W: Base>(mut items: Vec<Ext<W>>) -> Ext<W> {
    if items.is_empty() {
        return Ext::zero();
    }
    while items.len() > 1 {
        items = items
            .chunks(2)
            .map(|pair| match pair {
                [a, c] => a.add(c),
                [a] => a.clone(),
                _ => unreachable!(),
            })
            .collect();
    }
    items.pop().expect("nonempty sum")
}
/// `T[x] = eq(r, bits(x))`, in the index order of [`crate::field::build_eq_table_ext4`]:
/// bit `i` of `x` belongs to `r[i]`.
fn eq_table<B: Backend>(b: &mut B, r: &[Ext<B::W>]) -> Vec<Ext<B::W>> {
    let mut table = vec![Ext::one()];
    for ri in r.iter().rev() {
        let mut next = Vec::with_capacity(2 * table.len());
        for v in &table {
            let vr = mul_pin(b, v, ri);
            next.push(v.sub(&vr));
            next.push(vr);
        }
        table = next;
    }
    table
}
/// The eight bytes of the canonical representative of `limb`, least significant first.
fn le_bytes<B: Backend>(b: &mut B, limb: &B::W) -> [B::W; 8] {
    let bit = bits(b, limb, 64);
    core::array::from_fn(|k| {
        (0..8).fold(B::W::constant(F::ZERO), |acc, j| {
            acc.plus(&bit[8 * k + j].scale(f(1 << j)))
        })
    })
}

/// `mu` of one key for the shard message: the gadget form of
/// [`crate::sig::compute_message_mu`] for a `JortsPoseidon2` key (any height `6..=20`) and a 32-byte message.
fn message_mu<B: Backend>(
    b: &mut B,
    profile: AggSigProfile,
    key: &[B::W; 8],
    message: &[B::W],
) -> [B::W; 5] {
    assert_eq!(message.len(), SHARD_MESSAGE_BYTES);
    let byte = |v: u8| B::W::constant(f(u64::from(v)));
    // `encode_multi_frame(&[b"QSAG.MU/v2", &pk.to_bytes(), message])`.
    let mut frame = vec![byte(3), byte(10)];
    frame.extend(b"QSAG.MU/v2".iter().map(|&c| byte(c)));
    frame.extend([byte(65), byte(profile.to_u8())]);
    for limb in key {
        frame.extend(le_bytes(b, limb));
    }
    frame.push(byte(SHARD_MESSAGE_BYTES as u8));
    frame.extend(message.iter().cloned());
    // `bytes_to_limbs56`: a `0x01` delimiter, zero fill, big-endian seven-byte limbs.
    frame.push(byte(1));
    while !frame.len().is_multiple_of(7) {
        frame.push(byte(0));
    }
    let mut limbs: Vec<B::W> = frame
        .chunks(7)
        .map(|chunk| {
            chunk
                .iter()
                .fold(B::W::constant(F::ZERO), |acc, v| acc.scale(f(256)).plus(v))
        })
        .collect();
    // `poseidon2_pad`, rate 8.
    let fill = (8 - (limbs.len() + 1) % 8) % 8;
    if fill == 0 {
        limbs.push(B::W::constant(f((1 << 56) + 1)));
    } else {
        limbs.push(B::W::constant(F::ONE));
        limbs.extend((1..fill).map(|_| B::W::constant(F::ZERO)));
        limbs.push(B::W::constant(f(1 << 56)));
    }
    // `poseidon2_hash32`: capacity `(8, 4, 32, IV)`, output lanes as big-endian bytes.
    let mut state: [B::W; 12] = core::array::from_fn(|i| {
        B::W::constant(match i {
            8 => f(8),
            9 => f(4),
            10 => f(32),
            11 => f(POSEIDON2_CONST_IV),
            _ => F::ZERO,
        })
    });
    for block in limbs.chunks(8) {
        for (lane, limb) in state.iter_mut().zip(block) {
            *lane = lane.plus(limb);
        }
        b.perm(&mut state);
    }
    let mut digest = Vec::with_capacity(32);
    for lane in &state[..4] {
        let mut le = le_bytes(b, lane);
        le.reverse();
        digest.extend(le);
    }
    // `bytes32_to_limbs56`: four little-endian 56-bit limbs and one 32-bit limb.
    core::array::from_fn(|i| {
        let width = if i < 4 { 7 } else { 4 };
        let packed = (0..width).fold(B::W::constant(F::ZERO), |acc, k| {
            acc.plus(&digest[7 * i + k].scale(f(1 << (8 * k))))
        });
        b.pin(packed)
    })
}

/// Digest of a committee of `size` keys in `slots` slots; unused slots hold the zero key.
fn committee_gadget<B: Backend>(b: &mut B, size: &B::W, keys: &[[B::W; 8]]) -> [B::W; 4] {
    let mut message = vec![
        B::W::constant(f(VERSION)),
        B::W::constant(f(keys.len() as u64)),
        size.clone(),
    ];
    message.extend(keys.iter().flatten().cloned());
    let mut tr = Transcript::new();
    tr.absorb(b, T_COMMITTEE, &message);
    core::array::from_fn(|i| tr.state[i].clone())
}

/// The transcript up to and including the witness commitment.
fn bind_statement<B: Backend>(
    b: &mut B,
    params: &FullShardParams,
    public: &[B::W],
    signer_bits: &[B::W],
    commitment: &[B::W; 4],
) -> Transcript<B::W> {
    let mut tr = Transcript::new();
    let mut geometry = vec![
        f(VERSION),
        f(params.slots as u64),
        f(u64::from(params.profile.to_u8())),
        f(params.whir.domain_log2 as u64),
    ];
    geometry.extend(
        params
            .whir
            .schedule
            .to_bytes()
            .iter()
            .map(|&x| f(u64::from(x))),
    );
    let geometry: Vec<_> = geometry.into_iter().map(B::W::constant).collect();
    tr.absorb(b, T_PARAMS, &geometry);
    tr.absorb(b, T_STATEMENT, public);
    let packed: Vec<B::W> = signer_bits
        .chunks(32)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(B::W::constant(F::ZERO), |acc, (j, bit)| {
                    acc.plus(&bit.scale(f(1 << j)))
                })
        })
        .collect();
    tr.absorb(b, T_SIGNERS, &packed);
    tr.absorb(b, T_COMMITMENT, commitment);
    tr
}

/// Private inputs of one child.
pub(crate) struct ShardWitness<'a> {
    /// `slots` keys as `pk_seed ++ pk_root`; slots past `size` hold zeros.
    pub(crate) keys: Vec<[F; 8]>,
    pub(crate) size: usize,
    /// One flag per slot.
    pub(crate) active: Vec<bool>,
    pub(crate) proof: &'a RecursiveShardProof,
}

/// The whole verifier of one recursive shard proof. `public` is
/// `committee digest ++ message bytes ++ signer count`.
pub(crate) fn shard_gadget<B: Backend>(
    b: &mut B,
    params: &FullShardParams,
    public: &[B::W],
    w: &ShardWitness<'_>,
) {
    assert_eq!(public.len(), PUBLIC_WORDS);
    let zero = B::W::constant(F::ZERO);
    let one = B::W::constant(F::ONE);
    let circuit = &params.circuit;
    let log_local = circuit.log_local();
    let log_rows = circuit.log_rows();

    // 1. Committee: the witnessed keys are the ones the public digest names.
    let size = b.alloc(f(w.size as u64));
    let keys: Vec<[B::W; 8]> = w.keys.iter().map(|k| k.map(|v| b.alloc(v))).collect();
    let digest = committee_gadget(b, &size, &keys);
    for (computed, expected) in digest.iter().zip(public) {
        b.equal(computed, expected);
    }

    // 2. Signer set: a Boolean per slot, clear outside the first `size` slots; each
    //    signer's rank among the signers is its trace slot.
    let mut count = zero.clone();
    let mut real_sum = zero.clone();
    let mut previous_real: Option<B::W> = None;
    let mut signer_bits = Vec::with_capacity(params.slots);
    let mut ranks = Vec::with_capacity(params.slots);
    for i in 0..params.slots {
        let real = boolean(b, i < w.size);
        if let Some(previous) = &previous_real {
            b.product(&real, &one.minus(previous), &zero);
        }
        let bit = boolean(b, w.active[i]);
        b.product(&bit, &one.minus(&real), &zero);
        let rank = b.value(&count).to_canonical_u64();
        let rank_bits: Vec<B::W> = (0..params.log_slots)
            .map(|j| boolean(b, (rank >> j) & 1 == 1))
            .collect();
        let packed = rank_bits
            .iter()
            .enumerate()
            .fold(zero.clone(), |acc, (j, v)| acc.plus(&v.scale(f(1 << j))));
        b.product(&bit, &count.minus(&packed), &zero);
        count = b.pin(count.plus(&bit));
        real_sum = real_sum.plus(&real);
        previous_real = Some(real);
        signer_bits.push(bit);
        ranks.push(rank_bits);
    }
    b.equal(&real_sum, &size);
    b.equal(&count, &public[PUBLIC_WORDS - 1]);

    // 3. Every member's message representative.
    let message = &public[4..4 + SHARD_MESSAGE_BYTES];
    let mus: Vec<[B::W; 5]> = keys
        .iter()
        .map(|key| message_mu(b, params.profile, key, message))
        .collect();

    // 4. Statement and commitment, then the row-sumcheck challenges.
    let commitment: [B::W; 4] = w.proof.commitment.map(|v| b.alloc(v));
    let mut tr = bind_statement(b, params, public, &signer_bits, &commitment);
    let tau: Vec<Ext<B::W>> = (0..log_rows).map(|_| tr.ext(b, T_TAU)).collect();
    let gamma = tr.ext(b, T_GAMMA);

    // 5. Row sumcheck: `P(0) + P(1) = claim` holds by reconstruction of the linear term.
    let mut claim = Ext::zero();
    let mut challenges = Vec::with_capacity(log_rows);
    for round in &w.proof.row_sumcheck_polys {
        let wire: Vec<Ext<B::W>> = round.iter().map(|&c| Ext::alloc(b, c)).collect();
        tr.absorb_exts(b, T_ROUND, &wire);
        let challenge = tr.ext(b, T_ROUND_CHALLENGE);
        let high = wire[1..].iter().fold(Ext::zero(), |acc, c| acc.add(c));
        let linear = claim.sub(&wire[0].scale(F::TWO)).sub(&high);
        let mut coeffs = vec![wire[0].clone(), linear];
        coeffs.extend_from_slice(&wire[1..]);
        let (last, rest) = coeffs.split_last().expect("nonempty round polynomial");
        claim = rest
            .iter()
            .rev()
            .fold(last.clone(), |acc, c| mul_pin(b, &acc, &challenge).add(c));
        challenges.push(challenge);
    }
    let cols: Vec<Ext<B::W>> = w.proof.col_evals.iter().map(|&v| Ext::alloc(b, v)).collect();
    tr.absorb_exts(b, T_COLUMNS, &cols);
    let mut rx = challenges;
    rx.reverse();
    let (r_local, r_signer) = rx.split_at(log_local);

    // 6. Public inputs at the row point. Step-local tables are fixed by the program.
    let eq_local = eq_table(b, r_local);
    let mut op_terms: Vec<Vec<Ext<B::W>>> = vec![Vec::new(); circuit.unique_ops.len()];
    let mut step_terms = Vec::with_capacity(eq_local.len());
    for (t, weight) in eq_local.iter().enumerate() {
        op_terms[circuit.step_to_uid[t]].push(weight.clone());
        step_terms.push(weight.scale(circuit.step_c0_base[t]));
    }
    let step_c0 = pin_ext(b, sum_exts(step_terms));
    let row_first = pin_ext(b, eq_local[0].clone());
    let row_last = pin_ext(b, eq_local[eq_local.len() - 1].clone());

    // Signer tables: member `i`, when signing, sits in trace slot `rank_i`.
    let mut active_terms = Vec::with_capacity(params.slots);
    let mut key_terms: [Vec<Ext<B::W>>; 8] = core::array::from_fn(|_| Vec::new());
    let mut mu_terms: [Vec<Ext<B::W>>; 5] = core::array::from_fn(|_| Vec::new());
    for i in 0..params.slots {
        let mut weight: Option<Ext<B::W>> = None;
        for (r, bit) in r_signer.iter().zip(&ranks[i]) {
            // `bit ? r : 1 - r`.
            let factor = Ext::one()
                .sub(r)
                .add(&r.scale(F::TWO).sub(&Ext::one()).mul_base(b, bit));
            weight = Some(match weight {
                None => factor,
                Some(product) => mul_pin(b, &product, &factor),
            });
        }
        let weight = weight.expect("at least two signer slots");
        let gated = weight.mul_base(b, &signer_bits[i]);
        let gated = pin_ext(b, gated);
        for (terms, limb) in key_terms.iter_mut().zip(&keys[i]) {
            terms.push(gated.mul_base(b, limb));
        }
        for (terms, limb) in mu_terms.iter_mut().zip(&mus[i]) {
            terms.push(gated.mul_base(b, limb));
        }
        active_terms.push(gated);
    }
    let active = pin_ext(b, sum_exts(active_terms));
    let mut key_evals = key_terms
        .map(|terms| pin_ext(b, sum_exts(terms)))
        .into_iter();
    let pk_seed: [Ext<B::W>; 4] = core::array::from_fn(|_| key_evals.next().expect("pk_seed"));
    let pk_root: [Ext<B::W>; 4] = core::array::from_fn(|_| key_evals.next().expect("pk_root"));
    let mu = mu_terms.map(|terms| pin_ext(b, sum_exts(terms)));
    let gated_op_sels: Vec<Ext<B::W>> = op_terms
        .into_iter()
        .map(|terms| {
            let raw = pin_ext(b, sum_exts(terms));
            mul_pin(b, &active, &raw)
        })
        .collect();

    // Row kernels `eq(tau, r)`, `eq(tau, r) - prod(tau_i r_i)` and the shift kernel, as in
    // `eq_poly_ext4`, `eval_eq_not_last_ext4` and `eval_shift_kernel_ext4`.
    let mut eq = Ext::one();
    let mut all_ones = Ext::one();
    let mut factors = Vec::with_capacity(log_rows);
    let mut products = Vec::with_capacity(log_rows);
    for (t, x) in tau.iter().zip(&rx) {
        let product = mul_pin(b, t, x);
        let factor = Ext::one().sub(t).sub(x).add(&product.scale(F::TWO));
        eq = mul_pin(b, &eq, &factor);
        all_ones = mul_pin(b, &all_ones, &product);
        factors.push(factor);
        products.push(product);
    }
    let eq_not_last = pin_ext(b, eq.sub(&all_ones));
    let mut suffix = vec![Ext::one(); log_rows];
    let mut running = Ext::one();
    for j in (0..log_rows).rev() {
        suffix[j] = running.clone();
        running = mul_pin(b, &running, &factors[j]);
    }
    let mut shift_terms = Vec::with_capacity(log_rows);
    let mut carry = Ext::one();
    for j in 0..log_rows {
        // `carry * (1 - tau_j) * r_j * suffix_j`, then `carry *= tau_j * (1 - r_j)`.
        let head = mul_pin(b, &carry, &rx[j].sub(&products[j]));
        shift_terms.push(head.mul(b, &suffix[j]));
        carry = mul_pin(b, &carry, &tau[j].sub(&products[j]));
    }
    let shift = pin_ext(b, sum_exts(shift_terms));

    // 7. Terminal check of the row sumcheck.
    let inputs = params.tape.inputs(
        &cols,
        active,
        pk_seed,
        pk_root,
        mu,
        step_c0,
        row_first,
        row_last,
        [eq, eq_not_last, shift],
        gamma,
        gated_op_sels,
    );
    let expected = params.tape.run(b, &inputs);
    claim.equal(b, &expected);

    // 8. Column fold and the opening of the committed witness at `(r_z, r_x)`.
    let rz: Vec<Ext<B::W>> = (0..LOG_TRACE_COLS)
        .map(|_| tr.ext(b, T_COLUMN_POINT))
        .collect();
    let eq_cols = eq_table(b, &rz);
    let column_terms: Vec<Ext<B::W>> = eq_cols
        .iter()
        .zip(&cols)
        .map(|(weight, col)| weight.mul(b, col))
        .collect();
    let value = pin_ext(b, sum_exts(column_terms));
    let mut opening: Vec<B::W> = OPENING_HEADER
        .as_chunks::<4>()
        .0
        .iter()
        .map(|x| B::W::constant(f(u64::from(u32::from_le_bytes(*x)))))
        .collect();
    opening.extend(commitment);
    opening.extend(rz.iter().chain(&rx).flat_map(|v| v.0.clone()));
    opening.extend(value.0);
    verify_gadget(b, &params.whir, &opening, &w.proof.opening);
}

// ============================================================================
// Parameters, statements, child proofs
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FullShardError {
    /// Slot count, regime or fan-in outside the supported range.
    InvalidParameters,
    /// Committee, signer set or signature count inconsistent with the parameters.
    InvalidStatement,
    /// A signature does not verify for its key and the shard message.
    InvalidSignature,
    /// A child proof does not verify.
    InvalidChild,
    Whir(RecursiveWhirError),
}

/// Verifier geometry of recursive `JortsPoseidon2` shards (`height 6..=20`) with `slots` signer slots.
#[derive(Clone)]
pub struct FullShardParams {
    whir: FixedPathWhirParams,
    profile: AggSigProfile,
    slots: usize,
    log_slots: usize,
    circuit: ShardCircuit,
    tape: AirTape,
}

impl FullShardParams {
    /// `slots` is a power of two in `2..=max_shard_signers(JortsPoseidon2)`; `regime` must be
    /// a Poseidon2 regime. Uses default height-6 [`AggSigProfile::JortsPoseidon2`].
    pub fn new(regime: WhirSecurityRegime, slots: usize) -> Result<Self, FullShardError> {
        Self::with_profile(regime, AggSigProfile::JortsPoseidon2, slots)
    }

    /// Construct recursive shard parameters for any configurable `JortsPoseidon2` XMSS height
    /// (`6..=20`, up to $2^{20} = 1{,}048{,}576$ signatures per key at zero extra trace rows).
    pub fn with_profile(
        regime: WhirSecurityRegime,
        profile: AggSigProfile,
        slots: usize,
    ) -> Result<Self, FullShardError> {
        if !profile.is_jorts()
            || !slots.is_power_of_two()
            || slots < 2
            || slots > crate::max_shard_signers(profile)
        {
            return Err(FullShardError::InvalidParameters);
        }
        let circuit = ShardCircuit::new(profile, slots);
        let whir = FixedPathWhirParams::new(regime, LOG_TRACE_COLS + circuit.log_rows())
            .map_err(|_| FullShardError::InvalidParameters)?;
        let tape = AirTape::record(&circuit);
        Ok(Self {
            whir,
            profile,
            slots,
            log_slots: slots.trailing_zeros() as usize,
            circuit,
            tape,
        })
    }

    pub fn profile(&self) -> AggSigProfile {
        self.profile
    }
    pub fn slots(&self) -> usize {
        self.slots
    }
    pub fn regime(&self) -> WhirSecurityRegime {
        self.whir.schedule.regime
    }
    /// Variables of a shard's witness polynomial.
    pub fn num_vars(&self) -> usize {
        LOG_TRACE_COLS + self.circuit.log_rows()
    }
}

fn key_limbs(key: &ValidatorPublicKey) -> [F; 8] {
    core::array::from_fn(|i| {
        if i < 4 {
            key.pk_seed[i]
        } else {
            key.pk_root[i - 4]
        }
    })
}

/// Digest naming an ordered committee of at most `params.slots()` distinct keys matching
/// `params.profile()`. The relation counts committee slots, so a verifier that accepts a digest
/// from elsewhere must know it names distinct keys.
pub fn committee_digest(params: &FullShardParams, keys: &[ValidatorPublicKey]) -> Option<Digest> {
    let mut identities = alloc::collections::BTreeSet::new();
    if keys.is_empty()
        || keys.len() > params.slots
        || keys
            .iter()
            .any(|k| k.profile != params.profile || !identities.insert((k.pk_seed, k.pk_root)))
    {
        return None;
    }
    let mut padded: Vec<[F; 8]> = keys.iter().map(key_limbs).collect();
    padded.resize(params.slots, [F::ZERO; 8]);
    Some(committee_gadget(
        &mut Native::default(),
        &f(keys.len() as u64),
        &padded,
    ))
}

/// What a parent proof states about one shard.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardPublic {
    /// [`committee_digest`] of the shard's committee.
    pub committee: Digest,
    /// The message every counted signer signed.
    pub message: [u8; SHARD_MESSAGE_BYTES],
    /// Number of distinct committee members that signed.
    pub signers: u32,
}
impl ShardPublic {
    fn words(&self) -> Vec<F> {
        let mut out = self.committee.to_vec();
        out.extend(self.message.iter().map(|&x| f(u64::from(x))));
        out.push(f(u64::from(self.signers)));
        out
    }
}

/// A shard's committee, signer set and message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveShardStatement {
    pub keys: Vec<ValidatorPublicKey>,
    pub bitmap: SignerBitmap,
    pub message: [u8; SHARD_MESSAGE_BYTES],
}
impl RecursiveShardStatement {
    /// The statement's public form, or `None` if it does not fit `params`.
    pub fn public(&self, params: &FullShardParams) -> Option<ShardPublic> {
        if self.bitmap.num_validators() as usize != self.keys.len() || self.bitmap.count_ones() == 0
        {
            return None;
        }
        Some(ShardPublic {
            committee: committee_digest(params, &self.keys)?,
            message: self.message,
            signers: self.bitmap.count_ones() as u32,
        })
    }
    pub(crate) fn witness<'a>(
        &self,
        params: &FullShardParams,
        proof: &'a RecursiveShardProof,
    ) -> ShardWitness<'a> {
        let mut keys: Vec<[F; 8]> = self.keys.iter().map(key_limbs).collect();
        keys.resize(params.slots, [F::ZERO; 8]);
        ShardWitness {
            keys,
            size: self.keys.len(),
            active: (0..params.slots)
                .map(|i| self.bitmap.contains(i))
                .collect(),
            proof,
        }
    }
}

/// Proof that every signer of a [`RecursiveShardStatement`] signed its message, in the
/// format the parent relation verifies. Not hiding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveShardProof {
    pub commitment: Digest,
    pub row_sumcheck_polys: Vec<[E; ROW_SUMCHECK_WIRE_COEFFS]>,
    pub col_evals: Vec<E>,
    pub opening: FixedPathWhirProof,
}

/// Canonical 8-byte wire header for [`RecursiveShardProof`].
pub const RECURSIVE_SHARD_WIRE_MAGIC: &[u8; 8] = b"QSAGRSP1";

impl RecursiveShardProof {
    pub(crate) fn placeholder(params: &FullShardParams) -> Self {
        Self {
            commitment: [F::ZERO; 4],
            row_sumcheck_polys: vec![[E::ZERO; ROW_SUMCHECK_WIRE_COEFFS]; params.circuit.log_rows()],
            col_evals: vec![E::ZERO; NUM_TRACE_COLS],
            opening: params.whir.placeholder(),
        }
    }
    pub(crate) fn well_formed(&self, params: &FullShardParams) -> bool {
        self.row_sumcheck_polys.len() == params.circuit.log_rows()
            && self.col_evals.len() == NUM_TRACE_COLS
            && params.whir.well_formed(
                &ChildWhirStatement {
                    shard_header: OPENING_HEADER,
                    commitment: self.commitment,
                    point: vec![E::ZERO; params.num_vars()],
                    value: E::ZERO,
                },
                &self.opening,
            )
    }
    /// Canonical wire serialization (`QSAGRSP1` header).
    pub fn to_bytes(&self) -> Vec<u8> {
        let opening_bytes = self.opening.to_bytes();
        let mut out = Vec::with_capacity(
            8 + 32
                + 32 * ROW_SUMCHECK_WIRE_COEFFS * self.row_sumcheck_polys.len()
                + 32 * self.col_evals.len()
                + opening_bytes.len(),
        );
        out.extend_from_slice(RECURSIVE_SHARD_WIRE_MAGIC);
        for &limb in &self.commitment {
            out.extend_from_slice(&limb.to_le_bytes());
        }
        for poly in &self.row_sumcheck_polys {
            for &c in poly {
                out.extend_from_slice(&c.to_le_bytes());
            }
        }
        for &col in &self.col_evals {
            out.extend_from_slice(&col.to_le_bytes());
        }
        out.extend_from_slice(&opening_bytes);
        out
    }

    /// Canonical wire decoding for `params`, rejecting non-canonical limbs and trailing bytes.
    pub fn from_bytes(params: &FullShardParams, bytes: &[u8]) -> Option<Self> {
        if bytes.get(..8)? != RECURSIVE_SHARD_WIRE_MAGIC {
            return None;
        }
        let mut pos = 8usize;
        fn take_f(bytes: &[u8], pos: &mut usize) -> Option<F> {
            let chunk: [u8; 8] = bytes.get(*pos..*pos + 8)?.try_into().ok()?;
            *pos += 8;
            F::from_le_bytes_canonical(chunk).ok()
        }
        fn take_e(bytes: &[u8], pos: &mut usize) -> Option<E> {
            let chunk: [u8; 32] = bytes.get(*pos..*pos + 32)?.try_into().ok()?;
            *pos += 32;
            E::from_le_bytes_canonical(chunk)
        }
        let commitment = [
            take_f(bytes, &mut pos)?,
            take_f(bytes, &mut pos)?,
            take_f(bytes, &mut pos)?,
            take_f(bytes, &mut pos)?,
        ];
        let mut row_sumcheck_polys = Vec::with_capacity(params.circuit.log_rows());
        for _ in 0..params.circuit.log_rows() {
            let mut poly = [E::ZERO; ROW_SUMCHECK_WIRE_COEFFS];
            for slot in &mut poly {
                *slot = take_e(bytes, &mut pos)?;
            }
            row_sumcheck_polys.push(poly);
        }
        let mut col_evals = Vec::with_capacity(NUM_TRACE_COLS);
        for _ in 0..NUM_TRACE_COLS {
            col_evals.push(take_e(bytes, &mut pos)?);
        }
        let opening = FixedPathWhirProof::from_bytes(bytes.get(pos..)?, &params.whir)?;
        let out = Self {
            commitment,
            row_sumcheck_polys,
            col_evals,
            opening,
        };
        out.well_formed(params).then_some(out)
    }

    /// Canonical byte length of this proof.
    pub fn encoded_len(&self) -> usize {
        self.to_bytes().len()
    }
}

/// The native prover's view of the transcript.
struct NativeRows {
    b: Native,
    tr: Transcript<F>,
}
impl RowTranscript for NativeRows {
    fn row_tau(&mut self, count: usize) -> Vec<E> {
        (0..count)
            .map(|_| self.tr.ext(&mut self.b, T_TAU).value(&self.b))
            .collect()
    }
    fn row_gamma(&mut self) -> E {
        self.tr.ext(&mut self.b, T_GAMMA).value(&self.b)
    }
    fn row_round(&mut self, wire: &[E; ROW_SUMCHECK_WIRE_COEFFS]) -> E {
        let wire: Vec<_> = wire.iter().copied().map(Ext::constant).collect();
        self.tr.absorb_exts(&mut self.b, T_ROUND, &wire);
        self.tr
            .ext(&mut self.b, T_ROUND_CHALLENGE)
            .value(&self.b)
    }
    fn row_col_evals(&mut self, col_evals: &[E]) {
        let cols: Vec<_> = col_evals.iter().copied().map(Ext::constant).collect();
        self.tr.absorb_exts(&mut self.b, T_COLUMNS, &cols);
    }
    fn row_rz(&mut self) -> E {
        self.tr.ext(&mut self.b, T_COLUMN_POINT).value(&self.b)
    }
}

/// Prove a recursive shard. `signatures` are those of the signers of `statement.bitmap`,
/// in ascending index order, over `statement.message`. `blinding_seed` randomizes the idle
/// trace rows.
pub fn prove_recursive_shard(
    params: &FullShardParams,
    statement: &RecursiveShardStatement,
    signatures: &[ValidatorSignature],
    blinding_seed: &[u8; 32],
) -> Result<RecursiveShardProof, FullShardError> {
    let public = statement
        .public(params)
        .ok_or(FullShardError::InvalidStatement)?;
    let indices = statement.bitmap.active_indices();
    if signatures.len() != indices.len()
        || !crate::sig::validate_unique_active_committee(
            &statement.keys,
            &statement.bitmap,
            params.profile,
        )
    {
        return Err(FullShardError::InvalidStatement);
    }
    let phase = crate::profile::span("recursive_shard_signatures");
    let signers: Vec<ShardSigner> = indices
        .iter()
        .map(|&i| {
            let pk = statement.keys[i];
            let (_, mu) = compute_message_mu(&pk, &statement.message);
            ShardSigner { pk, mu }
        })
        .collect();
    if !signers
        .iter()
        .zip(signatures)
        .all(|(signer, sig)| verify_individual_signature_with_mu(&signer.pk, signer.mu, sig))
    {
        return Err(FullShardError::InvalidSignature);
    }
    drop(phase);
    let witness = build_shard_witness(&params.circuit, &signers, signatures, blinding_seed);
    let committed = commit_for_recursion(&params.whir, &witness).map_err(FullShardError::Whir)?;
    let commitment = committed.root();

    let mut b = Native::default();
    let signer_bits: Vec<F> = (0..params.slots)
        .map(|i| f(u64::from(statement.bitmap.contains(i))))
        .collect();
    let tr = bind_statement(&mut b, params, &public.words(), &signer_bits, &commitment);
    let mut rows = NativeRows { b, tr };
    let (row_proof, point, value) = prove_shard_rows(&mut rows, &params.circuit, &signers, &witness);
    drop(witness);
    let (opened, opening) = open_for_recursion(&params.whir, OPENING_HEADER, committed, &point)
        .map_err(FullShardError::Whir)?;
    if opened.value != value {
        return Err(FullShardError::InvalidChild);
    }
    Ok(RecursiveShardProof {
        commitment,
        row_sumcheck_polys: row_proof.row_sumcheck_polys,
        col_evals: row_proof.col_evals,
        opening,
    })
}

/// Verify one recursive shard proof on its own, by the same gadget the parent relation
/// records.
pub fn verify_recursive_shard(
    params: &FullShardParams,
    statement: &RecursiveShardStatement,
    proof: &RecursiveShardProof,
) -> bool {
    let Some(public) = statement.public(params) else {
        return false;
    };
    if !proof.well_formed(params) {
        return false;
    }
    let mut b = Native::default();
    shard_gadget(
        &mut b,
        params,
        &public.words(),
        &statement.witness(params, proof),
    );
    !b.failed
}

// ============================================================================
// The parent relation
// ============================================================================

/// Counts exclude padding and the masking rows of the outer protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FullShardRelationStats {
    pub sbox_rows: usize,
    pub multiplication_rows: usize,
    pub padded_rows: usize,
    pub variables: usize,
}

/// The relation "each of `children` recursive shard proofs verifies", precompiled with a
/// deterministic Spark [`ShapeHologram`] for `< 15 ms` sublinear verification.
#[derive(Clone)]
pub struct FullShardMergeRelation {
    params: FullShardParams,
    children: usize,
    shape: Shape,
    hologram: ShapeHologram,
    stats: FullShardRelationStats,
}

/// Largest fan-in of one relation.
pub const MAX_FULL_SHARD_CHILDREN: usize = 16;

impl FullShardMergeRelation {
    pub fn new(params: FullShardParams, children: usize) -> Result<Self, FullShardError> {
        if !(1..=MAX_FULL_SHARD_CHILDREN).contains(&children) {
            return Err(FullShardError::InvalidParameters);
        }
        let placeholder = RecursiveShardProof::placeholder(&params);
        let witness = ShardWitness {
            keys: vec![[F::ZERO; 8]; params.slots],
            size: 0,
            active: vec![false; params.slots],
            proof: &placeholder,
        };
        let publics = vec![vec![F::ZERO; PUBLIC_WORDS]; children];
        let witnesses: Vec<&ShardWitness<'_>> = (0..children).map(|_| &witness).collect();
        let mut cs = ConstraintSystem::new_hologram_aligned();
        populate(&mut cs, &params, &publics, &witnesses);
        let used = cs.num_rows();
        let (shape, mut z) = cs.finish();
        qsag_asm::volatile_fill(&mut z, F::ZERO);
        let hologram = ShapeHologram::compile_native(&shape, params.regime())
            .map_err(|_| FullShardError::InvalidParameters)?;
        let stats = FullShardRelationStats {
            sbox_rows: shape.num_sbox,
            multiplication_rows: used - shape.num_sbox,
            padded_rows: shape.num_rows(),
            variables: shape.num_vars,
        };
        Ok(Self {
            params,
            children,
            shape,
            hologram,
            stats,
        })
    }
    pub fn params(&self) -> &FullShardParams {
        &self.params
    }
    pub fn num_children(&self) -> usize {
        self.children
    }
    pub fn shape(&self) -> &Shape {
        &self.shape
    }
    pub fn hologram(&self) -> &ShapeHologram {
        &self.hologram
    }
    pub fn verifier_key(&self) -> &ShapeVerifierKey {
        self.hologram.verifier_key()
    }
    pub fn stats(&self) -> FullShardRelationStats {
        self.stats
    }

    /// The relation's assignment for these children. It satisfies the relation exactly when
    /// every child verifies.
    fn assignment(
        &self,
        statements: &[RecursiveShardStatement],
        proofs: &[RecursiveShardProof],
    ) -> Result<Vec<F>, FullShardError> {
        let publics: Vec<Vec<F>> = statements
            .iter()
            .map(|s| s.public(&self.params).map(|p| p.words()))
            .collect::<Option<_>>()
            .ok_or(FullShardError::InvalidStatement)?;
        let inputs: Vec<(&Vec<F>, &RecursiveShardStatement, &RecursiveShardProof)> = publics
            .iter()
            .zip(statements)
            .zip(proofs)
            .map(|((public, statement), proof)| (public, statement, proof))
            .collect();
        let build = |chunk: &[(&Vec<F>, &RecursiveShardStatement, &RecursiveShardProof)]| {
            chunk
                .iter()
                .map(|(public, statement, proof)| {
                    let mut assignment = Assignment::hologram_aligned();
                    shard_gadget(
                        &mut assignment,
                        &self.params,
                        public,
                        &statement.witness(&self.params, proof),
                    );
                    (assignment.p2_values, assignment.values)
                })
                .collect::<Vec<_>>()
        };
        #[cfg(feature = "std")]
        let assignments = crate::map_chunks_bounded_with_limit(&inputs, self.children, build)
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        #[cfg(not(feature = "std"))]
        let assignments = build(&inputs);
        let p2_var_base = 128 * self.shape.hologram_meta().pub_var_blocks;
        let mut z = Vec::with_capacity(self.shape.num_vars);
        z.push(F::ONE);
        z.extend(publics.iter().flatten());
        z.resize(p2_var_base, F::ZERO);
        for (p2_vals, _) in &assignments {
            z.extend_from_slice(p2_vals);
        }
        for (_, misc_vals) in assignments {
            z.extend(misc_vals);
        }
        if z.len() != self.shape.mask_var_base {
            return Err(FullShardError::InvalidParameters);
        }
        z.resize(self.shape.num_vars, F::ZERO);
        Ok(z)
    }
}

fn populate(
    cs: &mut ConstraintSystem,
    params: &FullShardParams,
    publics: &[Vec<F>],
    witnesses: &[&ShardWitness<'_>],
) {
    let public: Vec<Vec<Lc>> = publics
        .iter()
        .map(|words| words.iter().map(|&x| cs.public_input(x).into()).collect())
        .collect();
    let inputs: Vec<(&Vec<Lc>, &ShardWitness<'_>)> =
        public.iter().zip(witnesses.iter().copied()).collect();
    let build = |chunk: &[(&Vec<Lc>, &ShardWitness<'_>)]| {
        chunk
            .iter()
            .map(|(words, witness)| {
                let mut child = cs.fork_public_inputs();
                shard_gadget(&mut child, params, words, witness);
                child
            })
            .collect::<Vec<_>>()
    };
    #[cfg(feature = "std")]
    let circuits = crate::map_chunks_bounded_with_limit(&inputs, inputs.len(), build)
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    #[cfg(not(feature = "std"))]
    let circuits = build(&inputs);
    for circuit in circuits {
        cs.append(circuit);
    }
}

/// One parent proof for the shards named by its statement, verified in `< 15 ms` via Spark
/// [`ShapeHologram`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FullShardMergeProof {
    pub proof: HologramPublicProof,
}
impl FullShardMergeProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = b"QSAGFSM1".to_vec();
        out.extend(self.proof.to_bytes());
        out
    }
    pub fn from_bytes(
        bytes: &[u8],
        relation: &FullShardMergeRelation,
        regime: WhirSecurityRegime,
    ) -> Option<Self> {
        if bytes.get(..8)? != b"QSAGFSM1" || !regime.meets_qrom_128_floor() {
            return None;
        }
        if regime == relation.verifier_key().regime {
            let proof =
                HologramPublicProof::from_bytes(bytes.get(8..)?, relation.verifier_key())?;
            Some(Self { proof })
        } else {
            let alt = ShapeHologram::compile(&relation.shape, regime).ok()?;
            let proof = HologramPublicProof::from_bytes(bytes.get(8..)?, alt.verifier_key())?;
            Some(Self { proof })
        }
    }
}

/// Prove that every child verifies. The children are witnesses: the result carries none of
/// them. `regime` is the parent proof's own regime.
pub fn prove_full_shard_merge(
    relation: &FullShardMergeRelation,
    statements: &[RecursiveShardStatement],
    proofs: &[RecursiveShardProof],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
) -> Result<FullShardMergeProof, FullShardError> {
    if !regime.meets_qrom_128_floor()
        || statements.len() != relation.children
        || proofs.len() != relation.children
    {
        return Err(FullShardError::InvalidParameters);
    }
    if !proofs.iter().all(|p| p.well_formed(&relation.params)) {
        return Err(FullShardError::InvalidChild);
    }
    let z = relation.assignment(statements, proofs)?;
    let map_err = |e: protocol::ZkHemError| match e {
        protocol::ZkHemError::Unsatisfied => FullShardError::InvalidChild,
        _ => FullShardError::InvalidParameters,
    };
    let proof = if regime == relation.verifier_key().regime {
        protocol::prove_public_hologram(&relation.shape, &relation.hologram, z, PROOF_LABEL, seed)
            .map_err(map_err)?
    } else {
        let alt = ShapeHologram::compile(&relation.shape, regime).map_err(map_err)?;
        protocol::prove_public_hologram(&relation.shape, &alt, z, PROOF_LABEL, seed)
            .map_err(map_err)?
    };
    Ok(FullShardMergeProof { proof })
}

/// Verify a parent proof against the shards' public statements alone (`< 15 ms` sublinear!).
pub fn verify_full_shard_merge(
    relation: &FullShardMergeRelation,
    shards: &[ShardPublic],
    regime: WhirSecurityRegime,
    proof: &FullShardMergeProof,
) -> bool {
    if !regime.meets_qrom_128_floor() || shards.len() != relation.children {
        return false;
    }
    let public: Vec<F> = shards.iter().flat_map(ShardPublic::words).collect();
    if regime == relation.verifier_key().regime {
        protocol::verify_public_hologram(relation.verifier_key(), &public, PROOF_LABEL, &proof.proof)
    } else {
        let Ok(alt) = ShapeHologram::compile(&relation.shape, regime) else {
            return false;
        };
        protocol::verify_public_hologram(alt.verifier_key(), &public, PROOF_LABEL, &proof.proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sig::ValidatorKeypair;
    use crate::trace::{RowPublicEvalExt4, eval_batched_row_constraints_ext4};
    use std::time::Instant;

    const REGIME: WhirSecurityRegime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;

    fn sample(i: usize) -> E {
        E::from_limbs(core::array::from_fn(|j| {
            f((0x9E37_79B9_7F4A_7C15u64)
                .wrapping_mul(1 + i as u64)
                .wrapping_add(0x1234_5678 * (j as u64 + 1)))
        }))
    }
    fn keypairs(count: usize, tag: u8) -> Vec<ValidatorKeypair> {
        (0..count)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(
                    AggSigProfile::JortsPoseidon2,
                    &[tag; 32],
                    i as u32,
                )
            })
            .collect()
    }
    /// A shard over a fresh committee of `size` keys in which `signing` sign `message`.
    fn shard(
        size: usize,
        signing: &[usize],
        message: [u8; 32],
        tag: u8,
    ) -> (RecursiveShardStatement, Vec<ValidatorSignature>) {
        let mut keys = keypairs(size, tag);
        let signatures = signing
            .iter()
            .map(|&i| {
                keys[i]
                    .sign_stateful_for_unit_test(&message, (i % 64) as u32)
                    .unwrap()
            })
            .collect();
        let statement = RecursiveShardStatement {
            keys: keys.iter().map(|k| k.pk).collect(),
            bitmap: SignerBitmap::from_active_indices(size as u32, signing).unwrap(),
            message,
        };
        (statement, signatures)
    }

    #[test]
    fn message_representative_gadget_matches_the_signature_scheme() {
        for profile in [
            AggSigProfile::JortsPoseidon2,
            AggSigProfile::jorts_with_height(10).unwrap(),
            AggSigProfile::jorts_with_height(20).unwrap(),
        ] {
            for (tag, message) in [(3u8, [0u8; 32]), (9, [0xFF; 32]), (200, [0x5A; 32])] {
                let mut message = message;
                message[7] ^= tag;
                for i in 0..3 {
                    let key = ValidatorKeypair::keygen_deterministic(profile, &[tag; 32], i);
                    let mut b = Native::default();
                    let words: Vec<F> = message.iter().map(|&x| f(u64::from(x))).collect();
                    let mu = message_mu(&mut b, key.pk.profile, &key_limbs(&key.pk), &words);
                    assert!(!b.failed);
                    assert_eq!(mu, compute_message_mu(&key.pk, &message).1);
                }
            }
        }
    }

    #[test]
    fn recorded_row_constraints_equal_the_native_evaluator() {
        let circuit = ShardCircuit::new(AggSigProfile::JortsPoseidon2, 2);
        let tape = AirTape::record(&circuit);
        let ops = circuit.unique_ops.len();
        for round in 0..3 {
            let mut next = 1000 * round;
            let mut draw = || {
                next += 1;
                sample(next)
            };
            let cols: [E; NUM_TRACE_COLS] = core::array::from_fn(|_| draw());
            let sels: Vec<E> = (0..ops).map(|_| draw()).collect();
            let public = RowPublicEvalExt4 {
                active_signer: draw(),
                pk_seed: core::array::from_fn(|_| draw()),
                pk_root: core::array::from_fn(|_| draw()),
                mu: core::array::from_fn(|_| draw()),
                gated_op_sels: &sels,
                step_c0: draw(),
                is_row_first: draw(),
                is_row_last: draw(),
                eq_tau: draw(),
                eq_not_last: draw(),
                shift_tau: draw(),
            };
            let gamma = draw();
            let expected = eval_batched_row_constraints_ext4(&circuit.unique_ops, &cols, &public, gamma);
            let lift = |v: E| Ext::<F>::constant(v);
            let inputs = tape.inputs(
                &cols.map(lift),
                lift(public.active_signer),
                public.pk_seed.map(lift),
                public.pk_root.map(lift),
                public.mu.map(lift),
                lift(public.step_c0),
                lift(public.is_row_first),
                lift(public.is_row_last),
                [
                    lift(public.eq_tau),
                    lift(public.eq_not_last),
                    lift(public.shift_tau),
                ],
                lift(gamma),
                sels.iter().copied().map(lift).collect(),
            );
            let mut b = Native::default();
            assert_eq!(tape.run(&mut b, &inputs).value(&b), expected);
            // The recorded code and the relation agree on the number of wires.
            let mut assignment = Assignment::default();
            let mut cs = ConstraintSystem::new();
            let wires: Vec<Ext<Lc>> = inputs
                .iter()
                .map(|v| Ext::alloc(&mut cs, v.value(&b)))
                .collect();
            let recorded = tape.run(&mut cs, &wires);
            assert_eq!(recorded.value(&cs), expected);
            tape.run(&mut assignment, &inputs);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            assert_eq!(
                assignment.values.len() + 4 * inputs.len() + 1,
                shape.mask_var_base
            );
        }
    }

    #[test]
    fn committee_digest_binds_order_size_and_padding() {
        let params = FullShardParams::new(REGIME, 4).unwrap();
        let keys: Vec<_> = keypairs(4, 1).iter().map(|k| k.pk).collect();
        let base = committee_digest(&params, &keys[..3]).unwrap();
        assert_ne!(base, committee_digest(&params, &keys).unwrap());
        assert_ne!(base, committee_digest(&params, &keys[..2]).unwrap());
        let mut swapped = keys[..3].to_vec();
        swapped.swap(0, 1);
        assert_ne!(base, committee_digest(&params, &swapped).unwrap());
        assert!(committee_digest(&params, &[]).is_none());
        let mut five = keys.clone();
        five.push(keys[0]);
        assert!(committee_digest(&params, &five).is_none());
        let mut repeated = keys[..3].to_vec();
        repeated[2] = repeated[0];
        assert!(committee_digest(&params, &repeated).is_none());
        let mut other_profile = keys[..3].to_vec();
        other_profile[1].profile = AggSigProfile::CorduroyPoseidon2;
        assert!(committee_digest(&params, &other_profile).is_none());
    }

    /// Two real shards under one parent: the parent verifies from the public statements
    /// alone, and every altered child, witness or statement is refused.
    #[test]
    fn full_shard_merge_end_to_end_and_tamper_rejection() {
        let params = FullShardParams::new(REGIME, 2).unwrap();
        let (first, first_sigs) = shard(2, &[0, 1], [0x11; 32], 21);
        let (second, second_sigs) = shard(2, &[1], [0x22; 32], 22);
        let proofs = vec![
            prove_recursive_shard(&params, &first, &first_sigs, &[1; 32]).unwrap(),
            prove_recursive_shard(&params, &second, &second_sigs, &[2; 32]).unwrap(),
        ];
        let statements = vec![first.clone(), second.clone()];
        for (statement, proof) in statements.iter().zip(&proofs) {
            assert!(verify_recursive_shard(&params, statement, proof));
        }
        // A signature over another message, or by another key, is refused by the prover.
        let (_, wrong_sigs) = shard(2, &[0, 1], [0x12; 32], 21);
        assert_eq!(
            prove_recursive_shard(&params, &first, &wrong_sigs, &[1; 32]),
            Err(FullShardError::InvalidSignature)
        );
        assert_eq!(
            prove_recursive_shard(&params, &first, &first_sigs[..1], &[1; 32]),
            Err(FullShardError::InvalidStatement)
        );

        let relation = FullShardMergeRelation::new(params.clone(), 2).unwrap();
        let honest = relation.assignment(&statements, &proofs).unwrap();
        assert!(relation.shape().is_satisfied(&honest));

        // Child proofs: each altered field fails native verification and leaves the
        // relation unsatisfied.
        let mut tampered: Vec<(&str, RecursiveShardProof)> = Vec::new();
        let mut t = proofs[0].clone();
        t.col_evals[0] += E::ONE;
        tampered.push(("column evaluation", t));
        let mut t = proofs[0].clone();
        t.col_evals[NUM_TRACE_COLS - 1] += E::ONE;
        tampered.push(("last column evaluation", t));
        let mut t = proofs[0].clone();
        t.row_sumcheck_polys[0][0] += E::ONE;
        tampered.push(("first round polynomial", t));
        let mut t = proofs[0].clone();
        let last = t.row_sumcheck_polys.len() - 1;
        t.row_sumcheck_polys[last][7] += E::ONE;
        tampered.push(("last round polynomial", t));
        let mut t = proofs[0].clone();
        t.commitment[2] += F::ONE;
        tampered.push(("commitment", t));
        let mut t = proofs[0].clone();
        t.opening.final_coeffs[0] += E::ONE;
        tampered.push(("opening", t));
        tampered.push(("another shard's proof", proofs[1].clone()));
        for (what, bad) in &tampered {
            assert!(!verify_recursive_shard(&params, &first, bad), "{what}");
            let z = relation
                .assignment(&statements, &[bad.clone(), proofs[1].clone()])
                .unwrap();
            assert!(!relation.shape().is_satisfied(&z), "{what}");
        }
        assert_eq!(
            prove_full_shard_merge(
                &relation,
                &statements,
                &[tampered[0].1.clone(), proofs[1].clone()],
                REGIME,
                &[5; 32]
            ),
            Err(FullShardError::InvalidChild)
        );

        // Statements: a different message, key, signer set or committee size.
        let mut forged: Vec<(&str, RecursiveShardStatement)> = Vec::new();
        let mut s = second.clone();
        s.message[31] ^= 1;
        forged.push(("message", s));
        let mut s = second.clone();
        s.keys[1].pk_root[0] += F::ONE;
        forged.push(("signer key", s));
        let mut s = second.clone();
        s.keys[0].pk_seed[3] += F::ONE;
        forged.push(("non-signer key", s));
        let mut s = second.clone();
        s.bitmap = SignerBitmap::from_active_indices(2, &[0, 1]).unwrap();
        forged.push(("extra signer", s));
        let mut s = second.clone();
        s.bitmap = SignerBitmap::from_active_indices(2, &[0]).unwrap();
        forged.push(("other signer", s));
        for (what, bad) in &forged {
            assert!(!verify_recursive_shard(&params, bad, &proofs[1]), "{what}");
            let z = relation
                .assignment(&[first.clone(), bad.clone()], &proofs)
                .unwrap();
            assert!(!relation.shape().is_satisfied(&z), "{what}");
        }
        // A wrong public count with the honest witness: the count is a public cell.
        let mut miscounted = honest.clone();
        let count_cell = 2 * PUBLIC_WORDS;
        assert_eq!(miscounted[count_cell], F::ONE);
        miscounted[count_cell] = F::TWO;
        assert!(!relation.shape().is_satisfied(&miscounted));

        // The parent proof.
        let parent = prove_full_shard_merge(&relation, &statements, &proofs, REGIME, &[5; 32]).unwrap();
        let publics: Vec<ShardPublic> = statements
            .iter()
            .map(|s| s.public(&params).unwrap())
            .collect();
        assert_eq!(publics[0].signers, 2);
        assert_eq!(publics[1].signers, 1);
        assert!(verify_full_shard_merge(&relation, &publics, REGIME, &parent));
        let bytes = parent.to_bytes();
        assert_eq!(
            FullShardMergeProof::from_bytes(&bytes, &relation, REGIME).unwrap(),
            parent
        );
        let alter = |edit: &dyn Fn(&mut Vec<ShardPublic>)| {
            let mut bad = publics.clone();
            edit(&mut bad);
            assert!(!verify_full_shard_merge(&relation, &bad, REGIME, &parent));
        };
        alter(&|p| p[0].message[0] ^= 1);
        alter(&|p| p[1].message[31] ^= 0x80);
        alter(&|p| p[0].committee[0] += F::ONE);
        alter(&|p| p[1].committee[3] += F::ONE);
        alter(&|p| p[0].signers = 1);
        alter(&|p| p[1].signers = 2);
        alter(&|p| p.swap(0, 1));
        alter(&|p| {
            p.pop();
        });
        assert!(!verify_full_shard_merge(
            &relation,
            &publics,
            WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
            &parent
        ));
        let mut bad = parent.clone();
        bad.proof.row_rounds[0][0] += E::ONE;
        assert!(!verify_full_shard_merge(&relation, &publics, REGIME, &bad));
    }

    #[test]
    fn variable_height_jorts_recursive_shard_and_sublinear_hologram_merge() {
        let profile = AggSigProfile::jorts_with_height(10).unwrap();
        let params = FullShardParams::with_profile(REGIME, profile, 2).unwrap();
        assert_eq!(params.profile(), profile);
        let mut keys: Vec<ValidatorKeypair> = (0..2)
            .map(|i| ValidatorKeypair::keygen_deterministic(profile, &[0x7A; 32], i))
            .collect();
        let msg = [0x3C; 32];
        // Sign at epoch 777 > 64 to exercise `StatefulHmsgBlock0Var { height: 10 }` inside `AirTape`!
        let sig0 = keys[0].sign_stateful_for_unit_test(&msg, 777).unwrap();
        let sig1 = keys[1].sign_stateful_for_unit_test(&msg, 999).unwrap();
        let stmt = RecursiveShardStatement {
            keys: keys.iter().map(|k| k.pk).collect(),
            bitmap: SignerBitmap::from_active_indices(2, &[0, 1]).unwrap(),
            message: msg,
        };
        let child_proof = prove_recursive_shard(&params, &stmt, &[sig0, sig1], &[0x55; 32]).unwrap();
        assert!(verify_recursive_shard(&params, &stmt, &child_proof));
        let wire = child_proof.to_bytes();
        assert_eq!(
            RecursiveShardProof::from_bytes(&params, &wire).as_ref(),
            Some(&child_proof)
        );

        let relation = FullShardMergeRelation::new(params.clone(), 1).unwrap();
        let parent = prove_full_shard_merge(
            &relation,
            core::slice::from_ref(&stmt),
            core::slice::from_ref(&child_proof),
            REGIME,
            &[0x66; 32],
        )
        .unwrap();
        let pub_shard = stmt.public(&params).unwrap();
        let t0 = Instant::now();
        assert!(verify_full_shard_merge(
            &relation,
            core::slice::from_ref(&pub_shard),
            REGIME,
            &parent
        ));
        let ver_ms = t0.elapsed().as_secs_f64() * 1000.0;
        assert!(ver_ms < 25.0, "verify_ms={ver_ms}");
    }

    /// `QSAG_FULL_SHARD_SLOTS` signer slots per shard (all signing), `QSAG_FULL_SHARD_CHILDREN`
    /// shards under one parent.
    #[test]
    #[ignore = "measurement: QSAG_FULL_SHARD_SLOTS, QSAG_FULL_SHARD_CHILDREN"]
    fn bench_full_shard_merge() {
        let env = |name: &str, default: usize| {
            std::env::var(name)
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(default)
        };
        let slots = env("QSAG_FULL_SHARD_SLOTS", 128);
        let children = env("QSAG_FULL_SHARD_CHILDREN", 2);
        let start = Instant::now();
        let params = FullShardParams::new(REGIME, slots).unwrap();
        let relation = FullShardMergeRelation::new(params.clone(), children).unwrap();
        let setup_ms = start.elapsed().as_secs_f64() * 1000.;
        let stats = relation.stats();
        std::println!(
            "FULL_SHARD_RELATION slots={slots} children={children} child_nv={} sbox_rows={} multiplication_rows={} padded_rows={} variables={} setup_ms={setup_ms:.0}",
            params.num_vars(),
            stats.sbox_rows,
            stats.multiplication_rows,
            stats.padded_rows,
            stats.variables
        );
        let signing: Vec<usize> = (0..slots).collect();
        let mut statements = Vec::new();
        let mut proofs = Vec::new();
        for c in 0..children {
            let (statement, signatures) = shard(slots, &signing, [c as u8 + 1; 32], c as u8 + 50);
            let start = Instant::now();
            let proof = prove_recursive_shard(&params, &statement, &signatures, &[7; 32]).unwrap();
            let prove_ms = start.elapsed().as_secs_f64() * 1000.;
            let start = Instant::now();
            assert!(verify_recursive_shard(&params, &statement, &proof));
            std::println!(
                "FULL_SHARD_CHILD slots={slots} index={c} prove_ms={prove_ms:.0} verify_ms={:.1} bytes={}",
                start.elapsed().as_secs_f64() * 1000.,
                proof.encoded_len()
            );
            statements.push(statement);
            proofs.push(proof);
        }
        let start = Instant::now();
        let parent = prove_full_shard_merge(&relation, &statements, &proofs, REGIME, &[9; 32]).unwrap();
        let prove_ms = start.elapsed().as_secs_f64() * 1000.;
        let publics: Vec<ShardPublic> = statements
            .iter()
            .map(|s| s.public(&params).unwrap())
            .collect();
        let start = Instant::now();
        assert!(verify_full_shard_merge(&relation, &publics, REGIME, &parent));
        let verify_ms = start.elapsed().as_secs_f64() * 1000.;
        std::println!(
            "FULL_SHARD_MERGE slots={slots} children={children} signers={} parent_bytes={} prove_ms={prove_ms:.0} verify_ms={verify_ms:.1}",
            slots * children,
            parent.to_bytes().len()
        );
    }
}
