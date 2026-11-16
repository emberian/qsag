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

use super::protocol::{self, PublicHemProof};
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
const PUBLIC_WORDS: usize = 4 + SHARD_MESSAGE_BYTES + 1;
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

/// A value of the row-constraint evaluator while it is being recorded.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Sym(u32);

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

std::thread_local! {
    static TAPE: RefCell<Vec<Node>> = const { RefCell::new(Vec::new()) };
}

fn push(node: Node) -> Sym {
    TAPE.with(|t| {
        let mut t = t.borrow_mut();
        t.push(node);
        Sym(u32::try_from(t.len() - 1).expect("row-constraint tape length"))
    })
}
fn constant_of(s: Sym) -> Option<F> {
    TAPE.with(|t| match t.borrow()[s.0 as usize] {
        Node::Const(c) => Some(c),
        _ => None,
    })
}
fn constant(c: F) -> Sym {
    if c == F::ZERO {
        Sym(0)
    } else if c == F::ONE {
        Sym(1)
    } else {
        push(Node::Const(c))
    }
}
fn scaled(s: Sym, k: F) -> Sym {
    match constant_of(s) {
        Some(c) => constant(c * k),
        None if k == F::ONE => s,
        None if k == F::ZERO => Sym(0),
        None => push(Node::Scale(s.0, k)),
    }
}
fn linear_layer(st: &mut [Sym; 12], layer: fn(&mut [F; 12])) {
    // Column `j` of the layer's matrix is its image of the `j`-th unit vector.
    let columns: [[F; 12]; 12] = core::array::from_fn(|j| {
        let mut unit = [F::ZERO; 12];
        unit[j] = F::ONE;
        layer(&mut unit);
        unit
    });
    let input = *st;
    for (i, out) in st.iter_mut().enumerate() {
        *out = push(Node::Lin(
            (0..12).map(|j| (columns[j][i], input[j].0)).collect(),
        ));
    }
}

impl core::ops::Add for Sym {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        match (constant_of(self), constant_of(rhs)) {
            (Some(a), Some(b)) => constant(a + b),
            (Some(a), None) if a == F::ZERO => rhs,
            (None, Some(b)) if b == F::ZERO => self,
            _ => push(Node::Add(self.0, rhs.0)),
        }
    }
}
impl core::ops::AddAssign for Sym {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl core::ops::Sub for Sym {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        match (constant_of(self), constant_of(rhs)) {
            (Some(a), Some(b)) => constant(a - b),
            (None, Some(b)) if b == F::ZERO => self,
            _ => push(Node::Sub(self.0, rhs.0)),
        }
    }
}
impl core::ops::Mul for Sym {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        match (constant_of(self), constant_of(rhs)) {
            (Some(a), _) => scaled(rhs, a),
            (_, Some(b)) => scaled(self, b),
            _ => push(Node::Mul(self.0, rhs.0)),
        }
    }
}
impl TraceField for Sym {
    const ZERO: Self = Sym(0);
    const ONE: Self = Sym(1);
    fn from_base(b: F) -> Self {
        constant(b)
    }
    fn from_u64(v: u64) -> Self {
        constant(f(v))
    }
    fn mul_base_f(self, s: F) -> Self {
        scaled(self, s)
    }
    fn sbox7(self) -> Self {
        match constant_of(self) {
            Some(c) => constant(poseidon2_sbox7(c)),
            None => push(Node::Sbox(self.0)),
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
        TAPE.with(|t| {
            let mut t = t.borrow_mut();
            t.clear();
            t.extend([Node::Const(F::ZERO), Node::Const(F::ONE)]);
        });
        let mut next = 0u32;
        let mut input = || {
            next += 1;
            push(Node::Input(next - 1))
        };
        let cols: [Sym; NUM_TRACE_COLS] = core::array::from_fn(|_| input());
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
        let gated_op_sels: Vec<Sym> = (0..unique_ops).map(|_| input()).collect();
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
        let nodes = TAPE.with(|t| core::mem::take(&mut *t.borrow_mut()));
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
            output: out.0,
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
/// [`crate::sig::compute_message_mu`] for a `JortsPoseidon2` key and a 32-byte message.
fn message_mu<B: Backend>(b: &mut B, key: &[B::W; 8], message: &[B::W]) -> [B::W; 5] {
    assert_eq!(message.len(), SHARD_MESSAGE_BYTES);
    let byte = |v: u8| B::W::constant(f(u64::from(v)));
    // `encode_multi_frame(&[b"QSAG.MU/v2", &pk.to_bytes(), message])`.
    let mut frame = vec![byte(3), byte(10)];
    frame.extend(b"QSAG.MU/v2".iter().map(|&c| byte(c)));
    frame.extend([byte(65), byte(AggSigProfile::JortsPoseidon2 as u8)]);
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
        f(AggSigProfile::JortsPoseidon2 as u64),
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
struct ShardWitness<'a> {
    /// `slots` keys as `pk_seed ++ pk_root`; slots past `size` hold zeros.
    keys: Vec<[F; 8]>,
    size: usize,
    /// One flag per slot.
    active: Vec<bool>,
    proof: &'a RecursiveShardProof,
}

/// The whole verifier of one recursive shard proof. `public` is
/// `committee digest ++ message bytes ++ signer count`.
fn shard_gadget<B: Backend>(
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
    let mus: Vec<[B::W; 5]> = keys.iter().map(|key| message_mu(b, key, message)).collect();

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

/// Verifier geometry of recursive `JortsPoseidon2` shards with `slots` signer slots.
#[derive(Clone)]
pub struct FullShardParams {
    whir: FixedPathWhirParams,
    slots: usize,
    log_slots: usize,
    circuit: ShardCircuit,
    tape: AirTape,
}

impl FullShardParams {
    /// `slots` is a power of two in `2..=max_shard_signers(JortsPoseidon2)`; `regime` must be
    /// a Poseidon2 regime.
    pub fn new(regime: WhirSecurityRegime, slots: usize) -> Result<Self, FullShardError> {
        let profile = AggSigProfile::JortsPoseidon2;
        if !slots.is_power_of_two() || slots < 2 || slots > crate::max_shard_signers(profile) {
            return Err(FullShardError::InvalidParameters);
        }
        let circuit = ShardCircuit::new(profile, slots);
        let whir = FixedPathWhirParams::new(regime, LOG_TRACE_COLS + circuit.log_rows())
            .map_err(|_| FullShardError::InvalidParameters)?;
        let tape = AirTape::record(&circuit);
        Ok(Self {
            whir,
            slots,
            log_slots: slots.trailing_zeros() as usize,
            circuit,
            tape,
        })
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

/// Digest naming an ordered committee of at most `params.slots()` distinct `JortsPoseidon2`
/// keys. The relation counts committee slots, so a verifier that accepts a digest from
/// elsewhere must know it names distinct keys.
