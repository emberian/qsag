//! Field-exact parity of the `AirRowGroupA` / `AirRowGroupB` prover kernels with a host
//! evaluation of the same row constraints, on a trace of canonical hardened Poseidon2-12
//! rows and weighted-feed-forward WOTS / FORS hash rows.
//!
//! The host reference evaluates the constraint polynomials of the CPU AIR
//! (`qsag-agg`, `trace.rs`: `eval_group_a_and_boundaries_generic`,
//! `eval_single_op_constraints_generic`) over the quartic extension. Its permutation layers
//! are the crate's own `poseidon2_apply_me` / `poseidon2_apply_mi`, lifted coefficient-wise,
//! so the reference cannot drift from the canonical permutation without the Poseidon2 KATs
//! failing first. A second reference with the retired profile (`M4` on contiguous quads,
//! `-2` on the internal diagonal, unweighted `perm + cur` feed-forward) is evaluated on the
//! same data and must disagree with the device: that is what the kernels computed before
//! they were aligned with the CPU AIR.

#![cfg(feature = "std")]

use core::ops::{Add, Mul, Sub};

use qsag_accel::goldilocks::{gl_add, gl_mul, gl_neg, gl_reduce_u64, gl_sub};
use qsag_accel::poseidon2::{
    poseidon2_apply_me, poseidon2_apply_mi, poseidon2_const_at, poseidon2_perm12, poseidon2_sbox7,
};
use qsag_accel::{VulkanError, VulkanSpirvBackend};

// ---- trace layout (`qsag-agg`, `trace.rs`) -------------------------------------------------

const NUM_COLS: usize = 256;
const COL_ST_IN: usize = 0;
const COL_SBOX_OUT: usize = 12;
const COL_PREV: usize = 130;
const COL_NEXT: usize = 174;
const COL_AUX: usize = 218;
const NUM_STATE: usize = 44;
const NUM_SBOX: usize = 118;
const NUM_GROUP_A: usize = NUM_SBOX + 2 * NUM_STATE;

const ST_KP_IDX: usize = 4;
const ST_TREE_LO: usize = 5;
const ST_TREE_HI: usize = 6;
const ST_REM_PACK: usize = 7;
const ST_SUB_SPONGE: usize = 25;
const ST_WORK: usize = 37;
const ST_CURSOR_IDX: usize = 41;
const ST_ACC_OR_U1: usize = 42;
const ST_WOTS_U2: usize = 43;

const DOMAIN_WOTS_STEP: u64 = 0x5153_4147_5753_5450;
const DOMAIN_FORS_LEAF: u64 = 0x5153_4147_464C_4546;

// Opcode numbering of `encode_constraint_kind`.
const KIND_IDLE: u32 = 0;
const KIND_FORS_LEAF_HASH: u32 = 8;
const KIND_WOTS_CHAIN_STEP0: u32 = 17;
const KIND_WOTS_CHAIN_STEP1: u32 = 18;
const KIND_WOTS_CHAIN_STEP2: u32 = 19;

/// `(kind id, kind argument)` of every opcode the trace uses, indexed by `uid`.
const UNIQUE_OPS: [(u32, u32); 7] = [
    (KIND_WOTS_CHAIN_STEP1, 0),
    (KIND_WOTS_CHAIN_STEP0, 0),
    (KIND_WOTS_CHAIN_STEP0, 3),
    (KIND_WOTS_CHAIN_STEP2, 0),
    (KIND_WOTS_CHAIN_STEP2, 1),
    (KIND_FORS_LEAF_HASH, 2),
    (KIND_IDLE, 0),
];
const UID_STEP1: usize = 0;
const UID_IDLE: usize = 6;

const ROWS: usize = 256;

// ---- GoldilocksExt4 = Fp[u, v] / (u^2 - 7, v^2 - u), limbs `[c0, c1, c2, c3]` ---------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct E([u64; 4]);

impl E {
    const ZERO: Self = Self([0; 4]);
    const ONE: Self = Self([1, 0, 0, 0]);

    fn base(x: u64) -> Self {
        Self([gl_reduce_u64(x), 0, 0, 0])
    }
    fn scale(self, s: u64) -> Self {
        Self(self.0.map(|c| gl_mul(c, s)))
    }
    fn pow7(self) -> Self {
        let x2 = self * self;
        let x3 = x2 * self;
        x3 * (x2 * x2)
    }
    fn is_zero(self) -> bool {
        self == Self::ZERO
    }
}

impl Add for E {
    type Output = Self;
    fn add(self, o: Self) -> Self {
        Self(core::array::from_fn(|i| gl_add(self.0[i], o.0[i])))
    }
}

impl Sub for E {
    type Output = Self;
    fn sub(self, o: Self) -> Self {
        Self(core::array::from_fn(|i| gl_sub(self.0[i], o.0[i])))
    }
}

impl Mul for E {
    type Output = Self;
    fn mul(self, o: Self) -> Self {
        let mul2 = |x: [u64; 2], y: [u64; 2]| {
            [
                gl_add(gl_mul(x[0], y[0]), gl_mul(7, gl_mul(x[1], y[1]))),
                gl_add(gl_mul(x[0], y[1]), gl_mul(x[1], y[0])),
            ]
        };
        let (a_lo, a_hi) = ([self.0[0], self.0[1]], [self.0[2], self.0[3]]);
        let (b_lo, b_hi) = ([o.0[0], o.0[1]], [o.0[2], o.0[3]]);
        let lo = mul2(a_lo, b_lo);
        let hi = mul2(a_hi, b_hi);
        let c0 = mul2(a_lo, b_hi);
        let c1 = mul2(a_hi, b_lo);
        Self([
            gl_add(lo[0], gl_mul(7, hi[1])),
            gl_add(lo[1], hi[0]),
            gl_add(c0[0], c1[0]),
            gl_add(c0[1], c1[1]),
        ])
    }
}

fn interp(v0: E, v1: E, k: u64) -> E {
    v0 + (v1 - v0).scale(k)
}

// ---- the two Poseidon2 profiles ------------------------------------------------------------

#[derive(Clone, Copy)]
struct Profile {
    external: fn(&mut [u64; 12]),
    internal: fn(&mut [u64; 12]),
    /// `perm + in0 + 2 * in1 + 4 * tweak` when set, the retired `perm + in0` otherwise.
    weighted_feed_forward: bool,
}

const CANONICAL: Profile = Profile {
    external: poseidon2_apply_me,
    internal: poseidon2_apply_mi,
    weighted_feed_forward: true,
};

fn legacy_m4(b: [u64; 4]) -> [u64; 4] {
    let s = gl_add(gl_add(b[0], b[1]), gl_add(b[2], b[3]));
    [
        gl_add(s, gl_add(b[0], gl_add(b[1], b[1]))),
        gl_add(s, gl_add(b[1], gl_add(b[2], b[2]))),
        gl_add(s, gl_add(b[2], gl_add(b[3], b[3]))),
        gl_add(s, gl_add(b[3], gl_add(b[0], b[0]))),
    ]
}

/// The retired external layer: `M4` on the three contiguous quads, then column sums.
fn legacy_external(st: &mut [u64; 12]) {
    for g in (0..12).step_by(4) {
        let y = legacy_m4([st[g], st[g + 1], st[g + 2], st[g + 3]]);
        st[g..g + 4].copy_from_slice(&y);
    }
    for column in 0..4 {
        let (a, b, c) = (column, 4 + column, 8 + column);
        let s = gl_add(gl_add(st[a], st[b]), st[c]);
        st[a] = gl_add(st[a], s);
        st[b] = gl_add(st[b], s);
        st[c] = gl_add(st[c], s);
    }
}

/// The retired internal layer: `J + diag(-2, 1, 2, 4, ..., 1024)`.
fn legacy_internal(st: &mut [u64; 12]) {
    let s = st.iter().fold(0, |acc, &x| gl_add(acc, x));
    st[0] = gl_add(gl_neg(gl_add(st[0], st[0])), s);
    st[1] = gl_add(st[1], s);
    for (i, x) in st.iter_mut().enumerate().skip(2) {
        *x = gl_add(gl_mul(1 << (i - 1), *x), s);
    }
}

const LEGACY: Profile = Profile {
    external: legacy_external,
    internal: legacy_internal,
    weighted_feed_forward: false,
};

/// Apply a base-field linear layer to an extension-field state, one coefficient at a time.
fn lift_linear(st: &mut [E; 12], layer: fn(&mut [u64; 12])) {
    for c in 0..4 {
        let mut lane: [u64; 12] = core::array::from_fn(|i| st[i].0[c]);
        layer(&mut lane);
        for (dst, v) in st.iter_mut().zip(lane) {
            dst.0[c] = v;
        }
    }
}

// ---- host reference: the row constraints -----------------------------------------------------

/// Group A (the 118 S-box transitions of one permutation) and the 88 boundary constraints,
/// in the CPU AIR's emission order. Returns the recomputed permutation output.
fn group_a_and_boundaries(
    profile: Profile,
    cols: &[E; NUM_COLS],
    is_row_first: E,
    is_row_last: E,
    emit: &mut dyn FnMut(E),
) -> [E; 12] {
    let mut st: [E; 12] = core::array::from_fn(|i| cols[COL_ST_IN + i]);
    lift_linear(&mut st, profile.external);
    let mut sb = COL_SBOX_OUT;
    for (tag, rounds, full) in [(0u64, 4u64, true), (1, 22, false), (2, 4, true)] {
        for r in 0..rounds {
            let lanes = if full { 12 } else { 1 };
            for (lane, lane_val) in st.iter_mut().enumerate().take(lanes) {
                let rc = E::base(poseidon2_const_at(tag, r, lane as u64));
                let sbox_val = cols[sb];
                emit((*lane_val + rc).pow7() - sbox_val);
                *lane_val = sbox_val;
                sb += 1;
            }
            lift_linear(
                &mut st,
                if full {
                    profile.external
                } else {
                    profile.internal
                },
            );
        }
    }
    assert_eq!(sb, COL_SBOX_OUT + NUM_SBOX);
    for j in 0..NUM_STATE {
        emit(is_row_first * cols[COL_PREV + j]);
        emit(is_row_last * cols[COL_NEXT + j]);
    }
    st
}

fn bool_check(b: E) -> E {
    b * (E::ONE - b)
}

fn quartic_base4(d: E) -> E {
    (d * (d - E::ONE)) * ((d - E::base(2)) * (d - E::base(3)))
}

/// Transition constraints of one opcode, in the CPU AIR's emission order.
fn op_constraints(
    profile: Profile,
    (kind, arg): (u32, u32),
    step_c0: E,
    cols: &[E; NUM_COLS],
    perm_out: &[E; 12],
    pk_seed: &[E; 4],
    emit: &mut dyn FnMut(E),
) {
    let st_in = |i: usize| cols[COL_ST_IN + i];
    let prev = |j: usize| cols[COL_PREV + j];
    let next = |j: usize| cols[COL_NEXT + j];
    let aux = |i: usize| cols[COL_AUX + i];
    let feed_forward = |in0: E, i: usize| {
        let unweighted = perm_out[i] + in0;
        if profile.weighted_feed_forward {
            unweighted + st_in(4 + i).scale(2) + st_in(8 + i).scale(4)
        } else {
            unweighted
        }
    };
    let mut carry = [true; NUM_STATE];
    let addr_limb = step_c0 + prev(ST_KP_IDX).scale(1 << 16);

    match kind {
        KIND_IDLE => {
            for j in 0..NUM_STATE {
                emit(next(j));
            }
            return;
        }
        KIND_FORS_LEAF_HASH => {
            let slot = arg as usize;
            let mut idx_j = E::ZERO;
            for k in 0..4 {
                emit(quartic_base4(aux(4 + k)));
                idx_j = idx_j + aux(4 + k).scale(1 << (2 * k));
            }
            let quot = aux(8);
            emit(prev(ST_REM_PACK + slot) - (idx_j + quot.scale(256)));
            emit(next(ST_REM_PACK + slot) - quot);
            let tweak1 = prev(ST_KP_IDX).scale(1 << 24) + step_c0 + idx_j;
            for (i, &seed_i) in pk_seed.iter().enumerate() {
                emit(st_in(i) - aux(i));
                emit(st_in(4 + i) - seed_i);
                emit(next(ST_WORK + i) - feed_forward(aux(i), i));
            }
            emit(st_in(8) - E::base(DOMAIN_FORS_LEAF));
            emit(st_in(9) - tweak1);
            emit(st_in(10) - prev(ST_TREE_LO));
            emit(st_in(11) - prev(ST_TREE_HI));
            emit(next(ST_CURSOR_IDX) - idx_j);
            carry[ST_REM_PACK + slot] = false;
            carry[ST_WORK..ST_WORK + 4].fill(false);
            carry[ST_CURSOR_IDX] = false;
        }
        KIND_WOTS_CHAIN_STEP0 => {
            let slot = arg as usize;
            let (u0, u1, u2, quot) = (aux(4), aux(5), aux(6), aux(7));
            emit(bool_check(u0));
            emit(bool_check(u1));
            emit(bool_check(u2));
            emit(u1 * (E::ONE - u0));
            emit(u2 * (E::ONE - u1));
            let rem_r = E::base(3) - (u0 + u1 + u2);
            emit(prev(ST_REM_PACK + slot) - (rem_r + quot.scale(4)));
            emit(next(ST_REM_PACK + slot) - quot);
            for (i, &seed_i) in pk_seed.iter().enumerate() {
                let sig_i = aux(i);
                emit(st_in(i) - sig_i);
                emit(st_in(4 + i) - seed_i);
                let ff_i = feed_forward(sig_i, i);
                emit(next(ST_WORK + i) - (u0 * sig_i + (E::ONE - u0) * ff_i));
            }
            emit(st_in(8) - E::base(DOMAIN_WOTS_STEP));
            emit(st_in(9) - addr_limb);
            emit(st_in(10) - prev(ST_TREE_LO));
            emit(st_in(11) - prev(ST_TREE_HI));
            emit(next(ST_ACC_OR_U1) - u1);
            emit(next(ST_WOTS_U2) - u2);
            carry[ST_REM_PACK + slot] = false;
            carry[ST_WORK..ST_WORK + 4].fill(false);
            carry[ST_ACC_OR_U1] = false;
            carry[ST_WOTS_U2] = false;
        }
        KIND_WOTS_CHAIN_STEP1 | KIND_WOTS_CHAIN_STEP2 => {
            let (skip, dst) = match (kind, arg) {
                (KIND_WOTS_CHAIN_STEP1, _) => (prev(ST_ACC_OR_U1), ST_WORK),
                (_, 0) => (prev(ST_WOTS_U2), ST_SUB_SPONGE),
                _ => (prev(ST_WOTS_U2), ST_WORK),
            };
            for (i, &seed_i) in pk_seed.iter().enumerate() {
                let cur_i = prev(ST_WORK + i);
                emit(st_in(i) - cur_i);
                emit(st_in(4 + i) - seed_i);
                let ff_i = feed_forward(cur_i, i);
                emit(next(dst + i) - (skip * cur_i + (E::ONE - skip) * ff_i));
            }
            emit(st_in(8) - E::base(DOMAIN_WOTS_STEP));
            emit(st_in(9) - addr_limb);
            emit(st_in(10) - prev(ST_TREE_LO));
            emit(st_in(11) - prev(ST_TREE_HI));
            carry[dst..dst + 4].fill(false);
        }
        other => panic!("opcode {other} is not part of this trace"),
    }
    for (j, keep) in carry.into_iter().enumerate() {
        if keep {
            emit(next(j) - prev(j));
        }
    }
}

/// Number of constraints an opcode emits (its share of the gamma schedule).
fn op_constraint_count(op: (u32, u32)) -> usize {
    let mut count = 0usize;
    op_constraints(
        CANONICAL,
        op,
        E::ZERO,
        &[E::ZERO; NUM_COLS],
        &[E::ZERO; 12],
        &[E::ZERO; 4],
        &mut |_| count += 1,
    );
    count
}

// ---- deterministic data ------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn word(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn fe(&mut self) -> u64 {
        gl_reduce_u64(self.word())
    }
    fn ext(&mut self) -> E {
        E(core::array::from_fn(|_| self.fe()))
    }
}

/// Record the S-box outputs of the canonical permutation, as the prover's witness generator
/// does, and return the permutation output.
fn record_canonical_perm(st_in: [u64; 12], sbox_out: &mut [u64]) -> [u64; 12] {
    let mut st = st_in;
    let mut cursor = 0usize;
    poseidon2_apply_me(&mut st);
    for (tag, rounds, full) in [(0u64, 4u64, true), (1, 22, false), (2, 4, true)] {
        for r in 0..rounds {
            let lanes = if full { 12 } else { 1 };
            for (lane, x) in st.iter_mut().enumerate().take(lanes) {
                *x = poseidon2_sbox7(gl_add(*x, poseidon2_const_at(tag, r, lane as u64)));
                sbox_out[cursor] = *x;
                cursor += 1;
            }
            if full {
                poseidon2_apply_me(&mut st);
            } else {
                poseidon2_apply_mi(&mut st);
            }
        }
    }
    assert_eq!(cursor, NUM_SBOX);
    let mut direct = st_in;
    poseidon2_perm12(&mut direct);
    assert_eq!(st, direct, "recorded permutation is poseidon2_perm12");
    st
}

/// One honest row of opcode `(kind, arg)`: `st_in`, the canonical S-box columns, auxiliary
/// witnesses and `next` are derived from a random `prev` state exactly as the constraints
/// demand. `zero_prev` produces a row that also satisfies the first-row boundary.
fn honest_row(
    rng: &mut Rng,
    (kind, arg): (u32, u32),
    step_c0: u64,
    pk_seed: &[u64; 4],
    zero_prev: bool,
) -> [u64; NUM_COLS] {
    let mut prev = [0u64; NUM_STATE];
    if !zero_prev {
        prev = core::array::from_fn(|_| rng.fe());
    }
    let mut aux: [u64; 38] = core::array::from_fn(|_| rng.fe());
    let mut st_in: [u64; 12] = core::array::from_fn(|_| rng.fe());
    let weighted = |perm: &[u64; 12], st_in: &[u64; 12], in0: u64, i: usize| {
        gl_add(
            gl_add(perm[i], in0),
            gl_add(gl_mul(2, st_in[4 + i]), gl_mul(4, st_in[8 + i])),
        )
    };
    let hash_input =
        |st_in: &mut [u64; 12], in0: [u64; 4], domain: u64, tweak: u64, prev: &[u64]| {
            st_in[..4].copy_from_slice(&in0);
            st_in[4..8].copy_from_slice(pk_seed);
            st_in[8] = gl_reduce_u64(domain);
            st_in[9] = tweak;
            st_in[10] = prev[ST_TREE_LO];
            st_in[11] = prev[ST_TREE_HI];
        };
    let addr_limb = |prev: &[u64]| gl_add(step_c0, gl_mul(prev[ST_KP_IDX], 1 << 16));
    let mut sbox = [0u64; NUM_SBOX];
    let mut next;

    match kind {
        KIND_IDLE => {
            record_canonical_perm(st_in, &mut sbox);
            next = [0u64; NUM_STATE];
        }
        KIND_FORS_LEAF_HASH => {
            let slot = arg as usize;
            let mut idx_j = 0u64;
            for k in 0..4 {
                aux[4 + k] = if zero_prev { 0 } else { rng.word() & 3 };
                idx_j += aux[4 + k] << (2 * k);
            }
            aux[8] = if zero_prev { 0 } else { rng.word() >> 24 };
            prev[ST_REM_PACK + slot] = gl_add(idx_j, gl_mul(aux[8], 256));
            let tweak1 = gl_add(gl_mul(prev[ST_KP_IDX], 1 << 24), gl_add(step_c0, idx_j));
            let leaf = [aux[0], aux[1], aux[2], aux[3]];
            hash_input(&mut st_in, leaf, DOMAIN_FORS_LEAF, tweak1, &prev);
            let perm = record_canonical_perm(st_in, &mut sbox);
            next = prev;
            next[ST_REM_PACK + slot] = aux[8];
            for (i, &leaf_i) in leaf.iter().enumerate() {
                next[ST_WORK + i] = weighted(&perm, &st_in, leaf_i, i);
            }
            next[ST_CURSOR_IDX] = idx_j;
        }
        KIND_WOTS_CHAIN_STEP0 => {
            let slot = arg as usize;
            // `u0 >= u1 >= u2`: the remaining chain length is `3 - (u0 + u1 + u2)`.
            let ones = if zero_prev { 3 } else { rng.word() & 3 };
            let u = [ones >= 1, ones >= 2, ones >= 3].map(u64::from);
            aux[4..7].copy_from_slice(&u);
            aux[7] = if zero_prev { 0 } else { rng.word() >> 24 };
            prev[ST_REM_PACK + slot] = gl_add(3 - ones, gl_mul(aux[7], 4));
            let sig = [aux[0], aux[1], aux[2], aux[3]];
            let tweak = addr_limb(&prev);
            hash_input(&mut st_in, sig, DOMAIN_WOTS_STEP, tweak, &prev);
            let perm = record_canonical_perm(st_in, &mut sbox);
            next = prev;
            next[ST_REM_PACK + slot] = aux[7];
            for (i, &sig_i) in sig.iter().enumerate() {
                let ff = weighted(&perm, &st_in, sig_i, i);
                next[ST_WORK + i] = if u[0] == 1 { sig_i } else { ff };
            }
            next[ST_ACC_OR_U1] = u[1];
            next[ST_WOTS_U2] = u[2];
        }
        KIND_WOTS_CHAIN_STEP1 | KIND_WOTS_CHAIN_STEP2 => {
            let (skip_limb, dst) = match (kind, arg) {
                (KIND_WOTS_CHAIN_STEP1, _) => (ST_ACC_OR_U1, ST_WORK),
                (_, 0) => (ST_WOTS_U2, ST_SUB_SPONGE),
                _ => (ST_WOTS_U2, ST_WORK),
            };
            // The selector is a field element here on purpose: these rows constrain it only
            // through the degree-2 blend, and a generic value exercises both products.
            let skip = prev[skip_limb];
            let cur = [
                prev[ST_WORK],
                prev[ST_WORK + 1],
                prev[ST_WORK + 2],
                prev[ST_WORK + 3],
            ];
            let tweak = addr_limb(&prev);
            hash_input(&mut st_in, cur, DOMAIN_WOTS_STEP, tweak, &prev);
            let perm = record_canonical_perm(st_in, &mut sbox);
            next = prev;
            for (i, &cur_i) in cur.iter().enumerate() {
                let ff = weighted(&perm, &st_in, cur_i, i);
                next[dst + i] = gl_add(gl_mul(skip, cur_i), gl_mul(gl_sub(1, skip), ff));
            }
        }
        other => panic!("opcode {other} is not part of this trace"),
    }

    let mut row = [0u64; NUM_COLS];
    row[COL_ST_IN..COL_ST_IN + 12].copy_from_slice(&st_in);
    row[COL_SBOX_OUT..COL_SBOX_OUT + NUM_SBOX].copy_from_slice(&sbox);
    row[COL_PREV..COL_PREV + NUM_STATE].copy_from_slice(&prev);
    row[COL_NEXT..COL_NEXT + NUM_STATE].copy_from_slice(&next);
    row[COL_AUX..].copy_from_slice(&aux);
    row
}

/// Everything one sumcheck round's evaluation reads, in host form.
#[derive(Clone)]
struct RoundState {
    /// `cur_m` rows of 256 columns.
    cols: Vec<[E; NUM_COLS]>,
    eq_tau: Vec<E>,
    eq_not_last: Vec<E>,
    shift_tau: Vec<E>,
    is_first: Vec<E>,
    is_last: Vec<E>,
    step_c0: Vec<E>,
    /// Per local step: `(uid, selector)` of every opcode with a nonzero selector.
    ops: Vec<Vec<(usize, E)>>,
}

struct Fixture {
    witness_row_major: Vec<u64>,
    pk_seed: [u64; 4],
    pk_root: [u64; 4],
    mu: [u64; 5],
    group_a_gammas: Vec<E>,
    shift_gammas: Vec<E>,
    op_gammas: Vec<Vec<E>>,
    round0: RoundState,
}

fn step_uid(row: usize) -> usize {
    let half = ROWS / 2;
    if row == 0 {
        UID_STEP1
    } else if row == ROWS - 1 {
        UID_IDLE
    } else if row >= half && row.is_multiple_of(4) {
        // Same opcode as the row it is paired with in round 0.
        (row - half) % UNIQUE_OPS.len()
    } else {
        row % UNIQUE_OPS.len()
    }
}

fn fixture() -> Fixture {
    let mut rng = Rng(0x5153_4147_4149_5221);
    let pk_seed: [u64; 4] = core::array::from_fn(|_| rng.fe());
    let pk_root: [u64; 4] = core::array::from_fn(|_| rng.fe());
    let mu: [u64; 5] = core::array::from_fn(|_| rng.fe());
    let step_c0: Vec<u64> = (0..ROWS).map(|_| rng.word() >> 40).collect();

    let mut witness_row_major = Vec::with_capacity(ROWS * NUM_COLS);
    let mut cols = Vec::with_capacity(ROWS);
    for (row, &c0) in step_c0.iter().enumerate() {
        let uid = step_uid(row);
        let base_row = honest_row(&mut rng, UNIQUE_OPS[uid], c0, &pk_seed, row == 0);
        witness_row_major.extend_from_slice(&base_row);
        cols.push(base_row.map(E::base));
    }

    let unit = |at: usize| -> Vec<E> {
        (0..ROWS)
            .map(|i| if i == at { E::ONE } else { E::ZERO })
            .collect()
    };
    let round0 = RoundState {
        cols,
        eq_tau: (0..ROWS).map(|_| rng.ext()).collect(),
        eq_not_last: (0..ROWS).map(|_| rng.ext()).collect(),
        shift_tau: (0..ROWS).map(|_| rng.ext()).collect(),
        is_first: unit(0),
        is_last: unit(ROWS - 1),
        step_c0: step_c0.iter().map(|&c| E::base(c)).collect(),
        ops: (0..ROWS).map(|row| vec![(step_uid(row), E::ONE)]).collect(),
    };
    Fixture {
        witness_row_major,
        pk_seed,
        pk_root,
        mu,
        group_a_gammas: (0..NUM_GROUP_A).map(|_| rng.ext()).collect(),
        shift_gammas: (0..NUM_STATE).map(|_| rng.ext()).collect(),
        op_gammas: UNIQUE_OPS
            .iter()
            .map(|&op| (0..op_constraint_count(op)).map(|_| rng.ext()).collect())
            .collect(),
        round0,
    }
}

/// `(uid, selector at the low row, selector difference high - low)` over both rows of a pair.
fn union_ops(lo: &[(usize, E)], hi: &[(usize, E)]) -> Vec<(usize, E, E)> {
    let selector = |list: &[(usize, E)], uid: usize| {
        list.iter()
            .find(|&&(u, _)| u == uid)
            .map_or(E::ZERO, |&(_, v)| v)
    };
    let mut uids: Vec<usize> = lo.iter().chain(hi).map(|&(uid, _)| uid).collect();
    uids.sort_unstable();
    uids.dedup();
    uids.into_iter()
        .map(|uid| {
            let v0 = selector(lo, uid);
            (uid, v0, selector(hi, uid) - v0)
        })
        .collect()
}

impl Fixture {
    /// The batched constraint value of one (possibly interpolated) row: Group A and
    /// boundaries, plus every selected opcode, each weighted by its gamma.
    fn batched_row(
        &self,
        profile: Profile,
        cols: &[E; NUM_COLS],
        is_first: E,
        is_last: E,
        step_c0: E,
        ops: &[(usize, E)],
    ) -> E {
        let mut acc = E::ZERO;
        let mut c_idx = 0usize;
        let perm_out = group_a_and_boundaries(profile, cols, is_first, is_last, &mut |v| {
            acc = acc + self.group_a_gammas[c_idx] * v;
            c_idx += 1;
        });
        assert_eq!(c_idx, NUM_GROUP_A);
        let pk_seed = self.pk_seed.map(E::base);
        for &(uid, selector) in ops {
            let mut op_acc = E::ZERO;
            let mut g_idx = 0usize;
            op_constraints(
                profile,
                UNIQUE_OPS[uid],
                step_c0,
                cols,
                &perm_out,
                &pk_seed,
                &mut |v| {
                    op_acc = op_acc + self.op_gammas[uid][g_idx] * v;
                    g_idx += 1;
                },
            );
            assert_eq!(g_idx, self.op_gammas[uid].len());
            // The single signer of this trace is active (`act = 1`).
            acc = acc + selector * op_acc;
        }
        acc
    }

    /// The eight evaluations `[ev(0), ev(2), ..., ev(8)]` of the round polynomial
    /// `sum_idx eq(X) * batched_row(X) + eq_not_last(X) * <g, next(X)> - shift(X) * <g, prev(X)>`.
    ///
    /// `skip_eq_at_zero` mirrors the Round-0 base-field path, which evaluates only the shift
    /// bus at `X = 0` because every committed row satisfies its constraints there.
    fn round_evals(&self, profile: Profile, st: &RoundState, skip_eq_at_zero: bool) -> [E; 8] {
        let half = st.cols.len() / 2;
        let half_r = st.is_first.len() / 2;
        assert_eq!(half, half_r, "single signer: one local step per row");
        let mut evals = [E::ZERO; 8];
        for (slot, eval) in evals.iter_mut().enumerate() {
            let k = if slot == 0 { 0 } else { slot as u64 + 1 };
            for idx in 0..half {
                let hi = idx + half;
                let cols: [E; NUM_COLS] =
                    core::array::from_fn(|c| interp(st.cols[idx][c], st.cols[hi][c], k));
                let mut bus_next = E::ZERO;
                let mut bus_prev = E::ZERO;
                for j in 0..NUM_STATE {
                    bus_next = bus_next + self.shift_gammas[j] * cols[COL_NEXT + j];
                    bus_prev = bus_prev + self.shift_gammas[j] * cols[COL_PREV + j];
                }
                let mut total = interp(st.eq_not_last[idx], st.eq_not_last[hi], k) * bus_next
                    - interp(st.shift_tau[idx], st.shift_tau[hi], k) * bus_prev;
                if !(skip_eq_at_zero && k == 0) {
                    let ops: Vec<(usize, E)> = union_ops(&st.ops[idx], &st.ops[hi])
                        .into_iter()
                        .map(|(uid, v0, dv)| (uid, v0 + dv.scale(k)))
                        .collect();
                    let batched = self.batched_row(
                        profile,
                        &cols,
                        interp(st.is_first[idx], st.is_first[hi], k),
                        interp(st.is_last[idx], st.is_last[hi], k),
                        interp(st.step_c0[idx], st.step_c0[hi], k),
                        &ops,
                    );
                    total = total + interp(st.eq_tau[idx], st.eq_tau[hi], k) * batched;
                }
                *eval = *eval + total;
            }
        }
        evals
    }
}

/// Fold every table of a round at the challenge, as the prover does between rounds.
fn fold(st: &RoundState, chal: E) -> RoundState {
    let half = st.cols.len() / 2;
    let at = |v0: E, v1: E| v0 + chal * (v1 - v0);
    let fold_vec = |v: &[E]| -> Vec<E> { (0..half).map(|i| at(v[i], v[i + half])).collect() };
    RoundState {
        cols: (0..half)
            .map(|i| core::array::from_fn(|c| at(st.cols[i][c], st.cols[i + half][c])))
            .collect(),
        eq_tau: fold_vec(&st.eq_tau),
        eq_not_last: fold_vec(&st.eq_not_last),
        shift_tau: fold_vec(&st.shift_tau),
        is_first: fold_vec(&st.is_first),
        is_last: fold_vec(&st.is_last),
        step_c0: fold_vec(&st.step_c0),
        ops: (0..half)
            .map(|i| {
                union_ops(&st.ops[i], &st.ops[i + half])
                    .into_iter()
                    .map(|(uid, v0, dv)| (uid, v0 + chal * dv))
                    .filter(|(_, v)| !v.is_zero())
                    .collect()
            })
            .collect(),
    }
}

// ---- host-only checks ------------------------------------------------------------------------------

/// Every row of the trace satisfies every constraint of the canonical AIR at its own point,
/// and the retired profile rejects the same rows: the fixture is a canonical Poseidon2-12 +
/// weighted-WOTS trace, and the two references are distinguishable on it.
#[test]
fn fixture_rows_satisfy_the_canonical_air_and_violate_the_retired_one() {
    let fx = fixture();
    let st = &fx.round0;
    let pk_seed = fx.pk_seed.map(E::base);
    let mut kinds_seen = [0usize; UNIQUE_OPS.len()];
    let mut feed_forward_rows = 0usize;
    for row in 0..ROWS {
        let uid = step_uid(row);
        kinds_seen[uid] += 1;
        let residuals = |profile: Profile| -> (usize, usize, usize) {
            let mut group_a_bad = 0usize;
            let mut emitted = 0usize;
            let perm_out = group_a_and_boundaries(
                profile,
                &st.cols[row],
                st.is_first[row],
                st.is_last[row],
                &mut |v| {
                    emitted += 1;
                    group_a_bad += usize::from(!v.is_zero());
                },
            );
            let mut op_bad = 0usize;
            op_constraints(
                profile,
                UNIQUE_OPS[uid],
                st.step_c0[row],
                &st.cols[row],
                &perm_out,
                &pk_seed,
                &mut |v| op_bad += usize::from(!v.is_zero()),
            );
            (emitted, group_a_bad, op_bad)
        };
        assert_eq!(
            residuals(CANONICAL),
            (NUM_GROUP_A, 0, 0),
            "row {row} uid {uid}"
        );
        let (_, legacy_group_a_bad, legacy_op_bad) = residuals(LEGACY);
        assert!(
            legacy_group_a_bad > 0,
            "row {row}: retired matrices accepted"
        );
        // The feed-forward is live unless the row is idle or a first chain step that skips
        // the hash (`u0 = 1` keeps the signature limb).
        let kind = UNIQUE_OPS[uid].0;
        let skips_hash = kind == KIND_WOTS_CHAIN_STEP0 && st.cols[row][COL_AUX + 4] == E::ONE;
        if kind != KIND_IDLE && !skips_hash {
            feed_forward_rows += 1;
            assert!(
                legacy_op_bad > 0,
                "row {row}: retired feed-forward accepted"
            );
        }
    }
    assert!(kinds_seen.iter().all(|&n| n >= 8), "{kinds_seen:?}");
    assert!(feed_forward_rows >= ROWS / 2, "{feed_forward_rows}");
    // Round 0 pairs both equal and different opcodes.
    let half = ROWS / 2;
    let same = (0..half)
        .filter(|&i| step_uid(i) == step_uid(i + half))
        .count();
    assert!(same >= 8 && half - same >= 8, "{same}");
    assert_ne!(
        fx.round_evals(CANONICAL, st, true),
        fx.round_evals(LEGACY, st, true)
    );
}

// ---- the device ----------------------------------------------------------------------------------------

fn push_ext(dst: &mut Vec<u64>, e: E) {
    dst.extend_from_slice(&e.0);
}

fn to_e(raw: [[u64; 4]; 8]) -> [E; 8] {
    raw.map(E)
}

struct StaticTables {
    words: Vec<[u64; 4]>,
    /// Ext4 offset of each opcode's gamma block.
    op_gamma_base: Vec<u64>,
    id_sorted_u64_off: u32,
    dyn_ext4_off: u32,
}

/// The static part of the `sched + pub` buffer, laid out as the prover lays it out:
/// 206 Group-A gammas, 44 shift gammas, the per-opcode gammas, then the identity row order.
fn static_tables(fx: &Fixture) -> StaticTables {
    let mut words: Vec<[u64; 4]> = Vec::new();
    words.extend(fx.group_a_gammas.iter().map(|g| g.0));
    words.extend(fx.shift_gammas.iter().map(|g| g.0));
    assert_eq!(words.len(), 250);
    let mut op_gamma_base = Vec::new();
    for gammas in &fx.op_gammas {
        op_gamma_base.push(words.len() as u64);
        words.extend(gammas.iter().map(|g| g.0));
    }
    let id_sorted_u64_off = (words.len() * 4) as u32;
    let half_r = ROWS / 2;
    for base in (0..half_r).step_by(4) {
        words.push(core::array::from_fn(|i| (base + i).min(half_r - 1) as u64));
    }
    let dyn_ext4_off = words.len() as u32;
    StaticTables {
        words,
        op_gamma_base,
        id_sorted_u64_off,
        dyn_ext4_off,
    }
}

struct DynTables {
    words: Vec<u64>,
    signers_off: u32,
    steps_off: u32,
    op_hdr_off: u32,
    op_ent_off: u32,
}

/// The per-round part of the `sched + pub` buffer for a single signer whose step dimension
/// is being folded: signer fields, step publics, opcode headers and opcode entries.
fn dyn_tables(fx: &Fixture, tables: &StaticTables, st: &RoundState) -> DynTables {
    let cur_r = st.is_first.len();
    let half_r = cur_r / 2;
    let mut words = Vec::new();
    let signers_off = tables.dyn_ext4_off;
    push_ext(&mut words, E::ONE);
    for v in fx.pk_seed.iter().chain(&fx.pk_root).chain(&fx.mu) {
        push_ext(&mut words, E::base(*v));
    }
    let steps_off = signers_off + 14;
    for loc in 0..cur_r {
        push_ext(&mut words, st.is_first[loc]);
        push_ext(&mut words, st.is_last[loc]);
        push_ext(&mut words, st.step_c0[loc]);
    }
    let op_hdr_off = steps_off + 3 * cur_r as u32;
    let mut entries: Vec<[u64; 4]> = Vec::new();
    for idx in 0..half_r {
        let pairs = union_ops(&st.ops[idx], &st.ops[idx + half_r]);
        words.extend_from_slice(&[(entries.len() / 3) as u64, pairs.len() as u64, 0, 0]);
        for (uid, v0, dv) in pairs {
            let (kind, arg) = UNIQUE_OPS[uid];
            entries.push([
                u64::from(kind),
                u64::from(arg),
                tables.op_gamma_base[uid],
                0,
            ]);
            entries.push(v0.0);
            entries.push(dv.0);
        }
    }
    let op_ent_off = op_hdr_off + half_r as u32;
    for entry in &entries {
        words.extend_from_slice(entry);
    }
    DynTables {
        words,
        signers_off,
        steps_off,
        op_hdr_off,
        op_ent_off,
    }
}

fn audit_required() -> bool {
    std::env::var_os("QSAG_REQUIRE_GPU_AUDIT").is_some()
}

#[test]
fn air_row_group_kernels_match_the_canonical_poseidon2_and_weighted_wots_reference() {
    let gpu = match VulkanSpirvBackend::try_new_audited() {
        Ok(gpu) => gpu,
        Err(
            err @ (VulkanError::UnsupportedPlatform
            | VulkanError::LibraryLoadFailed
            | VulkanError::NoDiscreteGpuFound
            | VulkanError::PipelineAuditFailed(_)),
        ) => {
            // The audit gate must not turn missing hardware or telemetry into a green skip.
            assert!(
                !audit_required(),
                "QSAG_REQUIRE_GPU_AUDIT is set but no audited Vulkan device: {err}"
            );
            return;
        }
        Err(other) => panic!("unexpected Vulkan initialization error: {other}"),
    };
    let fx = fixture();
    let tables = static_tables(&fx);

    gpu.try_acquire_prover_session().expect("prover session");
    // The witness enters VRAM through the Round-0 commitment, row-major, with room behind it
    // for the column-major transpose.
    let witness_words = ROWS * NUM_COLS;
    let num_vars = witness_words.trailing_zeros() as usize;
    gpu.prover_whir_commit_round0(
        &[fx.witness_row_major.as_slice()],
        &[0x5a; 32],
        num_vars,
        4,
        16,
        0,
        0,
        witness_words,
    )
    .expect("commit the witness");
    let cols_base_word_offset = witness_words as u32;

    let st0 = &fx.round0;
    let mut shift_tables: Vec<[u64; 4]> = Vec::with_capacity(3 * ROWS);
    for table in [&st0.eq_tau, &st0.eq_not_last, &st0.shift_tau] {
        shift_tables.extend(table.iter().map(|e| e.0));
    }
    gpu.prover_air_init_shard(0, cols_base_word_offset, ROWS, &shift_tables, &tables.words)
        .expect("init shard");

    // Round 0: base-field columns, opcode pairs `(row, row + ROWS / 2)`.
    let dyn0 = dyn_tables(&fx, &tables, st0);
    let gpu_round0 = to_e(
        gpu.prover_air_eval_round(
            true,
            ROWS,
            ROWS,
            1,
            false,
            cols_base_word_offset,
            0,
            tables.dyn_ext4_off,
            &dyn0.words,
            dyn0.signers_off,
            dyn0.steps_off,
            dyn0.op_hdr_off,
            dyn0.op_ent_off,
            tables.id_sorted_u64_off,
        )
        .expect("round 0 evaluation"),
    );
    let host_round0 = fx.round_evals(CANONICAL, st0, true);
    assert_eq!(
        gpu_round0, host_round0,
        "Round-0 base-field AIR evaluations differ from the canonical reference"
    );
    // The skipped `X = 0` constraint part is zero on this trace, so the device's slot 0 is
    // also the full evaluation.
    assert_eq!(host_round0, fx.round_evals(CANONICAL, st0, false));
    let legacy_round0 = fx.round_evals(LEGACY, st0, true);
    for (slot, (device, retired)) in gpu_round0.iter().zip(&legacy_round0).enumerate().skip(1) {
        assert_ne!(
            device, retired,
            "slot {slot}: the device still evaluates the retired Poseidon2 profile"
        );
    }

    // Fold at a challenge and compare the folded columns and shift tables word for word.
    let chal = E([
        0x0123_4567_89ab_cdef,
        0x0fed_cba9_8765_4321,
        0x1111_2222_3333_4444,
        0x5555_6666_7777_8888,
    ]);
    let col_dst = 0u32;
    let sh_dst = (3 * ROWS) as u32;
    gpu.prover_air_fold_round(
        true,
        ROWS,
        cols_base_word_offset,
        col_dst,
        0,
        sh_dst,
        chal.0,
    )
    .expect("round 0 fold");
    let st1 = fold(st0, chal);
    let half = ROWS / 2;
    let mut gpu_cols = vec![[0u64; 4]; NUM_COLS * half];
    let mut gpu_shifts = vec![[0u64; 4]; 3 * half];
    gpu.prover_air_read_tail(col_dst, sh_dst, &mut gpu_cols, &mut gpu_shifts)
        .expect("read folded tables");
    for c in 0..NUM_COLS {
        for row in 0..half {
            assert_eq!(
                E(gpu_cols[c * half + row]),
                st1.cols[row][c],
                "col {c} row {row}"
            );
        }
    }
    for (t, table) in [&st1.eq_tau, &st1.eq_not_last, &st1.shift_tau]
        .into_iter()
        .enumerate()
    {
        for (row, want) in table.iter().enumerate() {
            assert_eq!(E(gpu_shifts[t * half + row]), *want, "table {t} row {row}");
        }
    }

    // Round 1: extension-field columns, blended opcode selectors, all eight points.
    let dyn1 = dyn_tables(&fx, &tables, &st1);
    let gpu_round1 = to_e(
        gpu.prover_air_eval_round(
            false,
            half,
            half,
            1,
            false,
            col_dst,
            sh_dst,
            tables.dyn_ext4_off,
            &dyn1.words,
            dyn1.signers_off,
            dyn1.steps_off,
            dyn1.op_hdr_off,
            dyn1.op_ent_off,
            tables.id_sorted_u64_off,
        )
        .expect("round 1 evaluation"),
    );
    let host_round1 = fx.round_evals(CANONICAL, &st1, false);
    assert_eq!(
        gpu_round1, host_round1,
        "Round-1 Ext4 AIR evaluations differ from the canonical reference"
    );
    let legacy_round1 = fx.round_evals(LEGACY, &st1, false);
    for (slot, (device, retired)) in gpu_round1.iter().zip(&legacy_round1).enumerate() {
        assert_ne!(
            device, retired,
            "slot {slot}: the device still evaluates the retired Poseidon2 profile"
        );
    }
    // The folded rows are no longer honest rows: the constraint part is live at every point.
    assert_ne!(host_round1[0], fx.round_evals(CANONICAL, &st1, true)[0]);

    gpu.release_prover_session();
}
