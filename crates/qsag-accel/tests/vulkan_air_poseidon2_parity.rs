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
            for i in 0..4 {
                emit(st_in(i) - aux(i));
                emit(st_in(4 + i) - pk_seed[i]);
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
            for i in 0..4 {
                let sig_i = aux(i);
                emit(st_in(i) - sig_i);
                emit(st_in(4 + i) - pk_seed[i]);
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
            for i in 0..4 {
                let cur_i = prev(ST_WORK + i);
                emit(st_in(i) - cur_i);
                emit(st_in(4 + i) - pk_seed[i]);
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
    let hash_input = |st_in: &mut [u64; 12], in0: [u64; 4], domain: u64, tweak: u64, prev: &[u64]| {
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
            let tweak1 = gl_add(
                gl_mul(prev[ST_KP_IDX], 1 << 24),
                gl_add(step_c0, idx_j),
            );
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
