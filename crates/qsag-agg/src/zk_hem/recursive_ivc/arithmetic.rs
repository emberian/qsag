//! Field-native transcript and arithmetic used by the width-24 opening verifier.
use super::super::relation::{ConstraintSystem, Lc, poseidon2_gl24_perm_gadget};
use super::*;
use crate::sponge::{POSEIDON2_GL24_IV, POSEIDON2_GL24_MERKLE_TAG, poseidon2_gl24_perm};

pub(super) trait Wide: Backend {
    fn perm_w24(&mut self, state: &mut [Self::W; 24]);
    fn quint_mul(&mut self, a: &Quint<Self::W>, b: &Quint<Self::W>) -> Quint<Self::W>
    where
        Self: Sized,
    {
        a.mul_rows(self, b)
    }
}
impl Wide for Native {
    fn quint_mul(&mut self, a: &Quint<F>, b: &Quint<F>) -> Quint<F> {
        Quint((E(a.0) * E(b.0)).0)
    }
    fn perm_w24(&mut self, state: &mut [F; 24]) {
        poseidon2_gl24_perm(state);
    }
}
impl Wide for ConstraintSystem {
    fn perm_w24(&mut self, state: &mut [Lc; 24]) {
        poseidon2_gl24_perm_gadget(self, state);
    }
}

#[derive(Default)]
pub(super) struct Counter {
    pub permutations: usize,
    pub products: usize,
    pub allocated: usize,
}
impl Backend for Counter {
    type W = F;
    fn alloc(&mut self, x: F) -> F {
        self.allocated += 1;
        x
    }
    fn value(&self, x: &F) -> F {
        *x
    }
    fn mul(&mut self, x: &F, y: &F) -> F {
        self.products += 1;
        self.allocated += 1;
        x.const_mul(*y)
    }
    fn product(&mut self, _: &F, _: &F, _: &F) {
        self.products += 1;
    }
    fn equal(&mut self, _: &F, _: &F) {
        self.products += 1;
    }
}
impl Wide for Counter {
    fn perm_w24(&mut self, state: &mut [F; 24]) {
        self.permutations += 1;
        self.allocated += crate::sponge::POSEIDON2_GL24_SBOX_COUNT;
        poseidon2_gl24_perm(state);
    }
}

#[derive(Clone)]
pub(super) struct Duplex<W>(pub [W; 24]);
impl<W: Base> Duplex<W> {
    pub fn new() -> Self {
        let mut state = core::array::from_fn(|_| W::constant(F::ZERO));
        state[23] = W::constant(f(POSEIDON2_GL24_IV));
        Self(state)
    }
    // A tag of at most 16 bytes fits injectively in three 7-byte words. Length
    // framing separates empty, full-rate and partial-block messages.
    pub fn frame<B: Wide<W = W>>(&mut self, b: &mut B, tag: &[u8], data: &[W]) {
        assert!(tag.len() <= 21);
        for (i, chunk) in tag.chunks(7).enumerate() {
            let mut bytes = [0; 8];
            bytes[..chunk.len()].copy_from_slice(chunk);
            self.0[16 + i] = self.0[16 + i].plus(&W::constant(f(u64::from_le_bytes(bytes))));
        }
        self.0[19] = self.0[19].plus(&W::constant(f(tag.len() as u64)));
        self.0[20] = self.0[20].plus(&W::constant(f(data.len() as u64)));
        if data.is_empty() {
            b.perm_w24(&mut self.0);
        }
        for block in data.chunks(16) {
            for (lane, x) in self.0.iter_mut().zip(block) {
                *lane = lane.plus(x);
            }
            b.perm_w24(&mut self.0);
        }
    }
    pub fn challenge<B: Wide<W = W>>(&mut self, b: &mut B, tag: &[u8]) -> Quint<W> {
        self.frame(b, tag, &[]);
        Quint(core::array::from_fn(|i| b.pin(self.0[i].clone())))
    }
    pub fn exts<B: Wide<W = W>>(&mut self, b: &mut B, tag: &[u8], data: &[Quint<W>]) {
        let limbs: Vec<_> = data.iter().flat_map(|x| x.0.clone()).collect();
        self.frame(b, tag, &limbs);
    }
}
pub(super) fn compress<B: Wide>(
    b: &mut B,
    stage: usize,
    level: usize,
    left: &[B::W; 7],
    right: &[B::W; 7],
) -> [B::W; 7] {
    let mut state = core::array::from_fn(|_| B::W::constant(F::ZERO));
    state[..7].clone_from_slice(left);
    state[7..14].clone_from_slice(right);
    for (i, v) in [
        stage as u64,
        level as u64,
        16,
        8,
        7,
        POSEIDON2_GL24_MERKLE_TAG,
    ]
    .into_iter()
    .enumerate()
    {
        state[14 + i] = B::W::constant(f(v));
    }
    state[23] = B::W::constant(f(POSEIDON2_GL24_IV));
    b.perm_w24(&mut state);
    core::array::from_fn(|i| {
        let mut v = state[i].plus(&left[i]).plus(&right[i].scale(F::TWO));
        if i < 2 {
            v = v.plus(&B::W::constant(f(4 * [stage, level][i] as u64)));
        }
        v
    })
}

#[derive(Clone)]
pub(super) struct Quint<W>(pub [W; 5]);
impl<W: Base> Quint<W> {
    pub fn constant(v: E) -> Self {
        Self(v.0.map(W::constant))
    }
    pub fn base(x: W) -> Self {
        let mut out = Self::constant(E::ZERO);
        out.0[0] = x;
        out
    }
    pub fn alloc<B: Backend<W = W>>(b: &mut B, v: E) -> Self {
        Self(v.0.map(|x| b.alloc(x)))
    }
    pub fn add(&self, rhs: &Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i].plus(&rhs.0[i])))
    }
    pub fn sub(&self, rhs: &Self) -> Self {
        Self(core::array::from_fn(|i| self.0[i].minus(&rhs.0[i])))
    }
    pub fn scale(&self, c: F) -> Self {
        Self(core::array::from_fn(|i| self.0[i].scale(c)))
    }
    pub fn by_base<B: Backend<W = W>>(&self, b: &mut B, x: &W) -> Self {
        Self(core::array::from_fn(|i| b.mul(&self.0[i], x)))
    }
    pub fn mul<B: Wide<W = W>>(&self, b: &mut B, rhs: &Self) -> Self {
        b.quint_mul(self, rhs)
    }
    fn mul_rows<B: Backend<W = W>>(&self, b: &mut B, rhs: &Self) -> Self {
        // Interpolate the degree-eight product at 0..8, reduced modulo X^5-3.
        let eval = |v: &Self, t| {
            v.0.iter()
                .rev()
                .fold(W::constant(F::ZERO), |a, x| a.scale(t).plus(x))
        };
        let products: [W; 9] =
            core::array::from_fn(|i| b.mul(&eval(self, f(i as u64)), &eval(rhs, f(i as u64))));
        Self(core::array::from_fn(|j| {
            products
                .iter()
                .zip(REDUCE[j])
                .fold(W::constant(F::ZERO), |a, (x, c)| a.plus(&x.scale(f(c))))
        }))
    }
    pub fn equal<B: Backend<W = W>>(&self, b: &mut B, rhs: &Self) {
        for (x, y) in self.0.iter().zip(&rhs.0) {
            b.equal(x, y);
        }
    }
}

const REDUCE: [[u64; 9]; 5] = [
    [
        6225776123427422209,
        11144907875271311363,
        8454757698481684473,
        12682136547722526734,
        16909515396963368946,
        4534824583731085323,
        16140901060737761276,
        13450750883948134402,
        2690150176789626880,
    ],
    [
        7222229709319906448,
        5610884654446936072,
        76861433622560755,
        3612487380260356113,
        5956761105748459505,
        7916727663123759114,
        16678931096095686653,
        6401459400278989679,
        1863889765347098624,
    ],
    [
        16279983654911918864,
        8048490120762434693,
        384307168112803871,
        742993858351420713,
        18062436901301780524,
        1306644371583533028,
        15192943379392845154,
        14438969316238201415,
        17776951576417983343,
    ],
    [
        14970136723594112438,
        9161150874155695358,
        2856683282971841852,
        2843873044034748456,
        14763800375000214147,
        9197751556833105265,
        12643705830911246325,
        4856910591292292343,
        2492963998865081100,
    ],
    [
        8176135001599901697,
        18241780246421088936,
        13207356344143358646,
        15987178193492639727,
        4579660420010912446,
        10863082618655255198,
        2959165194468589574,
        15167322901518658218,
        3052039426762517163,
    ],
];
