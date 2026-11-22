//! The Sapling key layer, natively: Jubjub, `GroupHash^J`, `PRF^expand`, the key
//! components of a spending key, diversified addresses, and ZIP 32 Sapling derivation.
//!
//! This file is a reference derivation only, for comparing keys and addresses byte for
//! byte with other implementations. It carries no circuit and no ownership statement:
//! Sapling note commitments are Pedersen commitments, binding only under discrete log,
//! so no sound post-quantum statement about Sapling notes exists (and ZIP 2005 does not
//! cover Sapling).
//!
//! Sources: Zcash protocol specification v2026.9.0 sections 4.2.2 (key components),
//! 5.4.1.6 (`DiversifyHash^Sapling`), 5.4.9.3 (Jubjub, `repr_J`, `abst_J`), 5.4.9.5
//! (group hash) and ZIP 32 ("Sapling extended keys", "Sapling child key derivation",
//! "Sapling internal key derivation", "Sapling diversifier derivation"). Every scalar is
//! a 32-byte little-endian integer and every point is `repr_J`, 32 bytes.
//!
//! Secret scalars (`ask`, `nsk`, `ivk`) go through a fixed 256-step double-and-add with
//! masked selection. Point decompression uses a fixed-schedule square root and reports
//! whether the input is a valid encoding.

use super::blake2::{Blake2b, blake2b_256, blake2s_256};
use super::ff1::ff1_aes256_encrypt_88;

type Limbs = [u64; 4];

/// `q_J`, the order of the Jubjub base field (the BLS12-381 scalar field).
const Q: Limbs = [
    0xffff_ffff_0000_0001,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
];

/// `r_J`, the order of the prime-order subgroup of Jubjub.
const R_J: Limbs = [
    0xd097_0e5e_d6f7_2cb7,
    0xa668_2093_ccc8_1082,
    0x0667_3b01_0134_3b00,
    0x0e7d_b4ea_6533_afa9,
];

/// `a - b`, and an all-ones mask if it borrowed.
const fn limbs_sub(a: &Limbs, b: &Limbs) -> (Limbs, u64) {
    let mut out = [0u64; 4];
    let mut borrow = 0u64;
    let mut i = 0;
    while i < 4 {
        let t = (a[i] as u128)
            .wrapping_sub(b[i] as u128)
            .wrapping_sub(borrow as u128);
        out[i] = t as u64;
        borrow = ((t >> 64) as u64) & 1;
        i += 1;
    }
    (out, borrow.wrapping_neg())
}

/// `a + b`, and the carry (0 or 1).
const fn limbs_add(a: &Limbs, b: &Limbs) -> (Limbs, u64) {
    let mut out = [0u64; 4];
    let mut carry = 0u64;
    let mut i = 0;
    while i < 4 {
        let t = a[i] as u128 + b[i] as u128 + carry as u128;
        out[i] = t as u64;
        carry = (t >> 64) as u64;
        i += 1;
    }
    (out, carry)
}

/// `a` where `mask` is all ones, `b` where it is zero.
const fn limbs_select(mask: u64, a: &Limbs, b: &Limbs) -> Limbs {
    let mut out = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        out[i] = (a[i] & mask) | (b[i] & !mask);
        i += 1;
    }
    out
}

/// `(hi * 2^256 + a) - m` if that is not negative, else `a`; for a value below `2m`.
const fn reduce_once(a: &Limbs, hi: u64, m: &Limbs) -> Limbs {
    let (d, borrow) = limbs_sub(a, m);
    limbs_select(hi.wrapping_neg() | !borrow, &d, a)
}

const fn add_mod(a: &Limbs, b: &Limbs, m: &Limbs) -> Limbs {
    let (s, carry) = limbs_add(a, b);
    reduce_once(&s, carry, m)
}

const fn sub_mod(a: &Limbs, b: &Limbs, m: &Limbs) -> Limbs {
    let (d, borrow) = limbs_sub(a, b);
    let masked = [m[0] & borrow, m[1] & borrow, m[2] & borrow, m[3] & borrow];
    limbs_add(&d, &masked).0
}

/// `-q^-1 mod 2^64`.
const Q_INV: u64 = {
    // `q0^(2^63 - 1)` is the inverse of the odd `q0` modulo `2^64`.
    let mut inv = 1u64;
    let mut i = 0;
    while i < 63 {
        inv = inv.wrapping_mul(inv).wrapping_mul(Q[0]);
        i += 1;
    }
    inv.wrapping_neg()
};

/// `2^k mod q`.
const fn pow2_mod_q(k: usize) -> Limbs {
    let mut x = [1u64, 0, 0, 0];
    let mut i = 0;
    while i < k {
        x = add_mod(&x, &x, &Q);
        i += 1;
    }
    x
}

const MONT_R: Limbs = pow2_mod_q(256);
const MONT_R2: Limbs = pow2_mod_q(512);

/// Montgomery multiplication modulo `q`: `a * b / 2^256`.
const fn mont_mul(a: &Limbs, b: &Limbs) -> Limbs {
    let mut t = [0u64; 6];
    let mut i = 0;
    while i < 4 {
        let mut carry = 0u128;
        let mut j = 0;
        while j < 4 {
            let x = t[j] as u128 + (a[j] as u128) * (b[i] as u128) + carry;
            t[j] = x as u64;
            carry = x >> 64;
            j += 1;
        }
        let x = t[4] as u128 + carry;
        t[4] = x as u64;
        t[5] = (x >> 64) as u64;

        let m = t[0].wrapping_mul(Q_INV);
        let mut carry = (t[0] as u128 + (m as u128) * (Q[0] as u128)) >> 64;
        let mut j = 1;
        while j < 4 {
            let x = t[j] as u128 + (m as u128) * (Q[j] as u128) + carry;
            t[j - 1] = x as u64;
            carry = x >> 64;
            j += 1;
        }
        let x = t[4] as u128 + carry;
        t[3] = x as u64;
        t[4] = t[5] + ((x >> 64) as u64);
        i += 1;
    }
    reduce_once(&[t[0], t[1], t[2], t[3]], t[4], &Q)
}

fn limbs_from_bytes(bytes: &[u8; 32]) -> Limbs {
    let mut out = [0u64; 4];
    for (limb, chunk) in out.iter_mut().zip(bytes.chunks_exact(8)) {
        *limb = u64::from_le_bytes(chunk.try_into().expect("8 bytes"));
    }
    out
}

fn limbs_to_bytes(limbs: &Limbs) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (chunk, limb) in out.chunks_exact_mut(8).zip(limbs) {
        chunk.copy_from_slice(&limb.to_le_bytes());
    }
    out
}

/// `q_J`, little-endian.
pub(super) const BASE_MODULUS_LE: [u8; 32] = limbs_to_le_bytes(&Q);
/// `r_J`, little-endian.
pub(super) const SCALAR_MODULUS_LE: [u8; 32] = limbs_to_le_bytes(&R_J);

const fn limbs_to_le_bytes(limbs: &Limbs) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        out[i] = (limbs[i / 8] >> (8 * (i % 8))) as u8;
        i += 1;
    }
    out
}

/// An element of the Jubjub base field, in Montgomery form and fully reduced.
#[derive(Clone, Copy)]
pub(super) struct Fq(Limbs);

impl PartialEq for Fq {
    fn eq(&self, other: &Self) -> bool {
        crate::limbs::ct_eq(self.0, other.0)
    }
}

impl Eq for Fq {}

impl Fq {
    pub(super) const ZERO: Fq = Fq([0; 4]);
    pub(super) const ONE: Fq = Fq(MONT_R);

    /// The element with the given canonical little-endian limbs (below `q`).
    const fn from_raw(limbs: Limbs) -> Fq {
        Fq(mont_mul(&limbs, &MONT_R2))
    }

    pub(super) fn from_bytes(bytes: &[u8; 32]) -> Option<Fq> {
        let limbs = limbs_from_bytes(bytes);
        let (_, borrow) = limbs_sub(&limbs, &Q);
        (borrow != 0).then(|| Fq::from_raw(limbs))
    }

    pub(super) fn to_bytes(self) -> [u8; 32] {
        limbs_to_bytes(&mont_mul(&self.0, &[1, 0, 0, 0]))
    }

    pub(super) fn add(&self, rhs: &Fq) -> Fq {
        Fq(add_mod(&self.0, &rhs.0, &Q))
    }

    pub(super) fn sub(&self, rhs: &Fq) -> Fq {
        Fq(sub_mod(&self.0, &rhs.0, &Q))
    }

    pub(super) fn neg(&self) -> Fq {
        Fq::ZERO.sub(self)
    }

    pub(super) const fn mul(&self, rhs: &Fq) -> Fq {
        Fq(mont_mul(&self.0, &rhs.0))
    }

    pub(super) fn square(&self) -> Fq {
        self.mul(self)
    }

    pub(super) fn double(&self) -> Fq {
        self.add(self)
    }

    /// `self^exp` for a public exponent.
    fn pow(&self, exp: &Limbs) -> Fq {
        let mut acc = Fq::ONE;
        for i in (0..256).rev() {
            acc = acc.square();
            if (exp[i / 64] >> (i % 64)) & 1 == 1 {
                acc = acc.mul(self);
            }
        }
        acc
    }

    /// The inverse, or zero for zero.
    pub(super) fn invert(&self) -> Fq {
        const Q_MINUS_2: Limbs = [Q[0] - 2, Q[1], Q[2], Q[3]];
        self.pow(&Q_MINUS_2)
    }

    fn select(mask: u64, a: &Fq, b: &Fq) -> Fq {
        Fq(limbs_select(mask, &a.0, &b.0))
    }

    fn is_odd(&self) -> bool {
        self.to_bytes()[0] & 1 == 1
    }

    /// Fixed-schedule Tonelli-Shanks for `q - 1 = 2^32 * t`.
    fn sqrt(&self) -> Option<Fq> {
        let w = self.pow(&T_MINUS_1_OVER_2);
        let mut x = self.mul(&w);
        let mut b = x.mul(&w);
        let mut c = ROOT_OF_UNITY;
        let minus_one = Fq::ONE.neg();
        for r in (2..=32).rev() {
            let mut d = b;
            for _ in 0..r - 2 {
                d = d.square();
            }
            let take = core::hint::black_box(0u64.wrapping_sub((d == minus_one) as u64));
            let c2 = c.square();
            x = Fq::select(take, &x.mul(&c), &x);
            b = Fq::select(take, &b.mul(&c2), &b);
            c = c2;
        }
        (x.square() == *self).then_some(x)
    }
}

/// `(t - 1) / 2` for `q - 1 = 2^32 * t`.
const T_MINUS_1_OVER_2: Limbs = [
    0x7fff_2dff_7fff_ffff,
    0x04d0_ec02_a9de_d201,
    0x94ce_bea4_199c_ec04,
    0x0000_0000_39f6_d3a9,
];

/// An element of order `2^32` (the constant of `zcash_test_vectors` `sapling/jubjub.py`).
const ROOT_OF_UNITY: Fq = Fq::from_raw([
    0x3829_971f_439f_0d2b,
    0xb636_8350_8c22_80b9,
    0xd09b_6819_22c8_13b4,
    0x16a2_a19e_dfe8_1f20,
]);

/// `d_J = -10240 / 10241`.
pub(super) const JUBJUB_D: Fq = Fq::from_raw([
    0x0106_5fd6_d634_3eb1,
    0x292d_7f6d_3757_9d26,
    0xf5fd_9207_e6bd_7fd4,
    0x2a93_18e7_4bfa_2b48,
]);
const JUBJUB_2D: Fq = Fq(add_mod(&JUBJUB_D.0, &JUBJUB_D.0, &Q));

/// A point of Jubjub, `-u^2 + v^2 = 1 + d u^2 v^2`, in extended coordinates
/// `(U : V : Z : T)` with `u = U/Z`, `v = V/Z`, `T = UV/Z`.
#[derive(Clone, Copy)]
pub(super) struct Point {
    u: Fq,
    v: Fq,
    z: Fq,
    t: Fq,
}

impl Point {
    pub(super) const IDENTITY: Point = Point {
        u: Fq::ZERO,
        v: Fq::ONE,
        z: Fq::ONE,
        t: Fq::ZERO,
    };

    /// The complete twisted Edwards addition law for `a = -1` (Hisil, Wong, Carter,
    /// Dawson 2008, section 3.1). It has no exceptional case on Jubjub because `a` is a
    /// square and `d` is not.
    pub(super) fn add(&self, rhs: &Point) -> Point {
        let a = self.v.sub(&self.u).mul(&rhs.v.sub(&rhs.u));
        let b = self.v.add(&self.u).mul(&rhs.v.add(&rhs.u));
        let c = self.t.mul(&JUBJUB_2D).mul(&rhs.t);
        let d = self.z.mul(&rhs.z).double();
        let e = b.sub(&a);
        let f = d.sub(&c);
        let g = d.add(&c);
        let h = b.add(&a);
        Point {
            u: e.mul(&f),
            v: g.mul(&h),
            z: f.mul(&g),
            t: e.mul(&h),
        }
    }

    pub(super) fn double(&self) -> Point {
        self.add(self)
    }

    fn select(mask: u64, a: &Point, b: &Point) -> Point {
        Point {
            u: Fq::select(mask, &a.u, &b.u),
            v: Fq::select(mask, &a.v, &b.v),
            z: Fq::select(mask, &a.z, &b.z),
            t: Fq::select(mask, &a.t, &b.t),
        }
    }

    /// `[scalar] self` for a 256-bit little-endian scalar: 256 doublings and 256
    /// additions whatever the scalar.
    pub(super) fn mul(&self, scalar: &[u8; 32]) -> Point {
        let mut acc = Point::IDENTITY;
        for i in (0..256).rev() {
            acc = acc.double();
            let sum = acc.add(self);
            let bit = u64::from((scalar[i / 8] >> (i % 8)) & 1);
            acc = Point::select(bit.wrapping_neg(), &sum, &acc);
        }
        acc
    }

    fn mul_by_cofactor(&self) -> Point {
        self.double().double().double()
    }

    fn is_identity(&self) -> bool {
        self.u == Fq::ZERO && self.v == self.z
    }

    /// The affine coordinates `(u, v)`.
    pub(super) fn to_affine(self) -> (Fq, Fq) {
        let zinv = self.z.invert();
        (self.u.mul(&zinv), self.v.mul(&zinv))
    }

    /// The affine coordinates of many points, with one inversion.
    pub(super) fn batch_to_affine(points: &[Point]) -> alloc::vec::Vec<(Fq, Fq)> {
        // prefix[i] = z_0 .. z_(i-1); no z is zero.
        let mut prefix = alloc::vec::Vec::with_capacity(points.len());
        let mut acc = Fq::ONE;
        for p in points {
            prefix.push(acc);
            acc = acc.mul(&p.z);
        }
        let mut inv = acc.invert();
        let mut out = alloc::vec![(Fq::ZERO, Fq::ZERO); points.len()];
        for (i, p) in points.iter().enumerate().rev() {
            let zinv = inv.mul(&prefix[i]);
            inv = inv.mul(&p.z);
            out[i] = (p.u.mul(&zinv), p.v.mul(&zinv));
        }
        out
    }

    /// `repr_J`.
    pub(super) fn to_bytes(self) -> [u8; 32] {
        let zinv = self.z.invert();
        let u = self.u.mul(&zinv);
        let v = self.v.mul(&zinv);
        let mut out = v.to_bytes();
        out[31] |= u8::from(u.is_odd()) << 7;
        out
    }

    /// `abst_J` as the current specification defines it: the two encodings with `u = 0`
    /// and the sign bit set are accepted.
    pub(super) fn from_bytes(bytes: &[u8; 32]) -> Option<Point> {
        let sign = bytes[31] >> 7 == 1;
        let mut v_bytes = *bytes;
        v_bytes[31] &= 0x7f;
        let v = Fq::from_bytes(&v_bytes)?;
        let v2 = v.square();
        // u^2 = (1 - v^2) / (a - d v^2) = (v^2 - 1) / (1 + d v^2); the denominator is
        // never zero because -1/d is not a square.
        let num = v2.sub(&Fq::ONE);
        let den = Fq::ONE.add(&JUBJUB_D.mul(&v2));
        let root = num.mul(&den.invert()).sqrt()?;
        let flip = core::hint::black_box(0u64.wrapping_sub((root.is_odd() ^ sign) as u64));
        let u = Fq::select(flip, &root.neg(), &root);
        Some(Point {
            u,
            v,
            z: Fq::ONE,
            t: u.mul(&v),
        })
    }
}

fn wipe(buf: &mut [u8]) {
    qsag_asm::volatile_fill(buf, 0);
}

// ---------------------------------------------------------------------------------------
// Scalars modulo r_J, as 32-byte little-endian integers.
// ---------------------------------------------------------------------------------------

/// `ToScalar^Sapling`: `LEOS2IP_512(wide) mod r_J`.
pub fn to_scalar(wide: &[u8; 64]) -> [u8; 32] {
    let mut acc = [0u64; 4];
    for i in (0..512).rev() {
        // `acc < r_J < 2^252`, so the shift cannot overflow and `2 acc + 1 < 2 r_J`.
        let bit = u64::from((wide[i / 8] >> (i % 8)) & 1);
        acc = [
            (acc[0] << 1) | bit,
            (acc[1] << 1) | (acc[0] >> 63),
            (acc[2] << 1) | (acc[1] >> 63),
            (acc[3] << 1) | (acc[2] >> 63),
        ];
        acc = reduce_once(&acc, 0, &R_J);
    }
    let bytes = limbs_to_bytes(&acc);
    qsag_asm::volatile_fill(&mut acc, 0);
    bytes
}

/// `(a + b) mod r_J` for `a, b < r_J`.
fn scalar_add(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    limbs_to_bytes(&add_mod(&limbs_from_bytes(a), &limbs_from_bytes(b), &R_J))
}

fn is_zero(bytes: &[u8; 32]) -> bool {
    bytes.iter().fold(0u8, |acc, b| acc | b) == 0
}

// ---------------------------------------------------------------------------------------
// Jubjub on byte encodings, group hash, generators.
// ---------------------------------------------------------------------------------------

/// `repr_J` of the zero point.
pub const JUBJUB_IDENTITY: [u8; 32] = {
    let mut out = [0u8; 32];
    out[0] = 1;
    out
};

/// `[scalar] P` for `P = abst_J(point)` and a 256-bit little-endian scalar; `None` if
/// `point` does not decode.
pub fn jubjub_scalar_mul(scalar: &[u8; 32], point: &[u8; 32]) -> Option<[u8; 32]> {
    Some(Point::from_bytes(point)?.mul(scalar).to_bytes())
}

/// `P + Q` on encodings; `None` if either does not decode.
pub fn jubjub_add(p: &[u8; 32], q: &[u8; 32]) -> Option<[u8; 32]> {
    Some(Point::from_bytes(p)?.add(&Point::from_bytes(q)?).to_bytes())
}

/// Whether `point` decodes to a point of the prime-order subgroup other than the zero
/// point (`J^(r)*`).
pub fn jubjub_is_prime_order(point: &[u8; 32]) -> bool {
    Point::from_bytes(point)
        .is_some_and(|p| !p.is_identity() && p.mul(&limbs_to_bytes(&R_J)).is_identity())
}

/// The uniform random string of the group hash (specification section 5.9).
pub const GROUP_HASH_URS: &[u8; 64] =
    b"096b36a5804bfacef1691e173c366a47ff5ba84a44f26ddd7e8d9f79d5b42df0";

pub(super) fn group_hash_point(personal: &[u8; 8], message: &[u8]) -> Option<Point> {
    let digest = blake2s_256(personal, &[GROUP_HASH_URS, message]);
    let q = Point::from_bytes(&digest)?.mul_by_cofactor();
    (!q.is_identity()).then_some(q)
}

/// `GroupHash^J(D, M)` (specification section 5.4.9.5): BLAKE2s-256 with personalization
/// `D` over `URS || M`, decoded as a point and multiplied by the cofactor; `None` if the
/// digest does not decode or the result is the zero point.
pub fn jubjub_group_hash(personal: &[u8; 8], message: &[u8]) -> Option<[u8; 32]> {
    group_hash_point(personal, message).map(Point::to_bytes)
}

fn find_group_hash_point(personal: &[u8; 8], message: &[u8]) -> Point {
    let mut input = alloc::vec::Vec::with_capacity(message.len() + 1);
    input.extend_from_slice(message);
    input.push(0);
    for i in 0..=255u8 {
        *input.last_mut().expect("non-empty") = i;
        if let Some(p) = group_hash_point(personal, &input) {
            return p;
        }
    }
    // Each try fails with probability about 1/2.
    unreachable!("no group hash among 256 counters")
}

/// `FindGroupHash^J(D, M)`: the first `GroupHash^J(D, M || [i])` that is defined.
pub fn jubjub_find_group_hash(personal: &[u8; 8], message: &[u8]) -> [u8; 32] {
    find_group_hash_point(personal, message).to_bytes()
}

pub(super) fn spend_auth_point() -> Point {
    find_group_hash_point(b"Zcash_G_", b"")
}

pub(super) fn proof_generation_point() -> Point {
    find_group_hash_point(b"Zcash_H_", b"")
}

/// `G^Sapling = FindGroupHash^J("Zcash_G_", "")`, the `SpendAuthSig` base.
pub fn spend_auth_base() -> [u8; 32] {
    spend_auth_point().to_bytes()
}

/// `H^Sapling = FindGroupHash^J("Zcash_H_", "")`, the proof generation key base.
pub fn proof_generation_base() -> [u8; 32] {
    proof_generation_point().to_bytes()
}

// ---------------------------------------------------------------------------------------
// Key components (specification section 4.2.2).
// ---------------------------------------------------------------------------------------

/// `PRF^expand(sk, t) = BLAKE2b-512("Zcash_ExpandSeed", sk || t)`, with `t` given in
/// parts.
pub fn prf_expand(sk: &[u8], t: &[&[u8]]) -> [u8; 64] {
    let mut state = Blake2b::new(64, b"Zcash_ExpandSeed");
    state.update(sk);
    for part in t {
        state.update(part);
    }
    state.finalize()
}

fn prf_expand_scalar(sk: &[u8], t: &[&[u8]]) -> [u8; 32] {
    let mut wide = prf_expand(sk, t);
    let scalar = to_scalar(&wide);
    wipe(&mut wide);
    scalar
}

fn prf_expand_32(sk: &[u8], t: &[&[u8]]) -> [u8; 32] {
    let mut wide = prf_expand(sk, t);
    let out: [u8; 32] = wide[..32].try_into().expect("32 bytes");
    wipe(&mut wide);
    out
}

/// A Sapling expanded spending key `(ask, nsk, ovk)`. Erased on drop.
#[derive(Clone)]
pub struct SaplingExpandedSpendingKey {
    pub ask: [u8; 32],
    pub nsk: [u8; 32],
    pub ovk: [u8; 32],
}

impl Drop for SaplingExpandedSpendingKey {
    fn drop(&mut self) {
        wipe(&mut self.ask);
        wipe(&mut self.nsk);
        wipe(&mut self.ovk);
    }
}

/// A Sapling full viewing key `(ak, nk, ovk)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaplingFullViewingKey {
    pub ak: [u8; 32],
    pub nk: [u8; 32],
    pub ovk: [u8; 32],
}

/// `ask = ToScalar(PRF^expand(sk, [0]))`, `nsk = ToScalar(PRF^expand(sk, [1]))`,
/// `ovk = truncate_32(PRF^expand(sk, [2]))`.
pub fn expand_spending_key(sk: &[u8; 32]) -> SaplingExpandedSpendingKey {
    SaplingExpandedSpendingKey {
        ask: prf_expand_scalar(sk, &[&[0x00]]),
        nsk: prf_expand_scalar(sk, &[&[0x01]]),
        ovk: prf_expand_32(sk, &[&[0x02]]),
    }
}

/// `ak = [ask] G^Sapling`.
pub fn derive_ak(ask: &[u8; 32]) -> [u8; 32] {
    spend_auth_point().mul(ask).to_bytes()
}

/// `nk = [nsk] H^Sapling`.
pub fn derive_nk(nsk: &[u8; 32]) -> [u8; 32] {
    proof_generation_point().mul(nsk).to_bytes()
}

impl SaplingExpandedSpendingKey {
    /// The full viewing key `(ak, nk, ovk)`.
    pub fn full_viewing_key(&self) -> SaplingFullViewingKey {
        SaplingFullViewingKey {
            ak: derive_ak(&self.ask),
            nk: derive_nk(&self.nsk),
            ovk: self.ovk,
        }
    }
}

/// `ivk = CRH^ivk(ak, nk)`: BLAKE2s-256("Zcashivk", ak || nk) with the top five bits
/// cleared.
pub fn crh_ivk(ak: &[u8; 32], nk: &[u8; 32]) -> [u8; 32] {
    let mut ivk = blake2s_256(b"Zcashivk", &[ak, nk]);
    ivk[31] &= 0x07;
    ivk
}

impl SaplingFullViewingKey {
    /// The incoming viewing key.
    pub fn ivk(&self) -> [u8; 32] {
        crh_ivk(&self.ak, &self.nk)
    }
}

/// `g_d = DiversifyHash^Sapling(d) = GroupHash^J("Zcash_gd", d)`; `None` for an invalid
/// diversifier.
pub fn diversify_hash(d: &[u8; 11]) -> Option<[u8; 32]> {
    jubjub_group_hash(b"Zcash_gd", d)
}

/// The default diversifier of a spending key that is not an extended key: the first
/// `truncate_11(PRF^expand(sk, [3, i]))` with a defined `DiversifyHash`.
pub fn default_diversifier(sk: &[u8; 32]) -> [u8; 11] {
    for i in 0..=255u8 {
        let mut wide = prf_expand(sk, &[&[0x03, i]]);
        let d: [u8; 11] = wide[..11].try_into().expect("11 bytes");
        wipe(&mut wide);
        if group_hash_point(b"Zcash_gd", &d).is_some() {
            return d;
        }
    }
    unreachable!("no valid diversifier among 256 counters")
}

/// `pk_d = [ivk] g_d`; `None` for an invalid diversifier.
pub fn derive_pk_d(ivk: &[u8; 32], d: &[u8; 11]) -> Option<[u8; 32]> {
    Some(group_hash_point(b"Zcash_gd", d)?.mul(ivk).to_bytes())
}

/// The raw payment address `d || pk_d`; `None` for an invalid diversifier.
pub fn payment_address(ivk: &[u8; 32], d: &[u8; 11]) -> Option<[u8; 43]> {
    let pk_d = derive_pk_d(ivk, d)?;
    let mut out = [0u8; 43];
    out[..11].copy_from_slice(d);
    out[11..].copy_from_slice(&pk_d);
    Some(out)
}

// ---------------------------------------------------------------------------------------
// ZIP 32.
// ---------------------------------------------------------------------------------------

/// The first hardened child index.
pub const ZIP32_HARDENED: u32 = 0x8000_0000;

/// A Sapling extended spending key. Erased on drop.
#[derive(Clone)]
pub struct SaplingExtendedSpendingKey {
    pub depth: u8,
    pub parent_tag: [u8; 4],
    pub child_index: u32,
    pub chain_code: [u8; 32],
    pub ask: [u8; 32],
    pub nsk: [u8; 32],
    pub ovk: [u8; 32],
    pub dk: [u8; 32],
}

impl Drop for SaplingExtendedSpendingKey {
    fn drop(&mut self) {
        wipe(&mut self.chain_code);
        wipe(&mut self.ask);
        wipe(&mut self.nsk);
        wipe(&mut self.ovk);
        wipe(&mut self.dk);
    }
}

/// A Sapling extended full viewing key.
#[derive(Clone, Debug, PartialEq, Eq)]
