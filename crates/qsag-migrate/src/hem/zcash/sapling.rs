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
pub struct SaplingExtendedFullViewingKey {
    pub depth: u8,
    pub parent_tag: [u8; 4],
    pub child_index: u32,
    pub chain_code: [u8; 32],
    pub ak: [u8; 32],
    pub nk: [u8; 32],
    pub ovk: [u8; 32],
    pub dk: [u8; 32],
}

fn extended_key_bytes(
    depth: u8,
    parent_tag: &[u8; 4],
    child_index: u32,
    chain_code: &[u8; 32],
    parts: [&[u8; 32]; 4],
) -> [u8; 169] {
    let mut out = [0u8; 169];
    out[0] = depth;
    out[1..5].copy_from_slice(parent_tag);
    out[5..9].copy_from_slice(&child_index.to_le_bytes());
    out[9..41].copy_from_slice(chain_code);
    for (chunk, part) in out[41..].chunks_exact_mut(32).zip(parts) {
        chunk.copy_from_slice(part);
    }
    out
}

/// The parts of ZIP 32 child derivation that the spending and viewing sides share.
struct ChildParts {
    i_ask: [u8; 32],
    i_nsk: [u8; 32],
    ovk: [u8; 32],
    dk: [u8; 32],
    chain_code: [u8; 32],
}

impl Drop for ChildParts {
    fn drop(&mut self) {
        for field in [&mut self.i_ask, &mut self.i_nsk, &mut self.ovk, &mut self.dk, &mut self.chain_code] {
            wipe(field);
        }
    }
}

/// Splits and expands `I`, then erases it.
fn child_parts(i: &mut [u8; 64], ovk_par: &[u8; 32], dk_par: &[u8; 32]) -> ChildParts {
    let (i_l, i_r) = i.split_at(32);
    let parts = ChildParts {
        i_ask: prf_expand_scalar(i_l, &[&[0x13]]),
        i_nsk: prf_expand_scalar(i_l, &[&[0x14]]),
        ovk: prf_expand_32(i_l, &[&[0x15], ovk_par]),
        dk: prf_expand_32(i_l, &[&[0x16], dk_par]),
        chain_code: i_r.try_into().expect("32 bytes"),
    };
    wipe(i);
    parts
}

/// The parts of ZIP 32 internal key derivation: `(I_nsk, dk_internal, ovk_internal)`.
fn internal_parts(
    ak: &[u8; 32],
    nk: &[u8; 32],
    ovk: &[u8; 32],
    dk: &[u8; 32],
) -> ([u8; 32], [u8; 32], [u8; 32]) {
    let mut i = blake2b_256(b"Zcash_SaplingInt", &[ak, nk, ovk, dk]);
    let i_nsk = prf_expand_scalar(&i, &[&[0x17]]);
    let mut r = prf_expand(&i, &[&[0x18]]);
    let dk_internal: [u8; 32] = r[..32].try_into().expect("32 bytes");
    let ovk_internal: [u8; 32] = r[32..].try_into().expect("32 bytes");
    wipe(&mut i);
    wipe(&mut r);
    (i_nsk, dk_internal, ovk_internal)
}

impl SaplingExtendedSpendingKey {
    /// The master extended spending key of a seed of 32 to 252 bytes (ZIP 32, "Sapling
    /// master key generation"). `None` for a seed of another length, or if `ask` or
    /// `ivk` is zero.
    pub fn master(seed: &[u8]) -> Option<Self> {
        if !(32..=252).contains(&seed.len()) {
            return None;
        }
        let mut state = Blake2b::new(64, b"ZcashIP32Sapling");
        state.update(seed);
        let mut i = state.finalize();
        let (sk_m, c_m) = i.split_at(32);
        let key = Self {
            depth: 0,
            parent_tag: [0; 4],
            child_index: 0,
            chain_code: c_m.try_into().expect("32 bytes"),
            ask: prf_expand_scalar(sk_m, &[&[0x00]]),
            nsk: prf_expand_scalar(sk_m, &[&[0x01]]),
            ovk: prf_expand_32(sk_m, &[&[0x02]]),
            dk: prf_expand_32(sk_m, &[&[0x10]]),
        };
        wipe(&mut i);
        key.checked()
    }

    /// The validity conditions of ZIP 32: `ask` and `ivk` are not zero.
    fn checked(self) -> Option<Self> {
        let valid = !is_zero(&self.ask) && !is_zero(&self.to_extended_fvk().ivk());
        valid.then_some(self)
    }

    /// `CKDsk`: the child at index `i`, hardened if `i >= 2^31`. `None` if the child is
    /// invalid.
    pub fn child(&self, i: u32) -> Option<Self> {
        let fvk = self.to_extended_fvk();
        let index = i.to_le_bytes();
        let depth = self.depth.checked_add(1)?;
        let mut wide = if i >= ZIP32_HARDENED {
            prf_expand(
                &self.chain_code,
                &[&[0x11], &self.ask, &self.nsk, &self.ovk, &self.dk, &index],
            )
        } else {
            prf_expand(
                &self.chain_code,
                &[&[0x12], &fvk.ak, &fvk.nk, &fvk.ovk, &fvk.dk, &index],
            )
        };
        let mut parts = child_parts(&mut wide, &self.ovk, &self.dk);
        let child = Self {
            depth,
            parent_tag: fvk.tag(),
            child_index: i,
            chain_code: parts.chain_code,
            ask: scalar_add(&parts.i_ask, &self.ask),
            nsk: scalar_add(&parts.i_nsk, &self.nsk),
            ovk: parts.ovk,
            dk: parts.dk,
        };
        wipe(&mut parts.i_ask);
        wipe(&mut parts.i_nsk);
        wipe(&mut parts.chain_code);
        child.checked()
    }

    /// The key at `path` below the master key of `seed`.
    pub fn derive(seed: &[u8], path: &[u32]) -> Option<Self> {
        let mut key = Self::master(seed)?;
        for &i in path {
            key = key.child(i)?;
        }
        Some(key)
    }

    /// The internal (change) extended spending key of this external key.
    pub fn internal(&self) -> Self {
        let fvk = self.to_extended_fvk();
        let (mut i_nsk, dk, ovk) = internal_parts(&fvk.ak, &fvk.nk, &fvk.ovk, &fvk.dk);
        let key = Self {
            depth: self.depth,
            parent_tag: self.parent_tag,
            child_index: self.child_index,
            chain_code: self.chain_code,
            ask: self.ask,
            nsk: scalar_add(&i_nsk, &self.nsk),
            ovk,
            dk,
        };
        wipe(&mut i_nsk);
        key
    }

    /// The extended full viewing key.
    pub fn to_extended_fvk(&self) -> SaplingExtendedFullViewingKey {
        SaplingExtendedFullViewingKey {
            depth: self.depth,
            parent_tag: self.parent_tag,
            child_index: self.child_index,
            chain_code: self.chain_code,
            ak: derive_ak(&self.ask),
            nk: derive_nk(&self.nsk),
            ovk: self.ovk,
            dk: self.dk,
        }
    }

    /// The 169-byte encoding `depth || parent tag || index || c || ask || nsk || ovk || dk`.
    pub fn to_bytes(&self) -> [u8; 169] {
        extended_key_bytes(
            self.depth,
            &self.parent_tag,
            self.child_index,
            &self.chain_code,
            [&self.ask, &self.nsk, &self.ovk, &self.dk],
        )
    }
}

/// The 88-bit diversifier index after `index`, little-endian; `None` after the last.
fn next_diversifier_index(index: &[u8; 11]) -> Option<[u8; 11]> {
    let mut out = *index;
    for byte in out.iter_mut() {
        *byte = byte.wrapping_add(1);
        if *byte != 0 {
            return Some(out);
        }
    }
    None
}

impl SaplingExtendedFullViewingKey {
    /// The incoming viewing key.
    pub fn ivk(&self) -> [u8; 32] {
        crh_ivk(&self.ak, &self.nk)
    }

    /// The full viewing key fingerprint, BLAKE2b-256("ZcashSaplingFVFP", ak || nk || ovk).
    pub fn fingerprint(&self) -> [u8; 32] {
        blake2b_256(b"ZcashSaplingFVFP", &[&self.ak, &self.nk, &self.ovk])
    }

    /// The first four bytes of the fingerprint.
    pub fn tag(&self) -> [u8; 4] {
        let fp = self.fingerprint();
        [fp[0], fp[1], fp[2], fp[3]]
    }

    /// `CKDfvk`: the non-hardened child at index `i`. `None` for a hardened index, a
    /// parent whose `ak` or `nk` does not decode, or an invalid child.
    pub fn child(&self, i: u32) -> Option<Self> {
        if i >= ZIP32_HARDENED {
            return None;
        }
        let depth = self.depth.checked_add(1)?;
        let mut wide = prf_expand(
            &self.chain_code,
            &[
                &[0x12],
                &self.ak,
                &self.nk,
                &self.ovk,
                &self.dk,
                &i.to_le_bytes(),
            ],
        );
        let parts = child_parts(&mut wide, &self.ovk, &self.dk);
        let ak = spend_auth_point()
            .mul(&parts.i_ask)
            .add(&Point::from_bytes(&self.ak)?);
        let nk = proof_generation_point()
            .mul(&parts.i_nsk)
            .add(&Point::from_bytes(&self.nk)?);
        let child = Self {
            depth,
            parent_tag: self.tag(),
            child_index: i,
            chain_code: parts.chain_code,
            ak: ak.to_bytes(),
            nk: nk.to_bytes(),
            ovk: parts.ovk,
            dk: parts.dk,
        };
        let valid = !ak.is_identity() && !is_zero(&child.ivk());
        valid.then_some(child)
    }

    /// The internal (change) extended full viewing key of this external key. `None` if
    /// `nk` does not decode.
    pub fn internal(&self) -> Option<Self> {
        let (i_nsk, dk, ovk) = internal_parts(&self.ak, &self.nk, &self.ovk, &self.dk);
        let nk = proof_generation_point()
            .mul(&i_nsk)
            .add(&Point::from_bytes(&self.nk)?);
        Some(Self {
            nk: nk.to_bytes(),
            ovk,
            dk,
            ..self.clone()
        })
    }

    /// The 169-byte encoding `depth || parent tag || index || c || ak || nk || ovk || dk`.
    pub fn to_bytes(&self) -> [u8; 169] {
        extended_key_bytes(
            self.depth,
            &self.parent_tag,
            self.child_index,
            &self.chain_code,
            [&self.ak, &self.nk, &self.ovk, &self.dk],
        )
    }

    /// `d_j = FF1-AES256.Encrypt(dk, "", I2LEBSP_88(j))` for the little-endian index `j`,
    /// or `None` if `DiversifyHash^Sapling(d_j)` is undefined.
    pub fn diversifier(&self, index: &[u8; 11]) -> Option<[u8; 11]> {
        let d = ff1_aes256_encrypt_88(&self.dk, index);
        group_hash_point(b"Zcash_gd", &d).map(|_| d)
    }

    /// The first index at or after `start` with a valid diversifier, and that diversifier.
    pub fn find_diversifier(&self, start: &[u8; 11]) -> Option<([u8; 11], [u8; 11])> {
        let mut index = *start;
        loop {
            if let Some(d) = self.diversifier(&index) {
                return Some((index, d));
            }
            index = next_diversifier_index(&index)?;
        }
    }

    /// The default diversifier: the one at the least valid index.
    pub fn default_diversifier(&self) -> ([u8; 11], [u8; 11]) {
        self.find_diversifier(&[0; 11])
            .expect("about half of all indices are valid")
    }

    /// The raw payment address `d_j || pk_d` at index `j`; `None` if `d_j` is invalid.
    pub fn address(&self, index: &[u8; 11]) -> Option<[u8; 43]> {
        payment_address(&self.ivk(), &self.diversifier(index)?)
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use alloc::vec::Vec;

    pub(crate) fn hex(s: &str) -> Vec<u8> {
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
            .collect()
    }

    fn arr<const N: usize>(s: &str) -> [u8; N] {
        hex(s).try_into().unwrap()
    }

    fn opt<const N: usize>(s: &str) -> Option<[u8; N]> {
        (!s.is_empty()).then(|| arr(s))
    }

    fn fq(n: u64) -> Fq {
        Fq::from_raw([n, 0, 0, 0])
    }

    #[test]
    fn field_constants() {
        // d = -10240 / 10241.
        assert!(JUBJUB_D.mul(&fq(10241)) == fq(10240).neg());
        assert!(JUBJUB_2D == JUBJUB_D.double());
        // q - 1 = 2^32 * t, and the exponent constant is (t - 1) / 2.
        let (q_minus_1, _) = limbs_sub(&Q, &[1, 0, 0, 0]);
        let mut t = [0u64; 4];
        for i in 0..4 {
            let above = if i < 3 { q_minus_1[i + 1] << 32 } else { 0 };
            t[i] = (q_minus_1[i] >> 32) | above;
        }
        assert_eq!(q_minus_1[0] & 0xffff_ffff, 0);
        let (twice, carry) = limbs_add(&T_MINUS_1_OVER_2, &T_MINUS_1_OVER_2);
        assert_eq!((limbs_add(&twice, &[1, 0, 0, 0]).0, carry), (t, 0));
        // The root of unity has order exactly 2^32.
        let mut x = ROOT_OF_UNITY;
        for _ in 0..31 {
            x = x.square();
        }
        assert!(x == Fq::ONE.neg());
        assert!(x.square() == Fq::ONE);
        assert!(ROOT_OF_UNITY.sqrt().is_none());
        // Montgomery constants: 1 * 1 = 1 and to_bytes inverts from_bytes.
        assert!(Fq::ONE.mul(&Fq::ONE) == Fq::ONE);
        let mut one = [0u8; 32];
        one[0] = 1;
        assert_eq!(Fq::ONE.to_bytes(), one);
        assert!(Fq::from_bytes(&one) == Some(Fq::ONE));
        assert_eq!(Q[0].wrapping_mul(Q_INV), u64::MAX);
        // Inversion and the canonical range.
        let x = fq(0x1234_5678_9abc_def1).mul(&JUBJUB_D);
        assert!(x.mul(&x.invert()) == Fq::ONE);
        assert!(Fq::from_bytes(&limbs_to_bytes(&Q)).is_none());
        assert!(Fq::from_bytes(&limbs_to_bytes(&q_minus_1)) == Some(Fq::ONE.neg()));
        assert!(Fq::from_bytes(&[0xff; 32]).is_none());
    }

    #[test]
    fn field_square_roots() {
        for n in [0u64, 1, 4, 9, 1 << 40, 10241 * 10241] {
            let root = fq(n).sqrt().expect("a square");
            assert!(root.square() == fq(n));
        }
        let x = JUBJUB_D.add(&fq(77));
        assert!(x.square().sqrt().is_some_and(|r| r == x || r == x.neg()));
        // d is not a square (that is what makes the addition law complete).
        assert!(JUBJUB_D.sqrt().is_none());
        let mut non_squares = 0;
        for n in 2..40u64 {
            match fq(n).sqrt() {
                Some(r) => assert!(r.square() == fq(n)),
                None => non_squares += 1,
            }
        }
        assert!((10..30).contains(&non_squares));
    }

    #[test]
    fn to_scalar_reduces() {
        let mut wide = [0u8; 64];
        wide[..32].copy_from_slice(&limbs_to_bytes(&R_J));
        assert_eq!(to_scalar(&wide), [0; 32]);
        wide[0] += 5;
        let mut five = [0u8; 32];
        five[0] = 5;
        assert_eq!(to_scalar(&wide), five);
        // 2^256 mod r_J equals the sum of r_J - 1 and (2^256 mod r_J) + 1.
        let mut pow256 = [0u8; 64];
        pow256[32] = 1;
        let reduced = to_scalar(&pow256);
        let (r_minus_1, _) = limbs_sub(&R_J, &[1, 0, 0, 0]);
        let mut plus_one = [0u8; 64];
        plus_one[0] = 1;
        plus_one[32] = 1;
        assert_eq!(
            scalar_add(&limbs_to_bytes(&r_minus_1), &to_scalar(&plus_one)),
            reduced
        );
        assert_ne!(reduced, [0; 32]);
    }

    /// sapling_generators.json (its single vector): `skb, pkb, npb, wprb, vcvb, vcrb,
    /// pb0, pb1, pb2, pb3`.
    const GENERATORS: [&str; 10] = [
        "30b5f2aaad325630bcdddbce4d67656d05fd1cc2d037bb5375b6e96d9e01a1d7",
        "e7e85de0f7f97a46d249a1f5ea51df50cc48490f8401c9de7a2adf1807d1b6d4",
        "65002bc736faf7a3422effffe8b855e18fba96a0158a9efca584bf40549d36e1",
        "ac776c796563fcd44cc49cfaea8bb796952c266e47779d94574c10ad01754b11",
        "d7c86706f5817aa718cd1cfad03233bcd64a7789fd9422d3b17af6823a7e6ac6",
        "8b6a0b38b9faae3c3b803b47b0f146ad50ab221e6e2afbe6dbde45cba9d381ed",
        "ca3c2432d4abbf7732464ec08b2e47f95edc7e836b16c979571b52d3a2879ea8",
        "9118bf4e3cc50d7be8d3fa98ebbe3a1f25d901c0421189f733fe435b7f8c5d01",
        "57d493972c50ed8098b484177f2ab28b53e88c8e6ca400e09eee4ed200152eb6",
        "e97035a3ec4b7184856a1fa1a1af0351b747d9d8cb0a0791d8ca564b0ce47e2f",
    ];

    #[test]
    fn generators_match_official_vector() {
        let got = [
            spend_auth_base(),
            proof_generation_base(),
            jubjub_find_group_hash(b"Zcash_J_", b""),
            jubjub_find_group_hash(b"Zcash_PH", b"r"),
            jubjub_find_group_hash(b"Zcash_cv", b"v"),
            jubjub_find_group_hash(b"Zcash_cv", b"r"),
            jubjub_find_group_hash(b"Zcash_PH", &0u32.to_le_bytes()),
            jubjub_find_group_hash(b"Zcash_PH", &1u32.to_le_bytes()),
            jubjub_find_group_hash(b"Zcash_PH", &2u32.to_le_bytes()),
            jubjub_find_group_hash(b"Zcash_PH", &3u32.to_le_bytes()),
        ];
        for (got, want) in got.iter().zip(GENERATORS) {
            assert_eq!(got.to_vec(), hex(want));
            assert!(jubjub_is_prime_order(got));
        }
    }

    #[test]
    fn group_law() {
        let g = Point::from_bytes(&spend_auth_base()).unwrap();
        let h = Point::from_bytes(&proof_generation_base()).unwrap();
        assert_eq!(g.add(&h).to_bytes(), h.add(&g).to_bytes());
        assert_eq!(g.add(&Point::IDENTITY).to_bytes(), g.to_bytes());
        assert_eq!(Point::IDENTITY.to_bytes(), JUBJUB_IDENTITY);
        // [r_J] G is the zero point and [r_J - 1] G + G as well.
        let (r_minus_1, _) = limbs_sub(&R_J, &[1, 0, 0, 0]);
        assert!(g.mul(&limbs_to_bytes(&R_J)).is_identity());
        let neg_g = g.mul(&limbs_to_bytes(&r_minus_1));
        assert!(!neg_g.is_identity());
        assert!(neg_g.add(&g).is_identity());
        // [5] G by repeated addition, and [2] G by the scalar route.
        let mut five = [0u8; 32];
        five[0] = 5;
        let by_add = g.add(&g).add(&g).add(&g).add(&g);
        assert_eq!(g.mul(&five).to_bytes(), by_add.to_bytes());
        assert_eq!(
            jubjub_scalar_mul(&five, &spend_auth_base()),
            Some(by_add.to_bytes())
        );
        assert_eq!(
            jubjub_add(&spend_auth_base(), &proof_generation_base()),
            Some(g.add(&h).to_bytes())
        );
        assert_ne!(g.add(&h).to_bytes(), g.to_bytes());
    }

    #[test]
    fn point_decoding_rejects_and_accepts_as_specified() {
        // v = q is not canonical.
        assert!(Point::from_bytes(&limbs_to_bytes(&Q)).is_none());
        assert_eq!(jubjub_scalar_mul(&[1; 32], &limbs_to_bytes(&Q)), None);
        assert_eq!(jubjub_add(&JUBJUB_IDENTITY, &[0xff; 32]), None);
        // About half of all v have no u: count over small v.
        let mut off_curve = 0;
        for n in 2..40u8 {
            let mut bytes = [0u8; 32];
            bytes[0] = n;
            match Point::from_bytes(&bytes) {
                Some(p) => assert_eq!(p.to_bytes(), bytes),
                None => off_curve += 1,
            }
        }
        assert!((10..30).contains(&off_curve));
        // Section 5.4.9.3, note: the encoding 2^255 + 1 decodes to the zero point.
        let mut non_canonical = JUBJUB_IDENTITY;
        non_canonical[31] = 0x80;
        let p = Point::from_bytes(&non_canonical).unwrap();
        assert!(p.is_identity());
        assert_eq!(p.to_bytes(), JUBJUB_IDENTITY);
        // The zero point and the point of order two are not in J^(r)*.
        assert!(!jubjub_is_prime_order(&JUBJUB_IDENTITY));
        let (q_minus_1, _) = limbs_sub(&Q, &[1, 0, 0, 0]);
        let order_two = limbs_to_bytes(&q_minus_1);
        assert!(Point::from_bytes(&order_two).is_some());
        assert!(!jubjub_is_prime_order(&order_two));
        assert!(jubjub_is_prime_order(&spend_auth_base()));
        // A sign flip gives the negated point.
        let mut flipped = spend_auth_base();
        flipped[31] ^= 0x80;
        assert_eq!(
            jubjub_add(&flipped, &spend_auth_base()),
            Some(JUBJUB_IDENTITY)
        );
    }

    #[test]
    fn diversify_hash_rejects_invalid_diversifier() {
        // `zcash_keys` 0.17.0 `src/encoding.rs`, test `invalid_diversifier`.
        assert_eq!(diversify_hash(&[1; 11]), None);
        assert_eq!(derive_pk_d(&[1; 32], &[1; 11]), None);
        assert_eq!(payment_address(&[1; 32], &[1; 11]), None);
    }

    /// sapling_key_components.json, all ten vectors: `sk, ask, nsk, ovk, ak, nk, ivk,
    /// default_d, default_pk_d`.
    pub(crate) const KEY_COMPONENTS: [[&str; 9]; 10] = [
        [
            "0000000000000000000000000000000000000000000000000000000000000000",
            "8548a14a473ea547aa2378402044f818cf1911cf5dd2054f678345f00d0e8806",
            "30114ea0dd0bb61cf0eaeab6ec3331f581b0425e27338501262d7eac745e6e05",
            "98d16913d99b04177caba44f6e4d224e03b5ac031d7ce45e865138e1b996d63b",
            "f344ec380fe1273e3098c2588c5d3a791fd7ba958032760777fd0efa8ef11620",
            "f7cf9e77f2e58683383c1519ac7b062d30040e27a725fb88fb19a978bd3fd6ba",
            "b70b7cd0ed03cbdfd7ada9502ee245b13e569d54a5719d2daa0f5f1451479204",
            "f19d9b797e39f337445839",
            "db4cd2b0aac4f7eb8ca131f16567c445a9555126d3c29f14e3d776e841ae7415",
        ],
        [
            "0101010101010101010101010101010101010101010101010101010101010101",
            "c9435629bf8bffe55e7335ec077718ba60ba28d7ac3794b74f512c31af0a5304",
            "11acc2ead07b5f008c1f0f090cc8ddf335236ff4b253c6495695e9d639dacd08",
            "3b946210ce6d1b1692d7392ac84a8bc8f03b72723c7d36721b809a79c9d6e45b",
            "82ff5effc527ae84020bf2d35201c10219131947ff4b96f881a45f2e8ae30518",
            "c4534d848bb918cf4a7f8b98740ab3ccee586795ff4df64547a8888a6c7415d2",
            "c518384466b26988b5109067418d192d9d6bd0d9232205d77418c240fc68a406",
            "aef180f6e34e354b888f81",
            "a6b13ea336ddb7a67bb09a0e68e9d3cfb39210831ea3a296ba09a922060fd38b",
        ],
        [
            "0202020202020202020202020202020202020202020202020202020202020202",
            "ee1c3d7efe0a78063d6af3d9d81212af47b7c1b761f85ccb066fc11a6a421703",
            "1d3b713755d74875e8ea38fd166e76c62a4250216e6bbfe48a5e2eabad117f0b",
            "8bf4390e28ddc95b8302c381d5810b84ba8e6096e5a76822774fd49f491e8f49",
            "ab83574eb5de859a0ab8629dec34c7bee8c3fc74dfa0b19a3a7468d15dca64c6",
            "95d58053e0592e4a169cc0b7928aaac3de24ef1531aa9eb6f4ab93914da8a06e",
            "471c24a3dc8730e75036c0a95f3e2f7dd1be6fb93ad29592203def3041954505",
            "7599f0bf9b57cd2dc299b6",
            "66141739514b28f05def8a18eeee5eed4d44c6225c3c65d88dd9907708012f5a",
        ],
        [
            "0303030303030303030303030303030303030303030303030303030303030303",
            "00c3a1e1ca8f4e0480ee1ee90ca7517879d3fc5c815c0903e5eebc94bb809503",
            "e66285a5e9b65e157ad2fcd543dad98c67a58abdf287e05506bd1c2e59b0720b",
            "147678e0553b97829347647c5bc7dab4cc2202b54ec29fd31a3de6be0825fc5e",
            "3c9cde7e5d0d38a8610faadbcf4c343f5d3cfa3155a5b94661a6753e96e884ea",
            "b77d36f508941dbd61cfd0f159ee05cfaa78a26c9492903806d83b598d3c1c2a",
            "636aa964bfc23ce4b1fcf7dfc99179ddc406ff55400c9295acfc14f031c72600",
            "1b81614f1dadea0f8d0a58",
            "25eb55fccf761fc64e85a588efe6ead7832fb1f0f7a83165895bdff942925f5c",
        ],
        [
            "0404040404040404040404040404040404040404040404040404040404040404",
            "8236d19d3205d85543a06811343f827b6563770a49aa4d0ca0081805d4c8ea0d",
            "7ec1ef0bed82718272f0f44f017c484174513d661dd168af02d2092a1d8a0507",
            "1b6e75ece3ace8dba6a5410d9ad4755668e4b39585d635ec1da7c8dcfd5fc4ed",
            "55e88389bb7e41de130cfa51a8715fde01ff9c6876647f0175ad34f058dde01a",
            "725d4ad6a15021cd1c48c5ee19de6c1e768a2cc0a9a730a01bb21c95e3d9e43c",
            "67fa2bf7c67d4658243c317c0cb41fd32064dfd3709fe0dcb724f14bb01a1d04",
            "fcfb68a40d4bc6a04b09c4",
            "8b2a337f03622c24ff381d4c546f6977f90522e92fde44c9d1bb099714b9db2b",
        ],
        [
            "0505050505050505050505050505050505050505050505050505050505050505",
            "eae6884d764a054061a8f1c0076c624dcb738789f7ad1e7408e31f24dfc82607",
            "fbe610f42a41749f9b6e6e4a54b5a32ebfe8f43800881ba6cd13ed0b05294601",
            "c6bc1f39f0d786314cb20bf9ab228540913555f970696b6d7c77bb332328372a",
            "e682765914e3864c339e5782b855c0fdf40e0dfcedb9e7b47bc94b90b3a4c988",
            "82256b95623c67024b4424d91400a370e7ac8e4d15482a3759e00d219749daee",
            "ea3f1d80e4307ca73b9f37801f91fba810cc41d279fc29f564235654a2178e03",
            "eb519882ad1e5cc654cd59",
            "6b27daccb5a8207f532d10ca238f9786648a11b5966e51a2f7d89e15d29b8fdf",
        ],
        [
            "0606060606060606060606060606060606060606060606060606060606060606",
            "e8f816b4bc08a7e566750cc28afe82a4cea9c2bef244fa4b13c4739b28074c0d",
            "32615b137f2801ed446e48781ab0634572e18cfb0693721b8803c05b8227d107",
            "f62c05e848a873ef885e12b08c5e7ca2f32424bacc754cb69750444d355f5106",
            "ff27db0751945d3ee4be9cf15c2ea211b24b164d5f2d7ddff5e4a0708f10b95e",
            "943885959d4ef8a9cfca07c457f09ec74b96f993d8e0fa32b19c03e3b07a420f",
            "b5c5894943956933c0e5c12d311fc12cba58354b5c389edc03da55084f74c205",
            "bebb0fb46b8aaff89040f6",
            "d11da01f0b43bdd5288d32385b8771d223493c69802544043f77cf1d71c1cb8c",
        ],
        [
            "0707070707070707070707070707070707070707070707070707070707070707",
            "74b44a37f15023c060427e1daea3f64312dd8feb7b2cedf0dd5544493f872c06",
            "075c35db8b1b25754223ecee34ab730dddd1f14a6a54f4c6f468453c3c6ed60b",
            "e9e0dc1ed311daed64bd74da5d94fe88a6ea414b7312de3d2a78f64632bbe373",
            "283f9aafa9bcb3e6ce17e63212634cb3ee550c476b676bd356a6df8adf51d25e",
            "dc4c67b10d4b0a218dc6e1487066740a409317866c32e664b50e397aa80389d4",
            "8716c82880e13683e1bb059dd06c80c90134a96d5afca8aac2bbf68bb05f8402",
            "ad6e2e185a3100e3a6a8b3",
            "32cb2806b882f1368b0d4a898f72c4c8f728132cc12456946e7f4cb0fb058da9",
        ],
        [
            "0808080808080808080808080808080808080808080808080808080808080808",
            "039dd93df311ff8fbab3fe230219cd42ac879484f30b903a3c1e67ccca5a7b0d",
            "049fa14f486c75b9fad7e3b673a443dd074eaa96edcb2a53eaaabdaf70ffbb08",
            "147dd11d77eba1b1636fd6190c62b9a5d0481bee7e917fab02e21858063ab504",
            "364048eedbe8ca205eb7e7ba0a9012166c7c7bd9eb228e08481448c488aa21d2",
            "ed60af1ce7df38070d3851432a96480db0b417c3682a1d68e3e89334235c0bdf",
            "99c9b4b84f4b4e350f787d1cf7051d50ecc34b1a5b20d2d2139b4af1f160e001",
            "21c90e1c658b3efe86af58",
            "9e64174b4ab981405c323b5e12475945a46d4fedf8060828041cd20e62fd2cef",
        ],
        [
            "0909090909090909090909090909090909090909090909090909090909090909",
            "ebbb40a980ba3b8860948d011e1bfb4affe16c652e90e98258302f4464c91e0c",
            "68431b199104215200b95ee5cb71bf8b883a3e95b7989cad197063141ebbfd00",
            "573467a7b30ead6ccc504744ca9e1a281a0d1a08738b06a0684feacd1e9d126d",
            "71c3523eeca35311fbd5d7e7d70b709d6c35a24f262b34bf64059bf2c02e0ba8",
            "624400103b6569b7358fe80f6f6cad4325defda9d9499c2b8f886a6269a2aa52",
            "db95ea8bd9f93d41b5ab2bebc91a38edd527083e2a6ef9f3c29702d5ff89ed00",
            "233c4ab886a55e3ba374c0",
            "b68e9ee0c0678d7b3036931c831a25255f7ee487385a30316e15f6482b874fda",
        ],
    ];
    /// sapling_zip32.json, all five vectors: `ask, nsk, ovk, dk, c, ak, nk, ivk, xsk, xfvk,
    /// fp, d0, d1, d2, dmax, internal_nsk, internal_ovk, internal_dk, internal_nk,
    /// internal_ivk, internal_xsk, internal_xfvk, internal_fp`; an empty string is `null`.
    const ZIP32: [[&str; 23]; 5] = [
        [
            "b6c00c93d36032b9a268e99e86a860776560bf0e83c1a10b51f607c954742506",
            "8204ede83b2f1fbd84f9b45d7f996e2ebd0a030ad243b48ed39f748a8821ea06",
            "395884890323b9d4933c021db89bcf767df21977b2ff0683848321a4df4afb21",
            "77c17cb75b7796afb39f0f3e91c924607da56fa9a20e283509bc8a3ef996a172",
            "d0947c4b03bf72a37ab44f72276d1cf3fdcd7ebf3e73348b7e550d752018668e",
            "93442e5feffbff16e7217202dc7306729ffffe85af5683bce2642e3eeb5d3871",
            "dce8e7edece04b8950417f85ba57691b783c45b1a27422db1693dceb67b10106",
            "4847a130e799d3dbea36a1c16467d621fb2d80e30b3b1d1a426893415dad6601",
            "000000000000000000d0947c4b03bf72a37ab44f72276d1cf3fdcd7ebf3e73348b7e550d752018668eb6c00c93d36032b9a268e99e86a860776560bf0e83c1a10b51f607c9547425068204ede83b2f1fbd84f9b45d7f996e2ebd0a030ad243b48ed39f748a8821ea06395884890323b9d4933c021db89bcf767df21977b2ff0683848321a4df4afb2177c17cb75b7796afb39f0f3e91c924607da56fa9a20e283509bc8a3ef996a172",
            "000000000000000000d0947c4b03bf72a37ab44f72276d1cf3fdcd7ebf3e73348b7e550d752018668e93442e5feffbff16e7217202dc7306729ffffe85af5683bce2642e3eeb5d3871dce8e7edece04b8950417f85ba57691b783c45b1a27422db1693dceb67b10106395884890323b9d4933c021db89bcf767df21977b2ff0683848321a4df4afb2177c17cb75b7796afb39f0f3e91c924607da56fa9a20e283509bc8a3ef996a172",
            "14c2713adce93a830ea83a051908b7447783f5d106c0985e02550e426f27597c",
            "d8621b981cf300e9d4cc89",
            "48ea17a199c84bd1baa5d4",
            "",
            "",
            "511233636b95fd0afb6bf8193a7d8f49efd736a988775c54f956687646eaab07",
            "9dc477fe1e7d282913f651654d3985f09d53c2d3b5763d7a723bcbd6ee053d5a",
            "40ddc56e6975138c0839e580b54d6d999dc616843cfe041e8f388b124ef7b5ed",
            "a3831a5c6933f8ec6aa5ce316c508b7991cd94d3bdb700a1c427a6ae15e72fb5",
            "790577321c511804636ee6baa4eea779b4a46a5a12f85d365074a09d054f3401",
            "000000000000000000d0947c4b03bf72a37ab44f72276d1cf3fdcd7ebf3e73348b7e550d752018668eb6c00c93d36032b9a268e99e86a860776560bf0e83c1a10b51f607c954742506511233636b95fd0afb6bf8193a7d8f49efd736a988775c54f956687646eaab079dc477fe1e7d282913f651654d3985f09d53c2d3b5763d7a723bcbd6ee053d5a40ddc56e6975138c0839e580b54d6d999dc616843cfe041e8f388b124ef7b5ed",
            "000000000000000000d0947c4b03bf72a37ab44f72276d1cf3fdcd7ebf3e73348b7e550d752018668e93442e5feffbff16e7217202dc7306729ffffe85af5683bce2642e3eeb5d3871a3831a5c6933f8ec6aa5ce316c508b7991cd94d3bdb700a1c427a6ae15e72fb59dc477fe1e7d282913f651654d3985f09d53c2d3b5763d7a723bcbd6ee053d5a40ddc56e6975138c0839e580b54d6d999dc616843cfe041e8f388b124ef7b5ed",
            "8264edec63b155001d8496685cc7c21ea957c6f591090a1c20e52a4189b8bb96",
        ],
        [
            "282bc197a516287c8ea8f68c424abad302b45cdf95407961d7b8b455267a350c",
            "e7a32988fdca1efcd6d1c4c562e629c2e96b2c3f7eda04ac4efd1810ff6bba01",
            "5f1381fc8886da6a02dffeefcf503c40fa8f5a36f7a7142fd81b5518c5a47474",
            "e04de832a2d791ec129ab9002b91c9e9cdeed79241a7c4960e5178d870c1b4dc",
            "0147110c691a03b9d9f0ba9005c5e790a595b7f04e3329d2fa438a6705dabce6",
            "dc14b514d3a92594c21925af2f7765a547b30e73fa7b700ea1bff2e5efaaa88b",
            "6152eb7fdb252779ddcb95d217ea4b6fd34036e9adadb3b5c9cbeceb41ba452a",
            "155a8ee205d3872d12f8a3e639914633c23cde1f30ed5051e52130b1d0104c06",
            "0114c2713a010000000147110c691a03b9d9f0ba9005c5e790a595b7f04e3329d2fa438a6705dabce6282bc197a516287c8ea8f68c424abad302b45cdf95407961d7b8b455267a350ce7a32988fdca1efcd6d1c4c562e629c2e96b2c3f7eda04ac4efd1810ff6bba015f1381fc8886da6a02dffeefcf503c40fa8f5a36f7a7142fd81b5518c5a47474e04de832a2d791ec129ab9002b91c9e9cdeed79241a7c4960e5178d870c1b4dc",
            "0114c2713a010000000147110c691a03b9d9f0ba9005c5e790a595b7f04e3329d2fa438a6705dabce6dc14b514d3a92594c21925af2f7765a547b30e73fa7b700ea1bff2e5efaaa88b6152eb7fdb252779ddcb95d217ea4b6fd34036e9adadb3b5c9cbeceb41ba452a5f1381fc8886da6a02dffeefcf503c40fa8f5a36f7a7142fd81b5518c5a47474e04de832a2d791ec129ab9002b91c9e9cdeed79241a7c4960e5178d870c1b4dc",
            "db999e071dcb58dd93029ae697053e90edb359d1a1b7a125167efbe928068423",
            "8b4138320dfafd7b399781",
            "",
            "5749a13352bc223e308078",
            "6389574cde0fbbc6368131",
            "74929f790c11dcab3a2f931235cdb267f5a31b9f139f2c9fd816b0444fb80505",
            "0cd4d7c5cc7f534b96d24182a31465b4781105489cd10d500cf5295a6fd818cc",
            "d278b72c621d19cb00f970079c8922761cdd3ae7f27b1847c55360dbebf65492",
            "2b5c78a2fba5019c15a751502ba9916faedae1fc14dc81b0b835f2bf95c068e8",
            "df4454a676d1de32e20ae6287a92fafefbbb3e54b588c8da2807ec43682c8500",
            "0114c2713a010000000147110c691a03b9d9f0ba9005c5e790a595b7f04e3329d2fa438a6705dabce6282bc197a516287c8ea8f68c424abad302b45cdf95407961d7b8b455267a350c74929f790c11dcab3a2f931235cdb267f5a31b9f139f2c9fd816b0444fb805050cd4d7c5cc7f534b96d24182a31465b4781105489cd10d500cf5295a6fd818ccd278b72c621d19cb00f970079c8922761cdd3ae7f27b1847c55360dbebf65492",
            "0114c2713a010000000147110c691a03b9d9f0ba9005c5e790a595b7f04e3329d2fa438a6705dabce6dc14b514d3a92594c21925af2f7765a547b30e73fa7b700ea1bff2e5efaaa88b2b5c78a2fba5019c15a751502ba9916faedae1fc14dc81b0b835f2bf95c068e80cd4d7c5cc7f534b96d24182a31465b4781105489cd10d500cf5295a6fd818ccd278b72c621d19cb00f970079c8922761cdd3ae7f27b1847c55360dbebf65492",
            "0de583ca502b1c4b87cac8c9786c619b79e169b41561f244eeec8686b8dbc4e1",
        ],
        [
            "8be8113cee3413a71f82c41fc8da517be134049832e6825c92da6b84fee4c60d",
            "3778059dc569e7d0d32391573f951bbde92fc6b9cf614773661c5c273aa6990c",
            "cf81182e96223c028ce3d6eb4794d3113b95069d14c57588e193b65efc2813bc",
            "a3eda19f9eff46ca12dfa1bf10371b48d1b4a40c4d05a0d8dce0e7dc62b07b37",
            "97ce15f4ed1b9739b0262a463bcb3dc9b3bd2323a9baa441ca42777383a8d435",
            "a6c5925a0f85fa4f1e405e3a4970d0c4a4b4814438f4e9d4520e20f7fdcf3841",
            "304e305916216beb7b654d8aae50ecd188fcb384bc36c00c664f307725e2ee11",
            "a2a13c1e38b45984445803e430a683c90bb2e14d4c8692ff253a6484dd9bb504",
            "02db999e070200008097ce15f4ed1b9739b0262a463bcb3dc9b3bd2323a9baa441ca42777383a8d4358be8113cee3413a71f82c41fc8da517be134049832e6825c92da6b84fee4c60d3778059dc569e7d0d32391573f951bbde92fc6b9cf614773661c5c273aa6990ccf81182e96223c028ce3d6eb4794d3113b95069d14c57588e193b65efc2813bca3eda19f9eff46ca12dfa1bf10371b48d1b4a40c4d05a0d8dce0e7dc62b07b37",
            "02db999e070200008097ce15f4ed1b9739b0262a463bcb3dc9b3bd2323a9baa441ca42777383a8d435a6c5925a0f85fa4f1e405e3a4970d0c4a4b4814438f4e9d4520e20f7fdcf3841304e305916216beb7b654d8aae50ecd188fcb384bc36c00c664f307725e2ee11cf81182e96223c028ce3d6eb4794d3113b95069d14c57588e193b65efc2813bca3eda19f9eff46ca12dfa1bf10371b48d1b4a40c4d05a0d8dce0e7dc62b07b37",
            "48c183757b5da6612a81b30e40b4acaa2d9e739512e1d2d0010e92a7f7f2fcdf",
            "e8d03793cdd2bacc9c7041",
            "020a7a6b0bf84d3e899f68",
            "",
            "",
            "347865acf47e504538f5ef8b04702080e6091cda5797cd7d235a546eb10f5508",
            "ddbac2a493f53c3b0933d913def88848654c087c12609df01baf9405ce7804fd",
            "602cd317b7cea11e8cc7ae2ea405b40d46b1592a30f0cb6e8c4f17d7f7c47feb",
            "f91287c06e30b65ea1bdb716b231de6778a5d80ee5cd9c060d1abacae0aae23b",
            "1d59ea2017881864d24eadb5cf3468a41a1b2aaa0d1b3a72c6da9ce6502a0a05",
            "02db999e070200008097ce15f4ed1b9739b0262a463bcb3dc9b3bd2323a9baa441ca42777383a8d4358be8113cee3413a71f82c41fc8da517be134049832e6825c92da6b84fee4c60d347865acf47e504538f5ef8b04702080e6091cda5797cd7d235a546eb10f5508ddbac2a493f53c3b0933d913def88848654c087c12609df01baf9405ce7804fd602cd317b7cea11e8cc7ae2ea405b40d46b1592a30f0cb6e8c4f17d7f7c47feb",
            "02db999e070200008097ce15f4ed1b9739b0262a463bcb3dc9b3bd2323a9baa441ca42777383a8d435a6c5925a0f85fa4f1e405e3a4970d0c4a4b4814438f4e9d4520e20f7fdcf3841f91287c06e30b65ea1bdb716b231de6778a5d80ee5cd9c060d1abacae0aae23bddbac2a493f53c3b0933d913def88848654c087c12609df01baf9405ce7804fd602cd317b7cea11e8cc7ae2ea405b40d46b1592a30f0cb6e8c4f17d7f7c47feb",
            "30fe0d610f947b2c260e7b29e79e5c2e7d3e14abf979f6406d07baf8faddf495",
        ],
        [
            "",
            "",
            "cf81182e96223c028ce3d6eb4794d3113b95069d14c57588e193b65efc2813bc",
            "a3eda19f9eff46ca12dfa1bf10371b48d1b4a40c4d05a0d8dce0e7dc62b07b37",
            "97ce15f4ed1b9739b0262a463bcb3dc9b3bd2323a9baa441ca42777383a8d435",
            "a6c5925a0f85fa4f1e405e3a4970d0c4a4b4814438f4e9d4520e20f7fdcf3841",
            "304e305916216beb7b654d8aae50ecd188fcb384bc36c00c664f307725e2ee11",
            "a2a13c1e38b45984445803e430a683c90bb2e14d4c8692ff253a6484dd9bb504",
            "",
            "02db999e070200008097ce15f4ed1b9739b0262a463bcb3dc9b3bd2323a9baa441ca42777383a8d435a6c5925a0f85fa4f1e405e3a4970d0c4a4b4814438f4e9d4520e20f7fdcf3841304e305916216beb7b654d8aae50ecd188fcb384bc36c00c664f307725e2ee11cf81182e96223c028ce3d6eb4794d3113b95069d14c57588e193b65efc2813bca3eda19f9eff46ca12dfa1bf10371b48d1b4a40c4d05a0d8dce0e7dc62b07b37",
            "48c183757b5da6612a81b30e40b4acaa2d9e739512e1d2d0010e92a7f7f2fcdf",
            "e8d03793cdd2bacc9c7041",
            "020a7a6b0bf84d3e899f68",
            "",
            "",
            "",
            "ddbac2a493f53c3b0933d913def88848654c087c12609df01baf9405ce7804fd",
            "602cd317b7cea11e8cc7ae2ea405b40d46b1592a30f0cb6e8c4f17d7f7c47feb",
            "f91287c06e30b65ea1bdb716b231de6778a5d80ee5cd9c060d1abacae0aae23b",
            "1d59ea2017881864d24eadb5cf3468a41a1b2aaa0d1b3a72c6da9ce6502a0a05",
            "",
            "02db999e070200008097ce15f4ed1b9739b0262a463bcb3dc9b3bd2323a9baa441ca42777383a8d435a6c5925a0f85fa4f1e405e3a4970d0c4a4b4814438f4e9d4520e20f7fdcf3841f91287c06e30b65ea1bdb716b231de6778a5d80ee5cd9c060d1abacae0aae23bddbac2a493f53c3b0933d913def88848654c087c12609df01baf9405ce7804fd602cd317b7cea11e8cc7ae2ea405b40d46b1592a30f0cb6e8c4f17d7f7c47feb",
            "30fe0d610f947b2c260e7b29e79e5c2e7d3e14abf979f6406d07baf8faddf495",
        ],
        [
            "",
            "",
            "69b9e0fa1c4b3deb91d53beee871156121474b8b62ef24134478dc3499691af6",
            "becb50c363bb2ed9da5c3043ceb0f1a0527bf836b29a35f7c0c9f261123be56e",
            "8d937bcf81ba430d5b49afc0a403367b1fd99879ecba41be051c5a4aa7d6e7e8",
            "b185c57b509c2536c4f2d326d766c8fab25447de5375a9328d649ddabd97a6a3",
            "db88049e02d207568afc42e07db2abed500b2701c01bbff36399764b81c0664f",
            "b0a5f337232f2c3dac70c2a410fa561fc45d8cc59cda246d31c8b1715a57d900",
            "",
            "0348c18375030000008d937bcf81ba430d5b49afc0a403367b1fd99879ecba41be051c5a4aa7d6e7e8b185c57b509c2536c4f2d326d766c8fab25447de5375a9328d649ddabd97a6a3db88049e02d207568afc42e07db2abed500b2701c01bbff36399764b81c0664f69b9e0fa1c4b3deb91d53beee871156121474b8b62ef24134478dc3499691af6becb50c363bb2ed9da5c3043ceb0f1a0527bf836b29a35f7c0c9f261123be56e",
            "2e08156df8dfa25b5055fc063c671535a6a65a60437d96e7930815d090f62d67",
            "",
            "030ffb263a939e230e96dd",
            "7bbf63934c7e92670cdb55",
            "1a730feb0059cf1f5bdea8",
            "",
            "bf19e257dd833e0294ec2acbdfa40e1452f8e6a1f0c7f6f3abe56afd5f6e2618",
            "1ffd6f81fe85c49fe3e73ef73e50113822ca6267312b7aced0c156a32b3f2438",
            "822f2f70960f05d6967458e39210d5771f9847aef9e34d94b8afbf95bbc4d227",
            "f98a76098e910503e8027752042de87e7d893ab0145ebc3b0597c2397f69d201",
            "",
            "0348c18375030000008d937bcf81ba430d5b49afc0a403367b1fd99879ecba41be051c5a4aa7d6e7e8b185c57b509c2536c4f2d326d766c8fab25447de5375a9328d649ddabd97a6a3822f2f70960f05d6967458e39210d5771f9847aef9e34d94b8afbf95bbc4d227bf19e257dd833e0294ec2acbdfa40e1452f8e6a1f0c7f6f3abe56afd5f6e26181ffd6f81fe85c49fe3e73ef73e50113822ca6267312b7aced0c156a32b3f2438",
            "ba64e40d086d362ca5a17f5e3b1bee6324c84f101244a4002a2ecaaf05bdd981",
        ],
    ];

    #[test]
    fn key_components_match_official_vectors() {
        for [sk, ask, nsk, ovk, ak, nk, ivk, default_d, default_pk_d] in KEY_COMPONENTS {
            let sk: [u8; 32] = arr(sk);
            let esk = expand_spending_key(&sk);
            assert_eq!(esk.ask.to_vec(), hex(ask));
            assert_eq!(esk.nsk.to_vec(), hex(nsk));
            assert_eq!(esk.ovk.to_vec(), hex(ovk));
            let fvk = esk.full_viewing_key();
            assert_eq!(fvk.ak.to_vec(), hex(ak));
            assert_eq!(fvk.nk.to_vec(), hex(nk));
            assert_eq!(fvk.ovk.to_vec(), hex(ovk));
            assert_eq!(fvk.ivk().to_vec(), hex(ivk));
            let d = default_diversifier(&sk);
            assert_eq!(d.to_vec(), hex(default_d));
            let pk_d = derive_pk_d(&fvk.ivk(), &d).unwrap();
            assert_eq!(pk_d.to_vec(), hex(default_pk_d));
            let address = payment_address(&fvk.ivk(), &d).unwrap();
            assert_eq!(address[..11], d);
            assert_eq!(address[11..], pk_d);
            assert!(jubjub_is_prime_order(&fvk.ak));
        }
    }

    fn check_fvk_row(fvk: &SaplingExtendedFullViewingKey, row: &[&str; 23]) {
        assert_eq!(fvk.ovk.to_vec(), hex(row[2]));
        assert_eq!(fvk.dk.to_vec(), hex(row[3]));
        assert_eq!(fvk.chain_code.to_vec(), hex(row[4]));
        assert_eq!(fvk.ak.to_vec(), hex(row[5]));
        assert_eq!(fvk.nk.to_vec(), hex(row[6]));
        assert_eq!(fvk.ivk().to_vec(), hex(row[7]));
        assert_eq!(fvk.to_bytes().to_vec(), hex(row[9]));
        assert_eq!(fvk.fingerprint().to_vec(), hex(row[10]));
        let mut one = [0u8; 11];
        one[0] = 1;
        let mut two = [0u8; 11];
        two[0] = 2;
        let indices = [[0u8; 11], one, two, [0xff; 11]];
        for (index, want) in indices.iter().zip(&row[11..15]) {
            assert_eq!(fvk.diversifier(index), opt(want));
            assert_eq!(fvk.address(index).is_some(), !want.is_empty());
        }
        let (index, d) = fvk.default_diversifier();
        let first = (0..3).find(|&j| !row[11 + j].is_empty()).unwrap();
        assert_eq!(index, indices[first]);
        assert_eq!(d.to_vec(), hex(row[11 + first]));
        assert_eq!(
            fvk.address(&index).unwrap()[11..],
            derive_pk_d(&fvk.ivk(), &d).unwrap()
        );
        let internal = fvk.internal().unwrap();
        assert_eq!(internal.ovk.to_vec(), hex(row[16]));
        assert_eq!(internal.dk.to_vec(), hex(row[17]));
        assert_eq!(internal.nk.to_vec(), hex(row[18]));
        assert_eq!(internal.ivk().to_vec(), hex(row[19]));
        assert_eq!(internal.to_bytes().to_vec(), hex(row[21]));
        assert_eq!(internal.fingerprint().to_vec(), hex(row[22]));
    }

    fn check_xsk_row(xsk: &SaplingExtendedSpendingKey, row: &[&str; 23]) {
        assert_eq!(xsk.ask.to_vec(), hex(row[0]));
        assert_eq!(xsk.nsk.to_vec(), hex(row[1]));
        assert_eq!(xsk.to_bytes().to_vec(), hex(row[8]));
        let internal = xsk.internal();
        assert_eq!(internal.nsk.to_vec(), hex(row[15]));
        assert_eq!(internal.to_bytes().to_vec(), hex(row[20]));
        // The commutative diagram of ZIP 32.
        assert_eq!(
            Some(internal.to_extended_fvk()),
            xsk.to_extended_fvk().internal()
        );
        check_fvk_row(&xsk.to_extended_fvk(), row);
    }

    #[test]
    fn zip32_matches_official_vectors() {
        // sapling_zip32.json: m, m/1, m/1/2', the viewing key of m/1/2', and its child 3.
        let seed: Vec<u8> = (0..32).collect();
        let m = SaplingExtendedSpendingKey::master(&seed).unwrap();
        let m_1 = m.child(1).unwrap();
        let m_1_2h = m_1.child(ZIP32_HARDENED + 2).unwrap();
        let m_1_2hv = m_1_2h.to_extended_fvk();
        let m_1_2hv_3 = m_1_2hv.child(3).unwrap();
        check_xsk_row(&m, &ZIP32[0]);
        check_xsk_row(&m_1, &ZIP32[1]);
        check_xsk_row(&m_1_2h, &ZIP32[2]);
        assert!(ZIP32[3][0].is_empty() && ZIP32[4][8].is_empty());
        check_fvk_row(&m_1_2hv, &ZIP32[3]);
        check_fvk_row(&m_1_2hv_3, &ZIP32[4]);
        // Non-hardened derivation commutes with taking the viewing key.
        assert_eq!(m.to_extended_fvk().child(1), Some(m_1.to_extended_fvk()));
        assert_eq!(
            m_1_2h.child(3).map(|k| k.to_extended_fvk()),
            Some(m_1_2hv_3)
        );
        let derived = SaplingExtendedSpendingKey::derive(&seed, &[1, ZIP32_HARDENED + 2]).unwrap();
        assert_eq!(derived.to_bytes(), m_1_2h.to_bytes());
    }

    #[test]
    fn zip32_refuses_invalid_requests() {
        let seed: Vec<u8> = (0..32).collect();
        assert!(SaplingExtendedSpendingKey::master(&seed[..31]).is_none());
        assert!(SaplingExtendedSpendingKey::master(&[0; 253]).is_none());
        assert!(SaplingExtendedSpendingKey::master(&[0; 252]).is_some());
        let m = SaplingExtendedSpendingKey::master(&seed).unwrap();
        let fvk = m.to_extended_fvk();
        // A viewing key has no hardened children.
        assert_eq!(fvk.child(ZIP32_HARDENED), None);
        assert!(fvk.child(ZIP32_HARDENED - 1).is_some());
        // A viewing key whose ak is not a point.
        let mut broken = fvk.clone();
        broken.ak = limbs_to_bytes(&Q);
        assert_eq!(broken.child(1), None);
        let mut broken = fvk.clone();
        broken.nk = [0xff; 32];
        assert_eq!(broken.internal(), None);
        // Hardened and non-hardened children at the same number differ.
        assert_ne!(
            m.child(5).unwrap().to_bytes(),
            m.child(ZIP32_HARDENED + 5).unwrap().to_bytes()
        );
        assert_eq!(next_diversifier_index(&[0xff; 11]), None);
        let mut carry = [0u8; 11];
        carry[0] = 0xff;
        let mut next = [0u8; 11];
        next[1] = 1;
        assert_eq!(next_diversifier_index(&carry), Some(next));
    }
}
