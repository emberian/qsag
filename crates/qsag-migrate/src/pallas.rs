//! Zcash Orchard (`Pallas` / `RedPallas`) post-quantum ownership migration (`Π_pallas_migrate`).
//!
//! Curve parameters (Zcash Protocol Specification §5.4.9.6 & §5.4.8.4 `SpendAuthSig`):
//! - Base field prime:
//!   `p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001` (`2^254 + c_p`)
//! - Scalar field prime (prime curve order, cofactor `h = 1`):
//!   `q = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001` (`2^254 + c_q`)
//! - Curve equation: `E(F_p) : y^2 = x^3 + 5` (`a = 0, b = 5, 3b = 15`).
//! - Spend-authorization basepoint:
//!   `SpendAuthG = GroupHash^Pallas("z.cash:Orchard", "G")` (`orchard` crate fixed base).
//!
//! Supports both direct spend-authorizing key ownership (`ak = [ask] SpendAuthG`) and
//! per-Action RedPallas rerandomized verification key ownership
//! (`rk = ak + [alpha] SpendAuthG = [ask + alpha mod q] SpendAuthG`), proving knowledge of
//! `(ask, alpha)` across 438 mixed-domain ZKBoo repetitions (`(2/3)^438 < 2^-256` classical
//! soundness error, `> 2^128` Grover oracle iterations) bound to a destination `QsagAddress`
//! without revealing `ask`, `alpha`, or `ak`.

use alloc::vec::Vec;
use core::cell::RefCell;
use core::fmt;

use qsag_accel::{
    AcceleratorBackend,
    ct::{RedactedSecret, ct_eq_u64, ct_select_u64, ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::{GOLDILOCKS_PRIME, gl_add, gl_mul, gl_sub, pack_bytes32_to_limbs56},
    keccak::{InterleavedTranscript, cshake256_framed_32},
    poseidon2::{POSEIDON2_CONST_IV, poseidon2_const_at, poseidon2_hash_limbs},
};
use qsag_addr::QsagAddress;

use crate::{
    scalar::NULLIFIER_DOMAIN,
    zk_engine::{
        MIT_REPETITIONS, MigrateError, MigrationZkProof, OpenedRepetitionView, PartyView,
        challenges, rep_root,
    },
};

/// Pallas base field modulus `p = 2^254 + 0x224698fc094cf91b992d30ed00000001` (LE limbs).
pub const PALLAS_P: [u64; 4] = [
    0x992d_30ed_0000_0001,
    0x2246_98fc_094c_f91b,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];

const PALLAS_P_MINUS_2: [u64; 4] = [
    0x992d_30ec_ffff_ffff,
    0x2246_98fc_094c_f91b,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];

/// `-p[0]^{-1} mod 2^64` for CIOS Montgomery reduction over `F_p`.
const PALLAS_P_INV: u64 = 0x992d_30ec_ffff_ffff;

/// `R^2 mod p` for `R = 2^256`.
const PALLAS_P_R2: [u64; 4] = [
    0x8c78_ecb3_0000_000f,
    0xd7d3_0dbd_8b0d_e0e7,
    0x7797_a99b_c3c9_5d18,
    0x096d_41af_7b9c_b714,
];

/// Tonelli-Shanks constants for `p - 1 = 2^32 * s`: `(s - 1) / 2` and primitive `2^32`-th root `5^s mod p`.
const PALLAS_S_MINUS_1_HALF: [u64; 4] = [
    0x04a6_7c8d_cc96_9876,
    0x0000_0000_1123_4c7e,
    0x0000_0000_0000_0000,
    0x0000_0000_2000_0000,
];
const PALLAS_ROOT_OF_UNITY: [u64; 4] = [
    0xbda_d6fa_bd87_ea32f,
    0xea32_2bf2_b7bb_7584,
    0x3621_2083_0561_f81a,
    0x2bce_74de_ac30_ebda,
];

/// Pallas scalar field modulus `q = 2^254 + 0x224698fc0994a8dd8c46eb2100000001` (LE limbs).
pub const PALLAS_Q: [u64; 4] = [
    0x8c46_eb21_0000_0001,
    0x2246_98fc_0994_a8dd,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];

const PALLAS_Q_MINUS_2: [u64; 4] = [
    0x8c46_eb20_ffff_ffff,
    0x2246_98fc_0994_a8dd,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];

const PALLAS_Q_INV: u64 = 0x8c46_eb20_ffff_ffff;
const PALLAS_Q_R2: [u64; 4] = [
    0xfc96_78ff_0000_000f,
    0x67bb_433d_891a_16e3,
    0x7fae_2310_04cc_f590,
    0x096d_41af_7ccf_daa9,
];

/// Official Zcash Orchard `SpendAuthG` affine `x` coordinate (`GroupHash^Pallas("z.cash:Orchard", "G")`).
pub const ORCHARD_SPEND_AUTH_GX: [u64; 4] = [
    0x8d1a_7284_b875_c963,
    0x0c7f_0ce3_7b70_a10c,
    0x3b8d_187c_3e5f_445f,
    0x3755_23b3_28f1_d606,
];

/// Official Zcash Orchard `SpendAuthG` affine `y` coordinate (`GroupHash^Pallas("z.cash:Orchard", "G")`).
pub const ORCHARD_SPEND_AUTH_GY: [u64; 4] = [
    0x4ce3_3e81_7b0c_3bc9,
    0xdfc9_14fe_c005_bdd8,
    0x7b10_bcfc_fed6_24fb,
    0x1ad0_357f_df1a_66db,
];

/// Pasta standard generator `(-1, 2)` on `y^2 = x^3 + 5`.
pub const PASTA_PALLAS_GX: [u64; 4] = [
    0x992d_30ed_0000_0000,
    0x2246_98fc_094c_f91b,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];
pub const PASTA_PALLAS_GY: [u64; 4] = [2, 0, 0, 0];

/// Nullifier subgroup tags separating Orchard `ak` and RedPallas rerandomized `rk` from `secp256k1` (1) and `Ed25519` (2).
pub const NULLIFIER_TAG_PALLAS_AK: u64 = 3;
pub const NULLIFIER_TAG_PALLAS_RK: u64 = 4;

#[inline]
fn sub4_borrow(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], bool) {
    let mut out = [0u64; 4];
    let mut br = 0u64;
    for i in 0..4 {
        let (d1, b1) = a[i].overflowing_sub(b[i]);
        let (d2, b2) = d1.overflowing_sub(br);
        out[i] = d2;
        br = (b1 as u64) | (b2 as u64);
    }
    (out, br != 0)
}

#[inline]
fn lt4(a: [u64; 4], b: [u64; 4]) -> bool {
    sub4_borrow(a, b).1
}

#[inline]
fn select4(choice: bool, t: [u64; 4], f: [u64; 4]) -> [u64; 4] {
    [
        ct_select_u64(choice, t[0], f[0]),
        ct_select_u64(choice, t[1], f[1]),
        ct_select_u64(choice, t[2], f[2]),
        ct_select_u64(choice, t[3], f[3]),
    ]
}

#[inline]
fn add4_mod(a: [u64; 4], b: [u64; 4], m: [u64; 4]) -> [u64; 4] {
    let mut sum = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let cur = (a[i] as u128) + (b[i] as u128) + carry;
        sum[i] = cur as u64;
        carry = cur >> 64;
    }
    let (diff, borrow) = sub4_borrow(sum, m);
    select4((carry != 0) | !borrow, diff, sum)
}

#[inline]
fn sub4_mod(a: [u64; 4], b: [u64; 4], m: [u64; 4]) -> [u64; 4] {
    let (diff, borrow) = sub4_borrow(a, b);
    let mut out = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let addend = ct_select_u64(borrow, m[i], 0);
        let cur = (diff[i] as u128) + (addend as u128) + carry;
        out[i] = cur as u64;
        carry = cur >> 64;
    }
    out
}

/// Constant-time 4-limb CIOS Montgomery product `a * b * 2^-256 mod m` (`m < 2^255`).
#[inline]
fn cios_mont_mul4(a: [u64; 4], b: [u64; 4], m: [u64; 4], inv: u64) -> [u64; 4] {
    let mut t = [0u64; 6];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let cur = (t[j] as u128) + (a[i] as u128) * (b[j] as u128) + carry;
            t[j] = cur as u64;
            carry = cur >> 64;
        }
        let cur = (t[4] as u128) + carry;
        t[4] = cur as u64;
        t[5] = (cur >> 64) as u64;

        let u = t[0].wrapping_mul(inv);
        let cur0 = (t[0] as u128) + (u as u128) * (m[0] as u128);
        let mut carry2 = cur0 >> 64;
        for j in 1..4 {
            let curj = (t[j] as u128) + (u as u128) * (m[j] as u128) + carry2;
            t[j - 1] = curj as u64;
            carry2 = curj >> 64;
        }
        let cur4 = (t[4] as u128) + carry2;
        t[3] = cur4 as u64;
        t[4] = t[5].wrapping_add((cur4 >> 64) as u64);
        t[5] = 0;
    }
    let raw = [t[0], t[1], t[2], t[3]];
    let (diff, borrow) = sub4_borrow(raw, m);
    select4((t[4] != 0) | !borrow, diff, raw)
}

#[inline]
fn pow4_ct(base: [u64; 4], exp: [u64; 4], m: [u64; 4], inv: u64, r2: [u64; 4]) -> [u64; 4] {
    let mut b_m = cios_mont_mul4(base, r2, m, inv);
    let mut acc_m = cios_mont_mul4([1, 0, 0, 0], r2, m, inv);
    for limb in exp {
        for bit in 0..64 {
            let take = ((limb >> bit) & 1) == 1;
            let prod = cios_mont_mul4(acc_m, b_m, m, inv);
            acc_m = select4(take, prod, acc_m);
            b_m = cios_mont_mul4(b_m, b_m, m, inv);
        }
    }
    cios_mont_mul4(acc_m, [1, 0, 0, 0], m, inv)
}

/// Canonical element of the Pallas base field `F_p` (`0 <= self < p`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FpPallas(pub [u64; 4]);

impl FpPallas {
    pub const ZERO: Self = Self([0; 4]);
    pub const ONE: Self = Self([1, 0, 0, 0]);
    /// `3 * b = 15` for `y^2 = x^3 + 5`.
    pub const B3: Self = Self([15, 0, 0, 0]);
    pub const B: Self = Self([5, 0, 0, 0]);

    pub fn from_le_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let limbs = crate::scalar::decode(bytes);
        if lt4(limbs, PALLAS_P) {
            Some(Self(limbs))
        } else {
            None
        }
    }

    pub fn to_le_bytes(self) -> [u8; 32] {
        crate::scalar::encode(self.0)
    }

    #[inline]
    pub fn ct_select(choice: bool, t: Self, f: Self) -> Self {
        Self(select4(choice, t.0, f.0))
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        ct_eq_u64(self.0[0] | self.0[1] | self.0[2] | self.0[3], 0)
    }

    #[inline]
    pub fn is_odd(self) -> bool {
        (self.0[0] & 1) == 1
    }

    #[inline]
    pub fn add_mod(self, rhs: Self) -> Self {
        Self(add4_mod(self.0, rhs.0, PALLAS_P))
    }

    #[inline]
    pub fn sub_mod(self, rhs: Self) -> Self {
        Self(sub4_mod(self.0, rhs.0, PALLAS_P))
    }

    #[inline]
    pub fn neg_mod(self) -> Self {
        Self::ZERO.sub_mod(self)
    }

    #[inline]
    pub fn mul_mod(self, rhs: Self) -> Self {
        let m1 = cios_mont_mul4(self.0, rhs.0, PALLAS_P, PALLAS_P_INV);
        Self(cios_mont_mul4(m1, PALLAS_P_R2, PALLAS_P, PALLAS_P_INV))
    }

    #[inline]
    pub fn sq(self) -> Self {
        self.mul_mod(self)
    }

    /// Constant-time Fermat inversion `a^(p - 2) mod p` (`0 -> 0`).
    pub fn inv_or_zero(self) -> Self {
        Self(pow4_ct(
            self.0,
            PALLAS_P_MINUS_2,
            PALLAS_P,
            PALLAS_P_INV,
            PALLAS_P_R2,
        ))
    }

    /// Constant-time 32-adic Tonelli-Shanks square root in `F_p`.
    pub fn sqrt_ct(self) -> Option<Self> {
        let w = Self(pow4_ct(
            self.0,
            PALLAS_S_MINUS_1_HALF,
            PALLAS_P,
            PALLAS_P_INV,
            PALLAS_P_R2,
        ));
        let mut x = self.mul_mod(w);
        let mut b = x.mul_mod(w);
        let mut c = Self(PALLAS_ROOT_OF_UNITY);
        let minus_one = Self::ONE.neg_mod();
        for r in (2..=32).rev() {
            let mut d = b;
            for _ in 0..(r - 2) {
                d = d.sq();
            }
            let need_mul = ct_eq_u64(
                (d.0[0] ^ minus_one.0[0])
                    | (d.0[1] ^ minus_one.0[1])
                    | (d.0[2] ^ minus_one.0[2])
                    | (d.0[3] ^ minus_one.0[3]),
                0,
            );
            let c2 = c.sq();
            x = Self::ct_select(need_mul, x.mul_mod(c), x);
            b = Self::ct_select(need_mul, b.mul_mod(c2), b);
            c = c2;
        }
        if x.sq() == self {
            Some(x)
        } else {
            None
        }
    }
}

impl core::ops::Add for FpPallas {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.add_mod(rhs)
    }
}
impl core::ops::Sub for FpPallas {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.sub_mod(rhs)
    }
}
impl core::ops::Mul for FpPallas {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.mul_mod(rhs)
    }
}
impl core::ops::Neg for FpPallas {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.neg_mod()
    }
}

/// Canonical element of the Pallas scalar field `F_q` (`0 <= self < q`), wiped on `Drop`.
#[derive(Clone, PartialEq, Eq)]
pub struct FqPallas(pub [u64; 4]);

impl fmt::Debug for FqPallas {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("FqPallas").field(&"<REDACTED>").finish()
    }
}

impl Drop for FqPallas {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
}

impl FqPallas {
    pub const ZERO: Self = Self([0; 4]);
    pub const ONE: Self = Self([1, 0, 0, 0]);

    pub fn from_le_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let mut limbs = crate::scalar::decode(bytes);
        if lt4(limbs, PALLAS_Q) {
            Some(Self(limbs))
        } else {
            ct_zeroize_u64s(&mut limbs);
            None
        }
    }

    pub fn from_nonzero_le_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let s = Self::from_le_bytes(bytes)?;
        if s.is_zero() { None } else { Some(s) }
    }

    pub fn to_le_bytes(&self) -> [u8; 32] {
        crate::scalar::encode(self.0)
    }

    pub fn to_be_bytes(&self) -> [u8; 32] {
        let mut le = self.to_le_bytes();
        le.reverse();
        le
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        ct_eq_u64(self.0[0] | self.0[1] | self.0[2] | self.0[3], 0)
    }

    #[inline]
    pub fn add_mod(&self, rhs: &Self) -> Self {
        Self(add4_mod(self.0, rhs.0, PALLAS_Q))
    }

    #[inline]
    pub fn sub_mod(&self, rhs: &Self) -> Self {
        Self(sub4_mod(self.0, rhs.0, PALLAS_Q))
    }

    #[inline]
    pub fn neg_mod(&self) -> Self {
        Self::ZERO.sub_mod(self)
    }

    #[inline]
    pub fn mul_mod(&self, rhs: &Self) -> Self {
        let m1 = cios_mont_mul4(self.0, rhs.0, PALLAS_Q, PALLAS_Q_INV);
        Self(cios_mont_mul4(m1, PALLAS_Q_R2, PALLAS_Q, PALLAS_Q_INV))
    }

    pub fn inv_or_zero(&self) -> Self {
        Self(pow4_ct(
            self.0,
            PALLAS_Q_MINUS_2,
            PALLAS_Q,
            PALLAS_Q_INV,
            PALLAS_Q_R2,
        ))
    }

    pub fn compute_nullifier(&self, tag: u64, migration_domain: &[u8; 32]) -> [u64; 4] {
        let mut be = self.to_be_bytes();
        let mut limbs = pack_bytes32_to_limbs56(&be);
        ct_zeroize_bytes(&mut be);
        let dom = pack_bytes32_to_limbs56(migration_domain);
        let mut input = [0u64; 11];
        input[0] = tag;
        input[1..6].copy_from_slice(&limbs);
        input[6..11].copy_from_slice(&dom);
        ct_zeroize_u64s(&mut limbs);
        let out = poseidon2_hash_limbs(NULLIFIER_DOMAIN, &input);
        ct_zeroize_u64s(&mut input);
        out
    }
}

/// Homogeneous projective point `(X : Y : Z)` on Pallas `y^2 = x^3 + 5` (`O = (0 : 1 : 0)`).
#[derive(Clone)]
pub struct PallasPoint {
    pub x: FpPallas,
    pub y: FpPallas,
    pub z: FpPallas,
}

impl Drop for PallasPoint {
    fn drop(&mut self) {
        self.wipe();
    }
}

impl PallasPoint {
    pub const IDENTITY: Self = Self {
        x: FpPallas::ZERO,
        y: FpPallas::ONE,
        z: FpPallas::ZERO,
    };

    /// Official Zcash Orchard `SpendAuthG` generator (`GroupHash^Pallas("z.cash:Orchard", "G")`).
    pub const ORCHARD_SPEND_AUTH_G: Self = Self {
        x: FpPallas(ORCHARD_SPEND_AUTH_GX),
        y: FpPallas(ORCHARD_SPEND_AUTH_GY),
        z: FpPallas::ONE,
    };

    /// Pasta cycle standard generator `(-1, 2)`.
    pub const PASTA_GENERATOR: Self = Self {
        x: FpPallas(PASTA_PALLAS_GX),
        y: FpPallas(PASTA_PALLAS_GY),
        z: FpPallas::ONE,
    };

    pub fn wipe(&mut self) {
        ct_zeroize_u64s(&mut self.x.0);
        ct_zeroize_u64s(&mut self.y.0);
        ct_zeroize_u64s(&mut self.z.0);
    }

    #[inline]
    pub fn is_identity(&self) -> bool {
        self.z.is_zero()
    }

    pub fn is_on_curve(&self) -> bool {
        if self.z.is_zero() {
            return self.x.is_zero() && !self.y.is_zero();
        }
        // Homogeneous check: Y^2 * Z == X^3 + 5 * Z^3
        let z2 = self.z.sq();
        let z3 = z2 * self.z;
        let lhs = self.y.sq() * self.z;
        let rhs = self.x.sq() * self.x + FpPallas::B * z3;
        lhs == rhs
    }

    #[inline]
    pub fn ct_cswap(swap: bool, a: &mut Self, b: &mut Self) {
        let nx = FpPallas::ct_select(swap, b.x, a.x);
        let bx = FpPallas::ct_select(swap, a.x, b.x);
        let ny = FpPallas::ct_select(swap, b.y, a.y);
        let by = FpPallas::ct_select(swap, a.y, b.y);
        let nz = FpPallas::ct_select(swap, b.z, a.z);
        let bz = FpPallas::ct_select(swap, a.z, b.z);
        a.x = nx;
        a.y = ny;
        a.z = nz;
        b.x = bx;
        b.y = by;
        b.z = bz;
    }

    /// Complete exception-free Renes-Costello-Batina (2016) Algorithm 7 addition for `a = 0, 3b = 15`.
    pub fn complete_add(&self, other: &Self) -> Self {
        let mut t0 = self.x * other.x;
        let mut t1 = self.y * other.y;
        let mut t2 = self.z * other.z;
        let t3 = (self.x + self.y) * (other.x + other.y) - (t0 + t1);
        let t4 = (self.y + self.z) * (other.y + other.z) - (t1 + t2);
        let mut y3 = (self.x + self.z) * (other.x + other.z) - (t0 + t2);

        t0 = (t0 + t0) + t0;
        t2 = FpPallas::B3 * t2;
        let mut z3 = t1 + t2;
        t1 = t1 - t2;
        y3 = FpPallas::B3 * y3;

        let x3 = (t3 * t1) - (t4 * y3);
        y3 = (t1 * z3) + (y3 * t0);
        t0 = t0 * t3;
        z3 = (z3 * t4) + t0;
        Self {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    pub fn neg_point(&self) -> Self {
        Self {
            x: self.x,
            y: -self.y,
            z: self.z,
        }
    }

    /// Constant-time 256-bit Montgomery ladder `[k] self` for raw LE limbs (including `q`).
    pub fn scalar_mul_limbs_ct(&self, limbs_le: &[u64; 4]) -> Self {
        let mut r0 = Self::IDENTITY;
        let mut r1 = self.clone();
        for &limb in limbs_le.iter().rev() {
            for bit_pos in (0..64).rev() {
                let bit = ((limb >> bit_pos) & 1) == 1;
                Self::ct_cswap(bit, &mut r0, &mut r1);
                let sum = r0.complete_add(&r1);
                let dbl = r0.complete_add(&r0);
                r0 = dbl;
                r1 = sum;
                Self::ct_cswap(bit, &mut r0, &mut r1);
            }
        }
        r0
    }

    pub fn scalar_mul_ct(&self, scalar: &FqPallas) -> Self {
        self.scalar_mul_limbs_ct(&scalar.0)
    }

    /// Constant-time `[scalar] SpendAuthG`.
    pub fn spend_auth_mul_ct(scalar: &FqPallas) -> Self {
        Self::ORCHARD_SPEND_AUTH_G.scalar_mul_ct(scalar)
    }

    pub fn to_affine(&self) -> Option<(FpPallas, FpPallas)> {
        if self.z.is_zero() {
            return None;
        }
        let z_inv = self.z.inv_or_zero();
        Some((self.x * z_inv, self.y * z_inv))
    }

    /// Canonical 32-byte Zcash Pasta / RedPallas encoding: LE `x` in bits `0..254`, `y & 1` in bit `255`.
    /// Returns `[0u8; 32]` for the identity point.
    pub fn to_compressed_bytes(&self) -> [u8; 32] {
        let Some((x, y)) = self.to_affine() else {
            return [0u8; 32];
        };
        let mut out = x.to_le_bytes();
        out[31] |= (y.is_odd() as u8) << 7;
        out
    }

    /// Decode a canonical non-identity RedPallas verification key (`ak` or `rk`), rejecting `O`
    /// (`[0u8; 32]`), non-canonical `x >= p`, and off-curve `x`.
    pub fn from_nonidentity_bytes(bytes: &[u8; 32]) -> Option<Self> {
        if bytes.iter().all(|&b| b == 0) {
            return None;
        }
        let y_odd = (bytes[31] >> 7) == 1;
        let mut x_bytes = *bytes;
        x_bytes[31] &= 0x7f;
        let x = FpPallas::from_le_bytes(&x_bytes)?;
        let rhs = x.sq() * x + FpPallas::B;
        let y0 = rhs.sqrt_ct()?;
        if y0.is_zero() && y_odd {
            return None;
        }
        let y = FpPallas::ct_select(y0.is_odd() ^ y_odd, -y0, y0);
        Some(Self {
            x,
            y,
            z: FpPallas::ONE,
        })
    }
}

impl PartialEq for PallasPoint {
    fn eq(&self, other: &Self) -> bool {
        match (self.z.is_zero(), other.z.is_zero()) {
            (true, true) => true,
            (true, false) | (false, true) => false,
            (false, false) => (self.x * other.z == other.x * self.z) && (self.y * other.z == other.y * self.z),
        }
    }
}
impl Eq for PallasPoint {}

/// Zcash Orchard Pallas / RedPallas commitment mode for post-quantum migration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PallasCommitmentKind {
    /// Direct Orchard spend-authorizing public key `ak = [ask] SpendAuthG` (`32 B` compressed).
    OrchardSpendAuthKey([u8; 32]),
    /// Rerandomized RedPallas action verification key `rk = ak + [alpha] SpendAuthG` (`32 B` compressed).
    OrchardRedPallasRk([u8; 32]),
}

impl PallasCommitmentKind {
    pub fn compressed_bytes(&self) -> &[u8; 32] {
        match self {
            Self::OrchardSpendAuthKey(b) | Self::OrchardRedPallasRk(b) => b,
        }
    }

    pub fn is_rerandomized(&self) -> bool {
        matches!(self, Self::OrchardRedPallasRk(_))
    }

    pub fn to_canonical_limbs56(&self) -> [u64; 6] {
        let (tag, b) = match *self {
            Self::OrchardSpendAuthKey(ak) => (5u64, ak),
            Self::OrchardRedPallasRk(rk) => (6u64, rk),
        };
        let l5 = pack_bytes32_to_limbs56(&b);
        [tag, l5[0], l5[1], l5[2], l5[3], l5[4]]
    }
}

/// Secret Orchard spend-authorizing witness `(ask, alpha)` with redacted `Debug` and volatile `Drop`.
pub struct PallasOwnershipWitness {
    ask_le: RedactedSecret<32>,
    alpha_le: Option<RedactedSecret<32>>,
}

impl fmt::Debug for PallasOwnershipWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PallasOwnershipWitness")
            .field("ask", &"<REDACTED>")
            .field("rerandomized", &self.alpha_le.is_some())
            .finish()
    }
}

impl PallasOwnershipWitness {
    /// Construct from a canonical nonzero Orchard spend-authorizing scalar `ask` (`1 <= ask < q`, LE bytes).
    pub fn from_spend_auth_scalar_le(ask_le: [u8; 32]) -> Option<Self> {
        let _ = FqPallas::from_nonzero_le_bytes(&ask_le)?;
        Some(Self {
            ask_le: RedactedSecret::new(ask_le),
            alpha_le: None,
        })
    }

    /// Construct a RedPallas rerandomized action witness `(ask, alpha)` for `rk = [ask + alpha] SpendAuthG`.
    pub fn from_rerandomized_le(ask_le: [u8; 32], alpha_le: [u8; 32]) -> Option<Self> {
        let ask = FqPallas::from_nonzero_le_bytes(&ask_le)?;
        let alpha = FqPallas::from_le_bytes(&alpha_le)?;
        let rsk = ask.add_mod(&alpha);
        if rsk.is_zero() {
            return None;
        }
        Some(Self {
            ask_le: RedactedSecret::new(ask_le),
            alpha_le: Some(RedactedSecret::new(alpha_le)),
        })
    }

    /// Compute direct spend-authorizing key `ak = [ask] SpendAuthG`.
    pub fn compute_spend_auth_key(&self) -> Option<PallasCommitmentKind> {
        let ask = FqPallas::from_nonzero_le_bytes(self.ask_le.expose())?;
        let pt = PallasPoint::spend_auth_mul_ct(&ask);
        let bytes = pt.to_compressed_bytes();
        if bytes == [0u8; 32] {
            return None;
        }
        Some(PallasCommitmentKind::OrchardSpendAuthKey(bytes))
    }

    /// Compute RedPallas rerandomized action key `rk = ak + [alpha] SpendAuthG = [ask + alpha] SpendAuthG`.
    pub fn compute_rerandomized_rk(&self) -> Option<PallasCommitmentKind> {
        let ask = FqPallas::from_nonzero_le_bytes(self.ask_le.expose())?;
        let alpha = match &self.alpha_le {
            Some(a) => FqPallas::from_le_bytes(a.expose())?,
            None => FqPallas::ZERO,
        };
        let rsk = ask.add_mod(&alpha);
        if rsk.is_zero() {
            return None;
        }
        let rk_pt = PallasPoint::spend_auth_mul_ct(&rsk);
        Some(PallasCommitmentKind::OrchardRedPallasRk(
            rk_pt.to_compressed_bytes(),
        ))
    }

    pub fn effective_scalar(&self, kind: &PallasCommitmentKind) -> Option<(FqPallas, FqPallas, FqPallas)> {
        let ask = FqPallas::from_nonzero_le_bytes(self.ask_le.expose())?;
        match kind {
            PallasCommitmentKind::OrchardSpendAuthKey(_) => {
                if self.alpha_le.is_some() {
                    return None;
                }
                let rsk = ask.clone();
                Some((ask, FqPallas::ZERO, rsk))
            }
            PallasCommitmentKind::OrchardRedPallasRk(_) => {
                let alpha = match &self.alpha_le {
                    Some(a) => FqPallas::from_le_bytes(a.expose())?,
                    None => FqPallas::ZERO,
                };
                let rsk = ask.add_mod(&alpha);
                if rsk.is_zero() {
                    return None;
                }
                Some((ask, alpha, rsk))
            }
        }
    }

    pub fn matches_commitment(&self, target: &PallasCommitmentKind) -> bool {
        let Some((_, _, rsk)) = self.effective_scalar(target) else {
            return false;
        };
        let pt = PallasPoint::spend_auth_mul_ct(&rsk);
        &pt.to_compressed_bytes() == target.compressed_bytes()
    }
}

/// Request for a Zcash Orchard `Pallas` / `RedPallas` post-quantum ownership migration proof.
#[derive(Clone, Debug)]
pub struct PallasMigrationRequest {
    pub commitment: PallasCommitmentKind,
    pub target: QsagAddress,
    pub epoch: u64,
    pub domain: [u8; 32],
}

/// Public statement of a Zcash Orchard `Pallas` / `RedPallas` PQ ownership migration proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PallasMigrationStatement {
    pub commitment: PallasCommitmentKind,
    pub target_pq_address: QsagAddress,
    pub epoch_anchor: u64,
    pub migration_domain: [u8; 32],
    pub migration_nullifier: [u64; 4],
}

impl PallasMigrationStatement {
    pub fn to_transcript_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(192);
        out.extend_from_slice(b"QSAG.PALLAS.MIGRATE.STMT.V1");
        out.extend_from_slice(&self.migration_domain);
        for l in self.commitment.to_canonical_limbs56() {
            out.extend_from_slice(&l.to_le_bytes());
        }
        out.extend_from_slice(&(self.target_pq_address.hrp.len() as u64).to_le_bytes());
        out.extend_from_slice(self.target_pq_address.hrp.as_bytes());
        out.push(self.target_pq_address.version as u8);
        out.extend_from_slice(&(self.target_pq_address.suite_tag as u16).to_be_bytes());
        out.push(self.target_pq_address.kind as u8);
        out.extend_from_slice(&self.target_pq_address.commitment_256);
        out.extend_from_slice(&self.epoch_anchor.to_le_bytes());
        for n in &self.migration_nullifier {
            out.extend_from_slice(&n.to_le_bytes());
        }
        out
    }
}

// ============================================================================
// Self-Contained Mixed-Domain (`GF(2)` + `Goldilocks` + `FpPallas`) ZKBoo Engine
// ============================================================================

type Wire = usize;
type Val4 = [u64; 4];
const ZERO4: Val4 = [0; 4];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PalDom {
    Bit,
    Gold,
    PallasFp,
}

impl PalDom {
    #[inline]
    fn byte_len(self) -> usize {
        match self {
            Self::Bit => 1,
            Self::Gold => 8,
            Self::PallasFp => 32,
        }
    }

    #[inline]
    fn canonical(self, x: Val4) -> bool {
        match self {
            Self::Bit => x[0] <= 1 && x[1] == 0 && x[2] == 0 && x[3] == 0,
            Self::Gold => x[0] < GOLDILOCKS_PRIME && x[1] == 0 && x[2] == 0 && x[3] == 0,
            Self::PallasFp => lt4(x, PALLAS_P),
        }
    }

    #[inline]
    fn add(self, a: Val4, b: Val4) -> Val4 {
        match self {
            Self::Bit => [(a[0] ^ b[0]) & 1, 0, 0, 0],
            Self::Gold => [gl_add(a[0], b[0]), 0, 0, 0],
            Self::PallasFp => add4_mod(a, b, PALLAS_P),
        }
    }

    #[inline]
    fn sub(self, a: Val4, b: Val4) -> Val4 {
        match self {
            Self::Bit => [(a[0] ^ b[0]) & 1, 0, 0, 0],
            Self::Gold => [gl_sub(a[0], b[0]), 0, 0, 0],
            Self::PallasFp => sub4_mod(a, b, PALLAS_P),
        }
    }

    #[inline]
    fn mul(self, a: Val4, b: Val4) -> Val4 {
        match self {
            Self::Bit => [(a[0] & b[0]) & 1, 0, 0, 0],
            Self::Gold => [gl_mul(a[0], b[0]), 0, 0, 0],
            Self::PallasFp => (FpPallas(a) * FpPallas(b)).0,
        }
    }
}

#[derive(Clone, Copy)]
enum PalOp {
    Input,
    Constant(Val4),
    Add(Wire, Wire),
    Sub(Wire, Wire),
    Scale(Wire, Val4),
    Mul(Wire, Wire),
    Lift(Wire, usize),
}

struct PalNode {
    domain: PalDom,
    op: PalOp,
    value: Val4,
}

impl Drop for PalNode {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.value);
    }
}

/// Mixed-domain ZKBoo circuit for Zcash Orchard `Pallas` / `RedPallas` ownership.
