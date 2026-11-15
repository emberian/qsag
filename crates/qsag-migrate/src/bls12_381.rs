//! Ethereum Beacon Validator (`BLS12-381` `G_1`) post-quantum ownership migration (`Π_bls381_migrate`).
//!
//! Curve parameters (IETF RFC 9380 / draft-irtf-cfrg-bls-signature / Ethereum Consensus Specs):
//! - Base field prime (`381` bits, `p ≡ 3 (mod 4)`):
//!   `p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab`
//! - Prime subgroup order (`255` bits):
//!   `r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`
//! - Curve equation: `E(F_p) : y^2 = x^3 + 4` (`a = 0, b = 4, 3b = 12`), `G_1 = E(F_p)[r]`.
//!
//! Supports two validator post-quantum migration modes into Beam Chain (`Hem` / `Jorts` / `QSAG`) keys:
//! 1. `BeaconValidatorPubkey([u8; 48])`: proves knowledge of `sk ∈ [1, r - 1]` with `pk = [sk] G_1`
//!    bound to `validator_index`, `withdrawal_credentials` (`0x01` 32 ETH or `0x02` EIP-7251 2048 ETH
//!    compounding credentials), and `target_pq_address` using 438-repetition mixed-domain ZKBoo
//!    without emitting any pairing-friendly BLS signature.
//! 2. `UnrevealedBls0x00Credential([u8; 32])`: proves knowledge of `sk ∈ [1, r - 1]` whose compressed
//!    48-byte `G_1` public key hashes to `0x00 || SHA256(pk_48)[1..32]` **without ever revealing
//!    `pk_48` on-chain**, protecting legacy `0x00` validators against quantum harvest-now-decrypt-later.

use alloc::vec::Vec;
use core::cell::RefCell;
use core::fmt;

use qsag_accel::{
    AcceleratorBackend,
    ct::{RedactedSecret, ct_eq_u64, ct_select_u64, ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::{GOLDILOCKS_PRIME, gl_add, gl_mul, gl_sub, pack_bytes32_to_limbs56},
    keccak::{InterleavedTranscript, cshake256_framed_32},
    poseidon2::{POSEIDON2_CONST_IV, poseidon2_const_at, poseidon2_hash_limbs},
    sha2::sha256,
};
use qsag_addr::QsagAddress;

use crate::{
    scalar::NULLIFIER_DOMAIN,
    zk_engine::{
        MIT_REPETITIONS, MigrateError, MigrationZkProof, OpenedRepetitionView, PartyView,
        challenges, rep_root,
    },
};

/// `BLS12-381` base field modulus `p` (`381` bits, little-endian `u64` limbs).
pub const BLS_P: [u64; 6] = [
    0xb9fe_ffff_ffff_aaab,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

const BLS_P_MINUS_2: [u64; 6] = [
    0xb9fe_ffff_ffff_aaa9,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

/// `-p[0]^{-1} mod 2^64` for 6-limb CIOS Montgomery reduction over `F_p`.
const BLS_P_INV: u64 = 0x89f3_fffc_fffc_fffd;

/// `R^2 mod p` for `R = 2^384`.
const BLS_P_R2: [u64; 6] = [
    0xf4df_1f34_1c34_1746,
    0x0a76_e6a6_09d1_04f1,
    0x8de5_476c_4c95_b6d5,
    0x67eb_88a9_939d_83c0,
    0x9a79_3e85_b519_952d,
    0x1198_8fe5_92ca_e3aa,
];

/// `(p + 1) / 4` for constant-time square roots when `p ≡ 3 (mod 4)`.
const BLS_P_PLUS_1_DIV_4: [u64; 6] = [
    0xee7f_bfff_ffff_eaab,
    0x07aa_ffff_ac54_ffff,
    0xd9cc_34a8_3dac_3d89,
    0xd91d_d2e1_3ce1_44af,
    0x92c6_e9ed_90d2_eb35,
    0x0680_447a_8e5f_f9a6,
];

/// `(p + 1) / 2`: `y` is lexicographically larger than `-y mod p` iff `y >= (p + 1) / 2`.
const BLS_P_HALF_CEIL: [u64; 6] = [
    0xdcff_7fff_ffff_d556,
    0x0f55_ffff_58a9_ffff,
    0xb398_6950_7b58_7b12,
    0xb23b_a5c2_79c2_895f,
    0x258d_d3db_21a5_d66b,
    0x0d00_88f5_1cbf_f34d,
];

/// `BLS12-381` prime subgroup order `r` (`255` bits, little-endian `u64` limbs).
pub const BLS_R: [u64; 4] = [
    0xffff_ffff_0000_0001,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
];

const BLS_R_MINUS_2: [u64; 4] = [
    0xffff_fffe_ffff_ffff,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
];

const BLS_R_INV: u64 = 0xffff_fffe_ffff_ffff;

const BLS_R_R2: [u64; 4] = [
    0xc999_e990_f3f2_9c6d,
    0x2b6c_edcb_8792_5c23,
    0x05d3_1496_7254_398f,
    0x0748_d9d9_9f59_ff11,
];

/// `G_1` cofactor `h_1 = (x_0 - 1)^2 / 3 = 0x396c8c005555e1568c00aaab0000aaab`.
pub const BLS_G1_COFACTOR: [u64; 2] = [0x8c00_aaab_0000_aaab, 0x396c_8c00_5555_e156];

/// Official IETF / Ethereum Beacon `G_1` affine generator `x` coordinate (`LE` limbs).
pub const BLS_G1_GX: [u64; 6] = [
    0xfb3a_f00a_db22_c6bb,
    0x6c55_e83f_f97a_1aef,
    0xa14e_3a3f_171b_ac58,
    0xc368_8c4f_9774_b905,
    0x2695_638c_4fa9_ac0f,
    0x17f1_d3a7_3197_d794,
];

/// Official IETF / Ethereum Beacon `G_1` affine generator `y` coordinate (`LE` limbs).
pub const BLS_G1_GY: [u64; 6] = [
    0x0caa_2329_46c5_e7e1,
    0xd03c_c744_a288_8ae4,
    0x00db_18cb_2c04_b3ed,
    0xfcf5_e095_d5d0_0af6,
    0xa09e_30ed_741d_8ae4,
    0x08b3_f481_e3aa_a0f1,
];

/// Subgroup tag separating `BLS12-381` validator scalars from `secp256k1` (1), `Ed25519` (2), and `Pallas` (3, 4).
pub const NULLIFIER_TAG_BLS12_381_G1: u64 = 5;

#[inline]
fn sub6_borrow(a: [u64; 6], b: [u64; 6]) -> ([u64; 6], bool) {
    let mut out = [0u64; 6];
    let mut br = 0u64;
    for i in 0..6 {
        let (d1, b1) = a[i].overflowing_sub(b[i]);
        let (d2, b2) = d1.overflowing_sub(br);
        out[i] = d2;
        br = (b1 as u64) | (b2 as u64);
    }
    (out, br != 0)
}

#[inline]
fn lt6(a: [u64; 6], b: [u64; 6]) -> bool {
    sub6_borrow(a, b).1
}

#[inline]
fn select6(choice: bool, t: [u64; 6], f: [u64; 6]) -> [u64; 6] {
    [
        ct_select_u64(choice, t[0], f[0]),
        ct_select_u64(choice, t[1], f[1]),
        ct_select_u64(choice, t[2], f[2]),
        ct_select_u64(choice, t[3], f[3]),
        ct_select_u64(choice, t[4], f[4]),
        ct_select_u64(choice, t[5], f[5]),
    ]
}

#[inline]
fn add6_mod(a: [u64; 6], b: [u64; 6], m: [u64; 6]) -> [u64; 6] {
    let mut sum = [0u64; 6];
    let mut carry = 0u128;
    for i in 0..6 {
        let cur = (a[i] as u128) + (b[i] as u128) + carry;
        sum[i] = cur as u64;
        carry = cur >> 64;
    }
    let (diff, borrow) = sub6_borrow(sum, m);
    select6((carry != 0) | !borrow, diff, sum)
}

#[inline]
fn sub6_mod(a: [u64; 6], b: [u64; 6], m: [u64; 6]) -> [u64; 6] {
    let (diff, borrow) = sub6_borrow(a, b);
    let mut out = [0u64; 6];
    let mut carry = 0u128;
    for i in 0..6 {
        let addend = ct_select_u64(borrow, m[i], 0);
        let cur = (diff[i] as u128) + (addend as u128) + carry;
        out[i] = cur as u64;
        carry = cur >> 64;
    }
    out
}

/// Constant-time 6-limb CIOS Montgomery product `a * b * 2^-384 mod m` (`m < 2^383`).
#[inline]
fn cios_mont_mul6(a: [u64; 6], b: [u64; 6], m: [u64; 6], inv: u64) -> [u64; 6] {
    let mut t = [0u64; 8];
    for i in 0..6 {
        let mut carry = 0u128;
        for j in 0..6 {
            let cur = (t[j] as u128) + (a[i] as u128) * (b[j] as u128) + carry;
            t[j] = cur as u64;
            carry = cur >> 64;
        }
        let cur = (t[6] as u128) + carry;
        t[6] = cur as u64;
        t[7] = (cur >> 64) as u64;

        let u = t[0].wrapping_mul(inv);
        let cur0 = (t[0] as u128) + (u as u128) * (m[0] as u128);
        let mut carry2 = cur0 >> 64;
        for j in 1..6 {
            let curj = (t[j] as u128) + (u as u128) * (m[j] as u128) + carry2;
            t[j - 1] = curj as u64;
            carry2 = curj >> 64;
        }
        let cur6 = (t[6] as u128) + carry2;
        t[5] = cur6 as u64;
        t[6] = t[7].wrapping_add((cur6 >> 64) as u64);
        t[7] = 0;
    }
    let raw = [t[0], t[1], t[2], t[3], t[4], t[5]];
    let (diff, borrow) = sub6_borrow(raw, m);
    select6((t[6] != 0) | !borrow, diff, raw)
}

#[inline]
fn pow6_ct(base: [u64; 6], exp: [u64; 6]) -> [u64; 6] {
    let mut b_m = cios_mont_mul6(base, BLS_P_R2, BLS_P, BLS_P_INV);
    let mut acc_m = cios_mont_mul6([1, 0, 0, 0, 0, 0], BLS_P_R2, BLS_P, BLS_P_INV);
    for limb in exp {
        for bit in 0..64 {
            let take = ((limb >> bit) & 1) == 1;
            let prod = cios_mont_mul6(acc_m, b_m, BLS_P, BLS_P_INV);
            acc_m = select6(take, prod, acc_m);
            b_m = cios_mont_mul6(b_m, b_m, BLS_P, BLS_P_INV);
        }
    }
    cios_mont_mul6(acc_m, [1, 0, 0, 0, 0, 0], BLS_P, BLS_P_INV)
}

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
fn decode6_le(bytes: &[u8; 48]) -> [u64; 6] {
    core::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}

#[inline]
fn encode6_le(limbs: [u64; 6]) -> [u8; 48] {
    let mut out = [0u8; 48];
    for (i, limb) in limbs.into_iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
    }
    out
}

/// Canonical element of the `BLS12-381` base field `F_p` (`0 <= self < p`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FpBls381(pub [u64; 6]);

impl FpBls381 {
    pub const ZERO: Self = Self([0; 6]);
    pub const ONE: Self = Self([1, 0, 0, 0, 0, 0]);
    pub const B: Self = Self([4, 0, 0, 0, 0, 0]);
    /// `3 * b = 12` for `y^2 = x^3 + 4`.
    pub const B3: Self = Self([12, 0, 0, 0, 0, 0]);

    pub fn from_le_bytes(bytes: &[u8; 48]) -> Option<Self> {
        let limbs = decode6_le(bytes);
        if lt6(limbs, BLS_P) {
            Some(Self(limbs))
        } else {
            None
        }
    }

    pub fn from_be_bytes(bytes: &[u8; 48]) -> Option<Self> {
        let mut le = *bytes;
        le.reverse();
        Self::from_le_bytes(&le)
    }

    pub fn to_le_bytes(self) -> [u8; 48] {
        encode6_le(self.0)
    }

    pub fn to_be_bytes(self) -> [u8; 48] {
        let mut out = self.to_le_bytes();
        out.reverse();
        out
    }

    #[inline]
    pub fn ct_select(choice: bool, t: Self, f: Self) -> Self {
        Self(select6(choice, t.0, f.0))
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        ct_eq_u64(
            self.0[0] | self.0[1] | self.0[2] | self.0[3] | self.0[4] | self.0[5],
            0,
        )
    }

    /// IETF / Zcash `BLS12-381` `A_flag`: returns `true` iff `self > -self mod p` (`self >= (p + 1) / 2`).
    #[inline]
    pub fn lexicographically_largest(self) -> bool {
        !lt6(self.0, BLS_P_HALF_CEIL)
    }

    #[inline]
    pub fn add_mod(self, rhs: Self) -> Self {
        Self(add6_mod(self.0, rhs.0, BLS_P))
    }

    #[inline]
    pub fn sub_mod(self, rhs: Self) -> Self {
        Self(sub6_mod(self.0, rhs.0, BLS_P))
    }

    #[inline]
    pub fn neg_mod(self) -> Self {
        Self::ZERO.sub_mod(self)
    }

    #[inline]
    pub fn mul_mod(self, rhs: Self) -> Self {
        let m1 = cios_mont_mul6(self.0, rhs.0, BLS_P, BLS_P_INV);
        Self(cios_mont_mul6(m1, BLS_P_R2, BLS_P, BLS_P_INV))
    }

    #[inline]
    pub fn sq(self) -> Self {
        self.mul_mod(self)
    }

    /// Constant-time Fermat inversion `a^(p - 2) mod p` (`0 -> 0`).
    pub fn inv_or_zero(self) -> Self {
        Self(pow6_ct(self.0, BLS_P_MINUS_2))
    }

    /// Constant-time square root `a^((p + 1) / 4) mod p` (`p ≡ 3 (mod 4)`).
    pub fn sqrt_ct(self) -> Option<Self> {
        let cand = Self(pow6_ct(self.0, BLS_P_PLUS_1_DIV_4));
        if cand.sq() == self {
            Some(cand)
        } else {
            None
        }
    }
}

impl core::ops::Add for FpBls381 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.add_mod(rhs)
    }
}
impl core::ops::Sub for FpBls381 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.sub_mod(rhs)
    }
}
impl core::ops::Mul for FpBls381 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.mul_mod(rhs)
    }
}
impl core::ops::Neg for FpBls381 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.neg_mod()
    }
}

/// Canonical `BLS12-381` scalar `0 <= sk < r`, zeroized on `Drop`.
#[derive(Clone, PartialEq, Eq)]
pub struct FrBls381(pub [u64; 4]);

impl fmt::Debug for FrBls381 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("FrBls381").field(&"<REDACTED>").finish()
    }
}

impl Drop for FrBls381 {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
}

impl FrBls381 {
    pub const ZERO: Self = Self([0; 4]);
    pub const ONE: Self = Self([1, 0, 0, 0]);

    pub fn from_le_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let mut limbs = crate::scalar::decode(bytes);
        if lt4(limbs, BLS_R) {
            Some(Self(limbs))
        } else {
            ct_zeroize_u64s(&mut limbs);
            None
        }
    }

    pub fn from_be_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let mut le = *bytes;
        le.reverse();
        let out = Self::from_le_bytes(&le);
        ct_zeroize_bytes(&mut le);
        out
    }

    /// Parse an IETF / EIP-2333 big-endian `BLS12-381` secret scalar `sk ∈ [1, r - 1]`.
    pub fn from_nonzero_be_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let s = Self::from_be_bytes(bytes)?;
        if s.is_zero() { None } else { Some(s) }
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
        Self(add4_mod(self.0, rhs.0, BLS_R))
    }

    #[inline]
    pub fn sub_mod(&self, rhs: &Self) -> Self {
        Self(sub4_mod(self.0, rhs.0, BLS_R))
    }

    #[inline]
    pub fn mul_mod(&self, rhs: &Self) -> Self {
        let m1 = cios_mont_mul4(self.0, rhs.0, BLS_R, BLS_R_INV);
        Self(cios_mont_mul4(m1, BLS_R_R2, BLS_R, BLS_R_INV))
    }

    pub fn inv_or_zero(&self) -> Self {
        let mut b_m = cios_mont_mul4(self.0, BLS_R_R2, BLS_R, BLS_R_INV);
        let mut acc_m = cios_mont_mul4([1, 0, 0, 0], BLS_R_R2, BLS_R, BLS_R_INV);
        for limb in BLS_R_MINUS_2 {
            for bit in 0..64 {
                let take = ((limb >> bit) & 1) == 1;
                let prod = cios_mont_mul4(acc_m, b_m, BLS_R, BLS_R_INV);
                acc_m = select4(take, prod, acc_m);
                b_m = cios_mont_mul4(b_m, b_m, BLS_R, BLS_R_INV);
            }
        }
        Self(cios_mont_mul4(acc_m, [1, 0, 0, 0], BLS_R, BLS_R_INV))
    }

    pub fn compute_nullifier(&self, migration_domain: &[u8; 32]) -> [u64; 4] {
        let mut be = self.to_be_bytes();
        let mut limbs = pack_bytes32_to_limbs56(&be);
        ct_zeroize_bytes(&mut be);
        let dom = pack_bytes32_to_limbs56(migration_domain);
        let mut input = [0u64; 11];
        input[0] = NULLIFIER_TAG_BLS12_381_G1;
        input[1..6].copy_from_slice(&limbs);
        input[6..11].copy_from_slice(&dom);
        ct_zeroize_u64s(&mut limbs);
        let out = poseidon2_hash_limbs(NULLIFIER_DOMAIN, &input);
        ct_zeroize_u64s(&mut input);
        out
    }
}

/// Homogeneous projective point `(X : Y : Z)` on `BLS12-381` `E(F_p) : y^2 = x^3 + 4`.
#[derive(Clone, Debug)]
pub struct BlsG1Point {
    pub x: FpBls381,
    pub y: FpBls381,
    pub z: FpBls381,
}

impl Drop for BlsG1Point {
    fn drop(&mut self) {
        self.wipe();
    }
}

impl BlsG1Point {
    pub const IDENTITY: Self = Self {
        x: FpBls381::ZERO,
        y: FpBls381::ONE,
        z: FpBls381::ZERO,
    };

    /// Official IETF / Ethereum Beacon `G_1` generator of prime order `r`.
    pub const GENERATOR: Self = Self {
        x: FpBls381(BLS_G1_GX),
        y: FpBls381(BLS_G1_GY),
        z: FpBls381::ONE,
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
        // Homogeneous check: Y^2 * Z == X^3 + 4 * Z^3
        let z2 = self.z.sq();
        let z3 = z2 * self.z;
        let lhs = self.y.sq() * self.z;
        let rhs = self.x.sq() * self.x + FpBls381::B * z3;
        lhs == rhs
    }

    #[inline]
    pub fn ct_cswap(swap: bool, a: &mut Self, b: &mut Self) {
        let nx = FpBls381::ct_select(swap, b.x, a.x);
        let bx = FpBls381::ct_select(swap, a.x, b.x);
        let ny = FpBls381::ct_select(swap, b.y, a.y);
        let by = FpBls381::ct_select(swap, a.y, b.y);
        let nz = FpBls381::ct_select(swap, b.z, a.z);
        let bz = FpBls381::ct_select(swap, a.z, b.z);
        a.x = nx;
        a.y = ny;
        a.z = nz;
        b.x = bx;
        b.y = by;
        b.z = bz;
    }

    /// Complete exception-free Renes-Costello-Batina (2016) Algorithm 7 addition for `a = 0, 3b = 12`.
    pub fn complete_add(&self, other: &Self) -> Self {
        let mut t0 = self.x * other.x;
        let mut t1 = self.y * other.y;
        let mut t2 = self.z * other.z;
        let t3 = (self.x + self.y) * (other.x + other.y) - (t0 + t1);
        let t4 = (self.y + self.z) * (other.y + other.z) - (t1 + t2);
        let mut y3 = (self.x + self.z) * (other.x + other.z) - (t0 + t2);

        t0 = (t0 + t0) + t0;
        t2 = FpBls381::B3 * t2;
        let mut z3 = t1 + t2;
        t1 = t1 - t2;
        y3 = FpBls381::B3 * y3;

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

    /// Constant-time Montgomery ladder `[k] self` over little-endian `u64` limbs.
    pub fn scalar_mul_limbs_ct(&self, limbs_le: &[u64]) -> Self {
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

    pub fn scalar_mul_ct(&self, scalar: &FrBls381) -> Self {
        self.scalar_mul_limbs_ct(&scalar.0)
    }

    pub fn generator_mul_ct(scalar: &FrBls381) -> Self {
        Self::GENERATOR.scalar_mul_ct(scalar)
    }

    /// Clear the `G_1` cofactor `[h_1] P` (`h_1 = (x_0 - 1)^2 / 3`).
    pub fn clear_cofactor(&self) -> Self {
        self.scalar_mul_limbs_ct(&BLS_G1_COFACTOR)
    }

    /// Returns `true` iff `self` lies on `E(F_p)` and inside the prime-order subgroup `G_1 = E(F_p)[r]`.
    pub fn is_in_g1_subgroup(&self) -> bool {
        self.is_on_curve() && self.scalar_mul_limbs_ct(&BLS_R).is_identity()
    }

    pub fn to_affine(&self) -> Option<(FpBls381, FpBls381)> {
        if self.z.is_zero() {
            return None;
        }
        let z_inv = self.z.inv_or_zero();
        Some((self.x * z_inv, self.y * z_inv))
    }

    /// Canonical 48-byte Zcash / IETF / Ethereum Beacon `G_1` compressed encoding (`C_flag = 1`).
    pub fn to_compressed_48(&self) -> [u8; 48] {
        let Some((x, y)) = self.to_affine() else {
            let mut inf = [0u8; 48];
            inf[0] = 0xc0;
            return inf;
        };
        let mut out = x.to_be_bytes();
        out[0] |= 0x80 | ((y.lexicographically_largest() as u8) << 5);
        out
    }

    /// Decode a canonical 48-byte compressed `G_1` point (including `0xc000...00` = `O`),
    /// enforcing `C_flag == 1`, canonical `x < p`, curve membership, and prime subgroup `[r] P = O`.
    pub fn from_compressed_48(bytes: &[u8; 48]) -> Option<Self> {
        let flags = bytes[0] & 0xe0;
        let c_flag = (flags & 0x80) != 0;
        let b_flag = (flags & 0x40) != 0;
        let a_flag = (flags & 0x20) != 0;
        if !c_flag {
            return None;
        }
        if b_flag {
            if a_flag || (bytes[0] & 0x1f) != 0 || bytes[1..].iter().any(|&b| b != 0) {
                return None;
            }
            return Some(Self::IDENTITY);
        }
        let mut x_be = *bytes;
        x_be[0] &= 0x1f;
        let x = FpBls381::from_be_bytes(&x_be)?;
        let rhs = x.sq() * x + FpBls381::B;
        let y0 = rhs.sqrt_ct()?;
        if y0.is_zero() && a_flag {
            return None;
        }
        let y = FpBls381::ct_select(y0.lexicographically_largest() ^ a_flag, -y0, y0);
        let pt = Self {
            x,
            y,
            z: FpBls381::ONE,
        };
        if pt.is_in_g1_subgroup() {
            Some(pt)
        } else {
            None
        }
    }

    /// Decode an active Ethereum Beacon validator 48-byte compressed `G_1` public key (rejecting `O` and non-`G_1` torsion points).
    pub fn from_validator_pubkey_48(bytes: &[u8; 48]) -> Option<Self> {
        let pt = Self::from_compressed_48(bytes)?;
        if pt.is_identity() { None } else { Some(pt) }
    }
}

impl PartialEq for BlsG1Point {
    fn eq(&self, other: &Self) -> bool {
        match (self.z.is_zero(), other.z.is_zero()) {
            (true, true) => true,
            (true, false) | (false, true) => false,
            (false, false) => {
                (self.x * other.z == other.x * self.z) && (self.y * other.z == other.y * self.z)
            }
        }
    }
}
impl Eq for BlsG1Point {}

/// Compute Ethereum Beacon Chain `0x00` `BLS_WITHDRAWAL_PREFIX` credential `0x00 || SHA256(pk_48)[1..32]`.
pub fn compute_bls_0x00_withdrawal_credentials(pubkey_48: &[u8; 48]) -> [u8; 32] {
    let mut out = sha256(pubkey_48);
    out[0] = 0x00;
    out
}

/// Ethereum Beacon validator `BLS12-381` target commitment for post-quantum Beam Chain migration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BlsValidatorCommitment {
    /// Active Beacon Chain 48-byte compressed `G_1` validator public key (`32 ETH` `0x01` or `2048 ETH` `0x02` stake).
    BeaconValidatorPubkey([u8; 48]),
    /// Unrevealed legacy `0x00` `BLS_WITHDRAWAL_PREFIX` credential (`0x00 || SHA256(pk_48)[1..32]`),
    /// proved in zero knowledge without ever exposing `pk_48` on-chain.
    UnrevealedBls0x00Credential([u8; 32]),
}

impl BlsValidatorCommitment {
    pub fn write_transcript(&self, out: &mut Vec<u8>) {
        match self {
            Self::BeaconValidatorPubkey(pk) => {
                out.push(1);
                out.extend_from_slice(pk);
            }
            Self::UnrevealedBls0x00Credential(cred) => {
                out.push(2);
                out.extend_from_slice(cred);
            }
        }
    }
}

/// Secret Ethereum Beacon validator `BLS12-381` scalar witness (`sk ∈ [1, r - 1]`) with redacted `Debug` and volatile `Drop`.
pub struct BlsOwnershipWitness {
    sk_be: RedactedSecret<32>,
}

impl fmt::Debug for BlsOwnershipWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BlsOwnershipWitness")
            .field("sk", &"<REDACTED>")
            .finish()
    }
}

impl BlsOwnershipWitness {
    /// Construct from an IETF / EIP-2333 big-endian 32-byte `BLS12-381` secret key `sk ∈ [1, r - 1]`.
    pub fn from_secret_scalar_be(sk_be: [u8; 32]) -> Option<Self> {
        let _ = FrBls381::from_nonzero_be_bytes(&sk_be)?;
        Some(Self {
            sk_be: RedactedSecret::new(sk_be),
        })
    }

    /// Construct from a little-endian 32-byte `BLS12-381` secret key `sk ∈ [1, r - 1]`.
    pub fn from_secret_scalar_le(mut sk_le: [u8; 32]) -> Option<Self> {
        sk_le.reverse();
        let res = Self::from_secret_scalar_be(sk_le);
        ct_zeroize_bytes(&mut sk_le);
        res
    }

    pub fn scalar(&self) -> Option<FrBls381> {
        FrBls381::from_nonzero_be_bytes(self.sk_be.expose())
    }

    /// Derive the 48-byte compressed `G_1` validator public key `[sk] G_1`.
    pub fn compute_validator_pubkey_48(&self) -> Option<[u8; 48]> {
        let sk = self.scalar()?;
        let pt = BlsG1Point::generator_mul_ct(&sk);
        if pt.is_identity() {
            return None;
        }
        Some(pt.to_compressed_48())
    }

    pub fn compute_beacon_commitment(&self) -> Option<BlsValidatorCommitment> {
        self.compute_validator_pubkey_48()
            .map(BlsValidatorCommitment::BeaconValidatorPubkey)
    }

    /// Derive the unrevealed `0x00 || SHA256(pk_48)[1..32]` withdrawal credential commitment.
    pub fn compute_unrevealed_0x00_commitment(&self) -> Option<BlsValidatorCommitment> {
        let mut pk = self.compute_validator_pubkey_48()?;
        let cred = compute_bls_0x00_withdrawal_credentials(&pk);
        ct_zeroize_bytes(&mut pk);
        Some(BlsValidatorCommitment::UnrevealedBls0x00Credential(cred))
    }

    pub fn matches_commitment(&self, commitment: &BlsValidatorCommitment) -> bool {
        let Some(mut pk) = self.compute_validator_pubkey_48() else {
            return false;
        };
        let ok = match commitment {
            BlsValidatorCommitment::BeaconValidatorPubkey(expected) => &pk == expected,
            BlsValidatorCommitment::UnrevealedBls0x00Credential(cred) => {
                cred[0] == 0x00 && &compute_bls_0x00_withdrawal_credentials(&pk) == cred
            }
        };
        ct_zeroize_bytes(&mut pk);
        ok
    }
}

/// Request for an Ethereum Beacon validator `BLS12-381` post-quantum ownership migration proof.
#[derive(Clone, Debug)]
pub struct BlsMigrationRequest {
    pub commitment: BlsValidatorCommitment,
    pub validator_index: u64,
    pub withdrawal_credentials: [u8; 32],
    pub target: QsagAddress,
    pub epoch: u64,
    pub domain: [u8; 32],
}

/// Public statement of an Ethereum Beacon validator `BLS12-381` PQ Beam Chain migration proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlsMigrationStatement {
    pub commitment: BlsValidatorCommitment,
    pub validator_index: u64,
    pub withdrawal_credentials: [u8; 32],
    pub target_pq_address: QsagAddress,
    pub epoch_anchor: u64,
    pub migration_domain: [u8; 32],
    pub migration_nullifier: [u64; 4],
}

impl BlsMigrationStatement {
    pub fn credentials_consistent(&self) -> bool {
        match &self.commitment {
            BlsValidatorCommitment::BeaconValidatorPubkey(_) => {
                matches!(self.withdrawal_credentials[0], 0x00..=0x02)
            }
            BlsValidatorCommitment::UnrevealedBls0x00Credential(cred) => {
                cred[0] == 0x00 && &self.withdrawal_credentials == cred
            }
        }
    }

    pub fn to_transcript_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(256);
        out.extend_from_slice(b"QSAG.BLS12_381.MIGRATE.STMT.V1");
        out.extend_from_slice(&self.migration_domain);
        self.commitment.write_transcript(&mut out);
        out.extend_from_slice(&self.validator_index.to_le_bytes());
        out.extend_from_slice(&self.withdrawal_credentials);
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
// Self-Contained Mixed-Domain (`GF(2)` + `Goldilocks` + `FpBls381`) ZKBoo Engine
// ============================================================================

type Wire = usize;
type Val6 = [u64; 6];
const ZERO6: Val6 = [0; 6];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BlsDom {
    Bit,
    Gold,
    BlsFp,
}

impl BlsDom {
    #[inline]
    fn byte_len(self) -> usize {
        match self {
            Self::Bit => 1,
            Self::Gold => 8,
            Self::BlsFp => 48,
        }
    }

    #[inline]
    fn canonical(self, x: Val6) -> bool {
        match self {
            Self::Bit => {
                x[0] <= 1 && x[1] == 0 && x[2] == 0 && x[3] == 0 && x[4] == 0 && x[5] == 0
            }
            Self::Gold => {
                x[0] < GOLDILOCKS_PRIME
                    && x[1] == 0
                    && x[2] == 0
                    && x[3] == 0
                    && x[4] == 0
                    && x[5] == 0
            }
            Self::BlsFp => lt6(x, BLS_P),
        }
    }

    #[inline]
    fn add(self, a: Val6, b: Val6) -> Val6 {
        match self {
            Self::Bit => [(a[0] ^ b[0]) & 1, 0, 0, 0, 0, 0],
            Self::Gold => [gl_add(a[0], b[0]), 0, 0, 0, 0, 0],
            Self::BlsFp => add6_mod(a, b, BLS_P),
        }
    }

    #[inline]
    fn sub(self, a: Val6, b: Val6) -> Val6 {
        match self {
            Self::Bit => [(a[0] ^ b[0]) & 1, 0, 0, 0, 0, 0],
            Self::Gold => [gl_sub(a[0], b[0]), 0, 0, 0, 0, 0],
            Self::BlsFp => sub6_mod(a, b, BLS_P),
        }
    }

    #[inline]
    fn mul(self, a: Val6, b: Val6) -> Val6 {
        match self {
            Self::Bit => [(a[0] & b[0]) & 1, 0, 0, 0, 0, 0],
            Self::Gold => [gl_mul(a[0], b[0]), 0, 0, 0, 0, 0],
            Self::BlsFp => (FpBls381(a) * FpBls381(b)).0,
        }
    }
}

#[derive(Clone, Copy)]
enum BlsOp {
    Input,
    Constant(Val6),
    Add(Wire, Wire),
    Sub(Wire, Wire),
    Scale(Wire, Val6),
    Mul(Wire, Wire),
    Lift(Wire, usize),
}

struct BlsNode {
    domain: BlsDom,
    op: BlsOp,
    value: Val6,
}

impl Drop for BlsNode {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.value);
    }
}

/// Mixed-domain ZKBoo circuit for Ethereum Beacon validator `BLS12-381` ownership.
