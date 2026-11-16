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
use core::fmt;

use qsag_accel::{
    AcceleratorBackend,
    ct::{RedactedSecret, ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::{GOLDILOCKS_PRIME, pack_bytes32_to_limbs56},
    keccak::{InterleavedTranscript, cshake256_framed_32},
    poseidon2::poseidon2_hash_limbs,
    sha2::sha256,
};
use qsag_addr::QsagAddress;

use crate::{
    boolean_hash,
    circuit::{Builder, Circuit, Domain, Wire, ZERO, lift4},
    limbs,
    ownership::{big_endian, pack56, sponge},
    scalar::NULLIFIER_DOMAIN,
    zk_engine::{
        MIT_REPETITIONS, MigrateError, MigrationZkProof, OpenedRepetitionView, Wires, challenges,
        rep_root, replay_with_scratch, simulate,
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

/// Canonical element of the `BLS12-381` base field `F_p` (`0 <= self < p`).
#[derive(Clone, Copy, Debug, Eq)]
pub struct FpBls381(pub [u64; 6]);

impl PartialEq for FpBls381 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        limbs::ct_eq(self.0, other.0)
    }
}

impl FpBls381 {
    pub const ZERO: Self = Self([0; 6]);
    pub const ONE: Self = Self([1, 0, 0, 0, 0, 0]);
    pub const B: Self = Self([4, 0, 0, 0, 0, 0]);
    /// `3 * b = 12` for `y^2 = x^3 + 4`.
    pub const B3: Self = Self([12, 0, 0, 0, 0, 0]);

    fn from_limbs(value: [u64; 6]) -> Option<Self> {
        if limbs::lt(value, BLS_P) {
            Some(Self(value))
        } else {
            None
        }
    }

    pub fn from_le_bytes(bytes: &[u8; 48]) -> Option<Self> {
        Self::from_limbs(limbs::from_le_bytes(bytes))
    }

    pub fn from_be_bytes(bytes: &[u8; 48]) -> Option<Self> {
        Self::from_limbs(limbs::from_be_bytes(bytes))
    }

    pub fn to_le_bytes(self) -> [u8; 48] {
        limbs::to_le_bytes(self.0)
    }

    pub fn to_be_bytes(self) -> [u8; 48] {
        limbs::to_be_bytes(self.0)
    }

    #[inline]
    pub fn ct_select(choice: bool, t: Self, f: Self) -> Self {
        Self(limbs::ct_select(choice, t.0, f.0))
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        limbs::is_zero(self.0)
    }

    /// IETF / Zcash `BLS12-381` `A_flag`: returns `true` iff `self > -self mod p` (`self >= (p + 1) / 2`).
    #[inline]
    pub fn lexicographically_largest(self) -> bool {
        !limbs::lt(self.0, BLS_P_HALF_CEIL)
    }

    #[inline]
    pub fn add_mod(self, rhs: Self) -> Self {
        Self(limbs::add_mod(self.0, rhs.0, BLS_P))
    }

    #[inline]
    pub fn sub_mod(self, rhs: Self) -> Self {
        Self(limbs::sub_mod(self.0, rhs.0, BLS_P))
    }

    #[inline]
    pub fn neg_mod(self) -> Self {
        Self(limbs::neg_mod(self.0, BLS_P))
    }

    #[inline]
    pub fn mul_mod(self, rhs: Self) -> Self {
        let m1 = limbs::mont_mul(self.0, rhs.0, BLS_P, BLS_P_INV);
        Self(limbs::mont_mul(m1, BLS_P_R2, BLS_P, BLS_P_INV))
    }

    #[inline]
    pub fn sq(self) -> Self {
        self.mul_mod(self)
    }

    #[inline]
    fn pow_ct(base: [u64; 6], exp: [u64; 6]) -> [u64; 6] {
        limbs::mont_pow(base, exp, BLS_P, BLS_P_INV, BLS_P_R2)
    }

    /// Constant-time Fermat inversion `a^(p - 2) mod p` (`0 -> 0`).
    pub fn inv_or_zero(self) -> Self {
        Self(Self::pow_ct(self.0, BLS_P_MINUS_2))
    }

    /// Constant-time square root `a^((p + 1) / 4) mod p` (`p ≡ 3 (mod 4)`).
    pub fn sqrt_ct(self) -> Option<Self> {
        let cand = Self(Self::pow_ct(self.0, BLS_P_PLUS_1_DIV_4));
        if cand.sq() == self { Some(cand) } else { None }
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
#[derive(Clone, Eq)]
pub struct FrBls381(pub [u64; 4]);

impl PartialEq for FrBls381 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        limbs::ct_eq(self.0, other.0)
    }
}

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

    fn from_limbs(mut value: [u64; 4]) -> Option<Self> {
        if limbs::lt(value, BLS_R) {
            Some(Self(value))
        } else {
            ct_zeroize_u64s(&mut value);
            None
        }
    }

    pub fn from_le_bytes(bytes: &[u8; 32]) -> Option<Self> {
        Self::from_limbs(limbs::from_le_bytes(bytes))
    }

    pub fn from_be_bytes(bytes: &[u8; 32]) -> Option<Self> {
        Self::from_limbs(limbs::from_be_bytes(bytes))
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
        limbs::to_le_bytes(self.0)
    }

    pub fn to_be_bytes(&self) -> [u8; 32] {
        limbs::to_be_bytes(self.0)
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        limbs::is_zero(self.0)
    }

    #[inline]
    pub fn add_mod(&self, rhs: &Self) -> Self {
        Self(limbs::add_mod(self.0, rhs.0, BLS_R))
    }

    #[inline]
    pub fn sub_mod(&self, rhs: &Self) -> Self {
        Self(limbs::sub_mod(self.0, rhs.0, BLS_R))
    }

    #[inline]
    pub fn mul_mod(&self, rhs: &Self) -> Self {
        let m1 = limbs::mont_mul(self.0, rhs.0, BLS_R, BLS_R_INV);
        Self(limbs::mont_mul(m1, BLS_R_R2, BLS_R, BLS_R_INV))
    }

    pub fn inv_or_zero(&self) -> Self {
        Self(limbs::mont_pow(
            self.0,
            BLS_R_MINUS_2,
            BLS_R,
            BLS_R_INV,
            BLS_R_R2,
        ))
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
        let z1_zero = self.z.is_zero();
        let z2_zero = other.z.is_zero();
        let both_inf = z1_zero & z2_zero;
        let neither_inf = (!z1_zero) & (!z2_zero);
        let x_eq = self.x * other.z == other.x * self.z;
        let y_eq = self.y * other.z == other.y * self.z;
        both_inf | (neither_inf & x_eq & y_eq)
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
            BlsValidatorCommitment::BeaconValidatorPubkey(expected) => {
                qsag_accel::ct::ct_eq_bytes(&pk, expected)
            }
            BlsValidatorCommitment::UnrevealedBls0x00Credential(cred) => {
                let mut actual = compute_bls_0x00_withdrawal_credentials(&pk);
                let eq = cred[0] == 0x00 && qsag_accel::ct::ct_eq_bytes(&actual, cred);
                ct_zeroize_bytes(&mut actual);
                eq
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
// Unified Mixed-Domain (`GF(2)` + `Goldilocks` + `FpBls381`) ZKBoo Circuit
// ============================================================================

type Val6 = [u64; 6];

/// Mixed-domain ZKBoo circuit for Ethereum Beacon validator `BLS12-381` ownership.
pub struct BlsOwnershipCircuit(pub(crate) Circuit);

fn bls_rcb_add(c: &Builder, a: [Wire; 3], b: [Wire; 3]) -> [Wire; 3] {
    let mut t0 = c.mul(a[0], b[0]);
    let mut t1 = c.mul(a[1], b[1]);
    let zz = c.mul(a[2], b[2]);
    let t2 = c.scale(zz, 12);
    let t3 = c.sub(c.mul(c.add(a[0], a[1]), c.add(b[0], b[1])), c.add(t0, t1));
    let t4 = c.sub(c.mul(c.add(a[1], a[2]), c.add(b[1], b[2])), c.add(t1, zz));
    let cross = c.scale(
        c.sub(c.mul(c.add(a[0], a[2]), c.add(b[0], b[2])), c.add(t0, zz)),
        12,
    );
    t0 = c.scale(t0, 3);
    let z = c.add(t1, t2);
    t1 = c.sub(t1, t2);
    [
        c.sub(c.mul(t3, t1), c.mul(t4, cross)),
        c.add(c.mul(t1, z), c.mul(cross, t0)),
        c.add(c.mul(z, t4), c.mul(t0, t3)),
    ]
}

/// Precompute 64 public 4-bit affine window tables `[v * 16^w] G_1` using a single batch inversion.
fn bls_g1_window_tables() -> Vec<[[Val6; 3]; 16]> {
    let mut tables = Vec::with_capacity(64);
    let mut base = BlsG1Point::GENERATOR;
    for _ in 0..64 {
        let mut p = BlsG1Point::IDENTITY;
        let table: [[Val6; 3]; 16] = core::array::from_fn(|v| {
            if v != 0 {
                p = p.complete_add(&base);
            }
            [p.x.0, p.y.0, p.z.0]
        });
        tables.push(table);
        for _ in 0..4 {
            base = base.complete_add(&base);
        }
    }
    let mut prefixes = Vec::with_capacity(64 * 15);
    let mut prod = FpBls381::ONE;
    for table in &tables {
        for p in &table[1..] {
            prefixes.push(prod);
            prod = prod * FpBls381(p[2]);
        }
    }
    let mut inv = prod.inv_or_zero();
    for table in tables.iter_mut().rev() {
        for p in table[1..].iter_mut().rev() {
            let z_inv = inv * prefixes.pop().unwrap();
            inv = inv * FpBls381(p[2]);
            p[0] = (FpBls381(p[0]) * z_inv).0;
            p[1] = (FpBls381(p[1]) * z_inv).0;
            p[2] = FpBls381::ONE.0;
        }
    }
    tables
}

fn fixed_base_bls_g1_mul(c: &Builder, bits: &[Wire]) -> [Wire; 3] {
    #[cfg(any(feature = "std", test))]
    let tables = {
        static TABLES: std::sync::OnceLock<Vec<[[Val6; 3]; 16]>> = std::sync::OnceLock::new();
        TABLES.get_or_init(bls_g1_window_tables)
    };
    #[cfg(not(any(feature = "std", test)))]
    let tables = &bls_g1_window_tables();
    let one = c.small(Domain::BlsFp, 1);
    let pairs = |a, b| {
        let ab = c.mul(a, b);
        let a_only = c.sub(a, ab);
        let b_only = c.sub(b, ab);
        [c.sub(c.sub(one, a_only), b), a_only, b_only, ab]
    };
    let mut acc: Option<[Wire; 3]> = None;
    for (nibble, table) in bits.chunks_exact(4).zip(tables) {
        let b: [Wire; 4] = core::array::from_fn(|i| c.lift(nibble[i], Domain::BlsFp));
        let lo = pairs(b[0], b[1]);
        let hi = pairs(b[2], b[3]);
        let mut sel = [c.small(Domain::BlsFp, 0); 16];
        for j in 0..3 {
            for i in 0..3 {
                sel[j * 4 + i] = c.mul(lo[i], hi[j]);
            }
            sel[j * 4 + 3] = c.sub(
                hi[j],
                c.add(c.add(sel[j * 4], sel[j * 4 + 1]), sel[j * 4 + 2]),
            );
        }
        for i in 0..4 {
            sel[12 + i] = c.sub(lo[i], c.add(c.add(sel[i], sel[4 + i]), sel[8 + i]));
        }
        let pt: [Wire; 3] = core::array::from_fn(|coord| {
            if coord == 2 {
                return c.sub(one, sel[0]);
            }
            sel.iter()
                .zip(table)
                .fold(c.small(Domain::BlsFp, 0), |sum, (&w, p)| {
                    c.add(sum, c.scale_value(w, p[coord]))
                })
        });
        acc = Some(match acc {
            None => pt,
            Some(prev) => bls_rcb_add(c, prev, pt),
        });
    }
    acc.unwrap()
}

/// Build the mixed-domain ZKBoo circuit for `statement`.
pub fn build_bls_ownership_circuit(
    statement: &BlsMigrationStatement,
    public_affine: Option<(FpBls381, FpBls381)>,
    sk_le: &[u8; 32],
) -> BlsOwnershipCircuit {
    let c = Builder::default();
    let sk_bits: Vec<_> = sk_le
        .iter()
        .flat_map(|&b| (0..8).map(move |i| (b >> i) & 1))
        .map(|b| c.input(b))
        .collect();
    c.require_scalar(&sk_bits, lift4(BLS_R));

    let proj = fixed_base_bls_g1_mul(&c, &sk_bits);
    let z_inv = c.inverse(proj[2]);

    match (&statement.commitment, public_affine) {
        (BlsValidatorCommitment::BeaconValidatorPubkey(_), Some((x_pub, y_pub))) => {
            c.equal(proj[0], c.scale_value(proj[2], x_pub.0));
            c.equal(proj[1], c.scale_value(proj[2], y_pub.0));
        }
        (BlsValidatorCommitment::UnrevealedBls0x00Credential(cred), None) => {
            // Decompose affine `(x, y) = (proj[0] * z_inv, proj[1] * z_inv)` directly via
            // `Op::Digit` so multi-custodian `co_zk_mpc` never reconstructs `pk_48` in the clear.
            let mut x_bits = c.bits(c.mul(proj[0], z_inv));
            let mut y_bits = c.bits(c.mul(proj[1], z_inv));
            x_bits.resize(384, c.small(Domain::Bit, 0));
            y_bits.resize(384, c.small(Domain::Bit, 0));

            // `a_flag = (y >= (p + 1) / 2)`
            let comp_half: Vec<_> = c
                .constant_bits(BLS_P_HALF_CEIL, 384)
                .into_iter()
                .map(|b| c.not(b))
                .collect();
            let (_, a_flag) = c.add_bits(&y_bits, &comp_half, c.small(Domain::Bit, 1));

            // Assemble 48-byte big-endian IETF compressed `G_1` bit stream:
            // Byte 0: bits `0..=4` = `x_bits[376..=380]`, bit 5 = `a_flag`, bit 6 = `0`, bit 7 = `1`.
            // Bytes `1..48`: byte `k` = `x_bits[8*(47 - k) .. 8*(47 - k) + 8]`.
            let mut pk_bits = Vec::with_capacity(384);
            pk_bits.extend_from_slice(&x_bits[376..381]);
            pk_bits.push(a_flag);
            pk_bits.push(c.small(Domain::Bit, 0));
            pk_bits.push(c.small(Domain::Bit, 1));
            for k in 1..48 {
                let base = 8 * (47 - k);
                pk_bits.extend_from_slice(&x_bits[base..base + 8]);
            }
            let digest_bits = boolean_hash::sha256(&c, &pk_bits);
            for (byte_idx, &expected_byte) in cred[1..32].iter().enumerate() {
                for bit_idx in 0..8 {
                    let expected_bit = u64::from((expected_byte >> bit_idx) & 1);
                    c.equal(
                        digest_bits[(byte_idx + 1) * 8 + bit_idx],
                        c.small(Domain::Bit, expected_bit),
                    );
                }
            }
        }
        _ => unreachable!("commitment mode and public_affine invariant violated"),
    }

    let mut nul_in = alloc::vec![c.small(Domain::Gold, NULLIFIER_TAG_BLS12_381_G1)];
    nul_in.extend(pack56(&c, &big_endian(&sk_bits)));
    nul_in.extend(
        pack_bytes32_to_limbs56(&statement.migration_domain).map(|v| c.small(Domain::Gold, v)),
    );
    let nul = sponge(&c, NULLIFIER_DOMAIN, &nul_in);
    for (w, expected) in nul.into_iter().zip(statement.migration_nullifier) {
        c.equal(w, c.small(Domain::Gold, expected));
    }
    BlsOwnershipCircuit(c.finish())
}

pub(crate) fn bls_transcript(
    statement: &BlsMigrationStatement,
    root: &[u8; 32],
) -> InterleavedTranscript {
    let mut t = InterleavedTranscript::new(
        b"QSAG.BLS12_381.MIGRATE.V1",
        &statement.to_transcript_bytes(),
    );
    t.absorb(b"VIEWS", root);
    t
}

fn bls_seeds(entropy: &[u8; 32], stmt_bytes: &[u8], rep: usize) -> [[u8; 32]; 3] {
    core::array::from_fn(|p| {
        cshake256_framed_32(
            b"QSAG.BLS12_381.SEEDS.V1",
            &[entropy, stmt_bytes, &(rep as u64).to_le_bytes(), &[p as u8]],
        )
    })
}

/// Prove Ethereum Beacon validator `BLS12-381` ownership in the default epoch campaign domain.
#[allow(clippy::too_many_arguments)]
pub fn prove_bls_migration<B: AcceleratorBackend>(
    witness: &BlsOwnershipWitness,
    commitment: BlsValidatorCommitment,
    validator_index: u64,
    withdrawal_credentials: [u8; 32],
    target: QsagAddress,
    epoch: u64,
    entropy: [u8; 32],
    accel: &B,
) -> Result<(BlsMigrationStatement, MigrationZkProof), MigrateError> {
    let domain = cshake256_framed_32(b"QSAG.BLS12_381.CAMPAIGN.V1", &[&epoch.to_le_bytes()]);
    prove_bls_migration_in_domain(
        witness,
        BlsMigrationRequest {
            commitment,
            validator_index,
            withdrawal_credentials,
            target,
            epoch,
            domain,
        },
        entropy,
        accel,
    )
}

/// Prove Ethereum Beacon validator `BLS12-381` ownership in an explicit campaign domain.
pub fn prove_bls_migration_in_domain<B: AcceleratorBackend>(
    witness: &BlsOwnershipWitness,
    request: BlsMigrationRequest,
    mut entropy: [u8; 32],
    accel: &B,
) -> Result<(BlsMigrationStatement, MigrationZkProof), MigrateError> {
    let result = (|| {
        if !witness.matches_commitment(&request.commitment) {
            return Err(MigrateError::WitnessMismatchWithLegacyCommitment);
        }
        let public_affine = match &request.commitment {
            BlsValidatorCommitment::BeaconValidatorPubkey(pk_48) => {
                let pt = BlsG1Point::from_validator_pubkey_48(pk_48)
                    .ok_or(MigrateError::WitnessMismatchWithLegacyCommitment)?;
                Some(
                    pt.to_affine()
                        .ok_or(MigrateError::WitnessMismatchWithLegacyCommitment)?,
                )
            }
            BlsValidatorCommitment::UnrevealedBls0x00Credential(_) => None,
        };
        let sk = witness
            .scalar()
            .ok_or(MigrateError::WitnessMismatchWithLegacyCommitment)?;
        let statement = BlsMigrationStatement {
            commitment: request.commitment,
            validator_index: request.validator_index,
            withdrawal_credentials: request.withdrawal_credentials,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: sk.compute_nullifier(&request.domain),
        };
        if !statement.credentials_consistent() {
            return Err(MigrateError::WitnessMismatchWithLegacyCommitment);
        }
        let mut sk_le = sk.to_le_bytes();
        let circuit = build_bls_ownership_circuit(&statement, public_affine, &sk_le);
        if circuit
            .0
            .outputs
            .iter()
            .any(|&w| circuit.0.nodes[w].value != ZERO)
        {
            ct_zeroize_bytes(&mut sk_le);
            return Err(MigrateError::WitnessMismatchWithLegacyCommitment);
        }
        let stmt_bytes = statement.to_transcript_bytes();
        entropy = cshake256_framed_32(b"QSAG.BLS12_381.HEDGE.V1", &[&entropy, &sk_le, &stmt_bytes]);
        ct_zeroize_bytes(&mut sk_le);

        let views = crate::parallel::map(MIT_REPETITIONS, |rep| {
            simulate(&circuit.0, bls_seeds(&entropy, &stmt_bytes, rep))
        });
        let commitments = crate::batch_hash::commit_views(accel, &views);
        let mut all_views = Vec::with_capacity(MIT_REPETITIONS);
        let mut roots = Vec::with_capacity(MIT_REPETITIONS * 32);
        for (rep, rep_views) in views.into_iter().enumerate() {
            let commits = core::array::from_fn(|p| commitments[3 * rep + p]);
            roots.extend_from_slice(&rep_root(
                rep,
                &commits,
                core::array::from_fn(|p| rep_views[p].outputs.as_slice()),
            ));
            all_views.push((rep_views, commits));
        }
        let root = cshake256_framed_32(b"QSAG.MIGRATE.ROOT.V3", &[&roots]);
        let mut t = bls_transcript(&statement, &root);
        let es = challenges(&mut t);
        let mut repetitions = Vec::with_capacity(MIT_REPETITIONS);
        for ((mut rep_views, commits), &e) in all_views.into_iter().zip(&es) {
            let e_idx = e as usize;
            let hidden = (e_idx + 2) % 3;
            let hidden_outputs = core::mem::take(&mut rep_views[hidden].outputs);
            repetitions.push(OpenedRepetitionView {
                opened_e: e,
                pair: [rep_views[e_idx].clone(), rep_views[(e_idx + 1) % 3].clone()],
                hidden_party_commit: commits[hidden],
                hidden_outputs,
            });
        }
        Ok((
            statement,
            MigrationZkProof {
                views_merkle_root: root,
                repetitions,
            },
        ))
    })();
    ct_zeroize_bytes(&mut entropy);
    result
}

/// Verify an Ethereum Beacon validator `BLS12-381` post-quantum ownership migration proof.
pub fn verify_bls_migration(
    statement: &BlsMigrationStatement,
    proof: &MigrationZkProof,
    expected_domain: &[u8; 32],
    expected_epoch: u64,
) -> Result<(), MigrateError> {
    verify_bls_migration_with_backend(
        statement,
        proof,
        expected_domain,
        expected_epoch,
        &qsag_accel::CpuReferenceBackend,
    )
}

/// Verify an Ethereum Beacon validator `BLS12-381` migration proof on a selected `AcceleratorBackend`.
pub fn verify_bls_migration_with_backend<B: AcceleratorBackend>(
    statement: &BlsMigrationStatement,
    proof: &MigrationZkProof,
    expected_domain: &[u8; 32],
    expected_epoch: u64,
    accel: &B,
) -> Result<(), MigrateError> {
    if &statement.migration_domain != expected_domain || statement.epoch_anchor != expected_epoch {
        return Err(MigrateError::SessionMismatch);
    }
    if !statement.credentials_consistent()
        || proof.repetitions.len() != MIT_REPETITIONS
        || statement
            .migration_nullifier
            .iter()
            .any(|&v| v >= GOLDILOCKS_PRIME)
    {
        return Err(MigrateError::MalformedProofStructure);
    }
    let public_affine = match &statement.commitment {
        BlsValidatorCommitment::BeaconValidatorPubkey(pk_48) => {
            let pt = BlsG1Point::from_validator_pubkey_48(pk_48)
                .ok_or(MigrateError::MalformedProofStructure)?;
            Some(
                pt.to_affine()
                    .ok_or(MigrateError::MalformedProofStructure)?,
            )
        }
        BlsValidatorCommitment::UnrevealedBls0x00Credential(_) => None,
    };

    let mut t = bls_transcript(statement, &proof.views_merkle_root);
    let es = challenges(&mut t);
    if proof
        .repetitions
        .iter()
        .zip(&es)
        .any(|(v, &e)| v.opened_e != e)
    {
        return Err(MigrateError::MalformedProofStructure);
    }
    if crate::zk_engine::is_cozk_proof(proof) {
        let mut dummy_one = [0u8; 32];
        dummy_one[0] = 1;
        let circuit = build_bls_ownership_circuit(statement, public_affine, &dummy_one);
        return crate::zk_engine::verify_cozk_v4_proof_body(&circuit.0, proof);
    }
    let indexed: Vec<_> = proof
        .repetitions
        .iter()
        .enumerate()
        .flat_map(|(rep, view)| {
            let e = view.opened_e as usize;
            [(rep, e, &view.pair[0]), (rep, (e + 1) % 3, &view.pair[1])]
        })
        .collect();
    let opened_commits = crate::batch_hash::commit_indexed(accel, &indexed);
    let roots: Vec<u8> = crate::parallel::map(MIT_REPETITIONS, |rep| {
        let view = &proof.repetitions[rep];
        let e = view.opened_e as usize;
        let mut commits = [[0u8; 32]; 3];
        commits[e] = opened_commits[2 * rep];
        commits[(e + 1) % 3] = opened_commits[2 * rep + 1];
        commits[(e + 2) % 3] = view.hidden_party_commit;
        let mut outs = [&[][..]; 3];
        outs[e] = &view.pair[0].outputs;
        outs[(e + 1) % 3] = &view.pair[1].outputs;
        outs[(e + 2) % 3] = &view.hidden_outputs;
        rep_root(rep, &commits, outs)
    })
    .into_iter()
    .flatten()
    .collect();
    if cshake256_framed_32(b"QSAG.MIGRATE.ROOT.V3", &[&roots]) != proof.views_merkle_root {
        return Err(MigrateError::ViewsMerkleRootMismatch);
    }
    let mut dummy_one = [0u8; 32];
    dummy_one[0] = 1;
    let circuit = build_bls_ownership_circuit(statement, public_affine, &dummy_one);
    let workers = crate::parallel::workers(MIT_REPETITIONS);
    let chunk = MIT_REPETITIONS.div_ceil(workers);
    for res in crate::parallel::map(workers, |worker| {
        let mut wires = core::array::from_fn(|_| Wires(alloc::vec![ZERO; circuit.0.nodes.len()]));
        for rep in worker * chunk..((worker + 1) * chunk).min(MIT_REPETITIONS) {
            replay_with_scratch(&circuit.0, rep, &proof.repetitions[rep], &mut wires)?;
        }
        Ok::<(), MigrateError>(())
    }) {
        res?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use qsag_accel::CpuReferenceBackend;
    use qsag_addr::{KeyIdentityKind, WitnessSuiteTag};

    fn sample_beam_pq_dest(tag: &[u8]) -> QsagAddress {
        QsagAddress::from_pubkey_poseidon2(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            tag,
        )
        .unwrap()
    }

    #[test]
    fn bls12_381_ietf_g1_constants_codec_and_subgroup_rejection_hold() {
        // `(p - 1)^2 == 1 (mod p)` (`p^2` wraparound check) & Fermat inversion:
        let pm1 = FpBls381([
            BLS_P[0] - 1,
            BLS_P[1],
            BLS_P[2],
            BLS_P[3],
            BLS_P[4],
            BLS_P[5],
        ]);
        assert_eq!(pm1 * pm1, FpBls381::ONE);
        assert_eq!(pm1 + FpBls381::ONE, FpBls381::ZERO);
        assert_eq!(FpBls381::B * FpBls381::B.inv_or_zero(), FpBls381::ONE);

        // Official IETF / Ethereum Beacon `G_1` compressed 48-byte hex vector:
        let expected_g1_compressed: [u8; 48] = [
            0x97, 0xf1, 0xd3, 0xa7, 0x31, 0x97, 0xd7, 0x94, 0x26, 0x95, 0x63, 0x8c, 0x4f, 0xa9,
            0xac, 0x0f, 0xc3, 0x68, 0x8c, 0x4f, 0x97, 0x74, 0xb9, 0x05, 0xa1, 0x4e, 0x3a, 0x3f,
            0x17, 0x1b, 0xac, 0x58, 0x6c, 0x55, 0xe8, 0x3f, 0xf9, 0x7a, 0x1a, 0xef, 0xfb, 0x3a,
            0xf0, 0x0a, 0xdb, 0x22, 0xc6, 0xbb,
        ];
        assert_eq!(
            BlsG1Point::GENERATOR.to_compressed_48(),
            expected_g1_compressed
        );
        assert!(BlsG1Point::GENERATOR.is_in_g1_subgroup());
        assert_eq!(
            BlsG1Point::from_validator_pubkey_48(&expected_g1_compressed).unwrap(),
            BlsG1Point::GENERATOR
        );

        // Identity `0xc000...00` accepted by `from_compressed_48` and rejected by `from_validator_pubkey_48`:
        let inf = BlsG1Point::IDENTITY.to_compressed_48();
        assert_eq!(inf[0], 0xc0);
        assert!(BlsG1Point::from_compressed_48(&inf).unwrap().is_identity());
        assert!(BlsG1Point::from_validator_pubkey_48(&inf).is_none());

        // `[r - 1] G_1 == -G_1` and `[r] G_1 == O`:
        let rm1 = FrBls381([BLS_R[0] - 1, BLS_R[1], BLS_R[2], BLS_R[3]]);
        assert_eq!(
            BlsG1Point::generator_mul_ct(&rm1),
            BlsG1Point::GENERATOR.neg_point()
        );

        // Small-subgroup attack point `(0, 2)` satisfies `2^2 = 0^3 + 4`, has exact torsion order 3,
        // and MUST be rejected by `is_in_g1_subgroup` and `from_compressed_48` / `from_validator_pubkey_48`!
        let torsion3 = BlsG1Point {
            x: FpBls381::ZERO,
            y: FpBls381([2, 0, 0, 0, 0, 0]),
            z: FpBls381::ONE,
        };
        assert!(torsion3.is_on_curve());
        assert!(torsion3.scalar_mul_limbs_ct(&[3]).is_identity());
        assert!(!torsion3.is_in_g1_subgroup());
        assert!(torsion3.clear_cofactor().is_identity());
        let torsion3_comp = torsion3.to_compressed_48();
        assert!(BlsG1Point::from_compressed_48(&torsion3_comp).is_none());
        assert!(BlsG1Point::from_validator_pubkey_48(&torsion3_comp).is_none());
    }

    #[test]
    fn bls12_381_beacon_validator_and_unrevealed_0x00_zk_migration_roundtrip_and_rejections() {
        let mut sk_be = [0u8; 32];
        sk_be[30] = 0x13;
        sk_be[31] = 0x37;
        let wit = BlsOwnershipWitness::from_secret_scalar_be(sk_be).unwrap();
        assert!(format!("{wit:?}").contains("<REDACTED>"));

        let backend = CpuReferenceBackend;
        let domain = [0xab; 32];
        let epoch = 360_000;
        let validator_index = 987_654;

        // 1. Active Beacon validator pubkey with EIP-7251 `0x02` compounding `2048 ETH` credentials:
        let beacon_comm = wit.compute_beacon_commitment().unwrap();
        let mut creds_0x02 = [0u8; 32];
        creds_0x02[0] = 0x02;
        creds_0x02[12..32].copy_from_slice(&[0x44; 20]);

        let req_beacon = BlsMigrationRequest {
            commitment: beacon_comm,
            validator_index,
            withdrawal_credentials: creds_0x02,
            target: sample_beam_pq_dest(b"eth-beam-chain-jorts-2048eth"),
            epoch,
            domain,
        };
        let (stmt, mut proof) =
            prove_bls_migration_in_domain(&wit, req_beacon.clone(), [0x77; 32], &backend).unwrap();
        assert_eq!(verify_bls_migration(&stmt, &proof, &domain, epoch), Ok(()));

        // Wrong validator secret key rejected:
        let mut wrong_sk = sk_be;
        wrong_sk[31] ^= 1;
        let wrong_wit = BlsOwnershipWitness::from_secret_scalar_be(wrong_sk).unwrap();
        assert_eq!(
            prove_bls_migration_in_domain(&wrong_wit, req_beacon, [0x11; 32], &backend),
            Err(MigrateError::WitnessMismatchWithLegacyCommitment)
        );

        // Wrong validator pubkey / mutated withdrawal credentials / mutated validator_index rejected:
        let mut bad_pub_stmt = stmt.clone();
        bad_pub_stmt.commitment = wrong_wit.compute_beacon_commitment().unwrap();
        assert!(verify_bls_migration(&bad_pub_stmt, &proof, &domain, epoch).is_err());

        let mut bad_creds_stmt = stmt.clone();
        bad_creds_stmt.withdrawal_credentials[31] ^= 1;
        assert!(verify_bls_migration(&bad_creds_stmt, &proof, &domain, epoch).is_err());

        let mut bad_idx_stmt = stmt.clone();
        bad_idx_stmt.validator_index += 1;
        assert!(verify_bls_migration(&bad_idx_stmt, &proof, &domain, epoch).is_err());

        // Small-subgroup point `(0, 2)` stuffed into statement commitment rejected:
        let torsion3 = BlsG1Point {
            x: FpBls381::ZERO,
            y: FpBls381([2, 0, 0, 0, 0, 0]),
            z: FpBls381::ONE,
        };
        let mut subgroup_stmt = stmt.clone();
        subgroup_stmt.commitment =
            BlsValidatorCommitment::BeaconValidatorPubkey(torsion3.to_compressed_48());
        assert_eq!(
            verify_bls_migration(&subgroup_stmt, &proof, &domain, epoch),
            Err(MigrateError::MalformedProofStructure)
        );

        // Tampered ZKBoo party view rejected:
        proof.repetitions[0].pair[0].products[0] ^= 1;
        assert!(verify_bls_migration(&stmt, &proof, &domain, epoch).is_err());
        proof.repetitions[0].pair[0].products[0] ^= 1;
        assert_eq!(verify_bls_migration(&stmt, &proof, &domain, epoch), Ok(()));

        // 2. Unrevealed `0x00` BLS withdrawal credential (`pk_48` never published on-chain!):
        let unrev_comm = wit.compute_unrevealed_0x00_commitment().unwrap();
        let BlsValidatorCommitment::UnrevealedBls0x00Credential(cred_0x00) = unrev_comm else {
            unreachable!()
        };
        let req_unrev = BlsMigrationRequest {
            commitment: unrev_comm,
            validator_index,
            withdrawal_credentials: cred_0x00,
            target: sample_beam_pq_dest(b"eth-unrevealed-0x00-pq-vault"),
            epoch,
            domain,
        };
        let (stmt_unrev, proof_unrev) =
            prove_bls_migration_in_domain(&wit, req_unrev, [0x99; 32], &backend).unwrap();
        assert_eq!(
            verify_bls_migration(&stmt_unrev, &proof_unrev, &domain, epoch),
            Ok(())
        );
    }
}

#[cfg(test)]
mod poseidon2_canonical_kat {
    use super::*;
    #[test]
    fn migration_poseidon2_circuit_matches_canonical_kat() {
        let c = Builder::default();
        let input: [Wire; 8] = core::array::from_fn(|i| c.small(Domain::Gold, i as u64));
        let out = sponge(&c, NULLIFIER_DOMAIN, &input);
        let expected = poseidon2_hash_limbs(NULLIFIER_DOMAIN, &[0, 1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(out.map(|w| c.value(w)[0]), expected);
    }
}
