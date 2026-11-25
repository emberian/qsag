//! Constant-time `BLS12-381` base/scalar field arithmetic, `G_1` curve operations,
//! and Ethereum `0x00` withdrawal-credential derivation (`#![no_std]`, zero `unsafe`).
//!
//! Curve parameters (IETF RFC 9380 / Ethereum Consensus Specs):
//! - Base field prime (`381` bits, `p ≡ 3 (mod 4)`):
//!   `p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab`
//! - Prime subgroup order (`255` bits):
//!   `r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`
//! - Curve equation: `E(F_p) : y^2 = x^3 + 4` (`a = 0, b = 4, 3b = 12`), `G_1 = E(F_p)[r]`.

use alloc::vec::Vec;
use core::fmt;

use qsag_accel::{
    ct::{RedactedSecret, ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::pack_bytes32_to_limbs56,
    poseidon2::poseidon2_hash_limbs,
    sha2::sha256,
};

use crate::{limbs, scalar::NULLIFIER_DOMAIN};

/// `BLS12-381` base field modulus `p` (`381` bits, little-endian `u64` limbs).
pub const BLS_P: [u64; 6] = [
    0xb9fe_ffff_ffff_aaab,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

pub(crate) const BLS_P_MINUS_2: [u64; 6] = [
    0xb9fe_ffff_ffff_aaa9,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

/// `-p[0]^{-1} mod 2^64` for 6-limb CIOS Montgomery reduction over `F_p`.
pub(crate) const BLS_P_INV: u64 = 0x89f3_fffc_fffc_fffd;

/// `R^2 mod p` for `R = 2^384`.
pub(crate) const BLS_P_R2: [u64; 6] = [
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

/// A reduced Montgomery residue modulo [`BLS_P`].
#[derive(Clone, Copy, Eq)]
pub struct FpBls381([u64; 6]);

limbs::montgomery_field!(FpBls381, 6, 48, BLS_P, BLS_P_INV, BLS_P_R2, BLS_P_MINUS_2);

impl FpBls381 {
    pub fn add_mod(self, rhs: Self) -> Self {
        self.sum(&rhs)
    }
    pub fn sub_mod(self, rhs: Self) -> Self {
        self.difference(&rhs)
    }
    pub fn mul_mod(self, rhs: Self) -> Self {
        self.product(&rhs)
    }

    pub const B: Self = Self::from_u64(4);
    pub const B3: Self = Self::from_u64(12);
    pub fn ct_select(choice: bool, t: Self, f: Self) -> Self {
        Self::select(choice, t, f)
    }
    pub fn sq(self) -> Self {
        self.square()
    }
    pub fn lexicographically_largest(self) -> bool {
        !limbs::lt(self.canonical_words(), BLS_P_HALF_CEIL)
    }
    pub fn sqrt_ct(self) -> Option<Self> {
        let cand = self.pow(&BLS_P_PLUS_1_DIV_4);
        (cand.sq() == self).then_some(cand)
    }
}

/// A reduced Montgomery residue modulo [`BLS_R`].
#[derive(Clone, Eq)]
pub struct FrBls381([u64; 4]);

limbs::montgomery_field!(FrBls381, 4, 32, BLS_R, BLS_R_INV, BLS_R_R2, BLS_R_MINUS_2);
impl Drop for FrBls381 {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
}

impl FrBls381 {
    pub(crate) fn select_ref(choice: bool, a: &Self, b: &Self) -> Self {
        Self(limbs::ct_select(choice, a.0, b.0))
    }

    pub fn add_mod(&self, rhs: &Self) -> Self {
        self.sum(rhs)
    }
    pub fn sub_mod(&self, rhs: &Self) -> Self {
        self.difference(rhs)
    }
    pub fn mul_mod(&self, rhs: &Self) -> Self {
        self.product(rhs)
    }
    pub fn from_nonzero_le_bytes(bytes: &[u8; 32]) -> Option<Self> {
        Self::from_le_bytes(bytes).filter(|s| !s.is_zero())
    }
    pub fn from_nonzero_be_bytes(bytes: &[u8; 32]) -> Option<Self> {
        Self::from_be_bytes(bytes).filter(|s| !s.is_zero())
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
        x: FpBls381::from_raw(BLS_G1_GX),
        y: FpBls381::from_raw(BLS_G1_GY),
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
        let words = qsag_asm::wipe::SecretBuffer(scalar.canonical_words());
        self.scalar_mul_limbs_ct(&words[..])
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

/// The key relation to prove. Only `BlsWithdrawalCredential` establishes withdrawal-key possession.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BlsValidatorCommitment {
    /// Validator signing-key possession only; conveys no withdrawal authority or authenticated validator membership.
    OperatorSigningPubkey([u8; 48]),
    /// Withdrawal-key possession for `0x00 || SHA256(withdrawal_pk_48)[1..32]`,
    /// with the public key hash constrained inside the circuit. The proof does not reveal the key.
    BlsWithdrawalCredential([u8; 32]),
}

impl BlsValidatorCommitment {
    pub fn write_transcript(&self, out: &mut Vec<u8>) {
        match self {
            Self::OperatorSigningPubkey(pk) => {
                out.push(1);
                out.extend_from_slice(pk);
            }
            Self::BlsWithdrawalCredential(cred) => {
                out.push(2);
                out.extend_from_slice(cred);
            }
        }
    }
}

/// Secret BLS signing or withdrawal scalar witness (`sk ∈ [1, r - 1]`) with redacted `Debug` and volatile `Drop`.
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
        let sk_be = RedactedSecret::new(sk_be);
        FrBls381::from_nonzero_be_bytes(sk_be.expose())?;
        Some(Self { sk_be })
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

    /// Derive an operator signing-key commitment, not a withdrawal credential.
    pub fn compute_operator_commitment(&self) -> Option<BlsValidatorCommitment> {
        self.compute_validator_pubkey_48()
            .map(BlsValidatorCommitment::OperatorSigningPubkey)
    }

    /// Hash this withdrawal key as `0x00 || SHA256(pk_48)[1..32]`.
    /// This does not attest that the public key has never been revealed.
    pub fn compute_withdrawal_commitment(&self) -> Option<BlsValidatorCommitment> {
        let mut pk = self.compute_validator_pubkey_48()?;
        let cred = compute_bls_0x00_withdrawal_credentials(&pk);
        ct_zeroize_bytes(&mut pk);
        Some(BlsValidatorCommitment::BlsWithdrawalCredential(cred))
    }

    pub fn matches_commitment(&self, commitment: &BlsValidatorCommitment) -> bool {
        let Some(mut pk) = self.compute_validator_pubkey_48() else {
            return false;
        };
        let ok = match commitment {
            BlsValidatorCommitment::OperatorSigningPubkey(expected) => {
                qsag_accel::ct::ct_eq_bytes(&pk, expected)
            }
            BlsValidatorCommitment::BlsWithdrawalCredential(cred) => {
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
