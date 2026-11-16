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
use core::fmt;

use qsag_accel::{
    AcceleratorBackend,
    ct::{RedactedSecret, ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::{GOLDILOCKS_PRIME, pack_bytes32_to_limbs56},
    keccak::{InterleavedTranscript, cshake256_framed_32},
    poseidon2::poseidon2_hash_limbs,
};
use qsag_addr::QsagAddress;

use crate::{
    circuit::{Builder, Circuit, Domain, Wire, ZERO, lift4},
    limbs,
    ownership::{big_endian, pack56, sponge},
    scalar::NULLIFIER_DOMAIN,
    zk_engine::{
        MIT_REPETITIONS, MigrateError, MigrationZkProof, OpenedRepetitionView, Wires, challenges,
        rep_root, replay_with_scratch, simulate,
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
    0xbdad_6fab_d87e_a32f,
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
        let value = limbs::from_le_bytes(bytes);
        if limbs::lt(value, PALLAS_P) {
            Some(Self(value))
        } else {
            None
        }
    }

    pub fn to_le_bytes(self) -> [u8; 32] {
        limbs::to_le_bytes(self.0)
    }

    #[inline]
    pub fn ct_select(choice: bool, t: Self, f: Self) -> Self {
        Self(limbs::ct_select(choice, t.0, f.0))
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        limbs::is_zero(self.0)
    }

    #[inline]
    pub fn is_odd(self) -> bool {
        (self.0[0] & 1) == 1
    }

    #[inline]
    pub fn add_mod(self, rhs: Self) -> Self {
        Self(limbs::add_mod(self.0, rhs.0, PALLAS_P))
    }

    #[inline]
    pub fn sub_mod(self, rhs: Self) -> Self {
        Self(limbs::sub_mod(self.0, rhs.0, PALLAS_P))
    }

    #[inline]
    pub fn neg_mod(self) -> Self {
        Self(limbs::neg_mod(self.0, PALLAS_P))
    }

    #[inline]
    pub fn mul_mod(self, rhs: Self) -> Self {
        let m1 = limbs::mont_mul(self.0, rhs.0, PALLAS_P, PALLAS_P_INV);
        Self(limbs::mont_mul(m1, PALLAS_P_R2, PALLAS_P, PALLAS_P_INV))
    }

    #[inline]
    pub fn sq(self) -> Self {
        self.mul_mod(self)
    }

    /// Constant-time Fermat inversion `a^(p - 2) mod p` (`0 -> 0`).
    pub fn inv_or_zero(self) -> Self {
        Self(limbs::mont_pow(
            self.0,
            PALLAS_P_MINUS_2,
            PALLAS_P,
            PALLAS_P_INV,
            PALLAS_P_R2,
        ))
    }

    /// Constant-time 32-adic Tonelli-Shanks square root in `F_p`.
    pub fn sqrt_ct(self) -> Option<Self> {
        let w = Self(limbs::mont_pow(
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
            let need_mul = limbs::ct_eq(d.0, minus_one.0);
            let c2 = c.sq();
            x = Self::ct_select(need_mul, x.mul_mod(c), x);
            b = Self::ct_select(need_mul, b.mul_mod(c2), b);
            c = c2;
        }
        if x.sq() == self { Some(x) } else { None }
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
        let mut value = limbs::from_le_bytes(bytes);
        if limbs::lt(value, PALLAS_Q) {
            Some(Self(value))
        } else {
            ct_zeroize_u64s(&mut value);
            None
        }
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
        Self(limbs::add_mod(self.0, rhs.0, PALLAS_Q))
    }

    #[inline]
    pub fn sub_mod(&self, rhs: &Self) -> Self {
        Self(limbs::sub_mod(self.0, rhs.0, PALLAS_Q))
    }

    #[inline]
    pub fn neg_mod(&self) -> Self {
        Self(limbs::neg_mod(self.0, PALLAS_Q))
    }

    #[inline]
    pub fn mul_mod(&self, rhs: &Self) -> Self {
        let m1 = limbs::mont_mul(self.0, rhs.0, PALLAS_Q, PALLAS_Q_INV);
        Self(limbs::mont_mul(m1, PALLAS_Q_R2, PALLAS_Q, PALLAS_Q_INV))
    }

    pub fn inv_or_zero(&self) -> Self {
        Self(limbs::mont_pow(
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
#[derive(Clone, Debug)]
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
            (false, false) => {
                (self.x * other.z == other.x * self.z) && (self.y * other.z == other.y * self.z)
            }
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

    pub fn effective_scalar(
        &self,
        kind: &PallasCommitmentKind,
    ) -> Option<(FqPallas, FqPallas, FqPallas)> {
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
// Unified Mixed-Domain (`GF(2)` + `Goldilocks` + `FpPallas`) ZKBoo Circuit
// ============================================================================

type Val4 = [u64; 4];

/// Mixed-domain ZKBoo circuit for Zcash Orchard `Pallas` / `RedPallas` ownership.
pub struct PallasOwnershipCircuit(pub(crate) Circuit);

/// Compute `(a + b) mod q_pallas` on canonical 256-bit LE bit vectors (`a, b < q < 2^255`).
pub(crate) fn add_mod_pallas_q_bits(c: &Builder, a: &[Wire], b: &[Wire]) -> Vec<Wire> {
    let (sum, carry) = c.add_bits(a, b, c.small(Domain::Bit, 0));
    // Since `a, b < 2^255`, `a + b < 2^256`, so `carry == 0`; include `carry` for completeness.
    let mut sum257 = sum;
    sum257.push(carry);
    let mut q_bits = c.constant_bits(lift4(PALLAS_Q), 256);
    q_bits.push(c.small(Domain::Bit, 0));
    let comp: Vec<_> = q_bits.into_iter().map(|w| c.not(w)).collect();
    let (diff, ge_q) = c.add_bits(&sum257, &comp, c.small(Domain::Bit, 1));
    sum257
        .iter()
        .zip(&diff)
        .take(256)
        .map(|(&s, &d)| c.select(ge_q, d, s))
        .collect()
}

fn pallas_rcb_add(c: &Builder, a: [Wire; 3], b: [Wire; 3]) -> [Wire; 3] {
    let mut t0 = c.mul(a[0], b[0]);
    let mut t1 = c.mul(a[1], b[1]);
    let zz = c.mul(a[2], b[2]);
    let t2 = c.scale(zz, 15);
    let t3 = c.sub(c.mul(c.add(a[0], a[1]), c.add(b[0], b[1])), c.add(t0, t1));
    let t4 = c.sub(c.mul(c.add(a[1], a[2]), c.add(b[1], b[2])), c.add(t1, zz));
    let cross = c.scale(
        c.sub(c.mul(c.add(a[0], a[2]), c.add(b[0], b[2])), c.add(t0, zz)),
        15,
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

/// Precompute 64 public 4-bit affine window tables `[v * 16^w] SpendAuthG` using a single batch inversion.
fn spend_auth_window_tables() -> Vec<[[Val4; 3]; 16]> {
    let mut tables = Vec::with_capacity(64);
    let mut base = PallasPoint::ORCHARD_SPEND_AUTH_G;
    for _ in 0..64 {
        let mut p = PallasPoint::IDENTITY;
        let table: [[Val4; 3]; 16] = core::array::from_fn(|v| {
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
    let mut prod = FpPallas::ONE;
    for table in &tables {
        for p in &table[1..] {
            prefixes.push(prod);
            prod = prod * FpPallas(p[2]);
        }
    }
    let mut inv = prod.inv_or_zero();
    for table in tables.iter_mut().rev() {
        for p in table[1..].iter_mut().rev() {
            let z_inv = inv * prefixes.pop().unwrap();
            inv = inv * FpPallas(p[2]);
            p[0] = (FpPallas(p[0]) * z_inv).0;
            p[1] = (FpPallas(p[1]) * z_inv).0;
            p[2] = FpPallas::ONE.0;
        }
    }
    tables
}

fn fixed_base_spend_auth_mul(c: &Builder, bits: &[Wire]) -> [Wire; 3] {
    #[cfg(any(feature = "std", test))]
    let tables = {
        static TABLES: std::sync::OnceLock<Vec<[[Val4; 3]; 16]>> = std::sync::OnceLock::new();
        TABLES.get_or_init(spend_auth_window_tables)
    };
    #[cfg(not(any(feature = "std", test)))]
    let tables = &spend_auth_window_tables();
    let one = c.small(Domain::PallasFp, 1);
    let pairs = |a, b| {
        let ab = c.mul(a, b);
        let a_only = c.sub(a, ab);
        let b_only = c.sub(b, ab);
        [c.sub(c.sub(one, a_only), b), a_only, b_only, ab]
    };
    let mut acc: Option<[Wire; 3]> = None;
    for (nibble, table) in bits.chunks_exact(4).zip(tables) {
        let b: [Wire; 4] = core::array::from_fn(|i| c.lift(nibble[i], Domain::PallasFp));
        let lo = pairs(b[0], b[1]);
        let hi = pairs(b[2], b[3]);
        let mut sel = [c.small(Domain::PallasFp, 0); 16];
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
                .fold(c.small(Domain::PallasFp, 0), |sum, (&w, p)| {
                    c.add(sum, c.scale_value(w, lift4(p[coord])))
                })
        });
        acc = Some(match acc {
            None => pt,
            Some(prev) => pallas_rcb_add(c, prev, pt),
        });
    }
    acc.unwrap()
}

/// Build the mixed-domain ZKBoo circuit for `statement` (ready for single-prover or MPC replay).
pub fn build_pallas_ownership_circuit(
    statement: &PallasMigrationStatement,
    expected_affine: (FpPallas, FpPallas),
    ask_le: &[u8; 32],
    alpha_le: &[u8; 32],
) -> PallasOwnershipCircuit {
    let c = Builder::default();
    let ask_bits: Vec<_> = ask_le
        .iter()
        .flat_map(|&b| (0..8).map(move |i| (b >> i) & 1))
        .map(|b| c.input(b))
        .collect();
    c.require_canonical(&ask_bits, lift4(PALLAS_Q));
    c.require_nonzero(&ask_bits);

    let (eff_bits, nul_tag) = if statement.commitment.is_rerandomized() {
        let alpha_bits: Vec<_> = alpha_le
            .iter()
            .flat_map(|&b| (0..8).map(move |i| (b >> i) & 1))
            .map(|b| c.input(b))
            .collect();
        c.require_canonical(&alpha_bits, lift4(PALLAS_Q));
        let sum_bits = add_mod_pallas_q_bits(&c, &ask_bits, &alpha_bits);
        c.require_nonzero(&sum_bits);
        (sum_bits, NULLIFIER_TAG_PALLAS_RK)
    } else {
        (ask_bits, NULLIFIER_TAG_PALLAS_AK)
    };

    let proj = fixed_base_spend_auth_mul(&c, &eff_bits);
    // Constrain `Z * z_inv == 1` (proving `Z != 0`) and `(X, Y) == (x_pub * Z, y_pub * Z)`.
    let _z_inv = c.inverse(proj[2]);
    c.equal(proj[0], c.scale_value(proj[2], lift4(expected_affine.0.0)));
    c.equal(proj[1], c.scale_value(proj[2], lift4(expected_affine.1.0)));

    let mut nul_in = alloc::vec![c.small(Domain::Gold, nul_tag)];
    nul_in.extend(pack56(&c, &big_endian(&eff_bits)));
    nul_in.extend(
        pack_bytes32_to_limbs56(&statement.migration_domain).map(|v| c.small(Domain::Gold, v)),
    );
    let nul = sponge(&c, NULLIFIER_DOMAIN, &nul_in);
    for (w, expected) in nul.into_iter().zip(statement.migration_nullifier) {
        c.equal(w, c.small(Domain::Gold, expected));
    }
    PallasOwnershipCircuit(c.finish())
}

pub(crate) fn pallas_transcript(
    statement: &PallasMigrationStatement,
    root: &[u8; 32],
) -> InterleavedTranscript {
    let mut t =
        InterleavedTranscript::new(b"QSAG.PALLAS.MIGRATE.V1", &statement.to_transcript_bytes());
    t.absorb(b"VIEWS", root);
    t
}

fn pallas_seeds(entropy: &[u8; 32], stmt_bytes: &[u8], rep: usize) -> [[u8; 32]; 3] {
    core::array::from_fn(|p| {
        cshake256_framed_32(
            b"QSAG.PALLAS.SEEDS.V1",
            &[entropy, stmt_bytes, &(rep as u64).to_le_bytes(), &[p as u8]],
        )
    })
}

/// Prove Zcash Orchard `Pallas` / `RedPallas` spending-key ownership in the default epoch domain.
pub fn prove_pallas_migration<B: AcceleratorBackend>(
    witness: &PallasOwnershipWitness,
    commitment: PallasCommitmentKind,
    target: QsagAddress,
    epoch: u64,
    entropy: [u8; 32],
    accel: &B,
) -> Result<(PallasMigrationStatement, MigrationZkProof), MigrateError> {
    let domain = cshake256_framed_32(b"QSAG.PALLAS.CAMPAIGN.V1", &[&epoch.to_le_bytes()]);
    prove_pallas_migration_in_domain(
        witness,
        PallasMigrationRequest {
            commitment,
            target,
            epoch,
            domain,
        },
        entropy,
        accel,
    )
}

/// Prove Zcash Orchard `Pallas` / `RedPallas` spending-key ownership in an explicit campaign domain.
pub fn prove_pallas_migration_in_domain<B: AcceleratorBackend>(
    witness: &PallasOwnershipWitness,
    request: PallasMigrationRequest,
    mut entropy: [u8; 32],
    accel: &B,
) -> Result<(PallasMigrationStatement, MigrationZkProof), MigrateError> {
    let result = (|| {
        if !witness.matches_commitment(&request.commitment) {
            return Err(MigrateError::WitnessMismatchWithLegacyCommitment);
        }
        let pub_pt = PallasPoint::from_nonidentity_bytes(request.commitment.compressed_bytes())
            .ok_or(MigrateError::WitnessMismatchWithLegacyCommitment)?;
        let expected_affine = pub_pt
            .to_affine()
            .ok_or(MigrateError::WitnessMismatchWithLegacyCommitment)?;
        let (ask, alpha, rsk) = witness
            .effective_scalar(&request.commitment)
            .ok_or(MigrateError::WitnessMismatchWithLegacyCommitment)?;
        let tag = if request.commitment.is_rerandomized() {
            NULLIFIER_TAG_PALLAS_RK
        } else {
            NULLIFIER_TAG_PALLAS_AK
        };
        let statement = PallasMigrationStatement {
            commitment: request.commitment,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: rsk.compute_nullifier(tag, &request.domain),
        };
        let mut ask_bytes = ask.to_le_bytes();
        let mut alpha_bytes = alpha.to_le_bytes();
        let circuit =
            build_pallas_ownership_circuit(&statement, expected_affine, &ask_bytes, &alpha_bytes);
        if circuit
            .0
            .outputs
            .iter()
            .any(|&w| circuit.0.nodes[w].value != ZERO)
        {
            ct_zeroize_bytes(&mut ask_bytes);
            ct_zeroize_bytes(&mut alpha_bytes);
            return Err(MigrateError::WitnessMismatchWithLegacyCommitment);
        }
        let stmt_bytes = statement.to_transcript_bytes();
        entropy = cshake256_framed_32(
            b"QSAG.PALLAS.HEDGE.V1",
            &[&entropy, &ask_bytes, &alpha_bytes, &stmt_bytes],
        );
        ct_zeroize_bytes(&mut ask_bytes);
        ct_zeroize_bytes(&mut alpha_bytes);

        let views = crate::parallel::map(MIT_REPETITIONS, |rep| {
            simulate(&circuit.0, pallas_seeds(&entropy, &stmt_bytes, rep))
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
        let mut t = pallas_transcript(&statement, &root);
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

/// Verify a Zcash Orchard `Pallas` / `RedPallas` post-quantum ownership migration proof.
pub fn verify_pallas_migration(
    statement: &PallasMigrationStatement,
    proof: &MigrationZkProof,
    expected_domain: &[u8; 32],
    expected_epoch: u64,
) -> Result<(), MigrateError> {
    verify_pallas_migration_with_backend(
        statement,
        proof,
        expected_domain,
        expected_epoch,
        &qsag_accel::CpuReferenceBackend,
    )
}

/// Verify a Zcash Orchard `Pallas` / `RedPallas` migration proof on a selected `AcceleratorBackend`.
pub fn verify_pallas_migration_with_backend<B: AcceleratorBackend>(
    statement: &PallasMigrationStatement,
    proof: &MigrationZkProof,
    expected_domain: &[u8; 32],
    expected_epoch: u64,
    accel: &B,
) -> Result<(), MigrateError> {
    if &statement.migration_domain != expected_domain || statement.epoch_anchor != expected_epoch {
        return Err(MigrateError::SessionMismatch);
    }
    if proof.repetitions.len() != MIT_REPETITIONS
        || statement
            .migration_nullifier
            .iter()
            .any(|&v| v >= GOLDILOCKS_PRIME)
    {
        return Err(MigrateError::MalformedProofStructure);
    }
    let pub_pt = PallasPoint::from_nonidentity_bytes(statement.commitment.compressed_bytes())
        .ok_or(MigrateError::MalformedProofStructure)?;
    let expected_affine = pub_pt
        .to_affine()
        .ok_or(MigrateError::MalformedProofStructure)?;

    let mut t = pallas_transcript(statement, &proof.views_merkle_root);
    let es = challenges(&mut t);
    if proof
        .repetitions
        .iter()
        .zip(&es)
        .any(|(v, &e)| v.opened_e != e)
    {
        return Err(MigrateError::MalformedProofStructure);
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
    let dummy_one = [1u8; 32];
    let circuit = build_pallas_ownership_circuit(statement, expected_affine, &dummy_one, &[0; 32]);
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

    fn sample_pq_dest(tag: &[u8]) -> QsagAddress {
        QsagAddress::from_pubkey_poseidon2(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            tag,
        )
        .unwrap()
    }

    #[test]
    fn pasta_pallas_and_orchard_generator_constants_hold() {
        // Verify `(p - 1)^2 == 1 (mod p)` (`p^2` wraparound check) and Fermat inversion.
        let pm1 = FpPallas([PALLAS_P[0] - 1, PALLAS_P[1], PALLAS_P[2], PALLAS_P[3]]);
        assert_eq!(pm1 * pm1, FpPallas::ONE);
        assert_eq!(pm1 + FpPallas::ONE, FpPallas::ZERO);
        let five_inv = FpPallas::B.inv_or_zero();
        assert_eq!(five_inv * FpPallas::B, FpPallas::ONE);

        // Both Pasta `(-1, 2)` and Zcash Orchard `SpendAuthG` lie on `y^2 = x^3 + 5`
        // and satisfy exact prime subgroup order `[q]G = O`!
        assert!(PallasPoint::PASTA_GENERATOR.is_on_curve());
        assert!(PallasPoint::ORCHARD_SPEND_AUTH_G.is_on_curve());
        assert!(
            PallasPoint::PASTA_GENERATOR
                .scalar_mul_limbs_ct(&PALLAS_Q)
                .is_identity()
        );
        assert!(
            PallasPoint::ORCHARD_SPEND_AUTH_G
                .scalar_mul_limbs_ct(&PALLAS_Q)
                .is_identity()
        );

        // `[q - 1] SpendAuthG == -SpendAuthG`
        let qm1 = FqPallas([PALLAS_Q[0] - 1, PALLAS_Q[1], PALLAS_Q[2], PALLAS_Q[3]]);
        assert_eq!(
            PallasPoint::spend_auth_mul_ct(&qm1),
            PallasPoint::ORCHARD_SPEND_AUTH_G.neg_point()
        );

        // Compressed 32-byte encoding round-trips and rejects `[0u8; 32]` (identity).
        let comp = PallasPoint::ORCHARD_SPEND_AUTH_G.to_compressed_bytes();
        assert_eq!(
            PallasPoint::from_nonidentity_bytes(&comp).unwrap(),
            PallasPoint::ORCHARD_SPEND_AUTH_G
        );
        assert!(PallasPoint::from_nonidentity_bytes(&[0u8; 32]).is_none());

        // RedPallas rerandomization homomorphism: `ak + [alpha] SpendAuthG == [ask + alpha] SpendAuthG`!
        let mut ask_le = [0u8; 32];
        ask_le[0] = 42;
        let mut alpha1 = [0u8; 32];
        alpha1[0] = 99;
        alpha1[7] = 0x13;
        let mut alpha2 = [0u8; 32];
        alpha2[0] = 201;
        alpha2[9] = 0x77;

        let ask = FqPallas::from_nonzero_le_bytes(&ask_le).unwrap();
        let a1 = FqPallas::from_le_bytes(&alpha1).unwrap();
        let a2 = FqPallas::from_le_bytes(&alpha2).unwrap();
        let ak = PallasPoint::spend_auth_mul_ct(&ask);
        let rk1_hom = ak.complete_add(&PallasPoint::spend_auth_mul_ct(&a1));
        let rk1_dir = PallasPoint::spend_auth_mul_ct(&ask.add_mod(&a1));
        let rk2_dir = PallasPoint::spend_auth_mul_ct(&ask.add_mod(&a2));
        assert_eq!(rk1_hom, rk1_dir);
        assert_ne!(rk1_dir, ak);
        assert_ne!(rk1_dir, rk2_dir);
    }

    #[test]
    fn pallas_and_redpallas_zk_migration_roundtrip_and_negative_rejections() {
        let mut ask_le = [0u8; 32];
        ask_le[0] = 0x37;
        ask_le[1] = 0x9a;
        let mut alpha_le = [0u8; 32];
        alpha_le[0] = 0xc5;
        alpha_le[4] = 0x11;

        let wit_ak = PallasOwnershipWitness::from_spend_auth_scalar_le(ask_le).unwrap();
        assert!(format!("{wit_ak:?}").contains("<REDACTED>"));
        let comm_ak = wit_ak.compute_spend_auth_key().unwrap();

        let wit_rk = PallasOwnershipWitness::from_rerandomized_le(ask_le, alpha_le).unwrap();
        let comm_rk = wit_rk.compute_rerandomized_rk().unwrap();
        assert_ne!(comm_ak.compressed_bytes(), comm_rk.compressed_bytes());

        let backend = CpuReferenceBackend;
        let domain = [0x5au8; 32];
        let epoch = 202_611;

        for (wit, comm) in [(&wit_ak, comm_ak), (&wit_rk, comm_rk)] {
            let req = PallasMigrationRequest {
                commitment: comm,
                target: sample_pq_dest(b"zcash-orchard-tachyon-pq"),
                epoch,
                domain,
            };
            let (stmt, mut proof) =
                prove_pallas_migration_in_domain(wit, req.clone(), [0x42; 32], &backend).unwrap();
            assert_eq!(
                verify_pallas_migration(&stmt, &proof, &domain, epoch),
                Ok(())
            );

            // Wrong key rejected at prover gate:
            let mut wrong_ask = ask_le;
            wrong_ask[0] ^= 1;
            let wrong_wit = PallasOwnershipWitness::from_spend_auth_scalar_le(wrong_ask).unwrap();
            assert_eq!(
                prove_pallas_migration_in_domain(&wrong_wit, req, [0x11; 32], &backend),
                Err(MigrateError::WitnessMismatchWithLegacyCommitment)
            );

            // Mutated destination PQ address rejected:
            let mut bad_dest = stmt.clone();
            bad_dest.target_pq_address = sample_pq_dest(b"attacker-pq-dest");
            assert!(verify_pallas_migration(&bad_dest, &proof, &domain, epoch).is_err());

            // Session / domain / nullifier tampering rejected:
            assert_eq!(
                verify_pallas_migration(&stmt, &proof, &[0xff; 32], epoch),
                Err(MigrateError::SessionMismatch)
            );
            assert_eq!(
                verify_pallas_migration(&stmt, &proof, &domain, epoch + 1),
                Err(MigrateError::SessionMismatch)
            );
            let mut bad_nul = stmt.clone();
            bad_nul.migration_nullifier[0] ^= 1;
            assert!(verify_pallas_migration(&bad_nul, &proof, &domain, epoch).is_err());

            // Forged party view products & hidden outputs rejected:
            proof.repetitions[0].pair[0].products[0] ^= 1;
            assert!(verify_pallas_migration(&stmt, &proof, &domain, epoch).is_err());
            proof.repetitions[0].pair[0].products[0] ^= 1;

            proof.repetitions[0].hidden_outputs[0] ^= 1;
            assert!(verify_pallas_migration(&stmt, &proof, &domain, epoch).is_err());
            proof.repetitions[0].hidden_outputs[0] ^= 1;

            assert_eq!(
                verify_pallas_migration(&stmt, &proof, &domain, epoch),
                Ok(())
            );
        }
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
