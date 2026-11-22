//! The Pallas curve `y^2 = x^3 + 5` natively: base field `F_p`, scalar field `F_q`,
//! points, the Zcash point encoding and `GroupHash^P` (hash-to-curve).
//!
//! Protocol specification (v2026.9.0) sections 5.4.9.6 (Pallas and Vesta), 5.4.9.7
//! (`Extract_P`) and 5.4.9.8 (group hash into Pallas: `hash_to_field` with
//! `expand_message_xmd` over BLAKE2b, simplified SWU on the isogenous curve iso-Pallas,
//! then the degree-3 isogeny). The constants are those of the `pasta_curves` crate
//! (0.6.3); every function here is checked against the Zcash test vectors
//! (`orchard_group_hash`, `orchard_map_to_curve`, `orchard_generators`).
//!
//! Field elements are kept in canonical form. Arithmetic on values that can be secret
//! (field operations, the ladder of [`Point::mul`]) is branch-free with fixed iteration
//! counts; decoding, hash-to-curve and affine conversion of public points are not.

use super::blake2::Blake2b;

type U256 = [u64; 4];

#[inline(always)]
fn adc(a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + c as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let t = (a as u128).wrapping_sub(b as u128 + borrow as u128);
    (t as u64, ((t >> 64) as u64) & 1)
}

#[inline(always)]
fn mac(acc: u64, a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = acc as u128 + (a as u128) * (b as u128) + c as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
fn select(mask: u64, a: &U256, b: &U256) -> U256 {
    core::array::from_fn(|i| (a[i] & mask) | (b[i] & !mask))
}

/// All ones when `flag`.
#[inline(always)]
fn mask(flag: bool) -> u64 {
    (flag as u64).wrapping_neg()
}

fn sub_borrow(a: &U256, b: &U256) -> (U256, u64) {
    let mut out = [0u64; 4];
    let mut c = 0;
    for i in 0..4 {
        (out[i], c) = sbb(a[i], b[i], c);
    }
    (out, c)
}

fn from_le(bytes: &[u8]) -> U256 {
    core::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}

fn to_le(a: &U256) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    out
}

/// A prime modulus below `2^255` with its Montgomery constants (`R = 2^256`).
struct Params {
    m: U256,
    /// `-m^-1 mod 2^64`.
    inv: u64,
    /// `R^2 mod m`.
    r2: U256,
    /// `m - 2`.
    m_minus_2: U256,
}

impl Params {
    /// `a - m` if `a >= m`, else `a`, for `a < 2 m`.
    fn reduce_once(&self, a: &U256) -> U256 {
        let (d, borrow) = sub_borrow(a, &self.m);
        select(mask(borrow == 0), &d, a)
    }

    fn add(&self, a: &U256, b: &U256) -> U256 {
        let mut s = [0u64; 4];
        let mut c = 0;
        for i in 0..4 {
            (s[i], c) = adc(a[i], b[i], c);
        }
        debug_assert_eq!(c, 0);
        self.reduce_once(&s)
    }

    fn sub(&self, a: &U256, b: &U256) -> U256 {
        let (d, borrow) = sub_borrow(a, b);
        let mut s = [0u64; 4];
        let mut c = 0;
        let m = mask(borrow == 1);
        for i in 0..4 {
            (s[i], c) = adc(d[i], self.m[i] & m, c);
        }
        s
    }

    /// `a b / R mod m` for `a, b < m`.
    fn mont(&self, a: &U256, b: &U256) -> U256 {
        let mut t = [0u64; 6];
        for &ai in a {
            let mut c = 0;
            for j in 0..4 {
                (t[j], c) = mac(t[j], ai, b[j], c);
            }
            let (s, c2) = adc(t[4], c, 0);
            t[4] = s;
            t[5] = c2;
            let k = t[0].wrapping_mul(self.inv);
            let (_, mut c) = mac(t[0], k, self.m[0], 0);
            for j in 1..4 {
                (t[j - 1], c) = mac(t[j], k, self.m[j], c);
            }
            let (s, c2) = adc(t[4], c, 0);
            t[3] = s;
            t[4] = t[5] + c2;
        }
        self.reduce_once(&[t[0], t[1], t[2], t[3]])
    }

    fn mul(&self, a: &U256, b: &U256) -> U256 {
        self.mont(&self.mont(a, b), &self.r2)
    }

    /// `a^e`, fixed 256 iterations.
    fn pow(&self, a: &U256, e: &U256) -> U256 {
        let am = self.mont(a, &self.r2);
        let mut acc = self.mont(&[1, 0, 0, 0], &self.r2);
        for i in (0..256).rev() {
            acc = self.mont(&acc, &acc);
            let with = self.mont(&acc, &am);
            acc = select(mask((e[i / 64] >> (i % 64)) & 1 == 1), &with, &acc);
        }
        self.mont(&acc, &[1, 0, 0, 0])
    }

    /// The residue of any 256-bit integer.
    fn reduce(&self, a: &U256) -> U256 {
        // m > 2^254, so three conditional subtractions suffice.
        let mut r = *a;
        for _ in 0..3 {
            let (d, borrow) = sub_borrow(&r, &self.m);
            r = select(mask(borrow == 0), &d, &r);
        }
        r
    }

    /// The residue of a 512-bit little-endian integer.
    fn reduce_wide(&self, bytes: &[u8; 64]) -> U256 {
        let lo = self.reduce(&from_le(&bytes[..32]));
        let hi = self.reduce(&from_le(&bytes[32..]));
        // mont(hi, R^2) = hi R = hi 2^256.
        self.add(&lo, &self.mont(&hi, &self.r2))
    }
}

const P: Params = Params {
    m: [
        0x992d_30ed_0000_0001,
        0x2246_98fc_094c_f91b,
        0,
        0x4000_0000_0000_0000,
    ],
    inv: 0x992d_30ec_ffff_ffff,
    r2: [
        0x8c78_ecb3_0000_000f,
        0xd7d3_0dbd_8b0d_e0e7,
        0x7797_a99b_c3c9_5d18,
        0x096d_41af_7b9c_b714,
    ],
    m_minus_2: [
        0x992d_30ec_ffff_ffff,
        0x2246_98fc_094c_f91b,
        0,
        0x4000_0000_0000_0000,
    ],
};

const Q: Params = Params {
    m: [
        0x8c46_eb21_0000_0001,
        0x2246_98fc_0994_a8dd,
        0,
        0x4000_0000_0000_0000,
    ],
    inv: 0x8c46_eb20_ffff_ffff,
    r2: [
        0xfc96_78ff_0000_000f,
        0x67bb_433d_891a_16e3,
        0x7fae_2310_04cc_f590,
        0x096d_41af_7ccf_daa9,
    ],
    m_minus_2: [
        0x8c46_eb20_ffff_ffff,
        0x2246_98fc_0994_a8dd,
        0,
        0x4000_0000_0000_0000,
    ],
};

/// The Pallas base field modulus `p`, little-endian bytes.
pub const BASE_MODULUS_LE: [u8; 32] = [
    0x01, 0x00, 0x00, 0x00, 0xed, 0x30, 0x2d, 0x99, 0x1b, 0xf9, 0x4c, 0x09, 0xfc, 0x98, 0x46, 0x22,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40,
];

/// The Pallas group order `q` (the scalar field modulus), little-endian bytes.
pub const SCALAR_MODULUS_LE: [u8; 32] = [
    0x01, 0x00, 0x00, 0x00, 0x21, 0xeb, 0x46, 0x8c, 0xdd, 0xa8, 0x94, 0x09, 0xfc, 0x98, 0x46, 0x22,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40,
];

macro_rules! field {
    ($name:ident, $params:ident, $doc:literal) => {
        #[doc = $doc]
        #[derive(Clone, Copy)]
        pub struct $name(U256);

        impl PartialEq for $name {
            fn eq(&self, rhs: &Self) -> bool {
                crate::limbs::ct_eq(self.0, rhs.0)
            }
        }
        impl Eq for $name {}

        impl qsag_core::wipe::SecretWipe for $name {
            fn secret_wipe(&mut self) {
                qsag_asm::volatile_fill(&mut self.0, 0);
            }
        }

        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(concat!(stringify!($name), "(..)"))
            }
        }

        impl $name {
            pub const ZERO: Self = Self([0; 4]);
            pub const ONE: Self = Self([1, 0, 0, 0]);

            pub const fn from_u64(v: u64) -> Self {
                Self([v, 0, 0, 0])
            }

            /// Words of a canonical value, least significant first.
            #[allow(dead_code)]
            const fn from_raw(words: U256) -> Self {
                Self(words)
            }

            /// Canonical 32-byte little-endian decoding; `None` at or above the modulus.
            pub fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
                let v = from_le(bytes);
                let (_, borrow) = sub_borrow(&v, &$params.m);
                (borrow == 1).then_some(Self(v))
            }

            /// The residue of a 256-bit little-endian integer.
            pub fn from_bytes_reduced(bytes: &[u8; 32]) -> Self {
                Self($params.reduce(&from_le(bytes)))
            }

            /// The residue of a 512-bit little-endian integer (`ToBase` / `ToScalar`).
            pub fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
                Self($params.reduce_wide(bytes))
            }

            pub fn to_bytes(self) -> [u8; 32] {
                to_le(&self.0)
            }

            pub fn is_zero(self) -> bool {
                (self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0
            }

            pub fn is_odd(self) -> bool {
                self.0[0] & 1 == 1
            }

            pub fn square(self) -> Self {
                self * self
            }

            pub fn double(self) -> Self {
                self + self
            }

            /// `self^e` for a public or secret exponent (fixed iteration count).
            pub fn pow(self, e: &[u64; 4]) -> Self {
                Self($params.pow(&self.0, e))
            }

            /// The inverse, or zero for zero.
            pub fn invert(self) -> Self {
                self.pow(&$params.m_minus_2)
            }

            /// `a` when `flag`, else `b`, without branching on `flag`.
            pub fn select(flag: bool, a: Self, b: Self) -> Self {
                Self(crate::limbs::ct_select(flag, a.0, b.0))
            }

        }

        impl core::ops::Add for $name {
            type Output = Self;
            fn add(self, rhs: Self) -> Self {
                Self($params.add(&self.0, &rhs.0))
            }
        }

        impl core::ops::Sub for $name {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self {
                Self($params.sub(&self.0, &rhs.0))
            }
        }

        impl core::ops::Neg for $name {
            type Output = Self;
            fn neg(self) -> Self {
                Self($params.sub(&[0; 4], &self.0))
            }
        }

        impl core::ops::Mul for $name {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self {
                Self($params.mul(&self.0, &rhs.0))
            }
        }
    };
}

field!(Fp, P, "Element of the Pallas base field, canonical.");
field!(Fq, Q, "Element of the Pallas scalar field, canonical.");

/// `(s - 1) / 2` for `p - 1 = 2^32 s`.
const P_S_MINUS_1_HALF: U256 = [0x04a6_7c8d_cc96_9876, 0x0000_0000_1123_4c7e, 0, 0x2000_0000];
/// `5^s`, a primitive `2^32`-th root of unity.
const P_ROOT_OF_UNITY: Fp = Fp::from_raw([
    0xbdad_6fab_d87e_a32f,
    0xea32_2bf2_b7bb_7584,
    0x3621_2083_0561_f81a,
    0x2bce_74de_ac30_ebda,
]);

impl Fp {
    /// A square root (Tonelli-Shanks with fixed iteration counts), if one exists.
    pub fn sqrt(self) -> Option<Self> {
        let w = self.pow(&P_S_MINUS_1_HALF);
        let mut x = self * w;
        let mut b = x * w;
        let mut c = P_ROOT_OF_UNITY;
        let minus_one = -Self::ONE;
        for r in (2..=32).rev() {
            let mut d = b;
            for _ in 0..(r - 2) {
                d = d.square();
            }
            let need = d == minus_one;
            let c2 = c.square();
            x = Self::select(need, x * c, x);
            b = Self::select(need, b * c2, b);
            c = c2;
        }
        (x.square() == self).then_some(x)
    }
}

impl Fq {
    /// The scalar with the same integer value as a base field element (`p < q`, so every
    /// base field element is a canonical scalar).
    pub fn from_base(x: Fp) -> Self {
        Self(x.0)
    }
}

// ============================================================================
// Points
// ============================================================================

const B3: Fp = Fp::from_u64(15);
const B: Fp = Fp::from_u64(5);

/// A point of Pallas in homogeneous projective coordinates; the identity is `(0 : 1 : 0)`.
#[derive(Clone, Copy, Debug)]
pub struct Point {
    x: Fp,
    y: Fp,
    z: Fp,
}

impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        let (a, b) = (self.z.is_zero(), other.z.is_zero());
        (a & b)
            | (!a
                & !b
                & (self.x * other.z == other.x * self.z)
                & (self.y * other.z == other.y * self.z))
    }
}

impl Eq for Point {}

impl Point {
    pub const IDENTITY: Self = Self {
        x: Fp::ZERO,
        y: Fp::ONE,
        z: Fp::ZERO,
    };

    /// The point with these affine coordinates; `None` if they are not on the curve.
    pub fn from_affine(x: Fp, y: Fp) -> Option<Self> {
        (y.square() == x.square() * x + B).then_some(Self { x, y, z: Fp::ONE })
    }

    /// Sinsemilla excludes infinity and coincident affine x coordinates.
    pub(super) fn incomplete_add_defined(&self, rhs: &Self) -> bool {
        !self.is_identity() & !rhs.is_identity() & (self.x * rhs.z != rhs.x * self.z)
    }

    pub fn is_identity(&self) -> bool {
        self.z.is_zero()
    }

    /// Complete addition (Renes, Costello, Batina 2016, algorithm 7, `a = 0`).
    #[allow(clippy::should_implement_trait)]
    pub fn add(&self, other: &Self) -> Self {
        let mut t0 = self.x * other.x;
        let mut t1 = self.y * other.y;
        let mut t2 = self.z * other.z;
        let t3 = (self.x + self.y) * (other.x + other.y) - (t0 + t1);
        let t4 = (self.y + self.z) * (other.y + other.z) - (t1 + t2);
        let mut y3 = (self.x + self.z) * (other.x + other.z) - (t0 + t2);
        t0 = t0 + t0 + t0;
        t2 = B3 * t2;
        let mut z3 = t1 + t2;
        t1 = t1 - t2;
        y3 = B3 * y3;
        let x3 = t3 * t1 - t4 * y3;
        y3 = t1 * z3 + y3 * t0;
        t0 = t0 * t3;
        z3 = z3 * t4 + t0;
        Self {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    pub fn double(&self) -> Self {
        self.add(self)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn neg(&self) -> Self {
        Self {
            x: self.x,
            y: -self.y,
            z: self.z,
        }
    }

    fn cswap(swap: bool, a: &mut Self, b: &mut Self) {
        let (ax, ay, az) = (a.x, a.y, a.z);
        a.x = Fp::select(swap, b.x, ax);
        a.y = Fp::select(swap, b.y, ay);
        a.z = Fp::select(swap, b.z, az);
        b.x = Fp::select(swap, ax, b.x);
        b.y = Fp::select(swap, ay, b.y);
        b.z = Fp::select(swap, az, b.z);
    }

    /// `[k] self` by a Montgomery ladder over all 256 bits of the scalar words.
    fn mul_words(&self, k: &[u64; 4]) -> Self {
        let mut r0 = Self::IDENTITY;
        let mut r1 = *self;
        for i in (0..256).rev() {
            let bit = (k[i / 64] >> (i % 64)) & 1 == 1;
            Self::cswap(bit, &mut r0, &mut r1);
            let sum = r0.add(&r1);
            r0 = r0.double();
            r1 = sum;
            Self::cswap(bit, &mut r0, &mut r1);
        }
        r0
    }

    /// `[k] self`; branch-free in `k`.
    pub fn mul(&self, k: &Fq) -> Self {
        self.mul_words(&k.0)
    }

    /// Affine coordinates; `None` for the identity.
    pub fn to_affine(&self) -> Option<(Fp, Fp)> {
        if self.z.is_zero() {
            return None;
        }
        let zi = self.z.invert();
        Some((self.x * zi, self.y * zi))
    }

    /// Affine coordinates of many points with one inversion; `None` for the identity.
    /// Public points only.
    pub fn batch_to_affine(points: &[Point]) -> alloc::vec::Vec<Option<(Fp, Fp)>> {
        let mut prefix = alloc::vec::Vec::with_capacity(points.len());
        let mut acc = Fp::ONE;
        for p in points {
            prefix.push(acc);
            if !p.z.is_zero() {
                acc = acc * p.z;
            }
        }
        let mut inv = acc.invert();
        let mut out = alloc::vec![None; points.len()];
        for (i, p) in points.iter().enumerate().rev() {
            if p.z.is_zero() {
                continue;
            }
            let zi = inv * prefix[i];
            inv = inv * p.z;
            out[i] = Some((p.x * zi, p.y * zi));
        }
        out
    }

    /// `Extract_P`: the affine `x` coordinate, or zero for the identity.
    pub fn extract(&self) -> Fp {
        self.x * self.z.invert()
    }

    /// `repr_P`: little-endian `x` with the parity of `y` in the top bit; all zero for the
    /// identity.
    pub fn to_bytes(&self) -> [u8; 32] {
        let zi = self.z.invert();
        let (x, y) = (self.x * zi, self.y * zi);
        let mut out = x.to_bytes();
        out[31] |= (y.is_odd() as u8) << 7;
        out
    }

    /// `abst_P`: strict decoding. The identity is the all-zero string only; `x` must be
    /// canonical and on the curve.
    pub fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let y_odd = bytes[31] >> 7 == 1;
        let mut xb = *bytes;
        xb[31] &= 0x7f;
        let x = Fp::from_bytes(&xb)?;
        if x.is_zero() && !y_odd {
            return Some(Self::IDENTITY);
        }
        let y = (x.square() * x + B).sqrt()?;
        let y = if y.is_odd() == y_odd { y } else { -y };
        Some(Self { x, y, z: Fp::ONE })
    }

    /// [`Self::from_bytes`] that also rejects the identity.
    pub fn from_bytes_nonidentity(bytes: &[u8; 32]) -> Option<Self> {
        Self::from_bytes(bytes).filter(|p| !p.is_identity())
    }
}

// ============================================================================
// Hash to curve
// ============================================================================

const ISO_A: Fp = Fp::from_raw([
    0x92bb_4b0b_657a_014b,
    0xb741_3458_1a27_a59f,
    0x49be_2d72_5837_0742,
    0x1835_4a2e_b0ea_8c9c,
]);
const ISO_B: Fp = Fp::from_u64(1265);
/// `Z = -13`.
const SWU_Z: Fp = Fp::from_raw([
    0x992d_30ec_ffff_fff4,
    0x2246_98fc_094c_f91b,
    0,
    0x4000_0000_0000_0000,
]);

/// Coefficients of the isogeny (`pasta_curves` `Ep::ISOGENY_CONSTANTS`).
const ISOGENY: [[u64; 4]; 13] = [
    [
        0x775f6034aaaaaaab,
        0x4081775473d8375b,
        0xe38e38e38e38e38e,
        0x0e38e38e38e38e38,
    ],
    [
        0x8cf863b02814fb76,
        0x0f93b82ee4b99495,
        0x267c7ffa51cf412a,
        0x3509afd51872d88e,
    ],
    [
        0x0eb64faef37ea4f7,
        0x380af066cfeb6d69,
        0x98c7d7ac3d98fd13,
        0x17329b9ec5253753,
    ],
    [
        0xeebec06955555580,
        0x8102eea8e7b06eb6,
        0xc71c71c71c71c71c,
        0x1c71c71c71c71c71,
    ],
    [
        0xc47f2ab668bcd71f,
        0x9c434ac1c96b6980,
        0x5a607fcce0494a79,
        0x1d572e7ddc099cff,
    ],
    [
        0x2aa3af1eae5b6604,
        0xb4abf9fb9a1fc81c,
        0x1d13bf2a7f22b105,
        0x325669becaecd5d1,
    ],
    [
        0x5ad985b5e38e38e4,
        0x7642b01ad461bad2,
        0x4bda12f684bda12f,
        0x1a12f684bda12f68,
    ],
    [
        0xc67c31d8140a7dbb,
        0x07c9dc17725cca4a,
        0x133e3ffd28e7a095,
        0x1a84d7ea8c396c47,
    ],
    [
        0x02e2be87d225b234,
        0x1765e924f7459378,
        0x303216cce1db9ff1,
        0x3fb98ff0d2ddcadd,
    ],
    [
        0x93e53ab371c71c4f,
        0x0ac03e8e134eb3e4,
        0x7b425ed097b425ed,
        0x025ed097b425ed09,
    ],
    [
        0x5a28279b1d1b42ae,
        0x5941a3a4a97aa1b3,
        0x0790bfb3506defb6,
        0x0c02c5bcca0e6b7f,
    ],
    [
        0x4d90ab820b12320a,
        0xd976bbfabbc5661d,
        0x573b3d7f7d681310,
        0x17033d3c60c68173,
    ],
    [
        0x992d30ecfffffde5,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ],
];

/// `hash_to_field` of the `pasta_curves` crate: two field elements from
/// `expand_message_xmd` over BLAKE2b-512 with the domain separation tag
/// `domain_prefix || "-pallas_XMD:BLAKE2b_SSWU_RO_"`.
pub fn hash_to_field(domain_prefix: &str, message: &[u8]) -> [Fp; 2] {
    const CURVE_ID: &[u8] = b"pallas";
    const SUFFIX: &[u8] = b"_XMD:BLAKE2b_SSWU_RO_";
    let dst_len = [(22 + CURVE_ID.len() + domain_prefix.len()) as u8];
    assert!(22 + CURVE_ID.len() + domain_prefix.len() < 256);
    let dst = |st: &mut Blake2b| {
        st.update(domain_prefix.as_bytes())
            .update(b"-")
            .update(CURVE_ID)
            .update(SUFFIX)
            .update(&dst_len);
    };
    let mut st = Blake2b::new(64, &[0; 16]);
    st.update(&[0; 128]).update(message).update(&[0, 128, 0]);
    dst(&mut st);
    let b0 = st.finalize();

    let mut st = Blake2b::new(64, &[0; 16]);
    st.update(&b0).update(&[1]);
    dst(&mut st);
    let b1 = st.finalize();

    let mut mixed = [0u8; 64];
    for i in 0..64 {
        mixed[i] = b0[i] ^ b1[i];
    }
    let mut st = Blake2b::new(64, &[0; 16]);
    st.update(&mixed).update(&[2]);
    dst(&mut st);
    let b2 = st.finalize();

    [b1, b2].map(|mut big| {
        big.reverse();
        Fp::from_bytes_wide(&big)
    })
}

/// Simplified SWU map to an affine point of iso-Pallas.
fn map_to_iso(u: Fp) -> (Fp, Fp) {
    let g = |x: Fp| (x.square() + ISO_A) * x + ISO_B;
    let z_u2 = SWU_Z * u.square();
    let ta = z_u2.square() + z_u2;
    let num_x1 = ISO_B * (ta + Fp::ONE);
    let div = ISO_A * if ta.is_zero() { SWU_Z } else { -ta };
    let x1 = num_x1 * div.invert();
    let (x, y) = match g(x1).sqrt() {
        Some(y) => (x1, y),
        None => {
            let x2 = z_u2 * x1;
            (x2, g(x2).sqrt().expect("one of g(x1), g(x2) is a square"))
        }
    };
    (x, if y.is_odd() == u.is_odd() { y } else { -y })
}

/// Affine addition on iso-Pallas; `None` is the identity.
fn iso_add(p: (Fp, Fp), q: (Fp, Fp)) -> Option<(Fp, Fp)> {
    let lambda = if p.0 == q.0 {
        if p.1 != q.1 || p.1.is_zero() {
            return None;
        }
        (p.0.square() * Fp::from_u64(3) + ISO_A) * p.1.double().invert()
    } else {
        (q.1 - p.1) * (q.0 - p.0).invert()
    };
    let x = lambda.square() - p.0 - q.0;
    Some((x, lambda * (p.0 - x) - p.1))
}

/// The degree-3 isogeny from iso-Pallas to Pallas.
fn iso_map(p: Option<(Fp, Fp)>) -> Point {
    let Some((x, y)) = p else {
        return Point::IDENTITY;
    };
    let iso = ISOGENY.map(Fp::from_raw);
    let num_x = ((iso[0] * x + iso[1]) * x + iso[2]) * x + iso[3];
    let div_x = (x + iso[4]) * x + iso[5];
    let num_y = (((iso[6] * x + iso[7]) * x + iso[8]) * x + iso[9]) * y;
    let div_y = ((x + iso[10]) * x + iso[11]) * x + iso[12];
    if div_x.is_zero() || div_y.is_zero() {
        return Point::IDENTITY;
    }
    Point {
        x: num_x * div_x.invert(),
        y: num_y * div_y.invert(),
        z: Fp::ONE,
    }
}

/// `GroupHash^P(domain_prefix, message)` (protocol specification 5.4.9.8). Public inputs
/// only: not constant time.
pub fn hash_to_curve(domain_prefix: &str, message: &[u8]) -> Point {
    let [u0, u1] = hash_to_field(domain_prefix, message);
    iso_map(iso_add(map_to_iso(u0), map_to_iso(u1)))
}

#[cfg(test)]
mod tests {
    use super::super::vectors::hex32;
    use super::*;

    #[test]
    fn field_constants_are_consistent() {
        // The moduli as bytes match the Montgomery parameters.
        assert_eq!(to_le(&P.m), BASE_MODULUS_LE);
        assert_eq!(to_le(&Q.m), SCALAR_MODULUS_LE);
        for params in [&P, &Q] {
            // m * (-inv) = 1 mod 2^64, R^2 as claimed, m - 2 as claimed.
            assert_eq!(params.m[0].wrapping_mul(params.inv.wrapping_neg()), 1);
            let (two, _) = sub_borrow(&params.m, &params.m_minus_2);
            assert_eq!(two, [2, 0, 0, 0]);
            // mont(1, R^2) = R mod m = 2^256 mod m; (2^128)^2 must agree.
            let r = params.mont(&[1, 0, 0, 0], &params.r2);
            let two128 = [0, 0, 1, 0];
            assert_eq!(params.mul(&two128, &two128), r);
        }
        // The root of unity has order exactly 2^32.
        let mut c = P_ROOT_OF_UNITY;
        for _ in 0..31 {
            c = c.square();
        }
        assert_eq!(c, -Fp::ONE);
        // Inversion and square roots.
        let a = Fp::from_u64(0xdead_beef_1234_5678);
        assert_eq!(a * a.invert(), Fp::ONE);
        assert_eq!(Fp::ZERO.invert(), Fp::ZERO);
        let r = (a * a).sqrt().unwrap();
        assert!(r == a || r == -a);
        assert!(
            Fp::from_u64(5).sqrt().is_none(),
            "5 is the non-residue behind the root"
        );
        let s = Fq::from_u64(77);
        assert_eq!(s * s.invert(), Fq::ONE);
    }

    #[test]
    fn wide_reduction_matches_schoolbook() {
        // 2^256 * hi + lo with small parts, against direct field arithmetic.
        let mut bytes = [0u8; 64];
        bytes[0] = 7;
        bytes[32] = 3;
        let two256 = Fp::from_u64(1 << 32).square().square().square();
        assert_eq!(
            Fp::from_bytes_wide(&bytes),
            two256 * Fp::from_u64(3) + Fp::from_u64(7)
        );
        // All ones: (2^512 - 1) mod p.
        let all = Fp::from_bytes_wide(&[0xff; 64]);
        assert_eq!(all + Fp::ONE, two256.square());
        assert!(Fp::from_bytes(&[0xff; 32]).is_none());
        assert!(Fp::from_bytes(&BASE_MODULUS_LE).is_none());
        let mut pm1 = BASE_MODULUS_LE;
        pm1[0] -= 1;
        assert_eq!(Fp::from_bytes(&pm1).unwrap(), -Fp::ONE);
    }

    #[test]
    fn group_hash_vectors() {
        assert!(super::super::vectors::GROUP_HASH.len() >= 10);
        for (domain, msg, want) in super::super::vectors::GROUP_HASH {
            let p = hash_to_curve(domain, &super::super::vectors::unhex(msg));
            assert_eq!(p.to_bytes(), hex32(want), "domain {domain}");
            assert_eq!(Point::from_bytes(&hex32(want)).unwrap(), p);
        }
    }

    #[test]
    fn map_to_curve_vectors() {
        // The vectors give the simplified-SWU output on iso-Pallas, before the isogeny,
        // in the same compressed encoding.
        assert!(super::super::vectors::MAP_TO_CURVE.len() >= 10);
        for (u, want) in super::super::vectors::MAP_TO_CURVE {
            let (x, y) = map_to_iso(Fp::from_bytes(&hex32(u)).unwrap());
            assert_eq!(y.square(), (x.square() + ISO_A) * x + ISO_B);
            let mut enc = x.to_bytes();
            enc[31] |= (y.is_odd() as u8) << 7;
            assert_eq!(enc, hex32(want));
        }
    }

    #[test]
    fn point_arithmetic_laws() {
        let g = hash_to_curve("z.cash:Orchard", b"G");
        let two = g.double();
        assert_eq!(two, g.add(&g));
        assert_eq!(g.mul(&Fq::from_u64(2)), two);
        assert_eq!(g.mul(&Fq::from_u64(5)), two.double().add(&g));
        assert!(g.add(&g.neg()).is_identity());
        assert_eq!(g.add(&Point::IDENTITY), g);
        // The group order annihilates the generator.
        assert!(g.mul_words(&Q.m).is_identity());
        assert_eq!(g.mul(&(-Fq::ONE)), g.neg());
        // Encoding round trip, sign bit and rejections.
        let enc = g.to_bytes();
        assert_eq!(Point::from_bytes(&enc).unwrap(), g);
        let mut flipped = enc;
        flipped[31] ^= 0x80;
        assert_eq!(Point::from_bytes(&flipped).unwrap(), g.neg());
        assert!(Point::from_bytes(&[0; 32]).unwrap().is_identity());
        assert!(Point::from_bytes_nonidentity(&[0; 32]).is_none());
        let mut sign_only = [0u8; 32];
        sign_only[31] = 0x80;
        assert!(Point::from_bytes(&sign_only).is_none());
        assert!(Point::from_bytes(&BASE_MODULUS_LE).is_none());
        // Batch conversion agrees with the single one, identity included.
        let pts = [g, Point::IDENTITY, two, g.mul(&Fq::from_u64(77))];
        let batch = Point::batch_to_affine(&pts);
        for (p, a) in pts.iter().zip(&batch) {
            assert_eq!(p.to_affine(), *a);
        }
    }
}
