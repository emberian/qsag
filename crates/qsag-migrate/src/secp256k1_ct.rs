//! Fixed-schedule pure-Rust `secp256k1` ($y^2 = x^3 + 7$ over
//! $p = 2^{256} - 2^{32} - 977$) field & Renes-Costello-Batina complete projective curve arithmetic
//! Source-level selection uses masks; generated-code timing has not been assessed.

use qsag_accel::ct::{ct_eq_u64, ct_lt_u64, ct_select_u64, ct_zeroize_u64s};

/// `secp256k1` prime $p = 2^{256} - 2^{32} - 977$ in little-endian 64-bit limbs.
pub const SECP_P: [u64; 4] = [
    0xFFFF_FFFE_FFFF_FC2F,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
];

/// Reduction constant $c = 2^{256} - p = 2^{32} + 977 = \text{0x1\_000003D1}$.
const SECP_C: u64 = 0x0000_0001_0000_03D1;

/// `secp256k1` group order $n$ in little-endian 64-bit limbs.
pub const SECP_N: [u64; 4] = [
    0xBFD2_5E8C_D036_4141,
    0xBAAEDCE6_AF48A03B,
    0xFFFF_FFFF_FFFF_FFFE,
    0xFFFF_FFFF_FFFF_FFFF,
];

/// Generator $G_x$ in little-endian 64-bit limbs.
pub const SECP_GX: [u64; 4] = [
    0x59F2_815B_16F8_1798,
    0x029B_FCDB_2DCE_28D9,
    0x55A0_6295_CE87_0B07,
    0x79BE_667E_F9DC_BBAC,
];

/// Generator $G_y$ in little-endian 64-bit limbs.
pub const SECP_GY: [u64; 4] = [
    0x9C47_D08F_FB10_D4B8,
    0xFD17_B448_A685_5419,
    0x5DA4_FBFC_0E11_08A8,
    0x483A_DA77_26A3_C465,
];

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Fp256(pub [u64; 4]);

impl Fp256 {
    pub const ZERO: Self = Self([0, 0, 0, 0]);
    pub const ONE: Self = Self([1, 0, 0, 0]);
    pub const B3: Self = Self([21, 0, 0, 0]); // 3 * b = 21 for y^2 = x^3 + 7

    pub fn from_be_bytes(bytes: &[u8; 32]) -> Self {
        let mut limbs = [0u64; 4];
        for (i, slot) in limbs.iter_mut().enumerate() {
            let off = (3 - i) * 8;
            *slot = u64::from_be_bytes(bytes[off..off + 8].try_into().unwrap());
        }
        Self(limbs).normalize()
    }

    pub fn to_be_bytes(self) -> [u8; 32] {
        let c = self.normalize();
        let mut out = [0u8; 32];
        for (i, &limb) in c.0.iter().enumerate() {
            let off = (3 - i) * 8;
            out[off..off + 8].copy_from_slice(&limb.to_be_bytes());
        }
        out
    }

    #[inline]
    fn sub_raw(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], bool) {
        let mut out = [0u64; 4];
        let mut br = 0u64;
        for (i, slot) in out.iter_mut().enumerate() {
            let (d1, b1) = a[i].overflowing_sub(b[i]);
            let (d2, b2) = d1.overflowing_sub(br);
            *slot = d2;
            br = (b1 as u64) | (b2 as u64);
        }
        (out, br != 0)
    }

    #[inline]
    pub fn ct_select(choice: bool, t: Self, f: Self) -> Self {
        Self([
            ct_select_u64(choice, t.0[0], f.0[0]),
            ct_select_u64(choice, t.0[1], f.0[1]),
            ct_select_u64(choice, t.0[2], f.0[2]),
            ct_select_u64(choice, t.0[3], f.0[3]),
        ])
    }

    #[inline]
    pub fn normalize(self) -> Self {
        let (diff, borrow) = Self::sub_raw(self.0, SECP_P);
        Self::ct_select(!borrow, Self(diff), self)
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        let c = self.normalize();
        ct_eq_u64(c.0[0] | c.0[1] | c.0[2] | c.0[3], 0)
    }

    #[inline]
    pub fn is_odd(self) -> bool {
        (self.normalize().0[0] & 1) == 1
    }

    #[inline]
    pub fn add_mod(self, rhs: Self) -> Self {
        let mut sum = [0u64; 4];
        let mut carry = 0u128;
        for (i, slot) in sum.iter_mut().enumerate() {
            let s = (self.0[i] as u128) + (rhs.0[i] as u128) + carry;
            *slot = s as u64;
            carry = s >> 64;
        }
        // Fold `carry * 2^256 == carry * SECP_C`
        let mut c2 = carry * (SECP_C as u128);
        for item in &mut sum {
            let s = (*item as u128) + (c2 & 0xFFFF_FFFF_FFFF_FFFF);
            *item = s as u64;
            c2 = (c2 >> 64) + (s >> 64);
        }
        c2 *= SECP_C as u128;
        for item in &mut sum {
            let s = (*item as u128) + c2;
            *item = s as u64;
            c2 = s >> 64;
        }
        Self(sum).normalize()
    }

    #[inline]
    pub fn neg_mod(self) -> Self {
        let c = self.normalize();
        let (diff, _) = Self::sub_raw(SECP_P, c.0);
        Self::ct_select(c.is_zero(), Self::ZERO, Self(diff))
    }

    #[inline]
    pub fn sub_mod(self, rhs: Self) -> Self {
        self.add_mod(rhs.neg_mod())
    }

    #[inline]
    pub fn mul_mod(self, rhs: Self) -> Self {
        let mut wide = [0u64; 8];
        for (i, &left) in self.0.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &right) in rhs.0.iter().enumerate() {
                let cur = (wide[i + j] as u128) + (left as u128) * (right as u128) + carry;
                wide[i + j] = cur as u64;
                carry = cur >> 64;
            }
            wide[i + 4] = carry as u64;
        }
        // First fold: `wide[4..8] * SECP_C + wide[0..4]` -> 5 limbs `acc[0..5]`
        let mut acc = [0u64; 5];
        let mut carry = 0u128;
        for (i, slot) in acc.iter_mut().take(4).enumerate() {
            let cur = (wide[i] as u128) + (wide[i + 4] as u128) * (SECP_C as u128) + carry;
            *slot = cur as u64;
            carry = cur >> 64;
        }
        acc[4] = carry as u64;

        // Second fold: `acc[4] * SECP_C + acc[0..4]`
        let mut out = [0u64; 4];
        let mut c2 = (acc[4] as u128) * (SECP_C as u128);
        for (i, slot) in out.iter_mut().enumerate() {
            let cur = (acc[i] as u128) + c2;
            *slot = cur as u64;
            c2 = cur >> 64;
        }
        // Final carry (at most 1): add `c2 * SECP_C` branchlessly
        let mut out2 = [0u64; 4];
        let mut c3 = c2 * (SECP_C as u128);
        for (i, slot) in out2.iter_mut().enumerate() {
            let cur = (out[i] as u128) + c3;
            *slot = cur as u64;
            c3 = cur >> 64;
        }
        Self(out2).normalize()
    }

    #[inline]
    pub fn sq(self) -> Self {
        self.mul_mod(self)
    }

    /// Constant-time fixed-256-iteration Fermat inversion $a^{p - 2} \bmod p$.
    pub fn inv_or_zero(self) -> Self {
        // p - 2 = FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFE_FFFFFC2D
        let p_minus_2: [u64; 4] = [
            0xFFFF_FFFE_FFFF_FC2D,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF,
        ];
        let mut base = self;
        let mut acc = Self::ONE;
        for limb in p_minus_2 {
            for bit in 0..64 {
                let take = ((limb >> bit) & 1) == 1;
                let prod = acc.mul_mod(base);
                acc = Self::ct_select(take, prod, acc);
                base = base.sq();
            }
        }
        acc
    }
}

impl core::ops::Add for Fp256 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        self.add_mod(rhs)
    }
}

impl core::ops::Sub for Fp256 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        self.sub_mod(rhs)
    }
}

impl core::ops::Mul for Fp256 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.mul_mod(rhs)
    }
}

impl core::ops::Neg for Fp256 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        self.neg_mod()
    }
}

/// Homogeneous projective point $(X : Y : Z)$ on `secp256k1` ($\mathcal{O} = (0 : 1 : 0)$).
#[derive(Clone)]
pub struct SecpPoint {
    pub x: Fp256,
    pub y: Fp256,
    pub z: Fp256,
}

impl Drop for SecpPoint {
    fn drop(&mut self) {
        self.wipe();
    }
}

impl SecpPoint {
    pub const IDENTITY: Self = Self {
        x: Fp256::ZERO,
        y: Fp256::ONE,
        z: Fp256::ZERO,
    };

    pub const GENERATOR: Self = Self {
        x: Fp256(SECP_GX),
        y: Fp256(SECP_GY),
        z: Fp256::ONE,
    };

    #[inline]
    pub fn ct_cswap(swap: bool, a: &mut Self, b: &mut Self) {
        let nx = Fp256::ct_select(swap, b.x, a.x);
        let bx = Fp256::ct_select(swap, a.x, b.x);
        let ny = Fp256::ct_select(swap, b.y, a.y);
        let by = Fp256::ct_select(swap, a.y, b.y);
        let nz = Fp256::ct_select(swap, b.z, a.z);
        let bz = Fp256::ct_select(swap, a.z, b.z);
        a.x = nx;
        a.y = ny;
        a.z = nz;
        b.x = bx;
        b.y = by;
        b.z = bz;
    }

    /// Complete exception-free Renes-Costello-Batina (2016) Algorithm 7 projective point addition
    /// for prime-order $y^2 = x^3 + b$ (`a = 0, 3b = 21`). Handles $\mathcal{O}$, doubling, and
    /// general addition identically with **zero branches**!
    pub fn complete_add(&self, other: &Self) -> Self {
        let mut t0 = self.x * other.x;
        let mut t1 = self.y * other.y;
        let mut t2 = self.z * other.z;
        let mut t3 = (self.x + self.y) * (other.x + other.y) - (t0 + t1);
        let t4 = (self.y + self.z) * (other.y + other.z) - (t1 + t2);
        let mut y3 = (self.x + self.z) * (other.x + other.z) - (t0 + t2);

        let x3_tmp = t0 + t0;
        t0 = x3_tmp + t0;
        t2 = Fp256::B3 * t2;
        let mut z3 = t1 + t2;
        t1 = t1 - t2;
        y3 = Fp256::B3 * y3;

        let x3 = (t3 * t1) - (t4 * y3);
        y3 = (t1 * z3) + (y3 * t0);
        t0 = t0 * t3;
        z3 = (z3 * t4) + t0;
        let _ = &mut t3;
        Self {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// Fixed-schedule 256-bit Montgomery ladder scalar multiplication $d \cdot P$.
    pub fn scalar_mul_ct(&self, scalar_be: &[u8; 32]) -> Self {
        let mut r0 = Self::IDENTITY;
        let mut r1 = self.clone();
        for &byte in scalar_be {
            for bit_in_byte in (0..8).rev() {
                let bit = ((byte >> bit_in_byte) & 1) == 1;
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

    /// Four-bit fixed-base multiplication with a full masked table scan.
    pub fn generator_mul_ct(scalar_be: &[u8; 32]) -> Self {
        let mut acc = Self::IDENTITY;
        for &byte in scalar_be {
            for nibble in [byte >> 4, byte & 15] {
                for _ in 0..4 {
                    acc = acc.complete_add(&acc);
                }
                let mut selected = Self::IDENTITY;
                for (index, coords) in GENERATOR_TABLE.iter().enumerate() {
                    let take = ct_eq_u64(index as u64, nibble as u64);
                    selected.x = Fp256::ct_select(take, Fp256(coords[0]), selected.x);
                    selected.y = Fp256::ct_select(take, Fp256(coords[1]), selected.y);
                    selected.z = Fp256::ct_select(take, Fp256(coords[2]), selected.z);
                }
                acc = acc.complete_add(&selected);
            }
        }
        acc
    }

    pub fn to_affine(&self) -> Option<(Fp256, Fp256)> {
        if self.z.is_zero() {
            return None;
        }
        let z_inv = self.z.inv_or_zero();
        Some((self.x * z_inv, self.y * z_inv))
    }

    pub fn to_compressed_bytes(&self) -> Option<[u8; 33]> {
        let (x, y) = self.to_affine()?;
        let mut out = [0u8; 33];
        out[0] = 0x02 | (y.is_odd() as u8);
        out[1..33].copy_from_slice(&x.to_be_bytes());
        Some(out)
    }

    pub fn to_uncompressed_64(&self) -> Option<[u8; 64]> {
        let (x, y) = self.to_affine()?;
        let mut out = [0u8; 64];
        out[0..32].copy_from_slice(&x.to_be_bytes());
        out[32..64].copy_from_slice(&y.to_be_bytes());
        Some(out)
    }

    pub fn wipe(&mut self) {
        ct_zeroize_u64s(&mut self.x.0);
        ct_zeroize_u64s(&mut self.y.0);
        ct_zeroize_u64s(&mut self.z.0);
    }
}

/// Check `0 <= scalar_be < SECP_N`, including the valid zero derivation offset.
pub fn secp_scalar_is_canonical(scalar_be: &[u8; 32]) -> bool {
    let mut limbs = [0u64; 4];
    for (i, slot) in limbs.iter_mut().enumerate() {
        let off = (3 - i) * 8;
        *slot = u64::from_be_bytes(scalar_be[off..off + 8].try_into().unwrap());
    }
    let mut br = 0u64;
    for (&limb, &order) in limbs.iter().zip(&SECP_N) {
        let (d1, b1) = limb.overflowing_sub(order);
        let (_, b2) = d1.overflowing_sub(br);
        br = (b1 as u64) | (b2 as u64);
    }
    ct_zeroize_u64s(&mut limbs);
    br != 0
}

/// Validate a private scalar, excluding zero.
pub fn secp_scalar_is_valid_nonzero(scalar_be: &[u8; 32]) -> bool {
    let nonzero = scalar_be.iter().fold(0u8, |a, b| a | b) != 0;
    secp_scalar_is_canonical(scalar_be) & nonzero
}

/// Constant-time modular addition `(a + b) mod SECP_N` on 32-byte big-endian scalars.
pub fn secp_scalar_add_mod_n(a_be: &[u8; 32], b_be: &[u8; 32]) -> [u8; 32] {
    let mut a = [0u64; 4];
    let mut b = [0u64; 4];
    for (i, slot) in a.iter_mut().enumerate() {
        let off = (3 - i) * 8;
        *slot = u64::from_be_bytes(a_be[off..off + 8].try_into().unwrap());
        b[i] = u64::from_be_bytes(b_be[off..off + 8].try_into().unwrap());
    }
    let reduce_once = |v: [u64; 4], carry: u64| -> [u64; 4] {
        let mut diff = [0u64; 4];
        let mut br = 0u64;
        for (i, slot) in diff.iter_mut().enumerate() {
            let (d1, b1) = v[i].overflowing_sub(SECP_N[i]);
            let (d2, b2) = d1.overflowing_sub(br);
            *slot = d2;
            br = (b1 as u64) | (b2 as u64);
        }
        let ge_n = (carry != 0) | (br == 0);
        [
            ct_select_u64(ge_n, diff[0], v[0]),
            ct_select_u64(ge_n, diff[1], v[1]),
            ct_select_u64(ge_n, diff[2], v[2]),
            ct_select_u64(ge_n, diff[3], v[3]),
        ]
    };

    let mut a_red = reduce_once(a, 0);
    let mut b_red = reduce_once(b, 0);
    let mut sum = [0u64; 4];
    let mut c = 0u128;
    for (i, slot) in sum.iter_mut().enumerate() {
        let s = (a_red[i] as u128) + (b_red[i] as u128) + c;
        *slot = s as u64;
        c = s >> 64;
    }
    let mut res = reduce_once(sum, c as u64);
    let mut out = [0u8; 32];
    for (i, &limb) in res.iter().enumerate() {
        let off = (3 - i) * 8;
        out[off..off + 8].copy_from_slice(&limb.to_be_bytes());
    }
    ct_zeroize_u64s(&mut a);
    ct_zeroize_u64s(&mut b);
    ct_zeroize_u64s(&mut sum);
    ct_zeroize_u64s(&mut a_red);
    ct_zeroize_u64s(&mut b_red);
    ct_zeroize_u64s(&mut res);
    out
}

/// Negate scalar `s` modulo `SECP_N` (`SECP_N - s`).
pub fn secp_scalar_neg_mod_n(s_be: &[u8; 32]) -> [u8; 32] {
    let mut s = [0u64; 4];
    for (i, slot) in s.iter_mut().enumerate() {
        let off = (3 - i) * 8;
        *slot = u64::from_be_bytes(s_be[off..off + 8].try_into().unwrap());
    }
    let mut diff = [0u64; 4];
    let mut br = 0u64;
    for (i, slot) in diff.iter_mut().enumerate() {
        let (d1, b1) = SECP_N[i].overflowing_sub(s[i]);
        let (d2, b2) = d1.overflowing_sub(br);
        *slot = d2;
        br = (b1 as u64) | (b2 as u64);
    }
    let is_z = ct_eq_u64(s[0] | s[1] | s[2] | s[3], 0);
    let mut out = [0u8; 32];
    for (i, &d_limb) in diff.iter().enumerate() {
        let v = ct_select_u64(is_z, 0, d_limb);
        let off = (3 - i) * 8;
        out[off..off + 8].copy_from_slice(&v.to_be_bytes());
    }
    ct_zeroize_u64s(&mut s);
    ct_zeroize_u64s(&mut diff);
    let _ = ct_lt_u64;
    out
}

pub(crate) const GENERATOR_TABLE: [[[u64; 4]; 3]; 16] = [
    [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
    [
        [
            6481385041966929816,
            188021827762530521,
            6170039885052185351,
            8772561819708210092,
        ],
        [
            11261198710074299576,
            18237243440184513561,
            6747795201694173352,
            5204712524664259685,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            12370272968204394213,
            6662950628856118439,
            3478257130916576472,
            14268669794154544493,
        ],
        [
            2550217892273579306,
            17867523981857706209,
            11800983642684844782,
            1936944757666071353,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            9656264143134537465,
            13056436995607206320,
            5274928500377997865,
            17956003453681058576,
        ],
        [
            7834571707967399538,
            7278003473310950171,
            1144820191972553558,
            4075611493812267028,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            8429213118642834707,
            14730169990667859332,
            6349592808634651652,
            16470750093596524787,
        ],
        [
            14981641821446445346,
            15665681366115024448,
            6215778966400472136,
            5903543180817880503,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            14675214035725643748,
            16756632789543131831,
            6175744766561243432,
            3426076364275916947,
        ],
        [
            15900096175289426646,
            17836549323988232256,
            15338039725391463462,
            15612891555711804374,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            3388248522597430614,
            9436808338628714891,
            2325328641075066323,
            18444909905599983268,
        ],
        [
            4361468193159901847,
            16033079614159971488,
            17563640529965925728,
            12543219280952145440,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            16801766848214661564,
            4413980075321516956,
            11788439643834972686,
            6682761736226714858,
        ],
        [
            11891796769454056666,
            12111253311957362613,
            11752017254187422939,
            7704473966897092960,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            7455795992471415297,
            728418782148528266,
            12678622785167113263,
            3387241150846481693,
        ],
        [
            13103835232102902020,
            14042808401065113111,
            2971540305937765300,
            6651157661005093193,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            14077989711946173630,
            16183569362544224020,
            697239401458408125,
            12453724979823375955,
        ],
        [
            417750830596201527,
            12526912602416057871,
            7221532385408147945,
            14714255185340258813,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            5955603869489842119,
            3765806001044046519,
            3839174075530784349,
            11548159211715414114,
        ],
        [
            4377187929474427095,
            8032535174475915609,
            11796836067076885609,
            9888420725886925863,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            13541224058344966347,
            6217667937428404369,
            6842133777754774188,
            8595937892615405854,
        ],
        [
            3467055698160109083,
            3976029634016433832,
            163217376571536229,
            15673828743714659865,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            14245154385136969818,
            7529161239585360219,
            1568254326717236787,
            14992788640288429595,
        ],
        [
            7711599709454213927,
            8728974837485694290,
            12156980350441740309,
            12246219763152707799,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            16063741251597392552,
            12715345952400890061,
            14398520405876049489,
            17476064159743682699,
        ],
        [
            3005531883061898625,
            4186666338344741151,
            8467351051644546887,
            770274065897753225,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            16472799757751296996,
            2786174986351102438,
            18258972222533373490,
            5305204758068228508,
        ],
        [
            14294215021635387227,
            5062742807299462588,
            10443923284728992868,
            14610511465859155281,
        ],
        [1, 0, 0, 0],
    ],
    [
        [
            4948819342687864846,
            3595443083002902430,
            6504986642944619537,
            15533563068553620118,
        ],
        [
            14196714504974396248,
            16879684006236836773,
            9476750927337385455,
            6349556997556040358,
        ],
        [1, 0, 0, 0],
    ],
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_offsets_include_zero_but_not_order() {
        assert!(secp_scalar_is_canonical(&[0; 32]));
        assert!(!secp_scalar_is_valid_nonzero(&[0; 32]));
        let mut order = [0; 32];
        for (chunk, limb) in order.chunks_exact_mut(8).zip(SECP_N.iter().rev()) {
            chunk.copy_from_slice(&limb.to_be_bytes());
        }
        assert!(!secp_scalar_is_canonical(&order));
        order[31] -= 1;
        assert!(secp_scalar_is_valid_nonzero(&order));
        let mut one = [0; 32];
        one[31] = 1;
        assert_eq!(secp_scalar_add_mod_n(&one, &[0; 32]), one);
        assert_eq!(secp_scalar_add_mod_n(&one, &order), [0; 32]);
    }

    #[test]
    fn field_add_wrap_and_fixed_base_agree() {
        let mut limbs = SECP_P;
        limbs[0] -= 1;
        let twice = Fp256(limbs) + Fp256(limbs);
        limbs[0] -= 1;
        assert!(twice == Fp256(limbs));
        for small in [1, 2, 15, 16, 255] {
            let mut scalar = [0; 32];
            scalar[31] = small;
            assert_eq!(
                SecpPoint::generator_mul_ct(&scalar).to_compressed_bytes(),
                SecpPoint::GENERATOR
                    .scalar_mul_ct(&scalar)
                    .to_compressed_bytes()
            );
        }
    }
}
