//! NIST FIPS 205 (`SLH-DSA-SHAKE`) 32-byte uncompressed `ADRS` framing, WOTS+ (`w = 16`,
//! `ell_1 = 32`, `ell_2 = 3`, `ell = 35`) base-16 digit + checksum encoding, WOTS+ chain step,
//! and Target-Sum Winternitz (`TSW`) constant-sum verification.

use crate::keccak::Shake256Sponge;

/// NIST FIPS 205 §4.2 address role (`type` word at bytes `16..20`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fips205AdrsType {
    WotsHash,
    WotsPk,
    Tree,
    ForsTree,
    ForsRoots,
    WotsPrf,
    ForsPrf,
}

impl Fips205AdrsType {
    #[inline]
    pub const fn to_u32(self) -> u32 {
        match self {
            Self::WotsHash => 0,
            Self::WotsPk => 1,
            Self::Tree => 2,
            Self::ForsTree => 3,
            Self::ForsRoots => 4,
            Self::WotsPrf => 5,
            Self::ForsPrf => 6,
        }
    }

    #[inline]
    pub const fn from_u32(v: u32) -> Option<Self> {
        match v {
            0 => Some(Self::WotsHash),
            1 => Some(Self::WotsPk),
            2 => Some(Self::Tree),
            3 => Some(Self::ForsTree),
            4 => Some(Self::ForsRoots),
            5 => Some(Self::WotsPrf),
            6 => Some(Self::ForsPrf),
            _ => None,
        }
    }
}

/// Canonical 256-bit (32-byte) NIST FIPS 205 §4.2 uncompressed `ADRS`:
/// - `layer`: 32-bit layer address (`bytes[0..4]`)
/// - `(tree_hi, tree_lo)`: exact 96-bit tree index (`bytes[4..8]` + `bytes[8..16]`)
/// - `adrs_type`: 32-bit role tag in `0..=6` (`bytes[16..20]`)
/// - `kp`: 32-bit key-pair address (`bytes[20..24]`)
/// - `chain`: 32-bit chain address / tree height (`bytes[24..28]`)
/// - `hash`: 32-bit hash address / tree index (`bytes[28..32]`)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fips205Adrs {
    pub layer: u32,
    pub tree_hi: u32,
    pub tree_lo: u64,
    pub adrs_type: Fips205AdrsType,
    pub kp: u32,
    pub chain: u32,
    pub hash: u32,
}

impl Fips205Adrs {
    /// Construct from a 96-bit tree index stored in the low 96 bits of a `u128`.
    #[inline]
    pub const fn from_tree_u96(
        layer: u32,
        tree: u128,
        adrs_type: Fips205AdrsType,
        kp: u32,
        chain: u32,
        hash: u32,
    ) -> Self {
        Self {
            layer,
            tree_hi: ((tree >> 64) & 0xFFFF_FFFF) as u32,
            tree_lo: (tree & 0xFFFF_FFFF_FFFF_FFFF) as u64,
            adrs_type,
            kp,
            chain,
            hash,
        }
    }
}

/// Encode `Fips205Adrs` to 32 big-endian bytes per NIST FIPS 205 §4.2.
/// Every bit of every field is preserved bijectively across the 32-byte output.
#[inline]
pub const fn encode_fips205_adrs(adrs: Fips205Adrs) -> [u8; 32] {
    let ty = adrs.adrs_type.to_u32();
    [
        ((adrs.layer >> 24) & 0xFF) as u8,
        ((adrs.layer >> 16) & 0xFF) as u8,
        ((adrs.layer >> 8) & 0xFF) as u8,
        (adrs.layer & 0xFF) as u8,
        ((adrs.tree_hi >> 24) & 0xFF) as u8,
        ((adrs.tree_hi >> 16) & 0xFF) as u8,
        ((adrs.tree_hi >> 8) & 0xFF) as u8,
        (adrs.tree_hi & 0xFF) as u8,
        ((adrs.tree_lo >> 56) & 0xFF) as u8,
        ((adrs.tree_lo >> 48) & 0xFF) as u8,
        ((adrs.tree_lo >> 40) & 0xFF) as u8,
        ((adrs.tree_lo >> 32) & 0xFF) as u8,
        ((adrs.tree_lo >> 24) & 0xFF) as u8,
        ((adrs.tree_lo >> 16) & 0xFF) as u8,
        ((adrs.tree_lo >> 8) & 0xFF) as u8,
        (adrs.tree_lo & 0xFF) as u8,
        ((ty >> 24) & 0xFF) as u8,
        ((ty >> 16) & 0xFF) as u8,
        ((ty >> 8) & 0xFF) as u8,
        (ty & 0xFF) as u8,
        ((adrs.kp >> 24) & 0xFF) as u8,
        ((adrs.kp >> 16) & 0xFF) as u8,
        ((adrs.kp >> 8) & 0xFF) as u8,
        (adrs.kp & 0xFF) as u8,
        ((adrs.chain >> 24) & 0xFF) as u8,
        ((adrs.chain >> 16) & 0xFF) as u8,
        ((adrs.chain >> 8) & 0xFF) as u8,
        (adrs.chain & 0xFF) as u8,
        ((adrs.hash >> 24) & 0xFF) as u8,
        ((adrs.hash >> 16) & 0xFF) as u8,
        ((adrs.hash >> 8) & 0xFF) as u8,
        (adrs.hash & 0xFF) as u8,
    ]
}

#[inline]
const fn be_u32(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32)
}

#[inline]
const fn be_u64(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u64 {
    ((b0 as u64) << 56)
        | ((b1 as u64) << 48)
        | ((b2 as u64) << 40)
        | ((b3 as u64) << 32)
        | ((b4 as u64) << 24)
        | ((b5 as u64) << 16)
        | ((b6 as u64) << 8)
        | (b7 as u64)
}

/// Decode a 32-byte big-endian NIST FIPS 205 `ADRS` (`None` iff `adrs_type > 6`).
pub const fn decode_fips205_adrs(bytes: &[u8; 32]) -> Option<Fips205Adrs> {
    let layer = be_u32(bytes[0], bytes[1], bytes[2], bytes[3]);
    let tree_hi = be_u32(bytes[4], bytes[5], bytes[6], bytes[7]);
    let tree_lo = be_u64(
        bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
    );
    let ty_raw = be_u32(bytes[16], bytes[17], bytes[18], bytes[19]);
    let adrs_type = match Fips205AdrsType::from_u32(ty_raw) {
        Some(t) => t,
        None => return None,
    };
    let kp = be_u32(bytes[20], bytes[21], bytes[22], bytes[23]);
    let chain = be_u32(bytes[24], bytes[25], bytes[26], bytes[27]);
    let hash = be_u32(bytes[28], bytes[29], bytes[30], bytes[31]);
    Some(Fips205Adrs {
        layer,
        tree_hi,
        tree_lo,
        adrs_type,
        kp,
        chain,
        hash,
    })
}

/// Unpack a 16-byte message block into `ell_1 = 32` MSB-first base-16 nibbles (`0..16`).
#[inline]
pub const fn wots_extract_base16_digits(msg16: &[u8; 16]) -> [u8; 32] {
    [
        msg16[0] >> 4,
        msg16[0] & 0x0F,
        msg16[1] >> 4,
        msg16[1] & 0x0F,
        msg16[2] >> 4,
        msg16[2] & 0x0F,
        msg16[3] >> 4,
        msg16[3] & 0x0F,
        msg16[4] >> 4,
        msg16[4] & 0x0F,
        msg16[5] >> 4,
        msg16[5] & 0x0F,
        msg16[6] >> 4,
        msg16[6] & 0x0F,
        msg16[7] >> 4,
        msg16[7] & 0x0F,
        msg16[8] >> 4,
        msg16[8] & 0x0F,
        msg16[9] >> 4,
        msg16[9] & 0x0F,
        msg16[10] >> 4,
        msg16[10] & 0x0F,
        msg16[11] >> 4,
        msg16[11] & 0x0F,
        msg16[12] >> 4,
        msg16[12] & 0x0F,
        msg16[13] >> 4,
        msg16[13] & 0x0F,
        msg16[14] >> 4,
        msg16[14] & 0x0F,
        msg16[15] >> 4,
        msg16[15] & 0x0F,
    ]
}

#[inline]
const fn wots_csum_term(d: u8) -> u16 {
    15u16 - ((d & 0x0F) as u16)
}

#[inline]
const fn wots_csum_oct(d0: u8, d1: u8, d2: u8, d3: u8, d4: u8, d5: u8, d6: u8, d7: u8) -> u16 {
    ((wots_csum_term(d0) + wots_csum_term(d1)) + (wots_csum_term(d2) + wots_csum_term(d3)))
        + ((wots_csum_term(d4) + wots_csum_term(d5)) + (wots_csum_term(d6) + wots_csum_term(d7)))
}

/// NIST FIPS 205 Winternitz base-16 checksum `sum_{i=0}^{31} (15 - d_i)` in `[0, 480]`.
/// Strictly increases whenever any canonical message digit (`< 16`) decreases without another increasing.
#[inline]
pub const fn wots_checksum_base16(msg_digits: &[u8; 32]) -> u16 {
    let s0 = wots_csum_oct(
        msg_digits[0],
        msg_digits[1],
        msg_digits[2],
        msg_digits[3],
        msg_digits[4],
        msg_digits[5],
        msg_digits[6],
        msg_digits[7],
    );
    let s1 = wots_csum_oct(
        msg_digits[8],
        msg_digits[9],
        msg_digits[10],
        msg_digits[11],
        msg_digits[12],
        msg_digits[13],
        msg_digits[14],
        msg_digits[15],
    );
    let s2 = wots_csum_oct(
        msg_digits[16],
        msg_digits[17],
        msg_digits[18],
        msg_digits[19],
        msg_digits[20],
        msg_digits[21],
        msg_digits[22],
        msg_digits[23],
    );
    let s3 = wots_csum_oct(
        msg_digits[24],
        msg_digits[25],
        msg_digits[26],
        msg_digits[27],
        msg_digits[28],
        msg_digits[29],
        msg_digits[30],
        msg_digits[31],
    );
    (s0 + s1) + (s2 + s3)
}

/// Full NIST FIPS 205 §5 (`w = 16, ell_1 = 32, ell_2 = 3, ell = 35`) WOTS+ digit + checksum vector:
/// `32` base-16 message digits followed by `3` big-endian base-16 nibbles of `csum << 4`.
#[inline]
pub const fn fips205_wots_checksum(msg16: &[u8; 16]) -> [u8; 35] {
    let md = wots_extract_base16_digits(msg16);
    let csum = wots_checksum_base16(&md);
    // csum <= 480 <= 4095: three MSB-first base-16 nibbles of (csum << 4) in 16-bit big-endian
    let c0 = ((csum >> 8) & 0x0F) as u8;
    let c1 = ((csum >> 4) & 0x0F) as u8;
    let c2 = (csum & 0x0F) as u8;
    [
        md[0], md[1], md[2], md[3], md[4], md[5], md[6], md[7], md[8], md[9], md[10], md[11],
        md[12], md[13], md[14], md[15], md[16], md[17], md[18], md[19], md[20], md[21], md[22],
        md[23], md[24], md[25], md[26], md[27], md[28], md[29], md[30], md[31], c0, c1, c2,
    ]
}

/// NIST FIPS 205 §11.1 tweakable hash `F(PK.seed, ADRS, M_1) = SHAKE256(PK.seed || ADRS || M_1, 128)`.
pub fn fips205_f(pk_seed: &[u8; 16], adrs: &Fips205Adrs, m1: &[u8; 16]) -> [u8; 16] {
    let adrs_bytes = encode_fips205_adrs(*adrs);
    let mut sp = Shake256Sponge::new_shake256();
    sp.absorb(pk_seed);
    sp.absorb(&adrs_bytes);
    sp.absorb(m1);
    let mut out = [0u8; 16];
    sp.squeeze(&mut out);
    out
}

/// NIST FIPS 205 Algorithm 5 `chain(X, i, s, PK.seed, ADRS)` with explicit `i + s <= 15` bound check.
pub fn fips205_wots_chain(
    mut x: [u8; 16],
    start_i: u32,
    steps_s: u32,
    pk_seed: &[u8; 16],
    base_adrs: Fips205Adrs,
) -> Option<[u8; 16]> {
    if start_i > 15 || steps_s > 15 - start_i {
        return None;
    }
    let end = start_i + steps_s;
    let mut j = start_i;
    while j < end {
        let mut adrs = base_adrs;
        adrs.hash = j;
        x = fips205_f(pk_seed, &adrs, &x);
        j += 1;
    }
    Some(x)
}

/// Canonical Target-Sum Winternitz (`TSW`) target sum `floor(ell_1 * (w - 1) / 2)`.
#[inline]
pub const fn tsw_canonical_target_sum(w: u32, ell1: u32) -> Option<u64> {
    if w < 2 {
        return None;
    }
    let wm1 = (w - 1) as u64;
    Some(((ell1 as u64) * wm1) / 2)
}

/// Target-Sum Winternitz (`TSW`) constant-sum verifier: checks `digits.len() == ell1`,
/// every `d < w`, and `sum(digits) == target` using overflow-free `u64` accumulation.
pub fn tsw_check_target_sum(w: u32, ell1: usize, target: u64, digits: &[u32]) -> bool {
    if digits.len() != ell1 {
        return false;
    }
    let mut sum: u64 = 0;
    let mut i: usize = 0;
    while i < digits.len() {
        let d = digits[i];
        if d >= w {
            return false;
        }
        let d64 = d as u64;
        if sum > u64::MAX - d64 {
            return false;
        }
        sum += d64;
        i += 1;
    }
    sum == target
}
