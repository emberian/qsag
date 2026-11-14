//! Exact byte-for-byte NIST FIPS 205 (`SLH-DSA-SHAKE`) implementation across **all 6 official
//! SHAKE parameter sets** (`128s`, `128f`, `192s`, `192f`, `256s`, `256f`), 32-byte uncompressed
//! `ADRS` framing, WOTS+ ($w = 16, \ell_1 = 2n, \ell_2 = 3, \ell = 2n + 3$), FORS, hypertree,
//! §9.2 Pure external API (`ctx` context string, `|ctx| <= 255`), §9.3 Pre-Hash `HashSLH-DSA`
//! (`SHA-256`, `SHA-512`, `SHA3-256`, `SHA3-384`, `SHA3-512`, `SHAKE128`, `SHAKE256`), X.509 SPKI
//! DER public-key encoding compatible with OpenSSL 3.5, and cut-boundary `SlhMpcOracles` for
//! distributed threshold MPC signing without reconstructing `SK.seed` or `SK.prf`.
//!
//! Matches `lean/Qsag/Fips205.lean` bit-for-bit across all algorithms (`slh_keygen_internal`,
//! `slh_sign_internal`, `slh_verify_internal`, pure `slh_sign`/`slh_verify`, `hash_slh_sign`/
//! `hash_slh_verify`, and `slhKeygenMpc`/`slhSignMpc`).

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::sponge::keccak::{Cshake256Xof, keccak_f1600, shake256_xof};
use crate::wipe::{ct_eq_bytes, wipe_bytes32, wipe_slice};

/// Maximum context string length permitted by NIST FIPS 205 §9.2 / §9.3 (`|ctx| <= 255`).
pub const FIPS205_MAX_CTX_LEN: usize = 255;

/// ASN.1 SubjectPublicKeyInfo (SPKI) DER prefix (`18` bytes) for `SLH-DSA-SHAKE-128s`
/// (`OID 2.16.840.1.101.3.4.3.26`, `PK = 32 B`, total DER `50 B`), verified against OpenSSL 3.5.
pub const SPKI_DER_PREFIX_SLH_SHAKE_128S: [u8; 18] = [
    0x30, 0x30, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x1a, 0x03,
    0x21, 0x00,
];

/// ASN.1 SubjectPublicKeyInfo (SPKI) DER prefix (`18` bytes) for `SLH-DSA-SHAKE-128f`
/// (`OID 2.16.840.1.101.3.4.3.27`, `PK = 32 B`, total DER `50 B`), verified against OpenSSL 3.5.
pub const SPKI_DER_PREFIX_SLH_SHAKE_128F: [u8; 18] = [
    0x30, 0x30, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x1b, 0x03,
    0x21, 0x00,
];

/// ASN.1 SubjectPublicKeyInfo (SPKI) DER prefix (`18` bytes) for `SLH-DSA-SHAKE-192s`
/// (`OID 2.16.840.1.101.3.4.3.28`, `PK = 48 B`, total DER `66 B`), verified against OpenSSL 3.5.
pub const SPKI_DER_PREFIX_SLH_SHAKE_192S: [u8; 18] = [
    0x30, 0x40, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x1c, 0x03,
    0x31, 0x00,
];

/// ASN.1 SubjectPublicKeyInfo (SPKI) DER prefix (`18` bytes) for `SLH-DSA-SHAKE-192f`
/// (`OID 2.16.840.1.101.3.4.3.29`, `PK = 48 B`, total DER `66 B`), verified against OpenSSL 3.5.
pub const SPKI_DER_PREFIX_SLH_SHAKE_192F: [u8; 18] = [
    0x30, 0x40, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x1d, 0x03,
    0x31, 0x00,
];

/// ASN.1 SubjectPublicKeyInfo (SPKI) DER prefix (`18` bytes) for `SLH-DSA-SHAKE-256s`
/// (`OID 2.16.840.1.101.3.4.3.30`, `PK = 64 B`, total DER `82 B`), verified against OpenSSL 3.5.
pub const SPKI_DER_PREFIX_SLH_SHAKE_256S: [u8; 18] = [
    0x30, 0x50, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x1e, 0x03,
    0x41, 0x00,
];

/// ASN.1 SubjectPublicKeyInfo (SPKI) DER prefix (`18` bytes) for `SLH-DSA-SHAKE-256f`
/// (`OID 2.16.840.1.101.3.4.3.31`, `PK = 64 B`, total DER `82 B`), verified against OpenSSL 3.5.
pub const SPKI_DER_PREFIX_SLH_SHAKE_256F: [u8; 18] = [
    0x30, 0x50, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x1f, 0x03,
    0x41, 0x00,
];

/// Errors returned by FIPS 205 encoding, signing, or verification entry points.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fips205Error {
    InvalidParameterSet,
    ContextTooLong(usize),
    PreHashCategoryMismatch { n: usize, pre_hash: SlhPreHash },
    InvalidNodeBytes { expected: usize, actual: usize },
    InvalidPublicKeyBytes(usize),
    InvalidSpkiDerHeader,
    InvalidSecretKeyBytes(usize),
    InvalidSignatureLength { expected: usize, actual: usize },
    MpcExecutionFailed,
    MpcActiveTamperDetected,
}

impl fmt::Display for Fips205Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameterSet => write!(f, "invalid FIPS 205 parameter set"),
            Self::ContextTooLong(n) => {
                write!(f, "FIPS 205 context length {} exceeds 255 bytes", n)
            }
            Self::PreHashCategoryMismatch { n, pre_hash } => write!(
                f,
                "FIPS 205 §9.3 pre-hash {:?} insufficient for security parameter n={}",
                pre_hash, n
            ),
            Self::InvalidNodeBytes { expected, actual } => write!(
                f,
                "invalid FIPS 205 n-byte block length: expected {}, got {}",
                expected, actual
            ),
            Self::InvalidPublicKeyBytes(n) => {
                write!(
                    f,
                    "invalid FIPS 205 public key byte length {} (expected 2*n in {{32, 48, 64}})",
                    n
                )
            }
            Self::InvalidSpkiDerHeader => write!(f, "invalid X.509 SPKI DER header for SLH-DSA"),
            Self::InvalidSecretKeyBytes(n) => {
                write!(
                    f,
                    "invalid FIPS 205 secret key byte length {} (expected 4*n in {{64, 96, 128}})",
                    n
                )
            }
            Self::InvalidSignatureLength { expected, actual } => write!(
                f,
                "invalid FIPS 205 signature length: expected {} bytes, got {}",
                expected, actual
            ),
            Self::MpcExecutionFailed => {
                write!(f, "distributed MPC oracle execution failed during SLH-DSA")
            }
            Self::MpcActiveTamperDetected => {
                write!(
                    f,
                    "active Byzantine tampering or MAC failure detected at SLH-DSA cut boundary"
                )
            }
        }
    }
}

/// Stack-allocated `n`-byte FIPS 205 hash node (`n` in `{16, 24, 32}`) avoiding heap allocation
/// inside WOTS+, FORS, and XMSS Merkle loops.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SlhBlock {
    pub(crate) bytes: [u8; 32],
    len: u8,
}

impl SlhBlock {
    #[inline]
    pub const fn zero(n: usize) -> Self {
        Self {
            bytes: [0u8; 32],
            len: n as u8,
        }
    }

    #[inline]
    pub fn from_slice(raw: &[u8]) -> Result<Self, Fips205Error> {
        if raw.len() != 16 && raw.len() != 24 && raw.len() != 32 {
            return Err(Fips205Error::InvalidNodeBytes {
                expected: 32,
                actual: raw.len(),
            });
        }
        let mut bytes = [0u8; 32];
        bytes[..raw.len()].copy_from_slice(raw);
        Ok(Self {
            bytes,
            len: raw.len() as u8,
        })
    }

    #[inline]
    pub fn from_slice_checked(n: usize, raw: &[u8]) -> Result<Self, Fips205Error> {
        if raw.len() != n || (n != 16 && n != 24 && n != 32) {
            return Err(Fips205Error::InvalidNodeBytes {
                expected: n,
                actual: raw.len(),
            });
        }
        let mut bytes = [0u8; 32];
        bytes[..n].copy_from_slice(raw);
        Ok(Self {
            bytes,
            len: n as u8,
        })
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.bytes[..self.len as usize]
    }

    #[inline]
    pub fn wipe(&mut self) {
        wipe_bytes32(&mut self.bytes);
        self.len = 0;
    }
}

/// NIST FIPS 205 §4.2 address types (`type` word at bytes `16..20`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum Fips205AdrsType {
    WotsHash = 0,
    WotsPk = 1,
    Tree = 2,
    ForsTree = 3,
    ForsRoots = 4,
    WotsPrf = 5,
    ForsPrf = 6,
}

impl Fips205AdrsType {
    #[inline]
    pub const fn to_u32(self) -> u32 {
        self as u32
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

/// NIST FIPS 205 §4.2 uncompressed 32-byte big-endian `ADRS` (`SLH-DSA-SHAKE-*`):
/// `[0..4) layer || [4..16) tree (96-bit BE) || [16..20) type || [20..24) keyPair || [24..28) f5 || [28..32) f6`.
///
/// `PartialEq`, `Eq`, and `Hash` compare the canonical 96-bit masked `to_bytes()` representation
/// so upper 32 bits of `tree` can never cause `Eq` vs wire-encoding divergence (`[P1-04]`, `[P1-08]`).
#[derive(Clone, Copy, Debug)]
pub struct Fips205Adrs {
    pub layer: u32,
    /// 96-bit tree index (upper 32 bits masked via `TREE_96_MASK`).
    pub tree: u128,
    pub adrs_type: Fips205AdrsType,
    pub key_pair: u32,
    pub f5: u32,
    pub f6: u32,
}

impl PartialEq for Fips205Adrs {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.to_bytes() == other.to_bytes()
    }
}

impl Eq for Fips205Adrs {}

impl core::hash::Hash for Fips205Adrs {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.to_bytes().hash(state);
    }
}

impl Fips205Adrs {
    pub const TREE_96_MASK: u128 = (1u128 << 96) - 1;

    pub const ZERO: Self = Self {
        layer: 0,
        tree: 0,
        adrs_type: Fips205AdrsType::WotsHash,
        key_pair: 0,
        f5: 0,
        f6: 0,
    };

    /// Set the full 96-bit `tree` address (`[4..16)` BE), masking bits `96..128` to zero (`[P1-04]`).
    #[inline]
    pub const fn set_tree_address(&mut self, tree: u128) {
        self.tree = tree & Self::TREE_96_MASK;
    }

    /// Encode to 32 big-endian bytes matching `Qsag.encodeFips205Adrs`.
    #[inline]
    pub const fn to_bytes(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        let lb = self.layer.to_be_bytes();
        out[0] = lb[0];
        out[1] = lb[1];
        out[2] = lb[2];
        out[3] = lb[3];

        // 96-bit big-endian tree index in bytes 4..16
        let tb = self.tree.to_be_bytes();
        let mut i = 0usize;
        while i < 12 {
            out[4 + i] = tb[4 + i];
            i += 1;
        }

        let ty = self.adrs_type.to_u32().to_be_bytes();
        out[16] = ty[0];
        out[17] = ty[1];
        out[18] = ty[2];
        out[19] = ty[3];

        let kp = self.key_pair.to_be_bytes();
        out[20] = kp[0];
        out[21] = kp[1];
        out[22] = kp[2];
        out[23] = kp[3];

        let b5 = self.f5.to_be_bytes();
        out[24] = b5[0];
        out[25] = b5[1];
        out[26] = b5[2];
        out[27] = b5[3];

        let b6 = self.f6.to_be_bytes();
        out[28] = b6[0];
        out[29] = b6[1];
        out[30] = b6[2];
        out[31] = b6[3];
        out
    }

    /// Decode a canonical 32-byte uncompressed `ADRS` (`None` if `type > 6`).
    pub fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let layer = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let mut tb = [0u8; 16];
        tb[4..16].copy_from_slice(&bytes[4..16]);
        let tree = u128::from_be_bytes(tb);
        let ty = u32::from_be_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]);
        let adrs_type = Fips205AdrsType::from_u32(ty)?;
        let key_pair = u32::from_be_bytes([bytes[20], bytes[21], bytes[22], bytes[23]]);
        let f5 = u32::from_be_bytes([bytes[24], bytes[25], bytes[26], bytes[27]]);
        let f6 = u32::from_be_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]);
        Some(Self {
            layer,
            tree,
            adrs_type,
            key_pair,
            f5,
            f6,
        })
    }

    /// NIST FIPS 205 §4.3 `setTypeAndClear`: sets `adrs_type` and clears `key_pair`, `f5`, `f6` to `0`.
    #[inline]
    pub const fn with_type_and_clear(mut self, adrs_type: Fips205AdrsType) -> Self {
        self.adrs_type = adrs_type;
        self.key_pair = 0;
        self.f5 = 0;
        self.f6 = 0;
        self
    }
}

/// NIST FIPS 205 `SLH-DSA-SHAKE` parameter profile ($n \in \{16, 24, 32\}, w = 16, \ell_1 = 2n, \ell_2 = 3, \ell = 2n + 3$).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fips205Params {
    pub name: &'static str,
    pub n: usize,
    pub h: usize,
    pub d: usize,
    pub hp: usize,
    pub a: usize,
    pub k: usize,
    pub lg_w: usize,
    pub m: usize,
}

impl Fips205Params {
    pub const W: usize = 16;
    pub const ELL2: usize = 3;
    /// Legacy constant for 128-bit (`n = 16`) callers; prefer [`Self::ell1`].
    pub const ELL1_128: usize = 32;
    /// Legacy constant for 128-bit (`n = 16`) callers; prefer [`Self::ell`].
    pub const ELL_128: usize = 35;

    /// Message WOTS+ chain count $\ell_1 = 2n$ (`32` for `n=16`, `48` for `n=24`, `64` for `n=32`).
    #[inline]
    pub const fn ell1(&self) -> usize {
        2 * self.n
    }

    /// Total WOTS+ chain count $\ell = \ell_1 + \ell_2 = 2n + 3$ (`35`, `51`, or `67`).
    #[inline]
    pub const fn ell(&self) -> usize {
        2 * self.n + Self::ELL2
    }

    /// Public key byte length `2 * n` (`32`, `48`, or `64` bytes).
    #[inline]
    pub const fn pk_bytes(&self) -> usize {
        2 * self.n
    }

    /// Secret key byte length `4 * n` (`64`, `96`, or `128` bytes).
    #[inline]
    pub const fn sk_bytes(&self) -> usize {
        4 * self.n
    }

    /// Exact signature byte length `n * (1 + k * (1 + a) + d * (ell + hp))`, checked against overflow.
    #[inline]
    pub const fn sig_bytes_checked(&self) -> Option<usize> {
        let Some(n2) = self.n.checked_mul(2) else {
            return None;
        };
        let Some(ell) = n2.checked_add(Self::ELL2) else {
            return None;
        };
        let Some(a1) = self.a.checked_add(1) else {
            return None;
        };
        let Some(ka) = self.k.checked_mul(a1) else {
            return None;
        };
        let Some(ell_hp) = ell.checked_add(self.hp) else {
            return None;
        };
        let Some(d_term) = self.d.checked_mul(ell_hp) else {
            return None;
        };
        let Some(b1) = 1usize.checked_add(ka) else {
            return None;
        };
        let Some(blocks) = b1.checked_add(d_term) else {
            return None;
        };
        self.n.checked_mul(blocks)
    }

    #[inline]
    pub const fn sig_bytes(&self) -> usize {
        match self.sig_bytes_checked() {
            Some(v) => v,
            None => 0,
        }
    }

    #[inline]
    pub const fn is_valid(&self) -> bool {
        let n_ok = self.n == 16 || self.n == 24 || self.n == 32;
        if !n_ok || self.lg_w != 4 || self.d == 0 || self.hp == 0 || self.hp > 16 {
            return false;
        }
        let Some(dhp) = self.d.checked_mul(self.hp) else {
            return false;
        };
        if self.h != dhp || self.k == 0 || self.a == 0 || self.a > 20 {
            return false;
        }
        let Some(ka_bits) = self.k.checked_mul(self.a) else {
            return false;
        };
        let Some(ka_plus7) = ka_bits.checked_add(7) else {
            return false;
        };
        let ka_bytes = ka_plus7 / 8;
        let tree_bits = self.h.saturating_sub(self.hp);
        if tree_bits > 96 {
            return false;
        }
        let tree_bytes = tree_bits.div_ceil(8);
        let leaf_bytes = self.hp.div_ceil(8);
        let Some(m1) = ka_bytes.checked_add(tree_bytes) else {
            return false;
        };
        let Some(expected_m) = m1.checked_add(leaf_bytes) else {
            return false;
        };
        self.m == expected_m && self.sig_bytes_checked().is_some()
    }

    /// Official NIST FIPS 205 Table 2 `SLH-DSA-SHAKE-128s` (`7,856` signature bytes, `PK = 32 B`).
    pub const SLH_DSA_SHAKE_128S: Self = Self {
        name: "SLH-DSA-SHAKE-128s",
        n: 16,
        h: 63,
        d: 7,
        hp: 9,
        a: 12,
        k: 14,
        lg_w: 4,
        m: 30,
    };

    /// Official NIST FIPS 205 Table 2 `SLH-DSA-SHAKE-128f` (`17,088` signature bytes, `PK = 32 B`).
    pub const SLH_DSA_SHAKE_128F: Self = Self {
        name: "SLH-DSA-SHAKE-128f",
        n: 16,
        h: 66,
        d: 22,
        hp: 3,
        a: 6,
        k: 33,
        lg_w: 4,
        m: 34,
    };

    /// Official NIST FIPS 205 Table 2 `SLH-DSA-SHAKE-192s` (`16,224` signature bytes, `PK = 48 B`).
    pub const SLH_DSA_SHAKE_192S: Self = Self {
        name: "SLH-DSA-SHAKE-192s",
        n: 24,
        h: 63,
        d: 7,
        hp: 9,
        a: 14,
        k: 17,
        lg_w: 4,
        m: 39,
    };

    /// Official NIST FIPS 205 Table 2 `SLH-DSA-SHAKE-192f` (`35,664` signature bytes, `PK = 48 B`).
    pub const SLH_DSA_SHAKE_192F: Self = Self {
        name: "SLH-DSA-SHAKE-192f",
        n: 24,
        h: 66,
        d: 22,
        hp: 3,
        a: 8,
        k: 33,
        lg_w: 4,
        m: 42,
    };

    /// Official NIST FIPS 205 Table 2 `SLH-DSA-SHAKE-256s` (`29,792` signature bytes, `PK = 64 B`).
    pub const SLH_DSA_SHAKE_256S: Self = Self {
        name: "SLH-DSA-SHAKE-256s",
        n: 32,
        h: 64,
        d: 8,
        hp: 8,
        a: 14,
        k: 22,
        lg_w: 4,
        m: 47,
    };

    /// Official NIST FIPS 205 Table 2 `SLH-DSA-SHAKE-256f` (`49,856` signature bytes, `PK = 64 B`).
    pub const SLH_DSA_SHAKE_256F: Self = Self {
        name: "SLH-DSA-SHAKE-256f",
        n: 32,
        h: 68,
        d: 17,
        hp: 4,
        a: 9,
        k: 35,
        lg_w: 4,
        m: 49,
    };

    /// Compact unit-test profile using the exact `SLH-DSA-SHAKE` primitives (`1,376` signature bytes).
    pub const SLH_DSA_SHAKE_COMPACT_TEST: Self = Self {
        name: "SLH-DSA-SHAKE-compact-test",
        n: 16,
        h: 4,
        d: 2,
        hp: 2,
        a: 2,
        k: 4,
        lg_w: 4,
        m: 3,
    };

    /// All 6 official NIST FIPS 205 Table 2 `SLH-DSA-SHAKE` parameter sets.
    pub const ALL_OFFICIAL: [Self; 6] = [
        Self::SLH_DSA_SHAKE_128S,
        Self::SLH_DSA_SHAKE_128F,
        Self::SLH_DSA_SHAKE_192S,
        Self::SLH_DSA_SHAKE_192F,
        Self::SLH_DSA_SHAKE_256S,
        Self::SLH_DSA_SHAKE_256F,
    ];

    /// Resolve a parameter set by canonical or short CLI name.
    pub fn by_name(name: &str) -> Option<Self> {
        match name {
            "SLH-DSA-SHAKE-128s" | "slh-dsa-shake-128s" | "128s" => Some(Self::SLH_DSA_SHAKE_128S),
            "SLH-DSA-SHAKE-128f" | "slh-dsa-shake-128f" | "128f" => Some(Self::SLH_DSA_SHAKE_128F),
            "SLH-DSA-SHAKE-192s" | "slh-dsa-shake-192s" | "192s" => Some(Self::SLH_DSA_SHAKE_192S),
            "SLH-DSA-SHAKE-192f" | "slh-dsa-shake-192f" | "192f" => Some(Self::SLH_DSA_SHAKE_192F),
            "SLH-DSA-SHAKE-256s" | "slh-dsa-shake-256s" | "256s" => Some(Self::SLH_DSA_SHAKE_256S),
            "SLH-DSA-SHAKE-256f" | "slh-dsa-shake-256f" | "256f" => Some(Self::SLH_DSA_SHAKE_256F),
            "SLH-DSA-SHAKE-compact-test" | "compact-test" => Some(Self::SLH_DSA_SHAKE_COMPACT_TEST),
            _ => None,
        }
    }

    /// Return the 18-byte ASN.1 X.509 SPKI DER header for this official parameter set.
    pub fn spki_der_prefix(&self) -> Result<[u8; 18], Fips205Error> {
        if *self == Self::SLH_DSA_SHAKE_128S {
            Ok(SPKI_DER_PREFIX_SLH_SHAKE_128S)
        } else if *self == Self::SLH_DSA_SHAKE_128F {
            Ok(SPKI_DER_PREFIX_SLH_SHAKE_128F)
        } else if *self == Self::SLH_DSA_SHAKE_192S {
            Ok(SPKI_DER_PREFIX_SLH_SHAKE_192S)
        } else if *self == Self::SLH_DSA_SHAKE_192F {
            Ok(SPKI_DER_PREFIX_SLH_SHAKE_192F)
        } else if *self == Self::SLH_DSA_SHAKE_256S {
            Ok(SPKI_DER_PREFIX_SLH_SHAKE_256S)
        } else if *self == Self::SLH_DSA_SHAKE_256F {
            Ok(SPKI_DER_PREFIX_SLH_SHAKE_256F)
        } else {
            Err(Fips205Error::InvalidParameterSet)
        }
    }
}

/// NIST FIPS 205 `SLH-DSA` public key `PK = PK.seed || PK.root` (`2 * n` bytes: `32`, `48`, or `64` B).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SlhPublicKey {
    pub n: usize,
    pub pk_seed: [u8; 32],
    pub pk_root: [u8; 32],
}

impl SlhPublicKey {
    pub fn new(pk_seed: &[u8], pk_root: &[u8]) -> Result<Self, Fips205Error> {
        let n = pk_seed.len();
        if (n != 16 && n != 24 && n != 32) || pk_root.len() != n {
            return Err(Fips205Error::InvalidPublicKeyBytes(
                pk_seed.len() + pk_root.len(),
            ));
        }
        let mut s = [0u8; 32];
        let mut r = [0u8; 32];
        s[..n].copy_from_slice(pk_seed);
        r[..n].copy_from_slice(pk_root);
        Ok(Self {
            n,
            pk_seed: s,
            pk_root: r,
        })
    }

    #[inline]
    pub fn pk_seed_slice(&self) -> &[u8] {
        &self.pk_seed[..self.n]
    }

    #[inline]
    pub fn pk_root_slice(&self) -> &[u8] {
        &self.pk_root[..self.n]
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(2 * self.n);
        out.extend_from_slice(self.pk_seed_slice());
        out.extend_from_slice(self.pk_root_slice());
        out
    }

    pub fn from_bytes(raw: &[u8]) -> Result<Self, Fips205Error> {
        if raw.len() != 32 && raw.len() != 48 && raw.len() != 64 {
            return Err(Fips205Error::InvalidPublicKeyBytes(raw.len()));
        }
        let n = raw.len() / 2;
        Self::new(&raw[..n], &raw[n..])
    }

    pub fn from_bytes_for_params(params: &Fips205Params, raw: &[u8]) -> Result<Self, Fips205Error> {
        if !params.is_valid() {
            return Err(Fips205Error::InvalidParameterSet);
        }
        if raw.len() != 2 * params.n {
            return Err(Fips205Error::InvalidPublicKeyBytes(raw.len()));
        }
        Self::new(&raw[..params.n], &raw[params.n..])
    }

    /// Encode as an X.509 SubjectPublicKeyInfo (SPKI) DER structure (`50`, `66`, or `82` bytes)
    /// accepted directly by `openssl pkeyutl -verify -pubin -keyform DER`.
    pub fn to_spki_der(&self, params: &Fips205Params) -> Result<Vec<u8>, Fips205Error> {
        if self.n != params.n {
            return Err(Fips205Error::InvalidPublicKeyBytes(2 * self.n));
        }
        let prefix = params.spki_der_prefix()?;
        let mut out = Vec::with_capacity(18 + 2 * self.n);
        out.extend_from_slice(&prefix);
        out.extend_from_slice(self.pk_seed_slice());
        out.extend_from_slice(self.pk_root_slice());
        Ok(out)
    }

    /// Parse an X.509 SubjectPublicKeyInfo (SPKI) DER public key emitted by OpenSSL 3.5 across all
    /// 6 `SLH-DSA-SHAKE` parameter sets (`50`, `66`, or `82` bytes).
    pub fn from_spki_der(der: &[u8]) -> Result<(Fips205Params, Self), Fips205Error> {
        if der.len() < 18 {
            return Err(Fips205Error::InvalidSpkiDerHeader);
        }
        let hdr = &der[0..18];
        let params = if hdr == SPKI_DER_PREFIX_SLH_SHAKE_128S {
            Fips205Params::SLH_DSA_SHAKE_128S
        } else if hdr == SPKI_DER_PREFIX_SLH_SHAKE_128F {
            Fips205Params::SLH_DSA_SHAKE_128F
        } else if hdr == SPKI_DER_PREFIX_SLH_SHAKE_192S {
            Fips205Params::SLH_DSA_SHAKE_192S
        } else if hdr == SPKI_DER_PREFIX_SLH_SHAKE_192F {
            Fips205Params::SLH_DSA_SHAKE_192F
        } else if hdr == SPKI_DER_PREFIX_SLH_SHAKE_256S {
            Fips205Params::SLH_DSA_SHAKE_256S
        } else if hdr == SPKI_DER_PREFIX_SLH_SHAKE_256F {
            Fips205Params::SLH_DSA_SHAKE_256F
        } else {
            return Err(Fips205Error::InvalidSpkiDerHeader);
        };
        if der.len() != 18 + 2 * params.n {
            return Err(Fips205Error::InvalidSpkiDerHeader);
        }
        let pk = Self::from_bytes_for_params(&params, &der[18..])?;
        Ok((params, pk))
    }
}

/// NIST FIPS 205 single-party `SLH-DSA` secret key `SK = SK.seed || SK.prf || PK.seed || PK.root`
/// (`4 * n` bytes: `64`, `96`, or `128` B).
///
/// ### Hygiene Invariants
/// - Intentionally **not** `Clone`;
/// - Redacted `Debug` implementation (`SlhSecretKey([REDACTED])`);
/// - Deterministically zeroized on `Drop`;
/// - Used **strictly** for single-party reference keygen/signing and threshold-equivalence KATs
///   (never instantiated inside threshold MPC sessions).
#[derive(PartialEq, Eq)]
pub struct SlhSecretKey {
    pub n: usize,
    sk_seed: [u8; 32],
    sk_prf: [u8; 32],
    pk_seed: [u8; 32],
    pk_root: [u8; 32],
}

impl fmt::Debug for SlhSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SlhSecretKey([REDACTED])")
    }
}

impl Drop for SlhSecretKey {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.sk_seed);
        wipe_bytes32(&mut self.sk_prf);
        wipe_bytes32(&mut self.pk_seed);
        wipe_bytes32(&mut self.pk_root);
        self.n = 0;
    }
}

impl SlhSecretKey {
    pub fn from_components(
        sk_seed_in: &[u8],
        sk_prf_in: &[u8],
        pk_seed_in: &[u8],
        pk_root_in: &[u8],
    ) -> Result<Self, Fips205Error> {
        let n = sk_seed_in.len();
        if (n != 16 && n != 24 && n != 32)
            || sk_prf_in.len() != n
            || pk_seed_in.len() != n
            || pk_root_in.len() != n
        {
            return Err(Fips205Error::InvalidSecretKeyBytes(
                sk_seed_in.len() + sk_prf_in.len() + pk_seed_in.len() + pk_root_in.len(),
            ));
        }
        let mut sk_seed = [0u8; 32];
        let mut sk_prf = [0u8; 32];
        let mut pk_seed = [0u8; 32];
        let mut pk_root = [0u8; 32];
        sk_seed[..n].copy_from_slice(sk_seed_in);
        sk_prf[..n].copy_from_slice(sk_prf_in);
        pk_seed[..n].copy_from_slice(pk_seed_in);
        pk_root[..n].copy_from_slice(pk_root_in);
        Ok(Self {
            n,
            sk_seed,
            sk_prf,
            pk_seed,
            pk_root,
        })
    }

    pub fn from_bytes(raw: &[u8]) -> Result<Self, Fips205Error> {
        if raw.len() != 64 && raw.len() != 96 && raw.len() != 128 {
            return Err(Fips205Error::InvalidSecretKeyBytes(raw.len()));
        }
        let n = raw.len() / 4;
        Self::from_components(
            &raw[0..n],
            &raw[n..2 * n],
            &raw[2 * n..3 * n],
            &raw[3 * n..4 * n],
        )
    }

    pub fn from_bytes_for_params(params: &Fips205Params, raw: &[u8]) -> Result<Self, Fips205Error> {
        if !params.is_valid() {
            return Err(Fips205Error::InvalidParameterSet);
        }
        if raw.len() != 4 * params.n {
            return Err(Fips205Error::InvalidSecretKeyBytes(raw.len()));
        }
        Self::from_bytes(raw)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(4 * self.n);
        out.extend_from_slice(self.sk_seed_slice());
        out.extend_from_slice(self.sk_prf_slice());
        out.extend_from_slice(self.pk_seed_slice());
        out.extend_from_slice(self.pk_root_slice());
        out
    }

    #[inline]
    pub fn sk_seed_slice(&self) -> &[u8] {
        &self.sk_seed[..self.n]
    }

    #[inline]
    pub fn sk_prf_slice(&self) -> &[u8] {
        &self.sk_prf[..self.n]
    }

    #[inline]
    pub fn pk_seed_slice(&self) -> &[u8] {
        &self.pk_seed[..self.n]
    }

    #[inline]
    pub fn pk_root_slice(&self) -> &[u8] {
        &self.pk_root[..self.n]
    }

    #[inline]
    pub const fn public_key(&self) -> SlhPublicKey {
        SlhPublicKey {
            n: self.n,
            pk_seed: self.pk_seed,
            pk_root: self.pk_root,
        }
    }
}

/// Structured representation of an `SLH-DSA` signature (`R || SIG_FORS || SIG_HT`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlhParsedSignature {
    pub r_rand: SlhBlock,
    pub fors_trees: Vec<(SlhBlock, Vec<SlhBlock>)>,
    pub ht_layers: Vec<(Vec<SlhBlock>, Vec<SlhBlock>)>,
}

// ============================================================================
// Pure-Rust Zero-Dependency FIPS 180-4 & FIPS 202 Pre-Hash Suite (§9.3 / §10.2.2)
// ============================================================================

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const SHA512_K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

/// Pure-Rust FIPS 180-4 `SHA-256` digest (`32` bytes).
pub fn sha256_digest(msg: &[u8]) -> [u8; 32] {
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = (msg.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity(msg.len() + 72);
    padded.extend_from_slice(msg);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0x00);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for blk in padded.as_chunks::<64>().0 {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([blk[4 * i], blk[4 * i + 1], blk[4 * i + 2], blk[4 * i + 3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(SHA256_K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// Pure-Rust FIPS 180-4 `SHA-512` digest (`64` bytes).
pub fn sha512_digest(msg: &[u8]) -> [u8; 64] {
    let mut h: [u64; 8] = [
        0x6a09e667f3bcc908,
        0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b,
        0xa54ff53a5f1d36f1,
        0x510e527fade682d1,
        0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b,
        0x5be0cd19137e2179,
    ];
    let bit_len = (msg.len() as u128).wrapping_mul(8);
    let mut padded = Vec::with_capacity(msg.len() + 144);
    padded.extend_from_slice(msg);
    padded.push(0x80);
    while (padded.len() % 128) != 112 {
        padded.push(0x00);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for blk in padded.as_chunks::<128>().0 {
        let mut w = [0u64; 80];
        let mut i = 0;
        while i < 16 {
            let o = 8 * i;
            w[i] = u64::from_be_bytes([
                blk[o],
                blk[o + 1],
                blk[o + 2],
                blk[o + 3],
                blk[o + 4],
                blk[o + 5],
                blk[o + 6],
                blk[o + 7],
            ]);
            i += 1;
        }
        for i in 16..80 {
            let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
            let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..80 {
            let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(SHA512_K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 64];
    for (i, word) in h.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// Generic FIPS 202 sponge evaluator over `keccak_f1600` (`SHA3-256/384/512` with `suffix = 0x06`,
/// `SHAKE128` with `rate = 168, suffix = 0x1F`).
fn keccak_sponge_eval(rate_bytes: usize, suffix: u8, out_len: usize, msg: &[u8]) -> Vec<u8> {
    let mut state = [0u64; 25];
    let mut off = 0usize;
    while off + rate_bytes <= msg.len() {
        let mut lane = 0;
        while lane < (rate_bytes / 8) {
            let b = off + 8 * lane;
            state[lane] ^= u64::from_le_bytes([
                msg[b],
                msg[b + 1],
                msg[b + 2],
                msg[b + 3],
                msg[b + 4],
                msg[b + 5],
                msg[b + 6],
                msg[b + 7],
            ]);
            lane += 1;
        }
        keccak_f1600(&mut state);
        off += rate_bytes;
    }
    let mut tail = [0u8; 168];
    let rem = msg.len() - off;
    tail[..rem].copy_from_slice(&msg[off..]);
    tail[rem] ^= suffix;
    tail[rate_bytes - 1] ^= 0x80;
    let mut lane = 0;
    while lane < (rate_bytes / 8) {
        let b = 8 * lane;
        state[lane] ^= u64::from_le_bytes([
            tail[b],
            tail[b + 1],
            tail[b + 2],
            tail[b + 3],
            tail[b + 4],
            tail[b + 5],
            tail[b + 6],
            tail[b + 7],
        ]);
        lane += 1;
    }
    keccak_f1600(&mut state);

    let mut out = Vec::with_capacity(out_len);
    while out.len() < out_len {
        let mut lane = 0;
        while lane < (rate_bytes / 8) {
            let bytes = state[lane].to_le_bytes();
            let take = (out_len - out.len()).min(8);
            out.extend_from_slice(&bytes[..take]);
            if out.len() == out_len {
                break;
            }
            lane += 1;
        }
        if out.len() < out_len {
            keccak_f1600(&mut state);
        }
    }
    out
}

/// NIST FIPS 205 §9.3 / §10.2.2 approved Pre-Hash (`PH`) algorithms for `HashSLH-DSA`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SlhPreHash {
    Sha256,
    Sha512,
    Sha3_256,
    Sha3_384,
    Sha3_512,
    Shake128,
    Shake256,
}

impl SlhPreHash {
    pub fn by_name(name: &str) -> Option<Self> {
        match name {
            "sha256" | "SHA-256" | "SHA256" => Some(Self::Sha256),
            "sha512" | "SHA-512" | "SHA512" => Some(Self::Sha512),
            "sha3-256" | "SHA3-256" => Some(Self::Sha3_256),
            "sha3-384" | "SHA3-384" => Some(Self::Sha3_384),
            "sha3-512" | "SHA3-512" => Some(Self::Sha3_512),
            "shake128" | "SHAKE128" => Some(Self::Shake128),
            "shake256" | "SHAKE256" => Some(Self::Shake256),
            _ => None,
        }
    }

    /// DER-encoded ASN.1 `OBJECT IDENTIFIER` (`06 09 60 86 48 01 65 03 04 02 <id>`, 11 bytes)
    /// specified in NIST FIPS 205 §10.2.2 / NIST CSOR.
    #[inline]
    pub const fn oid_der(self) -> [u8; 11] {
        let last = match self {
            Self::Sha256 => 0x01,
            Self::Sha512 => 0x03,
            Self::Sha3_256 => 0x08,
            Self::Sha3_384 => 0x09,
            Self::Sha3_512 => 0x0a,
            Self::Shake128 => 0x0b,
            Self::Shake256 => 0x0c,
        };
        [
            0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, last,
        ]
    }

    /// NIST FIPS 205 §9.3 / SP 800-57 security-category compatibility check (`[P1-08]`):
    /// - Category 1 (`n == 16`, 128-bit): allows all 7 approved pre-hash functions;
    /// - Category 3 (`n == 24`, 192-bit): requires `>= 384`-bit collision strength (`SHA-512`, `SHA3-384`, `SHA3-512`, `SHAKE256`);
    /// - Category 5 (`n == 32`, 256-bit): requires `512`-bit collision strength (`SHA-512`, `SHA3-512`, `SHAKE256`).
    #[inline]
    pub const fn is_allowed_for_security_n(self, n: usize) -> bool {
        match n {
            16 => true,
            24 => matches!(
                self,
                Self::Sha512 | Self::Sha3_384 | Self::Sha3_512 | Self::Shake256
            ),
            32 => matches!(self, Self::Sha512 | Self::Sha3_512 | Self::Shake256),
            _ => false,
        }
    }

    /// Evaluate `PH(M)` according to NIST FIPS 205 §10.2.2 (`SHAKE128(M, 256)` = 32 B,
    /// `SHAKE256(M, 512)` = 64 B).
    pub fn hash_message(self, msg: &[u8]) -> Vec<u8> {
        match self {
            Self::Sha256 => sha256_digest(msg).to_vec(),
            Self::Sha512 => sha512_digest(msg).to_vec(),
            Self::Sha3_256 => keccak_sponge_eval(136, 0x06, 32, msg),
            Self::Sha3_384 => keccak_sponge_eval(104, 0x06, 48, msg),
            Self::Sha3_512 => keccak_sponge_eval(72, 0x06, 64, msg),
            Self::Shake128 => keccak_sponge_eval(168, 0x1F, 32, msg),
            Self::Shake256 => shake256_xof(64, msg),
        }
    }
}

// ============================================================================
// NIST FIPS 205 §11.2.1 `SLH-DSA-SHAKE` Tweakable Hash & PRF Functions
// ============================================================================

/// `PRF_msg(SK.prf, opt_rand, M') = SHAKE256(SK.prf || opt_rand || M', 8n)`.
pub fn fips205_prf_msg(n: usize, sk_prf: &[u8], opt_rand: &[u8], m_prime: &[u8]) -> SlhBlock {
    debug_assert_eq!(sk_prf.len(), n);
    debug_assert_eq!(opt_rand.len(), n);
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(sk_prf);
    xof.absorb(opt_rand);
    xof.absorb(m_prime);
    let mut out = SlhBlock::zero(n);
    xof.squeeze(&mut out.bytes[..n]);
    out
}

/// `H_msg(R, PK.seed, PK.root, M') = SHAKE256(R || PK.seed || PK.root || M', 8m)`.
pub fn fips205_h_msg(
    m_bytes: usize,
    r_rand: &[u8],
    pk_seed: &[u8],
    pk_root: &[u8],
    m_prime: &[u8],
) -> Vec<u8> {
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(r_rand);
    xof.absorb(pk_seed);
    xof.absorb(pk_root);
    xof.absorb(m_prime);
    let mut out = vec![0u8; m_bytes];
    xof.squeeze(&mut out);
    out
}

/// `PRF(PK.seed, SK.seed, ADRS) = SHAKE256(PK.seed || ADRS || SK.seed, 8n)`.
/// Note: For all `n` in `{16, 24, 32}`, `2n + 32 <= 96 < 136`, so this is a single-block sponge!
#[inline]
pub fn fips205_prf(n: usize, pk_seed: &[u8], sk_seed: &[u8], adrs: &Fips205Adrs) -> SlhBlock {
    debug_assert_eq!(pk_seed.len(), n);
    debug_assert_eq!(sk_seed.len(), n);
    let mut pre = [0u8; 96];
    pre[0..n].copy_from_slice(pk_seed);
    pre[n..n + 32].copy_from_slice(&adrs.to_bytes());
    pre[n + 32..2 * n + 32].copy_from_slice(sk_seed);
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(&pre[..2 * n + 32]);
    let mut out = SlhBlock::zero(n);
    xof.squeeze(&mut out.bytes[..n]);
    wipe_slice(&mut pre);
    out
}

/// `F(PK.seed, ADRS, M_1) = SHAKE256(PK.seed || ADRS || M_1, 8n)`.
#[inline]
pub fn fips205_f(n: usize, pk_seed: &[u8], adrs: &Fips205Adrs, m1: &SlhBlock) -> SlhBlock {
    debug_assert_eq!(pk_seed.len(), n);
    debug_assert_eq!(m1.len(), n);
    let mut pre = [0u8; 96];
    pre[0..n].copy_from_slice(pk_seed);
    pre[n..n + 32].copy_from_slice(&adrs.to_bytes());
    pre[n + 32..2 * n + 32].copy_from_slice(m1.as_slice());
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(&pre[..2 * n + 32]);
    let mut out = SlhBlock::zero(n);
    xof.squeeze(&mut out.bytes[..n]);
    wipe_slice(&mut pre);
    out
}

/// `H(PK.seed, ADRS, M_1 || M_2) = SHAKE256(PK.seed || ADRS || M_1 || M_2, 8n)`.
#[inline]
pub fn fips205_h(
    n: usize,
    pk_seed: &[u8],
    adrs: &Fips205Adrs,
    m1: &SlhBlock,
    m2: &SlhBlock,
) -> SlhBlock {
    debug_assert_eq!(pk_seed.len(), n);
    debug_assert_eq!(m1.len(), n);
    debug_assert_eq!(m2.len(), n);
    let mut pre = [0u8; 128];
    pre[0..n].copy_from_slice(pk_seed);
    pre[n..n + 32].copy_from_slice(&adrs.to_bytes());
    pre[n + 32..2 * n + 32].copy_from_slice(m1.as_slice());
    pre[2 * n + 32..3 * n + 32].copy_from_slice(m2.as_slice());
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(&pre[..3 * n + 32]);
    let mut out = SlhBlock::zero(n);
    xof.squeeze(&mut out.bytes[..n]);
    out
}

/// `T_l(PK.seed, ADRS, M_l) = SHAKE256(PK.seed || ADRS || M_l, 8n)`.
