//! Exact byte-for-byte NIST FIPS 205 (`SLH-DSA-SHAKE`) implementation across **all 6 official
//! SHAKE parameter sets** (`128s`, `128f`, `192s`, `192f`, `256s`, `256f`), 32-byte uncompressed
//! `ADRS` framing, WOTS+ ($w = 16, \ell_1 = 2n, \ell_2 = 3, \ell = 2n + 3$), FORS, hypertree,
//! §9.2 Pure external API (`ctx` context string, `|ctx| <= 255`), §9.3 Pre-Hash `HashSLH-DSA`
//! (`SHA-256`, `SHA-512`, `SHA3-256`, `SHA3-384`, `SHA3-512`, `SHAKE128`, `SHAKE256`), X.509 SPKI
//! DER public-key encoding compatible with OpenSSL 3.5, and cut-boundary `SlhMpcOracles` for
//! distributed threshold MPC signing without reconstructing `SK.seed` or `SK.prf`.
//!
//! Matches `lean/Qsag/Protocol/Signing/Fips205.lean` bit-for-bit across all algorithms (`slh_keygen_internal`,
//! `slh_sign_internal`, `slh_verify_internal`, pure `slh_sign`/`slh_verify`, `hash_slh_sign`/
//! `hash_slh_verify`, and `slhKeygenMpc`/`slhSignMpc`).

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::sponge::keccak::{Cshake256Xof, keccak_f1600, shake256_xof};
use crate::wipe::{ct_eq_bytes, wipe_bytes32, wipe_slice};
use qsag_accel::ct::ct_eq_mask_u64;

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
        qsag_verified::encode_fips205_adrs(self.verified())
    }

    const fn verified(&self) -> qsag_verified::Fips205Adrs {
        let ty = match qsag_verified::Fips205AdrsType::from_u32(self.adrs_type.to_u32()) {
            Some(ty) => ty,
            None => unreachable!(),
        };
        qsag_verified::Fips205Adrs::from_tree_u96(
            self.layer,
            self.tree,
            ty,
            self.key_pair,
            self.f5,
            self.f6,
        )
    }

    /// Decode a canonical 32-byte uncompressed `ADRS` (`None` if `type > 6`).
    pub fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let adrs = qsag_verified::decode_fips205_adrs(bytes)?;
        Some(Self {
            layer: adrs.layer,
            tree: (u128::from(adrs.tree_hi) << 64) | u128::from(adrs.tree_lo),
            adrs_type: Fips205AdrsType::from_u32(adrs.adrs_type.to_u32())?,
            key_pair: adrs.kp,
            f5: adrs.chain,
            f6: adrs.hash,
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
        let Some(total_fors_leaves) = (self.k as u64).checked_shl(self.a as u32) else {
            return false;
        };
        if total_fors_leaves > (u32::MAX as u64) + 1 {
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
            #[cfg(any(test, feature = "testing-ephemeral"))]
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
// FIPS 180-4 & FIPS 202 Pre-Hash Suite (§9.3 / §10.2.2)
// ============================================================================

/// FIPS 180-4 `SHA-256` (`32` bytes) and `SHA-512` (`64` bytes) digests.
pub use qsag_accel::sha2::{sha256 as sha256_digest, sha512 as sha512_digest};

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
pub fn fips205_th(n: usize, pk_seed: &[u8], adrs: &Fips205Adrs, blocks: &[SlhBlock]) -> SlhBlock {
    debug_assert_eq!(pk_seed.len(), n);
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(pk_seed);
    xof.absorb(&adrs.to_bytes());
    for b in blocks {
        debug_assert_eq!(b.len(), n);
        xof.absorb(b.as_slice());
    }
    let mut out = SlhBlock::zero(n);
    xof.squeeze(&mut out.bytes[..n]);
    out
}

/// Format FIPS 205 §9.2 / §10.2.1 pure `SLH-DSA` message `M' = 0x00 || (ctx.len() as u8) || ctx || msg`.
pub fn format_pure_m_prime(msg: &[u8], ctx: &[u8]) -> Result<Vec<u8>, Fips205Error> {
    if ctx.len() > FIPS205_MAX_CTX_LEN {
        return Err(Fips205Error::ContextTooLong(ctx.len()));
    }
    let mut m_prime = Vec::with_capacity(2 + ctx.len() + msg.len());
    m_prime.push(0x00);
    m_prime.push(ctx.len() as u8);
    m_prime.extend_from_slice(ctx);
    m_prime.extend_from_slice(msg);
    Ok(m_prime)
}

/// Format FIPS 205 §9.3 / §10.2.2 Pre-Hash `HashSLH-DSA` message
/// `M' = 0x01 || (ctx.len() as u8) || ctx || OID || PH(msg)`.
pub fn format_prehash_m_prime(
    ph: SlhPreHash,
    msg: &[u8],
    ctx: &[u8],
) -> Result<Vec<u8>, Fips205Error> {
    if ctx.len() > FIPS205_MAX_CTX_LEN {
        return Err(Fips205Error::ContextTooLong(ctx.len()));
    }
    let oid = ph.oid_der();
    let digest = ph.hash_message(msg);
    let mut m_prime = Vec::with_capacity(2 + ctx.len() + oid.len() + digest.len());
    m_prime.push(0x01);
    m_prime.push(ctx.len() as u8);
    m_prime.extend_from_slice(ctx);
    m_prime.extend_from_slice(&oid);
    m_prime.extend_from_slice(&digest);
    Ok(m_prime)
}

// ============================================================================
// Base-16 WOTS+ Digits, Checksum (`csum << 4`), and Chain Evaluation (§5)
// ============================================================================

/// Fallible base-16 WOTS+ digit + checksum extractor rejecting block lengths outside `{16, 24, 32}` (`[P1-08]`).
pub fn try_wots_base16_digits_and_csum(msg_n: &[u8]) -> Result<([u8; 67], usize), Fips205Error> {
    let n = msg_n.len();
    if n != 16 && n != 24 && n != 32 {
        return Err(Fips205Error::InvalidNodeBytes {
            expected: 32,
            actual: n,
        });
    }
    Ok(wots_base16_digits_and_csum(msg_n))
}

/// Compute the `2n + 3` base-16 WOTS+ digits (`2n` message nibbles + `3` big-endian checksum
/// nibbles of `csum << 4`) for an `n`-byte message block (`n` in `{16, 24, 32}`).
/// Clamps `msg_n` to `<= 32` bytes so untrusted slices can never panic in release builds (`[P1-08]`).
pub fn wots_base16_digits_and_csum(msg_n: &[u8]) -> ([u8; 67], usize) {
    let n = msg_n.len().min(32);
    debug_assert!(msg_n.len() == 16 || msg_n.len() == 24 || msg_n.len() == 32);
    let ell1 = 2 * n;
    let mut digits = [0u8; 67];
    if let Ok(msg) = msg_n.try_into() {
        let verified = qsag_verified::fips205_wots_checksum(msg);
        digits[..verified.len()].copy_from_slice(&verified);
        return (digits, verified.len());
    }
    let mut csum: u32 = 0;
    for i in 0..n {
        let hi = msg_n[i] >> 4;
        let lo = msg_n[i] & 0x0F;
        digits[2 * i] = hi;
        digits[2 * i + 1] = lo;
        csum += (15 - hi as u32) + (15 - lo as u32);
    }
    let shifted = (csum << 4) as u16;
    let cbytes = shifted.to_be_bytes();
    digits[ell1] = cbytes[0] >> 4;
    digits[ell1 + 1] = cbytes[0] & 0x0F;
    digits[ell1 + 2] = cbytes[1] >> 4;
    (digits, ell1 + 3)
}

/// NIST FIPS 205 Algorithm 5 `chain(X, i, s, PK.seed, ADRS)` (wiping intermediate secret states).
pub fn fips205_chain(
    mut x: SlhBlock,
    start_i: u32,
    steps_s: u32,
    pk_seed: &[u8],
    base_adrs: Fips205Adrs,
) -> SlhBlock {
    let n = x.len();
    for j in start_i..start_i.saturating_add(steps_s) {
        let mut adrs = base_adrs;
        adrs.f6 = j;
        let next = fips205_f(n, pk_seed, &adrs, &x);
        x.wipe();
        x = next;
    }
    x
}

// ============================================================================
// 8-Way (`AVX-512`) & 4-Way (`AVX2` / `AArch64 FEAT_SHA3`) Batch SHAKE256 Helpers
// ============================================================================

#[inline]
fn ct_ge_u32_mask64(a: u32, b: u32) -> u64 {
    let borrow = core::hint::black_box(((a as u64).wrapping_sub(b as u64)) >> 63);
    borrow.wrapping_sub(1)
}

#[inline]
fn adrs_to_le_words(adrs: &Fips205Adrs) -> [u64; 4] {
    let b = adrs.to_bytes();
    [
        u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]),
        u64::from_le_bytes([b[8], b[9], b[10], b[11], b[12], b[13], b[14], b[15]]),
        u64::from_le_bytes([b[16], b[17], b[18], b[19], b[20], b[21], b[22], b[23]]),
        u64::from_le_bytes([b[24], b[25], b[26], b[27], b[28], b[29], b[30], b[31]]),
    ]
}

#[inline]
fn with_f6_in_w3(w3_f5_only: u64, f6: u32) -> u64 {
    (w3_f5_only & 0xFFFF_FFFF) | ((u32::from_le_bytes(f6.to_be_bytes()) as u64) << 32)
}

#[inline]
fn pack_seed_words(seed: &[u8], n_words: usize) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (w, slot) in out.iter_mut().enumerate().take(n_words) {
        let off = 8 * w;
        *slot = u64::from_le_bytes([
            seed[off],
            seed[off + 1],
            seed[off + 2],
            seed[off + 3],
            seed[off + 4],
            seed[off + 5],
            seed[off + 6],
            seed[off + 7],
        ]);
    }
    out
}

#[inline]
fn pack_block_words(blk: &SlhBlock, n_words: usize) -> [u64; 4] {
    pack_seed_words(&blk.bytes, n_words)
}

#[inline]
fn unpack_words_to_block(words: &[u64; 4], n: usize) -> SlhBlock {
    let n_words = n / 8;
    let mut bytes = [0u8; 32];
    for (w, &word) in words.iter().enumerate().take(n_words) {
        bytes[8 * w..8 * (w + 1)].copy_from_slice(&word.to_le_bytes());
    }
    SlhBlock {
        bytes,
        len: n as u8,
    }
}

/// 8-lane single-block `PRF(PK.seed, SK.seed, ADRS_i)` (`SHAKE256`, `2n + 32 <= 96 < 136` bytes).
pub fn shake256_prf_x8(
    n: usize,
    pk_seed: &[u8],
    sk_seed: &[u8],
    adrs: &[Fips205Adrs; 8],
) -> [SlhBlock; 8] {
    let n_words = n / 8;
    let pk_w = pack_seed_words(pk_seed, n_words);
    let mut sk_w = pack_seed_words(sk_seed, n_words);
    let mut state = qsag_asm::KeccakState8x::default();
    for w in 0..n_words {
        state.0[w] = [pk_w[w]; 8];
        state.0[n_words + 4 + w] = [sk_w[w]; 8];
    }
    let end_word = 2 * n_words + 4;
    state.0[end_word] = [0x1F; 8];
    state.0[16] = [1u64 << 63; 8];
    for (lane, a) in adrs.iter().enumerate() {
        let aw = adrs_to_le_words(a);
        state.0[n_words][lane] = aw[0];
        state.0[n_words + 1][lane] = aw[1];
        state.0[n_words + 2][lane] = aw[2];
        state.0[n_words + 3][lane] = aw[3];
    }
    qsag_asm::keccak_f1600_x8(&mut state);
    let out = core::array::from_fn(|lane| {
        let mut words = [0u64; 4];
        for (w, slot) in words.iter_mut().enumerate().take(n_words) {
            *slot = state.0[w][lane];
        }
        unpack_words_to_block(&words, n)
    });
    qsag_asm::volatile_fill(&mut state.0, [0; 8]);
    qsag_asm::volatile_fill(&mut sk_w, 0);
    out
}

/// 8-lane single-block `F(PK.seed, ADRS_i, M1_i)` (`SHAKE256`, `2n + 32 <= 96 < 136` bytes).
#[allow(clippy::needless_range_loop)]
pub fn shake256_f_x8(
    n: usize,
    pk_seed: &[u8],
    adrs: &[Fips205Adrs; 8],
    m1: &[SlhBlock; 8],
) -> [SlhBlock; 8] {
    let n_words = n / 8;
    let pk_w = pack_seed_words(pk_seed, n_words);
    let mut state = qsag_asm::KeccakState8x::default();
    for w in 0..n_words {
        state.0[w] = [pk_w[w]; 8];
    }
    let end_word = 2 * n_words + 4;
    state.0[end_word] = [0x1F; 8];
    state.0[16] = [1u64 << 63; 8];
    for lane in 0..8 {
        let aw = adrs_to_le_words(&adrs[lane]);
        let mw = pack_block_words(&m1[lane], n_words);
        state.0[n_words][lane] = aw[0];
        state.0[n_words + 1][lane] = aw[1];
        state.0[n_words + 2][lane] = aw[2];
        state.0[n_words + 3][lane] = aw[3];
        for w in 0..n_words {
            state.0[n_words + 4 + w][lane] = mw[w];
        }
    }
    qsag_asm::keccak_f1600_x8(&mut state);
    let out = core::array::from_fn(|lane| {
        let mut words = [0u64; 4];
        for (w, slot) in words.iter_mut().enumerate().take(n_words) {
            *slot = state.0[w][lane];
        }
        unpack_words_to_block(&words, n)
    });
    qsag_asm::volatile_fill(&mut state.0, [0; 8]);
    out
}

/// 8-lane single-block `H(PK.seed, ADRS_i, M1_i || M2_i)` (`SHAKE256`, `3n + 32 <= 128 < 136` bytes).
#[allow(clippy::needless_range_loop)]
pub fn shake256_h_x8(
    n: usize,
    pk_seed: &[u8],
    adrs: &[Fips205Adrs; 8],
    m1: &[SlhBlock; 8],
    m2: &[SlhBlock; 8],
) -> [SlhBlock; 8] {
    let n_words = n / 8;
    let pk_w = pack_seed_words(pk_seed, n_words);
    let mut state = qsag_asm::KeccakState8x::default();
    for w in 0..n_words {
        state.0[w] = [pk_w[w]; 8];
    }
    let end_word = 3 * n_words + 4;
    for lane in 0..8 {
        let aw = adrs_to_le_words(&adrs[lane]);
        let m1w = pack_block_words(&m1[lane], n_words);
        let m2w = pack_block_words(&m2[lane], n_words);
        state.0[n_words][lane] = aw[0];
        state.0[n_words + 1][lane] = aw[1];
        state.0[n_words + 2][lane] = aw[2];
        state.0[n_words + 3][lane] = aw[3];
        for w in 0..n_words {
            state.0[n_words + 4 + w][lane] = m1w[w];
            state.0[2 * n_words + 4 + w][lane] = m2w[w];
        }
        state.0[end_word][lane] ^= 0x1F;
        state.0[16][lane] ^= 1u64 << 63;
    }
    qsag_asm::keccak_f1600_x8(&mut state);
    let out = core::array::from_fn(|lane| {
        let mut words = [0u64; 4];
        for (w, slot) in words.iter_mut().enumerate().take(n_words) {
            *slot = state.0[w][lane];
        }
        unpack_words_to_block(&words, n)
    });
    qsag_asm::volatile_fill(&mut state.0, [0; 8]);
    out
}

/// Evaluate `wots_pkGen` across 8 consecutive key pairs (`start_kp..start_kp + 8`) in lockstep,
/// keeping all `ell` chain states and the final `T_ell` compression in 8-lane `[u64; 8]` ZMM layout.
#[allow(clippy::needless_range_loop)]
fn wots_pk_gen_8_leaves(
    params: &Fips205Params,
    sk_seed: &[u8],
    pk_seed: &[u8],
    base_adrs: Fips205Adrs,
    start_kp: u32,
    out_leaves: &mut Vec<SlhBlock>,
) {
    let n = params.n;
    let n_words = n / 8;
    let ell = params.ell();
    let pk_w = pack_seed_words(pk_seed, n_words);
    let mut sk_w = pack_seed_words(sk_seed, n_words);

    let mut prf_adrs_w2 = [0u64; 8];
    let mut hash_adrs_w2 = [0u64; 8];
    let mut wotspk_adrs_words = [[0u64; 8]; 4];

    let prf_proto = base_adrs.with_type_and_clear(Fips205AdrsType::WotsPrf);
    let hash_proto = base_adrs.with_type_and_clear(Fips205AdrsType::WotsHash);
    let pk_proto = base_adrs.with_type_and_clear(Fips205AdrsType::WotsPk);
    let common_aw = adrs_to_le_words(&hash_proto);

    for lane in 0..8 {
        let kp = start_kp + (lane as u32);
        let mut pa = prf_proto;
        pa.key_pair = kp;
        prf_adrs_w2[lane] = adrs_to_le_words(&pa)[2];

        let mut ha = hash_proto;
        ha.key_pair = kp;
        hash_adrs_w2[lane] = adrs_to_le_words(&ha)[2];

        let mut ka = pk_proto;
        ka.key_pair = kp;
        let kaw = adrs_to_le_words(&ka);
        for w in 0..4 {
            wotspk_adrs_words[w][lane] = kaw[w];
        }
    }

    let end_word = 2 * n_words + 4;
    let mut prf_base = qsag_asm::KeccakState8x::default();
    let mut hash_base = qsag_asm::KeccakState8x::default();
    for w in 0..n_words {
        prf_base.0[w] = [pk_w[w]; 8];
        prf_base.0[n_words + 4 + w] = [sk_w[w]; 8];
        hash_base.0[w] = [pk_w[w]; 8];
    }
    prf_base.0[n_words] = [common_aw[0]; 8];
    prf_base.0[n_words + 1] = [common_aw[1]; 8];
    prf_base.0[n_words + 2] = prf_adrs_w2;
    prf_base.0[end_word] = [0x1F; 8];
    prf_base.0[16] = [1u64 << 63; 8];

    hash_base.0[n_words] = [common_aw[0]; 8];
    hash_base.0[n_words + 1] = [common_aw[1]; 8];
    hash_base.0[n_words + 2] = hash_adrs_w2;
    hash_base.0[end_word] = [0x1F; 8];
    hash_base.0[16] = [1u64 << 63; 8];

    let mut endpoints = [[[0u64; 8]; 4]; 67];
    let mut state = qsag_asm::KeccakState8x::default();

    for (ch, ep_slot) in endpoints.iter_mut().enumerate().take(ell) {
        let f5_le = u32::from_le_bytes((ch as u32).to_be_bytes()) as u64;
        state = prf_base;
        state.0[n_words + 3] = [f5_le; 8];
        qsag_asm::keccak_f1600_x8(&mut state);

        for step in 0..15u32 {
            let mut cur_rows = [[0u64; 8]; 4];
            for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                *row = state.0[w];
            }
            state = hash_base;
            state.0[n_words + 3] = [with_f6_in_w3(f5_le, step); 8];
            for (w, row) in cur_rows.iter().enumerate().take(n_words) {
                state.0[n_words + 4 + w] = *row;
            }
            qsag_asm::keccak_f1600_x8(&mut state);
            qsag_asm::volatile_fill(&mut cur_rows, [0; 8]);
        }

        for (w, slot) in ep_slot.iter_mut().enumerate().take(n_words) {
            *slot = state.0[w];
        }
    }

    qsag_asm::volatile_fill(&mut state.0, [0; 8]);
    qsag_asm::volatile_fill(&mut prf_base.0, [0; 8]);
    qsag_asm::volatile_fill(&mut sk_w, 0);

    // Stream `PK.seed || wotspk_adrs || endpoints[0..ell]` directly in 8-way `[u64; 8]` rows.
    let mut th_state = qsag_asm::KeccakState8x::default();
    let mut slot = 0usize;
    let push_row = |row: &[u64; 8], st: &mut qsag_asm::KeccakState8x, s: &mut usize| {
        for lane in 0..8 {
            st.0[*s][lane] ^= row[lane];
        }
        *s += 1;
        if *s == 17 {
            qsag_asm::keccak_f1600_x8(st);
            *s = 0;
        }
    };

    for &pw in pk_w.iter().take(n_words) {
        push_row(&[pw; 8], &mut th_state, &mut slot);
    }
    for aw_row in &wotspk_adrs_words {
        push_row(aw_row, &mut th_state, &mut slot);
    }
    for ep in endpoints.iter().take(ell) {
        for row in ep.iter().take(n_words) {
            push_row(row, &mut th_state, &mut slot);
        }
    }
    for lane in 0..8 {
        th_state.0[slot][lane] ^= 0x1F;
        th_state.0[16][lane] ^= 1u64 << 63;
    }
    qsag_asm::keccak_f1600_x8(&mut th_state);

    for lane in 0..8 {
        let mut words = [0u64; 4];
        for (w, out_w) in words.iter_mut().enumerate().take(n_words) {
            *out_w = th_state.0[w][lane];
        }
        out_leaves.push(unpack_words_to_block(&words, n));
    }
    qsag_asm::volatile_fill(&mut th_state.0, [0; 8]);
}

/// Evaluate `wots_pkGen` across 4 consecutive key pairs (`start_kp..start_kp + 4`) in lockstep.
#[allow(clippy::needless_range_loop)]
fn wots_pk_gen_4_leaves(
    params: &Fips205Params,
    sk_seed: &[u8],
    pk_seed: &[u8],
    base_adrs: Fips205Adrs,
    start_kp: u32,
    out_leaves: &mut Vec<SlhBlock>,
) {
    let n = params.n;
    let n_words = n / 8;
    let ell = params.ell();
    let pk_w = pack_seed_words(pk_seed, n_words);
    let mut sk_w = pack_seed_words(sk_seed, n_words);

    let mut prf_adrs_w2 = [0u64; 4];
    let mut hash_adrs_w2 = [0u64; 4];
    let mut wotspk_adrs_words = [[0u64; 4]; 4];

    let prf_proto = base_adrs.with_type_and_clear(Fips205AdrsType::WotsPrf);
    let hash_proto = base_adrs.with_type_and_clear(Fips205AdrsType::WotsHash);
    let pk_proto = base_adrs.with_type_and_clear(Fips205AdrsType::WotsPk);
    let common_aw = adrs_to_le_words(&hash_proto);

    for lane in 0..4 {
        let kp = start_kp + (lane as u32);
        let mut pa = prf_proto;
        pa.key_pair = kp;
        prf_adrs_w2[lane] = adrs_to_le_words(&pa)[2];

        let mut ha = hash_proto;
        ha.key_pair = kp;
        hash_adrs_w2[lane] = adrs_to_le_words(&ha)[2];

        let mut ka = pk_proto;
        ka.key_pair = kp;
        let kaw = adrs_to_le_words(&ka);
        for w in 0..4 {
            wotspk_adrs_words[w][lane] = kaw[w];
        }
    }

    let end_word = 2 * n_words + 4;
    let mut prf_base = qsag_asm::KeccakState4x::default();
    let mut hash_base = qsag_asm::KeccakState4x::default();
    for w in 0..n_words {
        prf_base.0[w] = [pk_w[w]; 4];
        prf_base.0[n_words + 4 + w] = [sk_w[w]; 4];
        hash_base.0[w] = [pk_w[w]; 4];
    }
    prf_base.0[n_words] = [common_aw[0]; 4];
    prf_base.0[n_words + 1] = [common_aw[1]; 4];
    prf_base.0[n_words + 2] = prf_adrs_w2;
    prf_base.0[end_word] = [0x1F; 4];
    prf_base.0[16] = [1u64 << 63; 4];

    hash_base.0[n_words] = [common_aw[0]; 4];
    hash_base.0[n_words + 1] = [common_aw[1]; 4];
    hash_base.0[n_words + 2] = hash_adrs_w2;
    hash_base.0[end_word] = [0x1F; 4];
    hash_base.0[16] = [1u64 << 63; 4];

    let mut endpoints = [[[0u64; 4]; 4]; 67];
    let mut state = qsag_asm::KeccakState4x::default();

    for (ch, ep_slot) in endpoints.iter_mut().enumerate().take(ell) {
        let f5_le = u32::from_le_bytes((ch as u32).to_be_bytes()) as u64;
        state = prf_base;
        state.0[n_words + 3] = [f5_le; 4];
        qsag_asm::keccak_f1600_x4(&mut state);

        for step in 0..15u32 {
            let mut cur_rows = [[0u64; 4]; 4];
            for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                *row = state.0[w];
            }
            state = hash_base;
            state.0[n_words + 3] = [with_f6_in_w3(f5_le, step); 4];
            for (w, row) in cur_rows.iter().enumerate().take(n_words) {
                state.0[n_words + 4 + w] = *row;
            }
            qsag_asm::keccak_f1600_x4(&mut state);
            qsag_asm::volatile_fill(&mut cur_rows, [0; 4]);
        }

        for (w, slot) in ep_slot.iter_mut().enumerate().take(n_words) {
            *slot = state.0[w];
        }
    }

    qsag_asm::volatile_fill(&mut state.0, [0; 4]);
    qsag_asm::volatile_fill(&mut prf_base.0, [0; 4]);
    qsag_asm::volatile_fill(&mut sk_w, 0);

    let mut th_state = qsag_asm::KeccakState4x::default();
    let mut slot = 0usize;
    let push_row = |row: &[u64; 4], st: &mut qsag_asm::KeccakState4x, s: &mut usize| {
        for lane in 0..4 {
            st.0[*s][lane] ^= row[lane];
        }
        *s += 1;
        if *s == 17 {
            qsag_asm::keccak_f1600_x4(st);
            *s = 0;
        }
    };

    for &pw in pk_w.iter().take(n_words) {
        push_row(&[pw; 4], &mut th_state, &mut slot);
    }
    for aw_row in &wotspk_adrs_words {
        push_row(aw_row, &mut th_state, &mut slot);
    }
    for ep in endpoints.iter().take(ell) {
        for row in ep.iter().take(n_words) {
            push_row(row, &mut th_state, &mut slot);
        }
    }
    for lane in 0..4 {
        th_state.0[slot][lane] ^= 0x1F;
        th_state.0[16][lane] ^= 1u64 << 63;
    }
    qsag_asm::keccak_f1600_x4(&mut th_state);

    for lane in 0..4 {
        let mut words = [0u64; 4];
        for (w, out_w) in words.iter_mut().enumerate().take(n_words) {
            *out_w = th_state.0[w][lane];
        }
        out_leaves.push(unpack_words_to_block(&words, n));
    }
    qsag_asm::volatile_fill(&mut th_state.0, [0; 4]);
}

fn compute_xmss_subtree_leaves(
    params: &Fips205Params,
    sk_seed: &[u8],
    pk_seed: &[u8],
    base_adrs: Fips205Adrs,
) -> Vec<SlhBlock> {
    let n_leaves = 1usize << params.hp;
    let mut leaves = Vec::with_capacity(n_leaves);
    if matches!(params.n, 16 | 24 | 32) && sk_seed.len() == params.n && pk_seed.len() == params.n {
        if n_leaves >= 8 {
            for kp_base in (0..n_leaves).step_by(8) {
                wots_pk_gen_8_leaves(
                    params,
                    sk_seed,
                    pk_seed,
                    base_adrs,
                    kp_base as u32,
                    &mut leaves,
                );
            }
            return leaves;
        } else if n_leaves == 4 {
            wots_pk_gen_4_leaves(params, sk_seed, pk_seed, base_adrs, 0, &mut leaves);
            return leaves;
        }
    }
    for kp in 0..n_leaves {
        let mut leaf_adrs = base_adrs;
        leaf_adrs.key_pair = kp as u32;
        leaves.push(wots_pk_gen(params, sk_seed, pk_seed, leaf_adrs));
    }
    leaves
}

/// NIST FIPS 205 Algorithm 6 `wots_pkGen(SK.seed, PK.seed, ADRS)`.
#[allow(clippy::needless_range_loop)]
pub fn wots_pk_gen(
    params: &Fips205Params,
    sk_seed: &[u8],
    pk_seed: &[u8],
    adrs: Fips205Adrs,
) -> SlhBlock {
    let n = params.n;
    let ell = params.ell();
    let mut sk_adrs = adrs.with_type_and_clear(Fips205AdrsType::WotsPrf);
    sk_adrs.key_pair = adrs.key_pair;

    let mut chain_adrs = adrs.with_type_and_clear(Fips205AdrsType::WotsHash);
    chain_adrs.key_pair = adrs.key_pair;

    let mut tmp = [SlhBlock::zero(32); 67];
    if matches!(n, 16 | 24 | 32) && sk_seed.len() == n && pk_seed.len() == n {
        let n_words = n / 8;
        let pk_w = pack_seed_words(pk_seed, n_words);
        let mut sk_w = pack_seed_words(sk_seed, n_words);
        let sk_aw = adrs_to_le_words(&sk_adrs);
        let ch_aw = adrs_to_le_words(&chain_adrs);
        let end_word = 2 * n_words + 4;

        for base in (0..ell).step_by(8) {
            let count = (ell - base).min(8);
            if count > 4 {
                let mut f5_w = [0u64; 8];
                for (lane, slot) in f5_w.iter_mut().enumerate().take(count) {
                    *slot = u32::from_le_bytes(((base + lane) as u32).to_be_bytes()) as u64;
                }
                let mut state = qsag_asm::KeccakState8x::default();
                for w in 0..n_words {
                    state.0[w] = [pk_w[w]; 8];
                }
                for lane in 0..count {
                    state.0[n_words][lane] = sk_aw[0];
                    state.0[n_words + 1][lane] = sk_aw[1];
                    state.0[n_words + 2][lane] = sk_aw[2];
                    state.0[n_words + 3][lane] = f5_w[lane];
                    for w in 0..n_words {
                        state.0[n_words + 4 + w][lane] = sk_w[w];
                    }
                    state.0[end_word][lane] = 0x1F;
                    state.0[16][lane] = 1u64 << 63;
                }
                qsag_asm::keccak_f1600_x8(&mut state);

                for step in 0..15u32 {
                    let mut cur_rows = [[0u64; 8]; 4];
                    for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                        *row = state.0[w];
                    }
                    state = qsag_asm::KeccakState8x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 8];
                    }
                    for lane in 0..count {
                        state.0[n_words][lane] = ch_aw[0];
                        state.0[n_words + 1][lane] = ch_aw[1];
                        state.0[n_words + 2][lane] = ch_aw[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(f5_w[lane], step);
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = cur_rows[w][lane];
                        }
                        state.0[end_word][lane] = 0x1F;
                        state.0[16][lane] = 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x8(&mut state);
                    qsag_asm::volatile_fill(&mut cur_rows, [0; 8]);
                }

                for lane in 0..count {
                    let mut words = [0u64; 4];
                    for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                        *slot = state.0[w][lane];
                    }
                    tmp[base + lane] = unpack_words_to_block(&words, n);
                }
                qsag_asm::volatile_fill(&mut state.0, [0; 8]);
            } else {
                let mut f5_w = [0u64; 4];
                for (lane, slot) in f5_w.iter_mut().enumerate().take(count) {
                    *slot = u32::from_le_bytes(((base + lane) as u32).to_be_bytes()) as u64;
                }
                let mut state = qsag_asm::KeccakState4x::default();
                for w in 0..n_words {
                    state.0[w] = [pk_w[w]; 4];
                }
                for lane in 0..count {
                    state.0[n_words][lane] = sk_aw[0];
                    state.0[n_words + 1][lane] = sk_aw[1];
                    state.0[n_words + 2][lane] = sk_aw[2];
                    state.0[n_words + 3][lane] = f5_w[lane];
                    for w in 0..n_words {
                        state.0[n_words + 4 + w][lane] = sk_w[w];
                    }
                    state.0[end_word][lane] = 0x1F;
                    state.0[16][lane] = 1u64 << 63;
                }
                qsag_asm::keccak_f1600_x4(&mut state);

                for step in 0..15u32 {
                    let mut cur_rows = [[0u64; 4]; 4];
                    for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                        *row = state.0[w];
                    }
                    state = qsag_asm::KeccakState4x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 4];
                    }
                    for lane in 0..count {
                        state.0[n_words][lane] = ch_aw[0];
                        state.0[n_words + 1][lane] = ch_aw[1];
                        state.0[n_words + 2][lane] = ch_aw[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(f5_w[lane], step);
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = cur_rows[w][lane];
                        }
                        state.0[end_word][lane] = 0x1F;
                        state.0[16][lane] = 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x4(&mut state);
                    qsag_asm::volatile_fill(&mut cur_rows, [0; 4]);
                }

                for lane in 0..count {
                    let mut words = [0u64; 4];
                    for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                        *slot = state.0[w][lane];
                    }
                    tmp[base + lane] = unpack_words_to_block(&words, n);
                }
                qsag_asm::volatile_fill(&mut state.0, [0; 4]);
            }
        }
        qsag_asm::volatile_fill(&mut sk_w, 0);
    } else {
        let mut i = 0;
        while i < ell {
            sk_adrs.f5 = i as u32;
            let mut sk_i = fips205_prf(n, pk_seed, sk_seed, &sk_adrs);
            chain_adrs.f5 = i as u32;
            tmp[i] = fips205_chain(sk_i, 0, 15, pk_seed, chain_adrs);
            sk_i.wipe();
            i += 1;
        }
    }
    let mut wotspk_adrs = adrs.with_type_and_clear(Fips205AdrsType::WotsPk);
    wotspk_adrs.key_pair = adrs.key_pair;
    fips205_th(n, pk_seed, &wotspk_adrs, &tmp[..ell])
}

/// NIST FIPS 205 Algorithm 7 `wots_sign(M, SK.seed, PK.seed, ADRS)`.
#[allow(clippy::needless_range_loop)]
pub fn wots_sign(
    params: &Fips205Params,
    msg_n: &SlhBlock,
    sk_seed: &[u8],
    pk_seed: &[u8],
    adrs: Fips205Adrs,
) -> Vec<SlhBlock> {
    let n = params.n;
    let (digits, ell) = wots_base16_digits_and_csum(msg_n.as_slice());
    debug_assert_eq!(ell, params.ell());
    let mut sk_adrs = adrs.with_type_and_clear(Fips205AdrsType::WotsPrf);
    sk_adrs.key_pair = adrs.key_pair;

    let mut chain_adrs = adrs.with_type_and_clear(Fips205AdrsType::WotsHash);
    chain_adrs.key_pair = adrs.key_pair;

    let mut sig = Vec::with_capacity(ell);
    if matches!(n, 16 | 24 | 32) && sk_seed.len() == n && pk_seed.len() == n {
        let n_words = n / 8;
        let pk_w = pack_seed_words(pk_seed, n_words);
        let mut sk_w = pack_seed_words(sk_seed, n_words);
        let sk_aw = adrs_to_le_words(&sk_adrs);
        let ch_aw = adrs_to_le_words(&chain_adrs);
        let end_word = 2 * n_words + 4;

        for base in (0..ell).step_by(8) {
            let count = (ell - base).min(8);
            if count > 4 {
                let mut f5_w = [0u64; 8];
                let mut targets = [0u32; 8];
                for lane in 0..count {
                    f5_w[lane] = u32::from_le_bytes(((base + lane) as u32).to_be_bytes()) as u64;
                    targets[lane] = digits[base + lane] as u32;
                }
                let mut state = qsag_asm::KeccakState8x::default();
                for w in 0..n_words {
                    state.0[w] = [pk_w[w]; 8];
                }
                for lane in 0..count {
                    state.0[n_words][lane] = sk_aw[0];
                    state.0[n_words + 1][lane] = sk_aw[1];
                    state.0[n_words + 2][lane] = sk_aw[2];
                    state.0[n_words + 3][lane] = f5_w[lane];
                    for w in 0..n_words {
                        state.0[n_words + 4 + w][lane] = sk_w[w];
                    }
                    state.0[end_word][lane] = 0x1F;
                    state.0[16][lane] = 1u64 << 63;
                }
                qsag_asm::keccak_f1600_x8(&mut state);

                let mut acc_rows = [[0u64; 8]; 4];
                for (w, row) in acc_rows.iter_mut().enumerate().take(n_words) {
                    *row = state.0[w];
                }

                // Constant-trip 15-step lockstep chain with constant-time mask selection.
                for step in 0..15u32 {
                    let mut cur_rows = [[0u64; 8]; 4];
                    for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                        *row = state.0[w];
                    }
                    state = qsag_asm::KeccakState8x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 8];
                    }
                    for lane in 0..count {
                        state.0[n_words][lane] = ch_aw[0];
                        state.0[n_words + 1][lane] = ch_aw[1];
                        state.0[n_words + 2][lane] = ch_aw[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(f5_w[lane], step);
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = cur_rows[w][lane];
                        }
                        state.0[end_word][lane] = 0x1F;
                        state.0[16][lane] = 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x8(&mut state);
                    qsag_asm::volatile_fill(&mut cur_rows, [0; 8]);

                    let done_step = step + 1;
                    for lane in 0..count {
                        let mask = ct_eq_mask_u64(u64::from(done_step), u64::from(targets[lane]));
                        for (w, acc_row) in acc_rows.iter_mut().enumerate().take(n_words) {
                            acc_row[lane] = (acc_row[lane] & !mask) | (state.0[w][lane] & mask);
                        }
                    }
                }

                for lane in 0..count {
                    let mut words = [0u64; 4];
                    for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                        *slot = acc_rows[w][lane];
                    }
                    sig.push(unpack_words_to_block(&words, n));
                    qsag_asm::volatile_fill(&mut words, 0);
                }
                qsag_asm::volatile_fill(&mut acc_rows, [0; 8]);
                qsag_asm::volatile_fill(&mut state.0, [0; 8]);
            } else {
                let mut f5_w = [0u64; 4];
                let mut targets = [0u32; 4];
                for lane in 0..count {
                    f5_w[lane] = u32::from_le_bytes(((base + lane) as u32).to_be_bytes()) as u64;
                    targets[lane] = digits[base + lane] as u32;
                }
                let mut state = qsag_asm::KeccakState4x::default();
                for w in 0..n_words {
                    state.0[w] = [pk_w[w]; 4];
                }
                for lane in 0..count {
                    state.0[n_words][lane] = sk_aw[0];
                    state.0[n_words + 1][lane] = sk_aw[1];
                    state.0[n_words + 2][lane] = sk_aw[2];
                    state.0[n_words + 3][lane] = f5_w[lane];
                    for w in 0..n_words {
                        state.0[n_words + 4 + w][lane] = sk_w[w];
                    }
                    state.0[end_word][lane] = 0x1F;
                    state.0[16][lane] = 1u64 << 63;
                }
                qsag_asm::keccak_f1600_x4(&mut state);

                let mut acc_rows = [[0u64; 4]; 4];
                for (w, row) in acc_rows.iter_mut().enumerate().take(n_words) {
                    *row = state.0[w];
                }

                for step in 0..15u32 {
                    let mut cur_rows = [[0u64; 4]; 4];
                    for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                        *row = state.0[w];
                    }
                    state = qsag_asm::KeccakState4x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 4];
                    }
                    for lane in 0..count {
                        state.0[n_words][lane] = ch_aw[0];
                        state.0[n_words + 1][lane] = ch_aw[1];
                        state.0[n_words + 2][lane] = ch_aw[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(f5_w[lane], step);
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = cur_rows[w][lane];
                        }
                        state.0[end_word][lane] = 0x1F;
                        state.0[16][lane] = 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x4(&mut state);
                    qsag_asm::volatile_fill(&mut cur_rows, [0; 4]);

                    let done_step = step + 1;
                    for lane in 0..count {
                        let mask = ct_eq_mask_u64(u64::from(done_step), u64::from(targets[lane]));
                        for (w, acc_row) in acc_rows.iter_mut().enumerate().take(n_words) {
                            acc_row[lane] = (acc_row[lane] & !mask) | (state.0[w][lane] & mask);
                        }
                    }
                }

                for lane in 0..count {
                    let mut words = [0u64; 4];
                    for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                        *slot = acc_rows[w][lane];
                    }
                    sig.push(unpack_words_to_block(&words, n));
                    qsag_asm::volatile_fill(&mut words, 0);
                }
                qsag_asm::volatile_fill(&mut acc_rows, [0; 4]);
                qsag_asm::volatile_fill(&mut state.0, [0; 4]);
            }
        }
        qsag_asm::volatile_fill(&mut sk_w, 0);
        return sig;
    }

    let mut i = 0;
    while i < ell {
        sk_adrs.f5 = i as u32;
        let mut sk_i = fips205_prf(n, pk_seed, sk_seed, &sk_adrs);
        chain_adrs.f5 = i as u32;
        sig.push(fips205_chain(
            sk_i,
            0,
            digits[i] as u32,
            pk_seed,
            chain_adrs,
        ));
        sk_i.wipe();
        i += 1;
    }
    sig
}

/// NIST FIPS 205 Algorithm 8 `wots_pkFromSig(sig, M, PK.seed, ADRS)`.
#[allow(clippy::needless_range_loop)]
pub fn wots_pk_from_sig(
    params: &Fips205Params,
    sig: &[SlhBlock],
    msg_n: &SlhBlock,
    pk_seed: &[u8],
    adrs: Fips205Adrs,
) -> SlhBlock {
    let n = params.n;
    let (digits, ell) = wots_base16_digits_and_csum(msg_n.as_slice());
    debug_assert_eq!(ell, params.ell());
    let mut chain_adrs = adrs.with_type_and_clear(Fips205AdrsType::WotsHash);
    chain_adrs.key_pair = adrs.key_pair;

    let mut tmp = [SlhBlock::zero(32); 67];
    if matches!(n, 16 | 24 | 32) && pk_seed.len() == n && sig.len() >= ell {
        let n_words = n / 8;
        let pk_w = pack_seed_words(pk_seed, n_words);
        let ch_aw = adrs_to_le_words(&chain_adrs);
        let end_word = 2 * n_words + 4;

        for base in (0..ell).step_by(8) {
            let count = (ell - base).min(8);
            let min_d = digits[base..base + count]
                .iter()
                .copied()
                .min()
                .unwrap_or(15) as u32;

            if n == 16 && count < 4 {
                let seed = pk_seed.try_into().expect("16-byte seed");
                for index in base..base + count {
                    chain_adrs.f5 = index as u32;
                    let start = u32::from(digits[index]);
                    let endpoint = qsag_verified::fips205_wots_chain(
                        sig[index].bytes[..16].try_into().unwrap(),
                        start,
                        15 - start,
                        seed,
                        chain_adrs.verified(),
                    )
                    .expect("base-16 WOTS digit");
                    tmp[index] = SlhBlock::from_slice(&endpoint).unwrap();
                }
                continue;
            }
            if count > 4 {
                let mut f5_w = [0u64; 8];
                let mut starts = [15u32; 8];
                let mut cur_rows = [[0u64; 8]; 4];
                for lane in 0..count {
                    f5_w[lane] = u32::from_le_bytes(((base + lane) as u32).to_be_bytes()) as u64;
                    starts[lane] = digits[base + lane] as u32;
                    let sw = pack_block_words(&sig[base + lane], n_words);
                    for w in 0..n_words {
                        cur_rows[w][lane] = sw[w];
                    }
                }
                for step in min_d..15u32 {
                    let mut state = qsag_asm::KeccakState8x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 8];
                    }
                    for lane in 0..count {
                        state.0[n_words][lane] = ch_aw[0];
                        state.0[n_words + 1][lane] = ch_aw[1];
                        state.0[n_words + 2][lane] = ch_aw[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(f5_w[lane], step);
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = cur_rows[w][lane];
                        }
                        state.0[end_word][lane] = 0x1F;
                        state.0[16][lane] = 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x8(&mut state);
                    for lane in 0..count {
                        let active = ct_ge_u32_mask64(step, starts[lane]);
                        for (w, cur_row) in cur_rows.iter_mut().enumerate().take(n_words) {
                            cur_row[lane] = (cur_row[lane] & !active) | (state.0[w][lane] & active);
                        }
                    }
                }
                for lane in 0..count {
                    let mut words = [0u64; 4];
                    for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                        *slot = cur_rows[w][lane];
                    }
                    tmp[base + lane] = unpack_words_to_block(&words, n);
                }
            } else {
                let mut f5_w = [0u64; 4];
                let mut starts = [15u32; 4];
                let mut cur_rows = [[0u64; 4]; 4];
                for lane in 0..count {
                    f5_w[lane] = u32::from_le_bytes(((base + lane) as u32).to_be_bytes()) as u64;
                    starts[lane] = digits[base + lane] as u32;
                    let sw = pack_block_words(&sig[base + lane], n_words);
                    for w in 0..n_words {
                        cur_rows[w][lane] = sw[w];
                    }
                }
                for step in min_d..15u32 {
                    let mut state = qsag_asm::KeccakState4x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 4];
                    }
                    for lane in 0..count {
                        state.0[n_words][lane] = ch_aw[0];
                        state.0[n_words + 1][lane] = ch_aw[1];
                        state.0[n_words + 2][lane] = ch_aw[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(f5_w[lane], step);
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = cur_rows[w][lane];
                        }
                        state.0[end_word][lane] = 0x1F;
                        state.0[16][lane] = 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x4(&mut state);
                    for lane in 0..count {
                        let active = ct_ge_u32_mask64(step, starts[lane]);
                        for (w, cur_row) in cur_rows.iter_mut().enumerate().take(n_words) {
                            cur_row[lane] = (cur_row[lane] & !active) | (state.0[w][lane] & active);
                        }
                    }
                }
                for lane in 0..count {
                    let mut words = [0u64; 4];
                    for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                        *slot = cur_rows[w][lane];
                    }
                    tmp[base + lane] = unpack_words_to_block(&words, n);
                }
            }
        }
    } else {
        for i in 0..ell {
            let di = digits[i] as u32;
            chain_adrs.f5 = i as u32;
            tmp[i] = fips205_chain(sig[i], di, 15 - di, pk_seed, chain_adrs);
        }
    }
    let mut wotspk_adrs = adrs.with_type_and_clear(Fips205AdrsType::WotsPk);
    wotspk_adrs.key_pair = adrs.key_pair;
    fips205_th(n, pk_seed, &wotspk_adrs, &tmp[..ell])
}

// ============================================================================
// XMSS Subtrees (§6) & FORS (§8)
// ============================================================================

/// Build bottom-up Merkle root and authentication path (`auth[0]` = height-1 leaf sibling,
/// `auth[height - 1]` = top child sibling) from precomputed leaves `leaves[0..2^height]`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
#[allow(clippy::needless_range_loop)]
pub fn build_fips205_merkle_from_leaves(
    n: usize,
    pk_seed: &[u8],
    base_adrs: Fips205Adrs,
    node_adrs_type: Fips205AdrsType,
    preserve_key_pair: bool,
    leaves: &[SlhBlock],
    height: usize,
    tree_index_offset: u32,
    local_idx: usize,
) -> (SlhBlock, Vec<SlhBlock>) {
    debug_assert_eq!(leaves.len(), 1usize << height);
    let mut cur = leaves.to_vec();
    let mut auth = Vec::with_capacity(height);
    let mut idx = local_idx;

    if matches!(n, 16 | 24 | 32) && pk_seed.len() == n {
        let n_words = n / 8;
        let pk_w = pack_seed_words(pk_seed, n_words);
        let mut proto = base_adrs.with_type_and_clear(node_adrs_type);
        if preserve_key_pair {
            proto.key_pair = base_adrs.key_pair;
        }
        let aw_base = adrs_to_le_words(&proto);
        let end_word = 3 * n_words + 4;

        for z in 1..=height {
            auth.push(cur[idx ^ 1]);
            let next_len = cur.len() / 2;
            let base_off = tree_index_offset >> z;
            let z_w3 = u32::from_le_bytes((z as u32).to_be_bytes()) as u64;
            let mut next = Vec::with_capacity(next_len);

            for base in (0..next_len).step_by(8) {
                let count = (next_len - base).min(8);
                if count > 4 {
                    let mut state = qsag_asm::KeccakState8x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 8];
                    }
                    for lane in 0..count {
                        let p = base + lane;
                        let left_w = pack_block_words(&cur[2 * p], n_words);
                        let right_w = pack_block_words(&cur[2 * p + 1], n_words);
                        state.0[n_words][lane] = aw_base[0];
                        state.0[n_words + 1][lane] = aw_base[1];
                        state.0[n_words + 2][lane] = aw_base[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(z_w3, base_off + p as u32);
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = left_w[w];
                            state.0[2 * n_words + 4 + w][lane] = right_w[w];
                        }
                        state.0[end_word][lane] ^= 0x1F;
                        state.0[16][lane] ^= 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x8(&mut state);
                    for lane in 0..count {
                        let mut words = [0u64; 4];
                        for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                            *slot = state.0[w][lane];
                        }
                        next.push(unpack_words_to_block(&words, n));
                    }
                } else {
                    let mut state = qsag_asm::KeccakState4x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 4];
                    }
                    for lane in 0..count {
                        let p = base + lane;
                        let left_w = pack_block_words(&cur[2 * p], n_words);
                        let right_w = pack_block_words(&cur[2 * p + 1], n_words);
                        state.0[n_words][lane] = aw_base[0];
                        state.0[n_words + 1][lane] = aw_base[1];
                        state.0[n_words + 2][lane] = aw_base[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(z_w3, base_off + p as u32);
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = left_w[w];
                            state.0[2 * n_words + 4 + w][lane] = right_w[w];
                        }
                        state.0[end_word][lane] ^= 0x1F;
                        state.0[16][lane] ^= 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x4(&mut state);
                    for lane in 0..count {
                        let mut words = [0u64; 4];
                        for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                            *slot = state.0[w][lane];
                        }
                        next.push(unpack_words_to_block(&words, n));
                    }
                }
            }
            cur = next;
            idx >>= 1;
        }
        return (cur[0], auth);
    }

    for z in 1..=height {
        auth.push(cur[idx ^ 1]);
        let next_len = cur.len() / 2;
        let base_off = tree_index_offset >> z;
        let mut next = Vec::with_capacity(next_len);
        for base in (0..next_len).step_by(4) {
            let count = (next_len - base).min(4);
            let mut preimages = [[0u8; 128]; 4];
            for (j, pre) in preimages.iter_mut().enumerate().take(count) {
                let p = base + j;
                let mut adrs = base_adrs.with_type_and_clear(node_adrs_type);
                if preserve_key_pair {
                    adrs.key_pair = base_adrs.key_pair;
                }
                adrs.f5 = z as u32;
                adrs.f6 = base_off + p as u32;
                pre[..n].copy_from_slice(pk_seed);
                pre[n..n + 32].copy_from_slice(&adrs.to_bytes());
                pre[n + 32..2 * n + 32].copy_from_slice(cur[2 * p].as_slice());
                pre[2 * n + 32..3 * n + 32].copy_from_slice(cur[2 * p + 1].as_slice());
            }
            let inputs = core::array::from_fn(|j| &preimages[j][..3 * n + 32]);
            let hashes = crate::sponge::keccak::shake256_4x_32(inputs)
                .unwrap_or_else(|| inputs.map(crate::sponge::keccak::shake256_32));
            for hash in hashes.iter().take(count) {
                let mut block = SlhBlock::zero(n);
                block.bytes[..n].copy_from_slice(&hash[..n]);
                next.push(block);
            }
        }
        cur = next;
        idx >>= 1;
    }
    (cur[0], auth)
}

/// Walk a bottom-up FIPS 205 authentication path (`xmss_pkFromSig` / `fors_pkFromSig`).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn walk_fips205_auth_path(
    n: usize,
    pk_seed: &[u8],
    base_adrs: Fips205Adrs,
    node_adrs_type: Fips205AdrsType,
    preserve_key_pair: bool,
    mut node: SlhBlock,
    mut global_leaf_idx: u32,
    auth: &[SlhBlock],
) -> SlhBlock {
    for (k, sib) in auth.iter().enumerate() {
        let z = (k + 1) as u32;
        let mut adrs = base_adrs.with_type_and_clear(node_adrs_type);
        if preserve_key_pair {
            adrs.key_pair = base_adrs.key_pair;
        }
        adrs.f5 = z;
        let parent_idx = global_leaf_idx >> 1;
        adrs.f6 = parent_idx;
        if (global_leaf_idx & 1) == 0 {
            node = fips205_h(n, pk_seed, &adrs, &node, sib);
        } else {
            node = fips205_h(n, pk_seed, &adrs, sib, &node);
        }
        global_leaf_idx = parent_idx;
    }
    node
}

/// NIST FIPS 205 Algorithm 9 `xmss_node(SK.seed, 0, h', PK.seed, ADRS)` for a full subtree.
pub fn xmss_subtree_root(
    params: &Fips205Params,
    sk_seed: &[u8],
    pk_seed: &[u8],
    base_adrs: Fips205Adrs,
) -> SlhBlock {
    let leaves = compute_xmss_subtree_leaves(params, sk_seed, pk_seed, base_adrs);
    let (root, _) = build_fips205_merkle_from_leaves(
        params.n,
        pk_seed,
        base_adrs,
        Fips205AdrsType::Tree,
        false,
        &leaves,
        params.hp,
        0,
        0,
    );
    root
}

/// NIST FIPS 205 §8 `base_2^b(md, a, k)` + `(idx_tree, idx_leaf)` digest splitter,
/// matching `Qsag.fipsSplitDigest` bit-for-bit across all 6 parameter sets.
pub fn split_digest_indices(params: &Fips205Params, digest: &[u8]) -> (Vec<u32>, u128, u32) {
    let ka_bytes = (params.k * params.a).div_ceil(8);
    let tree_bits = params.h - params.hp;
    let tree_bytes = tree_bits.div_ceil(8);
    let leaf_bytes = params.hp.div_ceil(8);

    let md = &digest[0..ka_bytes];
    let tmp_idx_tree = &digest[ka_bytes..ka_bytes + tree_bytes];
    let tmp_idx_leaf = &digest[ka_bytes + tree_bytes..ka_bytes + tree_bytes + leaf_bytes];

    // base_2^b(md, a, k) (MSB-first bit stream per FIPS 205 Algorithm 4)
    let mut fors_indices = Vec::with_capacity(params.k);
    let mut bits_in_buf = 0usize;
    let mut total: u64 = 0;
    let mut in_off = 0usize;
    let mask_a = (1u64 << params.a) - 1;
    for _ in 0..params.k {
        while bits_in_buf < params.a {
            total = (total << 8) | (md[in_off] as u64);
            in_off += 1;
            bits_in_buf += 8;
        }
        bits_in_buf -= params.a;
        let idx = ((total >> bits_in_buf) & mask_a) as u32;
        fors_indices.push(idx);
    }

    let mut tree_acc: u128 = 0;
    for &b in tmp_idx_tree {
        tree_acc = (tree_acc << 8) | (b as u128);
    }
    let tree_mask = if tree_bits == 0 {
        0u128
    } else {
        (1u128 << tree_bits) - 1
    };
    let idx_tree = tree_acc & tree_mask;

    let mut leaf_acc: u32 = 0;
    for &b in tmp_idx_leaf {
        leaf_acc = (leaf_acc << 8) | (b as u32);
    }
    let leaf_mask = (1u32 << params.hp) - 1;
    let idx_leaf = leaf_acc & leaf_mask;

    (fors_indices, idx_tree, idx_leaf)
}

/// NIST FIPS 205 Algorithm 16 `fors_sign` + Algorithm 17 `fors_pkFromSig` root computation.
#[allow(clippy::needless_range_loop)]
pub fn fors_sign_and_pk(
    params: &Fips205Params,
    fors_indices: &[u32],
    sk_seed: &[u8],
    pk_seed: &[u8],
    adrs: Fips205Adrs,
) -> (Vec<(SlhBlock, Vec<SlhBlock>)>, SlhBlock) {
    let n = params.n;
    let t_leaves = 1usize << params.a;
    let mut fors_trees = Vec::with_capacity(params.k);
    let mut roots = Vec::with_capacity(params.k);

    let mut sk_adrs = adrs.with_type_and_clear(Fips205AdrsType::ForsPrf);
    sk_adrs.key_pair = adrs.key_pair;

    let mut leaf_adrs = adrs.with_type_and_clear(Fips205AdrsType::ForsTree);
    leaf_adrs.key_pair = adrs.key_pair;

    if matches!(n, 16 | 24 | 32) && sk_seed.len() == n && pk_seed.len() == n {
        let n_words = n / 8;
        let pk_w = pack_seed_words(pk_seed, n_words);
        let mut sk_w = pack_seed_words(sk_seed, n_words);
        let sk_aw = adrs_to_le_words(&sk_adrs);
        let lf_aw = adrs_to_le_words(&leaf_adrs);
        let end_word = 2 * n_words + 4;

        for (i, &target_idx_u32) in fors_indices.iter().enumerate().take(params.k) {
            let idx_i = target_idx_u32 as usize;
            let tree_off = (i * t_leaves) as u32;
            let mut leaves = Vec::with_capacity(t_leaves);
            let mut rev_words = [0u64; 4];

            if t_leaves >= 8 {
                let mut prf_base = qsag_asm::KeccakState8x::default();
                let mut lf_base = qsag_asm::KeccakState8x::default();
                for w in 0..n_words {
                    prf_base.0[w] = [pk_w[w]; 8];
                    prf_base.0[n_words + 4 + w] = [sk_w[w]; 8];
                    lf_base.0[w] = [pk_w[w]; 8];
                }
                prf_base.0[n_words] = [sk_aw[0]; 8];
                prf_base.0[n_words + 1] = [sk_aw[1]; 8];
                prf_base.0[n_words + 2] = [sk_aw[2]; 8];
                prf_base.0[end_word] = [0x1F; 8];
                prf_base.0[16] = [1u64 << 63; 8];

                lf_base.0[n_words] = [lf_aw[0]; 8];
                lf_base.0[n_words + 1] = [lf_aw[1]; 8];
                lf_base.0[n_words + 2] = [lf_aw[2]; 8];
                lf_base.0[end_word] = [0x1F; 8];
                lf_base.0[16] = [1u64 << 63; 8];

                let mut state = qsag_asm::KeccakState8x::default();
                for u_base in (0..t_leaves).step_by(8) {
                    let mut g_w3 = [0u64; 8];
                    for (lane, slot) in g_w3.iter_mut().enumerate() {
                        let g_idx = tree_off + ((u_base + lane) as u32);
                        *slot = with_f6_in_w3(0, g_idx);
                    }
                    state = prf_base;
                    state.0[n_words + 3] = g_w3;
                    qsag_asm::keccak_f1600_x8(&mut state);

                    let mut sk_rows = [[0u64; 8]; 4];
                    for (w, row) in sk_rows.iter_mut().enumerate().take(n_words) {
                        *row = state.0[w];
                    }
                    for lane in 0..8 {
                        let sel = ct_eq_mask_u64(
                            u64::from((u_base + lane) as u32),
                            u64::from(target_idx_u32),
                        );
                        for (w, slot) in rev_words.iter_mut().enumerate().take(n_words) {
                            *slot |= sk_rows[w][lane] & sel;
                        }
                    }

                    state = lf_base;
                    state.0[n_words + 3] = g_w3;
                    for (w, row) in sk_rows.iter().enumerate().take(n_words) {
                        state.0[n_words + 4 + w] = *row;
                    }
                    qsag_asm::keccak_f1600_x8(&mut state);
                    qsag_asm::volatile_fill(&mut sk_rows, [0; 8]);

                    for lane in 0..8 {
                        let mut words = [0u64; 4];
                        for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                            *slot = state.0[w][lane];
                        }
                        leaves.push(unpack_words_to_block(&words, n));
                    }
                }
                qsag_asm::volatile_fill(&mut state.0, [0; 8]);
                qsag_asm::volatile_fill(&mut prf_base.0, [0; 8]);
            } else {
                for u_base in (0..t_leaves).step_by(4) {
                    let count = (t_leaves - u_base).min(4);
                    let mut g_w3 = [0u64; 4];
                    let mut state = qsag_asm::KeccakState4x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 4];
                    }
                    for lane in 0..count {
                        let g_idx = tree_off + ((u_base + lane) as u32);
                        g_w3[lane] = with_f6_in_w3(0, g_idx);
                        state.0[n_words][lane] = sk_aw[0];
                        state.0[n_words + 1][lane] = sk_aw[1];
                        state.0[n_words + 2][lane] = sk_aw[2];
                        state.0[n_words + 3][lane] = g_w3[lane];
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = sk_w[w];
                        }
                        state.0[end_word][lane] = 0x1F;
                        state.0[16][lane] = 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x4(&mut state);

                    let mut sk_rows = [[0u64; 4]; 4];
                    for (w, row) in sk_rows.iter_mut().enumerate().take(n_words) {
                        *row = state.0[w];
                    }
                    for lane in 0..count {
                        let sel = ct_eq_mask_u64(
                            u64::from((u_base + lane) as u32),
                            u64::from(target_idx_u32),
                        );
                        for (w, slot) in rev_words.iter_mut().enumerate().take(n_words) {
                            *slot |= sk_rows[w][lane] & sel;
                        }
                    }

                    state = qsag_asm::KeccakState4x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 4];
                    }
                    for lane in 0..count {
                        state.0[n_words][lane] = lf_aw[0];
                        state.0[n_words + 1][lane] = lf_aw[1];
                        state.0[n_words + 2][lane] = lf_aw[2];
                        state.0[n_words + 3][lane] = g_w3[lane];
                        for w in 0..n_words {
                            state.0[n_words + 4 + w][lane] = sk_rows[w][lane];
                        }
                        state.0[end_word][lane] = 0x1F;
                        state.0[16][lane] = 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x4(&mut state);
                    qsag_asm::volatile_fill(&mut sk_rows, [0; 4]);

                    for lane in 0..count {
                        let mut words = [0u64; 4];
                        for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                            *slot = state.0[w][lane];
                        }
                        leaves.push(unpack_words_to_block(&words, n));
                    }
                    qsag_asm::volatile_fill(&mut state.0, [0; 4]);
                }
            }

            let revealed_sk = unpack_words_to_block(&rev_words, n);
            qsag_asm::volatile_fill(&mut rev_words, 0);

            let (root_i, auth_i) = build_fips205_merkle_from_leaves(
                n,
                pk_seed,
                adrs,
                Fips205AdrsType::ForsTree,
                true,
                &leaves,
                params.a,
                tree_off,
                idx_i,
            );
            roots.push(root_i);
            fors_trees.push((revealed_sk, auth_i));
        }
        qsag_asm::volatile_fill(&mut sk_w, 0);

        let mut pk_adrs = adrs.with_type_and_clear(Fips205AdrsType::ForsRoots);
        pk_adrs.key_pair = adrs.key_pair;
        let fors_pk = fips205_th(n, pk_seed, &pk_adrs, &roots);
        return (fors_trees, fors_pk);
    }

    let mut i = 0;
    while i < params.k {
        let idx_i = fors_indices[i] as usize;
        let tree_off = (i * t_leaves) as u32;
        let mut leaves = Vec::with_capacity(t_leaves);
        let mut revealed_sk = SlhBlock::zero(n);
        for u in 0..t_leaves {
            let g_idx = tree_off + (u as u32);
            sk_adrs.f6 = g_idx;
            let mut sk_val = fips205_prf(n, pk_seed, sk_seed, &sk_adrs);
            leaf_adrs.f5 = 0;
            leaf_adrs.f6 = g_idx;
            leaves.push(fips205_f(n, pk_seed, &leaf_adrs, &sk_val));
            if u == idx_i {
                revealed_sk = sk_val;
            } else {
                sk_val.wipe();
            }
        }
        let (root_i, auth_i) = build_fips205_merkle_from_leaves(
            n,
            pk_seed,
            adrs,
            Fips205AdrsType::ForsTree,
            true,
            &leaves,
            params.a,
            tree_off,
            idx_i,
        );
        roots.push(root_i);
        fors_trees.push((revealed_sk, auth_i));
        i += 1;
    }

    let mut pk_adrs = adrs.with_type_and_clear(Fips205AdrsType::ForsRoots);
    pk_adrs.key_pair = adrs.key_pair;
    let fors_pk = fips205_th(n, pk_seed, &pk_adrs, &roots);
    (fors_trees, fors_pk)
}

/// NIST FIPS 205 Algorithm 17 `fors_pkFromSig(SIG_FORS, md, PK.seed, ADRS)`.
#[allow(clippy::needless_range_loop)]
pub fn fors_pk_from_sig(
    params: &Fips205Params,
    fors_trees: &[(SlhBlock, Vec<SlhBlock>)],
    fors_indices: &[u32],
    pk_seed: &[u8],
    adrs: Fips205Adrs,
) -> SlhBlock {
    let n = params.n;
    let t_leaves = (1usize << params.a) as u32;
    let mut leaf_adrs = adrs.with_type_and_clear(Fips205AdrsType::ForsTree);
    leaf_adrs.key_pair = adrs.key_pair;

    let mut roots = Vec::with_capacity(params.k);
    if matches!(n, 16 | 24 | 32)
        && pk_seed.len() == n
        && fors_trees.len() >= params.k
        && fors_indices.len() >= params.k
        && fors_trees[..params.k]
            .iter()
            .all(|(_, auth)| auth.len() == params.a)
    {
        let n_words = n / 8;
        let pk_w = pack_seed_words(pk_seed, n_words);
        let aw_base = adrs_to_le_words(&leaf_adrs);
        let f_end_word = 2 * n_words + 4;
        let h_end_word = 3 * n_words + 4;

        for base in (0..params.k).step_by(8) {
            let count = (params.k - base).min(8);
            if count > 4 {
                let mut cur_idx = [0u32; 8];
                let mut state = qsag_asm::KeccakState8x::default();
                for w in 0..n_words {
                    state.0[w] = [pk_w[w]; 8];
                }
                for lane in 0..count {
                    let t_idx = base + lane;
                    let g_idx = (t_idx as u32) * t_leaves + fors_indices[t_idx];
                    cur_idx[lane] = g_idx;
                    let sk_w = pack_block_words(&fors_trees[t_idx].0, n_words);
                    state.0[n_words][lane] = aw_base[0];
                    state.0[n_words + 1][lane] = aw_base[1];
                    state.0[n_words + 2][lane] = aw_base[2];
                    state.0[n_words + 3][lane] = with_f6_in_w3(0, g_idx);
                    for w in 0..n_words {
                        state.0[n_words + 4 + w][lane] = sk_w[w];
                    }
                    state.0[f_end_word][lane] = 0x1F;
                    state.0[16][lane] = 1u64 << 63;
                }
                qsag_asm::keccak_f1600_x8(&mut state);

                let mut cur_rows = [[0u64; 8]; 4];
                for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                    *row = state.0[w];
                }

                for level in 0..params.a {
                    let z_w3 = u32::from_le_bytes(((level + 1) as u32).to_be_bytes()) as u64;
                    state = qsag_asm::KeccakState8x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 8];
                    }
                    for lane in 0..count {
                        let t_idx = base + lane;
                        let sib_w = pack_block_words(&fors_trees[t_idx].1[level], n_words);
                        let parent_idx = cur_idx[lane] >> 1;
                        let is_right = (cur_idx[lane] & 1) == 1;
                        cur_idx[lane] = parent_idx;

                        state.0[n_words][lane] = aw_base[0];
                        state.0[n_words + 1][lane] = aw_base[1];
                        state.0[n_words + 2][lane] = aw_base[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(z_w3, parent_idx);
                        for w in 0..n_words {
                            let (lw, rw) = if is_right {
                                (sib_w[w], cur_rows[w][lane])
                            } else {
                                (cur_rows[w][lane], sib_w[w])
                            };
                            state.0[n_words + 4 + w][lane] = lw;
                            state.0[2 * n_words + 4 + w][lane] = rw;
                        }
                        state.0[h_end_word][lane] ^= 0x1F;
                        state.0[16][lane] ^= 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x8(&mut state);
                    for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                        *row = state.0[w];
                    }
                }

                for lane in 0..count {
                    let mut words = [0u64; 4];
                    for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                        *slot = cur_rows[w][lane];
                    }
                    roots.push(unpack_words_to_block(&words, n));
                }
            } else {
                let mut cur_idx = [0u32; 4];
                let mut state = qsag_asm::KeccakState4x::default();
                for w in 0..n_words {
                    state.0[w] = [pk_w[w]; 4];
                }
                for lane in 0..count {
                    let t_idx = base + lane;
                    let g_idx = (t_idx as u32) * t_leaves + fors_indices[t_idx];
                    cur_idx[lane] = g_idx;
                    let sk_w = pack_block_words(&fors_trees[t_idx].0, n_words);
                    state.0[n_words][lane] = aw_base[0];
                    state.0[n_words + 1][lane] = aw_base[1];
                    state.0[n_words + 2][lane] = aw_base[2];
                    state.0[n_words + 3][lane] = with_f6_in_w3(0, g_idx);
                    for w in 0..n_words {
                        state.0[n_words + 4 + w][lane] = sk_w[w];
                    }
                    state.0[f_end_word][lane] = 0x1F;
                    state.0[16][lane] = 1u64 << 63;
                }
                qsag_asm::keccak_f1600_x4(&mut state);

                let mut cur_rows = [[0u64; 4]; 4];
                for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                    *row = state.0[w];
                }

                for level in 0..params.a {
                    let z_w3 = u32::from_le_bytes(((level + 1) as u32).to_be_bytes()) as u64;
                    state = qsag_asm::KeccakState4x::default();
                    for w in 0..n_words {
                        state.0[w] = [pk_w[w]; 4];
                    }
                    for lane in 0..count {
                        let t_idx = base + lane;
                        let sib_w = pack_block_words(&fors_trees[t_idx].1[level], n_words);
                        let parent_idx = cur_idx[lane] >> 1;
                        let is_right = (cur_idx[lane] & 1) == 1;
                        cur_idx[lane] = parent_idx;

                        state.0[n_words][lane] = aw_base[0];
                        state.0[n_words + 1][lane] = aw_base[1];
                        state.0[n_words + 2][lane] = aw_base[2];
                        state.0[n_words + 3][lane] = with_f6_in_w3(z_w3, parent_idx);
                        for w in 0..n_words {
                            let (lw, rw) = if is_right {
                                (sib_w[w], cur_rows[w][lane])
                            } else {
                                (cur_rows[w][lane], sib_w[w])
                            };
                            state.0[n_words + 4 + w][lane] = lw;
                            state.0[2 * n_words + 4 + w][lane] = rw;
                        }
                        state.0[h_end_word][lane] ^= 0x1F;
                        state.0[16][lane] ^= 1u64 << 63;
                    }
                    qsag_asm::keccak_f1600_x4(&mut state);
                    for (w, row) in cur_rows.iter_mut().enumerate().take(n_words) {
                        *row = state.0[w];
                    }
                }

                for lane in 0..count {
                    let mut words = [0u64; 4];
                    for (w, slot) in words.iter_mut().enumerate().take(n_words) {
                        *slot = cur_rows[w][lane];
                    }
                    roots.push(unpack_words_to_block(&words, n));
                }
            }
        }
    } else {
        for i in 0..params.k {
            let (ref sk_val, ref auth_i) = fors_trees[i];
            let g_idx = (i as u32) * t_leaves + fors_indices[i];
            leaf_adrs.f5 = 0;
            leaf_adrs.f6 = g_idx;
            let leaf_node = fips205_f(n, pk_seed, &leaf_adrs, sk_val);
            let root_i = walk_fips205_auth_path(
                n,
                pk_seed,
                adrs,
                Fips205AdrsType::ForsTree,
                true,
                leaf_node,
                g_idx,
                auth_i,
            );
            roots.push(root_i);
        }
    }

    let mut pk_adrs = adrs.with_type_and_clear(Fips205AdrsType::ForsRoots);
    pk_adrs.key_pair = adrs.key_pair;
    fips205_th(n, pk_seed, &pk_adrs, &roots)
}

// ============================================================================
// Flat Byte Serialization & Keygen / Sign / Verify Entry Points (§9–§10)
// ============================================================================

/// Encode structured `SlhParsedSignature` into the flat `params.sig_bytes()` byte vector.
pub fn encode_slh_sig(params: &Fips205Params, sig: &SlhParsedSignature) -> Vec<u8> {
    let mut out = Vec::with_capacity(params.sig_bytes());
    out.extend_from_slice(sig.r_rand.as_slice());
    for (sk_val, auth) in &sig.fors_trees {
        out.extend_from_slice(sk_val.as_slice());
        for sib in auth {
            out.extend_from_slice(sib.as_slice());
        }
    }
    for (wots, auth) in &sig.ht_layers {
        for blk in wots {
            out.extend_from_slice(blk.as_slice());
        }
        for sib in auth {
            out.extend_from_slice(sib.as_slice());
        }
    }
    out
}

/// Decode flat signature bytes into `SlhParsedSignature` (panic-free, exact length check).
pub fn decode_slh_sig(
    params: &Fips205Params,
    raw: &[u8],
) -> Result<SlhParsedSignature, Fips205Error> {
    if !params.is_valid() {
        return Err(Fips205Error::InvalidParameterSet);
    }
    let expected = params.sig_bytes();
    if raw.len() != expected {
        return Err(Fips205Error::InvalidSignatureLength {
            expected,
            actual: raw.len(),
        });
    }
    let n = params.n;
    let ell = params.ell();
    let mut off = 0usize;
    let r_rand = SlhBlock::from_slice_checked(n, &raw[off..off + n])?;
    off += n;

    let mut fors_trees = Vec::with_capacity(params.k);
    for _ in 0..params.k {
        let sk_val = SlhBlock::from_slice_checked(n, &raw[off..off + n])?;
        off += n;
        let mut auth = Vec::with_capacity(params.a);
        for _ in 0..params.a {
            let sib = SlhBlock::from_slice_checked(n, &raw[off..off + n])?;
            off += n;
            auth.push(sib);
        }
        fors_trees.push((sk_val, auth));
    }

    let mut ht_layers = Vec::with_capacity(params.d);
    for _ in 0..params.d {
        let mut wots = Vec::with_capacity(ell);
        for _ in 0..ell {
            let blk = SlhBlock::from_slice_checked(n, &raw[off..off + n])?;
            off += n;
            wots.push(blk);
        }
        let mut auth = Vec::with_capacity(params.hp);
        for _ in 0..params.hp {
            let sib = SlhBlock::from_slice_checked(n, &raw[off..off + n])?;
            off += n;
            auth.push(sib);
        }
        ht_layers.push((wots, auth));
    }
    debug_assert_eq!(off, expected);
    Ok(SlhParsedSignature {
        r_rand,
        fors_trees,
        ht_layers,
    })
}

/// NIST FIPS 205 Algorithm 18 `slh_keygen_internal(SK.seed, SK.prf, PK.seed)`.
pub fn slh_keygen_internal(
    params: &Fips205Params,
    sk_seed: &[u8],
    sk_prf: &[u8],
    pk_seed: &[u8],
) -> Result<(SlhSecretKey, SlhPublicKey), Fips205Error> {
    if !params.is_valid() {
        return Err(Fips205Error::InvalidParameterSet);
    }
    let n = params.n;
    if sk_seed.len() != n || sk_prf.len() != n || pk_seed.len() != n {
        return Err(Fips205Error::InvalidSecretKeyBytes(
            sk_seed.len() + sk_prf.len() + pk_seed.len(),
        ));
    }
    let mut top_adrs = Fips205Adrs::ZERO;
    top_adrs.layer = (params.d - 1) as u32;
    let pk_root = xmss_subtree_root(params, sk_seed, pk_seed, top_adrs);
    let sk = SlhSecretKey::from_components(sk_seed, sk_prf, pk_seed, pk_root.as_slice())?;
    let pk = sk.public_key();
    Ok((sk, pk))
}

/// Deterministic seed-expanded keypair helper (`SHAKE256(seed, 3*n)` -> `(SK.seed, SK.prf, PK.seed)`).
pub fn slh_keygen_from_seed(
    params: &Fips205Params,
    master_seed: &[u8],
) -> Result<(SlhSecretKey, SlhPublicKey), Fips205Error> {
    if !params.is_valid() {
        return Err(Fips205Error::InvalidParameterSet);
    }
    let n = params.n;
    let mut raw = shake256_xof(3 * n, master_seed);
    let res = slh_keygen_internal(params, &raw[0..n], &raw[n..2 * n], &raw[2 * n..3 * n]);
    wipe_slice(&mut raw);
    res
}

/// NIST FIPS 205 Algorithm 19 `slh_sign_internal(M', SK, addrnd)`.
/// Pass `addrnd = None` for deterministic signing (`opt_rand = PK.seed`).
pub fn slh_sign_internal(
    params: &Fips205Params,
    m_prime: &[u8],
    sk: &SlhSecretKey,
    addrnd: Option<&[u8]>,
) -> Result<Vec<u8>, Fips205Error> {
    if !params.is_valid() || sk.n != params.n {
        return Err(Fips205Error::InvalidParameterSet);
    }
    let n = params.n;
    let opt_rand = match addrnd {
        Some(r) => {
            if r.len() != n {
                return Err(Fips205Error::InvalidNodeBytes {
                    expected: n,
                    actual: r.len(),
                });
            }
            r
        }
        None => sk.pk_seed_slice(),
    };
    let r_rand = fips205_prf_msg(n, sk.sk_prf_slice(), opt_rand, m_prime);
    let digest = fips205_h_msg(
        params.m,
        r_rand.as_slice(),
        sk.pk_seed_slice(),
        sk.pk_root_slice(),
        m_prime,
    );
    let (fors_indices, mut idx_tree, mut idx_leaf) = split_digest_indices(params, &digest);

    let mut fors_adrs = Fips205Adrs::ZERO;
    fors_adrs.set_tree_address(idx_tree);
    fors_adrs.adrs_type = Fips205AdrsType::ForsTree;
    fors_adrs.key_pair = idx_leaf;
    let (fors_trees, mut cur_msg) = fors_sign_and_pk(
        params,
        &fors_indices,
        sk.sk_seed_slice(),
        sk.pk_seed_slice(),
        fors_adrs,
    );

    let n_leaves = 1usize << params.hp;
    let leaf_mask = (n_leaves as u128) - 1;
    let mut ht_layers = Vec::with_capacity(params.d);
    for layer in 0..params.d {
        let mut layer_adrs = Fips205Adrs::ZERO;
        layer_adrs.layer = layer as u32;
        layer_adrs.set_tree_address(idx_tree);
        layer_adrs.key_pair = idx_leaf;
        let wots_sig = wots_sign(
            params,
            &cur_msg,
            sk.sk_seed_slice(),
            sk.pk_seed_slice(),
            layer_adrs,
        );

        let leaves =
            compute_xmss_subtree_leaves(params, sk.sk_seed_slice(), sk.pk_seed_slice(), layer_adrs);
        let (root_l, auth_l) = build_fips205_merkle_from_leaves(
            n,
            sk.pk_seed_slice(),
            layer_adrs,
            Fips205AdrsType::Tree,
            false,
            &leaves,
            params.hp,
            0,
            idx_leaf as usize,
        );
        ht_layers.push((wots_sig, auth_l));
        cur_msg = root_l;
        idx_leaf = (idx_tree & leaf_mask) as u32;
        idx_tree >>= params.hp;
    }

    Ok(encode_slh_sig(
        params,
        &SlhParsedSignature {
            r_rand,
            fors_trees,
            ht_layers,
        },
    ))
}

/// NIST FIPS 205 Algorithm 20 `slh_verify_internal(M', SIG, PK)`.
pub fn slh_verify_internal(
    params: &Fips205Params,
    m_prime: &[u8],
    sig_bytes: &[u8],
    pk: &SlhPublicKey,
) -> bool {
    if pk.n != params.n {
        return false;
    }
    let Ok(parsed) = decode_slh_sig(params, sig_bytes) else {
        return false;
    };
    let digest = fips205_h_msg(
        params.m,
        parsed.r_rand.as_slice(),
        pk.pk_seed_slice(),
        pk.pk_root_slice(),
        m_prime,
    );
    let (fors_indices, mut idx_tree, mut idx_leaf) = split_digest_indices(params, &digest);

    let mut fors_adrs = Fips205Adrs::ZERO;
    fors_adrs.set_tree_address(idx_tree);
    fors_adrs.adrs_type = Fips205AdrsType::ForsTree;
    fors_adrs.key_pair = idx_leaf;
    let mut node = fors_pk_from_sig(
        params,
        &parsed.fors_trees,
        &fors_indices,
        pk.pk_seed_slice(),
        fors_adrs,
    );

    let leaf_mask = (1u128 << params.hp) - 1;
    for (layer, (wots_sig, auth_l)) in parsed.ht_layers.iter().enumerate() {
        let mut layer_adrs = Fips205Adrs::ZERO;
        layer_adrs.layer = layer as u32;
        layer_adrs.set_tree_address(idx_tree);
        layer_adrs.key_pair = idx_leaf;
        let wots_pk = wots_pk_from_sig(params, wots_sig, &node, pk.pk_seed_slice(), layer_adrs);
        node = walk_fips205_auth_path(
            params.n,
            pk.pk_seed_slice(),
            layer_adrs,
            Fips205AdrsType::Tree,
            false,
            wots_pk,
            idx_leaf,
            auth_l,
        );
        idx_leaf = (idx_tree & leaf_mask) as u32;
        idx_tree >>= params.hp;
    }

    ct_eq_bytes(node.as_slice(), pk.pk_root_slice())
}

/// NIST FIPS 205 §9.2 / §10.2.1 Algorithm 22 `slh_sign(M, ctx, addrnd, SK)`
/// (pure SLH-DSA with `M' = 0x00 || |ctx| || ctx || M`, rejecting `|ctx| > 255`).
pub fn slh_sign(
    params: &Fips205Params,
    msg: &[u8],
    ctx: &[u8],
    sk: &SlhSecretKey,
    addrnd: Option<&[u8]>,
) -> Result<Vec<u8>, Fips205Error> {
    let m_prime = format_pure_m_prime(msg, ctx)?;
    slh_sign_internal(params, &m_prime, sk, addrnd)
}

/// NIST FIPS 205 §9.2 / §10.3 Algorithm 24 `slh_verify(M, SIG, ctx, PK)` (pure SLH-DSA).
pub fn slh_verify(
    params: &Fips205Params,
    msg: &[u8],
    sig_bytes: &[u8],
    ctx: &[u8],
    pk: &SlhPublicKey,
) -> bool {
    let Ok(m_prime) = format_pure_m_prime(msg, ctx) else {
        return false;
    };
    slh_verify_internal(params, &m_prime, sig_bytes, pk)
}

/// NIST FIPS 205 §9.3 / §10.2.2 Algorithm 23 `hash_slh_sign(M, ctx, PH, addrnd, SK)`
/// (Pre-Hash `HashSLH-DSA` with `M' = 0x01 || |ctx| || ctx || OID || PH(M)`, rejecting `|ctx| > 255`
/// and enforcing security-category compatibility between `params.n` and `ph` `[P1-08]`).
pub fn hash_slh_sign(
    params: &Fips205Params,
    ph: SlhPreHash,
    msg: &[u8],
    ctx: &[u8],
    sk: &SlhSecretKey,
    addrnd: Option<&[u8]>,
) -> Result<Vec<u8>, Fips205Error> {
    if !params.is_valid() {
        return Err(Fips205Error::InvalidParameterSet);
    }
    if !ph.is_allowed_for_security_n(params.n) {
        return Err(Fips205Error::PreHashCategoryMismatch {
            n: params.n,
            pre_hash: ph,
        });
    }
    let m_prime = format_prehash_m_prime(ph, msg, ctx)?;
    slh_sign_internal(params, &m_prime, sk, addrnd)
}

/// NIST FIPS 205 §9.3 / §10.3 Algorithm 25 `hash_slh_verify(M, SIG, ctx, PH, PK)` (`HashSLH-DSA`,
/// rejecting pre-hashes weaker than `params.n` per §9.3 `[P1-08]`).
pub fn hash_slh_verify(
    params: &Fips205Params,
    ph: SlhPreHash,
    msg: &[u8],
    sig_bytes: &[u8],
    ctx: &[u8],
    pk: &SlhPublicKey,
) -> bool {
    if !params.is_valid() || !ph.is_allowed_for_security_n(params.n) {
        return false;
    }
    let Ok(m_prime) = format_prehash_m_prime(ph, msg, ctx) else {
        return false;
    };
    slh_verify_internal(params, &m_prime, sig_bytes, pk)
}

// ============================================================================
// Sealed Cut-Boundary Distributed MPC Oracles (`[P0-08]`)
// ============================================================================

/// Non-forgeable typestate proof token witnessing that a batch BDOZ / SPDZ / RSS active-security
/// consistency check (`MacCheck` / commit-then-open share equality) succeeded **strictly before**
/// declassifying cut-boundary digests (`R`, FORS revealed leaf + sibling hashes, or WOTS+ chain nodes).
///
/// External callers **cannot** construct [`CutBoundaryMacToken`]: its constructor is `pub(crate)`
/// and invoked strictly inside `qsag-core`'s verified committed `MacCheck` / RSS share-equality gates.
#[must_use = "cut-boundary MAC verification token must be bound before opening"]
#[derive(Debug)]
pub struct CutBoundaryMacToken {
    _sealed: (),
}

impl CutBoundaryMacToken {
    /// Crate-private minting witness: ONLY minted by verified `commit_and_open_spdz_*` /
    /// RSS commit-before-open equality barriers inside `qsag-core` (`keccak_mpc.rs`, `poseidon2_mpc.rs`).
    /// Accepts no caller-controlled `bool` parameter (`[P0-08]`).
    #[inline]
    pub(crate) fn mint_verified() -> Self {
        Self { _sealed: () }
    }
}

pub(crate) mod sealed_mpc_oracles {
    pub trait Sealed {}
}

/// Authorization issued by the signature driver for the WOTS signing oracle.
pub struct OracleCallToken {
    _private: (),
}

/// FORS values, public tree leaves, and their verified cut-boundary witness.
pub type ForsMpcOutput = (Vec<SlhBlock>, Vec<Vec<SlhBlock>>, CutBoundaryMacToken);

/// Sealed distributed MPC cut-boundary oracle trait (`[P0-08]`):
/// - Sealed via `sealed_mpc_oracles::Sealed` so external crates cannot forge unverified oracles;
/// - `SK.seed` and `SK.prf` are **NEVER** exposed in cleartext;
/// - Every oracle method MUST execute a committed active-security `MacCheck` barrier *before*
///   opening cut-boundary outputs and return a [`CutBoundaryMacToken`] proof witness;
/// - WOTS+ evaluation is split into [`Self::eval_wots_pkgen_subtree_mpc`] (hardcoded `15` steps for
///   keygen) and [`Self::eval_wots_layer_sign_and_siblings_mpc`] (which computes base-16 + checksum
///   digits **internally** from `msg_to_sign`, making raw `target_steps = 0` step-0 SK-dumping
///   unrepresentable in the type system!).
pub trait SlhMpcOracles: sealed_mpc_oracles::Sealed {
    /// Bind the suite and public seed before the first secret-derived output.
    fn bind_key_params(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error>;

    /// Evaluate `R = PRF_msg([SK.prf], opt_rand, M')` in MPC, verify cut-boundary MACs BEFORE
    /// opening `R`, and return `(R, mac_token)`.
    fn eval_prf_msg_mpc(
        &mut self,
        n: usize,
        opt_rand: &[u8],
        m_prime: &[u8],
    ) -> Result<(SlhBlock, CutBoundaryMacToken), Fips205Error>;

    /// Evaluate FORS across `k` trees of height `a` (`k * 2^a` leaves total), verify cut-boundary
    /// MACs BEFORE opening, and return `(revealed_sks, fors_all_leaves, mac_token)`.
    fn eval_fors_trees_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        base_adrs: Fips205Adrs,
        fors_indices: &[u32],
    ) -> Result<ForsMpcOutput, Fips205Error>;

    /// Evaluate ONLY full-length step-`15` public WOTS+ chain endpoints across an entire XMSS
    /// subtree `(layer, tree)` (`(1 << hp) * ell` endpoints; zero intermediate steps `< 15` opened!).
    fn eval_wots_pkgen_subtree_mpc(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
        layer: u32,
        tree: u128,
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error>;

    /// Evaluate hypertree layer `(layer, tree)` for `active_kp` signing `msg_to_sign`:
    /// computes `try_wots_base16_digits_and_csum(msg_to_sign)` **internally** (never accepting
    /// caller-chosen step counts!), evaluates `active_kp` chains to `digits[ch]` and all sibling
    /// leaves `kp != active_kp` to step `15`, verifies cut-boundary MACs BEFORE opening, and returns
    /// `(opened_nodes_len_nleaves_times_ell, mac_token)`.
    #[expect(
        clippy::too_many_arguments,
        reason = "Preserve the existing explicit protocol interface for callers"
    )]
    fn eval_wots_layer_sign_and_siblings_mpc(
        &mut self,
        _authorization: crate::fips205::OracleCallToken,
        params: &Fips205Params,
        pk_seed: &[u8],
        layer: u32,
        tree: u128,
        active_kp: u32,
        msg_to_sign: &SlhBlock,
    ) -> Result<(Vec<SlhBlock>, CutBoundaryMacToken), Fips205Error>;
}

/// Distributed MPC `SLH-DSA` key generation (`slhKeygenMpc`): derives `PK = (PK.seed, PK.root)`
/// solely via step-15 WOTS+ chain endpoint openings (`SK.seed` & `SK.prf` never reconstructed!).
pub fn slh_keygen_mpc<O: SlhMpcOracles>(
    params: &Fips205Params,
    oracles: &mut O,
    pk_seed: &[u8],
) -> Result<SlhPublicKey, Fips205Error> {
    if !params.is_valid() {
        return Err(Fips205Error::InvalidParameterSet);
    }
    if pk_seed.len() != params.n {
        return Err(Fips205Error::InvalidPublicKeyBytes(pk_seed.len()));
    }
    oracles.bind_key_params(params, pk_seed)?;
    let top_layer = (params.d - 1) as u32;
    let n_leaves = 1usize << params.hp;
    let ell = params.ell();

    let (endpoints, _mac_tok) =
        oracles.eval_wots_pkgen_subtree_mpc(params, pk_seed, top_layer, 0)?;
    if endpoints.len() != n_leaves * ell {
        return Err(Fips205Error::MpcActiveTamperDetected);
    }

    let mut top_adrs = Fips205Adrs::ZERO;
    top_adrs.layer = top_layer;
    let mut leaves = Vec::with_capacity(n_leaves);
    for kp in 0..n_leaves {
        let mut wotspk_adrs = top_adrs.with_type_and_clear(Fips205AdrsType::WotsPk);
        wotspk_adrs.key_pair = kp as u32;
        let slice = &endpoints[kp * ell..(kp + 1) * ell];
        leaves.push(fips205_th(params.n, pk_seed, &wotspk_adrs, slice));
    }
    let (pk_root, _) = build_fips205_merkle_from_leaves(
        params.n,
        pk_seed,
        top_adrs,
        Fips205AdrsType::Tree,
        false,
        &leaves,
        params.hp,
        0,
        0,
    );
    SlhPublicKey::new(pk_seed, pk_root.as_slice())
}

/// Domain-separation prefix for Round-1 hedged randomizer coin-tossing commitments
/// (`SHAKE256("QSAG.R_COMMIT/v1" || sid || party_id_le8 || r_len_le8 || R_i || open_i)`),
/// binding every custodian's randomizer contribution `R_i` strictly prior to openings and
/// prior to any Round-3 signature-share release.
pub const R_COMMIT_DOMAIN_V1: &[u8] = b"QSAG.R_COMMIT/v1";

/// Compute the 32-byte length-framed commitment digest
/// `H("QSAG.R_COMMIT/v1" || sid || party_id_le8 || r_len_le8 || r_share || open_salt)`
/// binding party `party_id`'s hedged randomizer contribution `r_share` within session `sid`.
pub fn compute_hedged_r_commit_v1(
    sid: &[u8; 32],
    party_id: u64,
    r_share: &[u8],
    open_salt: &[u8; 32],
) -> [u8; 32] {
    let mut preimage =
        Vec::with_capacity(R_COMMIT_DOMAIN_V1.len() + 32 + 8 + 8 + r_share.len() + 32);
    preimage.extend_from_slice(R_COMMIT_DOMAIN_V1);
    preimage.extend_from_slice(sid);
    preimage.extend_from_slice(&party_id.to_le_bytes());
    preimage.extend_from_slice(&(r_share.len() as u64).to_le_bytes());
    preimage.extend_from_slice(r_share);
    preimage.extend_from_slice(open_salt);
    let raw = shake256_xof(32, &preimage);
    wipe_slice(&mut preimage);
    let mut out = [0u8; 32];
    out.copy_from_slice(&raw[..32]);
    out
}

/// Round-1 commitment published by `party_id` for hedged threshold randomness coin-tossing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HedgedRandomizerCommit {
    pub party_id: u64,
    pub commit: [u8; 32],
}

/// Round-2 opening published by `party_id` after all Round-1 commitments have been collected
/// and strictly before Round-3 message-dependent signature shares are opened.
#[derive(Clone, PartialEq, Eq)]
pub struct HedgedRandomizerOpen {
    pub party_id: u64,
    pub r_share: Vec<u8>,
    pub open_salt: [u8; 32],
}

impl fmt::Debug for HedgedRandomizerOpen {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HedgedRandomizerOpen")
            .field("party_id", &self.party_id)
            .field("r_share", &"[REDACTED]")
            .field("open_salt", &"[REDACTED]")
            .finish()
    }
}

impl Drop for HedgedRandomizerOpen {
    fn drop(&mut self) {
        wipe_slice(&mut self.r_share);
        wipe_bytes32(&mut self.open_salt);
    }
}

impl HedgedRandomizerOpen {
    /// Construct a matching `(HedgedRandomizerCommit, HedgedRandomizerOpen)` pair bound to `sid`.
    pub fn commit_and_open(
        sid: &[u8; 32],
        party_id: u64,
        r_share: Vec<u8>,
        open_salt: [u8; 32],
    ) -> (HedgedRandomizerCommit, Self) {
        let commit = compute_hedged_r_commit_v1(sid, party_id, &r_share, &open_salt);
        (
            HedgedRandomizerCommit { party_id, commit },
            Self {
                party_id,
                r_share,
                open_salt,
            },
        )
    }
}

/// Unforgeable witness that a hedged MPC randomizer `opt_rand = ⊕_i R_i` was derived from a
/// complete, duplicate-free `QSAG.R_COMMIT/v1` commit-then-open coin-tossing transcript prior to
/// Round-3 share release, eliminating post-Round-3 rushing selective-abort bias on `R`.
#[derive(Clone, PartialEq, Eq)]
pub struct CommittedHedgedRandomizer {
    sid: [u8; 32],
    opt_rand: Vec<u8>,
}

impl fmt::Debug for CommittedHedgedRandomizer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CommittedHedgedRandomizer")
            .field("sid", &self.sid)
            .field("len", &self.opt_rand.len())
            .finish()
    }
}

impl Drop for CommittedHedgedRandomizer {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.sid);
        wipe_slice(&mut self.opt_rand);
    }
}

impl CommittedHedgedRandomizer {
    /// Verify every custodian's Round-1 `QSAG.R_COMMIT/v1` commitment against its Round-2 opening
    /// in constant time across the duplicate-free `roster`, then XOR-combine `opt_rand = ⊕_i R_i`.
    pub fn from_coin_toss(
        sid: &[u8; 32],
        roster: &[u64],
        n_bytes: usize,
        commits: &[HedgedRandomizerCommit],
        opens: &[HedgedRandomizerOpen],
    ) -> Result<Self, Fips205Error> {
        if n_bytes != 16 && n_bytes != 24 && n_bytes != 32 {
            return Err(Fips205Error::InvalidNodeBytes {
                expected: 32,
                actual: n_bytes,
            });
        }
        if roster.is_empty() || commits.len() != roster.len() || opens.len() != roster.len() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        for i in 0..roster.len() {
            for j in (i + 1)..roster.len() {
                if roster[i] == roster[j]
                    || commits[i].party_id == commits[j].party_id
                    || opens[i].party_id == opens[j].party_id
                {
                    return Err(Fips205Error::MpcActiveTamperDetected);
                }
            }
        }
        let mut combined = vec![0u8; n_bytes];
        for &pid in roster {
            let commit_entry = match commits.iter().find(|c| c.party_id == pid) {
                Some(c) => c,
                None => {
                    wipe_slice(&mut combined);
                    return Err(Fips205Error::MpcActiveTamperDetected);
                }
            };
            let open_entry = match opens.iter().find(|o| o.party_id == pid) {
                Some(o) => o,
                None => {
                    wipe_slice(&mut combined);
                    return Err(Fips205Error::MpcActiveTamperDetected);
                }
            };
            if open_entry.r_share.len() != n_bytes {
                wipe_slice(&mut combined);
                return Err(Fips205Error::InvalidNodeBytes {
                    expected: n_bytes,
                    actual: open_entry.r_share.len(),
                });
            }
            let expected =
                compute_hedged_r_commit_v1(sid, pid, &open_entry.r_share, &open_entry.open_salt);
            if !ct_eq_bytes(&expected, &commit_entry.commit) {
                wipe_slice(&mut combined);
                return Err(Fips205Error::MpcActiveTamperDetected);
            }
            for (dst, src) in combined.iter_mut().zip(&open_entry.r_share).take(n_bytes) {
                *dst ^= *src;
            }
        }
        Ok(Self {
            sid: *sid,
            opt_rand: combined,
        })
    }

    #[inline]
    pub fn sid(&self) -> &[u8; 32] {
        &self.sid
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.opt_rand
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.opt_rand.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.opt_rand.is_empty()
    }
}

/// Distributed MPC `SLH-DSA` internal signing (`slhSignMpc`):
/// - Takes ONLY sealed `oracles: &mut O` and public `pk: &SlhPublicKey` (`0` `SlhSecretKey`!);
/// - Gates hedged randomness behind [`CommittedHedgedRandomizer`] (`QSAG.R_COMMIT/v1` coin-tossing)
///   so `R` is uniquely bound prior to Round-3 share openings;
/// - Requires `CutBoundaryMacToken` barriers strictly before every cut opening;
/// - Cross-checks `F(PK.seed, leaf_adrs_i, revealed_sks[i]) == fors_all_leaves[i][idx_i]` (`[P0-08]`);
/// - Runs `slh_verify_internal(params, m_prime, &sig, pk)` before returning `Ok(sig)` (`[P0-08]`)!
pub fn slh_sign_internal_mpc<O: SlhMpcOracles>(
    params: &Fips205Params,
    oracles: &mut O,
    m_prime: &[u8],
    pk: &SlhPublicKey,
    addrnd: Option<&CommittedHedgedRandomizer>,
) -> Result<Vec<u8>, Fips205Error> {
    if !params.is_valid() || pk.n != params.n {
        return Err(Fips205Error::InvalidParameterSet);
    }
    oracles.bind_key_params(params, pk.pk_seed_slice())?;
    let n = params.n;
    let ell = params.ell();
    let opt_rand = match addrnd {
        Some(r) => {
            if r.len() != n {
                return Err(Fips205Error::InvalidNodeBytes {
                    expected: n,
                    actual: r.len(),
                });
            }
            r.as_slice()
        }
        None => pk.pk_seed_slice(),
    };

    // 1. Evaluate R = PRF_msg([SK.prf], opt_rand, M') in MPC with mandatory MAC check before opening.
    let (r_rand, _prf_mac_tok) = oracles.eval_prf_msg_mpc(n, opt_rand, m_prime)?;
    if r_rand.len() != n {
        return Err(Fips205Error::MpcActiveTamperDetected);
    }
    let digest = fips205_h_msg(
        params.m,
        r_rand.as_slice(),
        pk.pk_seed_slice(),
        pk.pk_root_slice(),
        m_prime,
    );
    let (fors_indices, mut idx_tree, mut idx_leaf) = split_digest_indices(params, &digest);

    // 2. Evaluate FORS trees in batched 64-way MPC with mandatory MAC check before opening.
    let mut fors_adrs = Fips205Adrs::ZERO;
    fors_adrs.set_tree_address(idx_tree);
    fors_adrs.adrs_type = Fips205AdrsType::ForsTree;
    fors_adrs.key_pair = idx_leaf;
    let (revealed_sks, fors_all_leaves, _fors_mac_tok) =
        oracles.eval_fors_trees_mpc(params, pk.pk_seed_slice(), fors_adrs, &fors_indices)?;

    let t_leaves = 1usize << params.a;
    if revealed_sks.len() != params.k || fors_all_leaves.len() != params.k {
        return Err(Fips205Error::MpcActiveTamperDetected);
    }
    let mut fors_trees = Vec::with_capacity(params.k);
    let mut fors_roots = Vec::with_capacity(params.k);
    for i in 0..params.k {
        let idx_i = fors_indices[i] as usize;
        if fors_all_leaves[i].len() != t_leaves || idx_i >= t_leaves {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        let tree_off = (i * t_leaves) as u32;
        // Cross-check revealed FORS secret value against its public leaf hash ([P0-08]):
        let mut check_leaf_adrs = fors_adrs;
        check_leaf_adrs.f5 = 0;
        check_leaf_adrs.f6 = tree_off + (idx_i as u32);
        let expected_leaf = fips205_f(n, pk.pk_seed_slice(), &check_leaf_adrs, &revealed_sks[i]);
        if !ct_eq_bytes(
            expected_leaf.as_slice(),
            fors_all_leaves[i][idx_i].as_slice(),
        ) {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }

        let (root_i, auth_i) = build_fips205_merkle_from_leaves(
            n,
            pk.pk_seed_slice(),
            fors_adrs,
            Fips205AdrsType::ForsTree,
            true,
            &fors_all_leaves[i],
            params.a,
            tree_off,
            idx_i,
        );
        fors_roots.push(root_i);
        fors_trees.push((revealed_sks[i], auth_i));
    }
    let mut pk_adrs = fors_adrs.with_type_and_clear(Fips205AdrsType::ForsRoots);
    pk_adrs.key_pair = idx_leaf;
    let mut cur_msg = fips205_th(n, pk.pk_seed_slice(), &pk_adrs, &fors_roots);

    // 3. Evaluate hypertree layers 0..d via sealed `eval_wots_layer_sign_and_siblings_mpc`!
    let n_leaves = 1usize << params.hp;
    let leaf_mask = (n_leaves as u128) - 1;
    let mut ht_layers = Vec::with_capacity(params.d);

    for layer in 0..params.d {
        let mut layer_adrs = Fips205Adrs::ZERO;
        layer_adrs.layer = layer as u32;
        layer_adrs.set_tree_address(idx_tree);
        layer_adrs.key_pair = idx_leaf;

        let (opened_nodes, _wots_mac_tok) = oracles.eval_wots_layer_sign_and_siblings_mpc(
            OracleCallToken { _private: () },
            params,
            pk.pk_seed_slice(),
            layer as u32,
            idx_tree,
            idx_leaf,
            &cur_msg,
        )?;
        if opened_nodes.len() != n_leaves * ell || (idx_leaf as usize) >= n_leaves {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }

        let active_start = (idx_leaf as usize) * ell;
        let wots_sig = opened_nodes[active_start..active_start + ell].to_vec();

        let mut leaves = Vec::with_capacity(n_leaves);
        for kp in 0..n_leaves {
            let mut leaf_adrs = layer_adrs;
            leaf_adrs.key_pair = kp as u32;
            if kp as u32 == idx_leaf {
                leaves.push(wots_pk_from_sig(
                    params,
                    &wots_sig,
                    &cur_msg,
                    pk.pk_seed_slice(),
                    leaf_adrs,
                ));
            } else {
                let mut wotspk_adrs = leaf_adrs.with_type_and_clear(Fips205AdrsType::WotsPk);
                wotspk_adrs.key_pair = kp as u32;
                let ep_slice = &opened_nodes[kp * ell..(kp + 1) * ell];
                leaves.push(fips205_th(n, pk.pk_seed_slice(), &wotspk_adrs, ep_slice));
            }
        }
        let (root_l, auth_l) = build_fips205_merkle_from_leaves(
            n,
            pk.pk_seed_slice(),
            layer_adrs,
            Fips205AdrsType::Tree,
            false,
            &leaves,
            params.hp,
            0,
            idx_leaf as usize,
        );
        ht_layers.push((wots_sig, auth_l));
        cur_msg = root_l;
        idx_leaf = (idx_tree & leaf_mask) as u32;
        idx_tree >>= params.hp;
    }

    let sig_bytes = encode_slh_sig(
        params,
        &SlhParsedSignature {
            r_rand,
            fors_trees,
            ht_layers,
        },
    );
    // Mandatory post-MPC signature verification against `pk` BEFORE releasing to caller ([P0-08]):
    if !slh_verify_internal(params, m_prime, &sig_bytes, pk) {
        return Err(Fips205Error::MpcActiveTamperDetected);
    }
    Ok(sig_bytes)
}

/// Pure NIST FIPS 205 §9.2 distributed MPC `SLH-DSA` signing (`ctx` <= 255 bytes).
/// Hedged randomness (`Some(...)`) requires a verified [`CommittedHedgedRandomizer`] from
/// Round-1 `QSAG.R_COMMIT/v1` coin-tossing prior to Round-3 share release.
pub fn slh_sign_mpc<O: SlhMpcOracles>(
    params: &Fips205Params,
    oracles: &mut O,
    msg: &[u8],
    ctx: &[u8],
    pk: &SlhPublicKey,
    addrnd: Option<&CommittedHedgedRandomizer>,
) -> Result<Vec<u8>, Fips205Error> {
    let m_prime = format_pure_m_prime(msg, ctx)?;
    slh_sign_internal_mpc(params, oracles, &m_prime, pk, addrnd)
}

impl core::error::Error for Fips205Error {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_six_fips205_shake_param_sizes_and_spki() {
        let expected = [
            (Fips205Params::SLH_DSA_SHAKE_128S, 16, 32, 64, 50, 7_856),
            (Fips205Params::SLH_DSA_SHAKE_128F, 16, 32, 64, 50, 17_088),
            (Fips205Params::SLH_DSA_SHAKE_192S, 24, 48, 96, 66, 16_224),
            (Fips205Params::SLH_DSA_SHAKE_192F, 24, 48, 96, 66, 35_664),
            (Fips205Params::SLH_DSA_SHAKE_256S, 32, 64, 128, 82, 29_792),
            (Fips205Params::SLH_DSA_SHAKE_256F, 32, 64, 128, 82, 49_856),
        ];
        for (p, n, pk_len, sk_len, der_len, sig_len) in expected {
            assert!(p.is_valid(), "{} must be valid", p.name);
            assert_eq!(p.n, n);
            assert_eq!(p.pk_bytes(), pk_len);
            assert_eq!(p.sk_bytes(), sk_len);
            assert_eq!(p.sig_bytes(), sig_len);
            assert_eq!(Fips205Params::by_name(p.name), Some(p));

            let seed = [0x5Au8; 32];
            // Test SPKI DER roundtrip using synthetic n-byte root (instantaneous)
            let pk = SlhPublicKey::new(&seed[..n], &[0xA5u8; 32][..n]).unwrap();
            let der = pk.to_spki_der(&p).unwrap();
            assert_eq!(der.len(), der_len);
            let (dec_p, dec_pk) = SlhPublicKey::from_spki_der(&der).unwrap();
            assert_eq!(dec_p, p);
            assert_eq!(dec_pk, pk);
        }
        assert!(Fips205Params::SLH_DSA_SHAKE_COMPACT_TEST.is_valid());
        assert_eq!(Fips205Params::SLH_DSA_SHAKE_COMPACT_TEST.sig_bytes(), 1_392);
    }

    #[test]
    fn sha2_digests_match_known_answers_at_every_padding_boundary() {
        const LENS: [usize; 18] = [
            0, 1, 55, 56, 57, 63, 64, 65, 111, 112, 113, 119, 120, 127, 128, 129, 200, 1000,
        ];
        // First 8 bytes of SHA-256 and last 8 bytes of SHA-512 over the message prefix.
        const SHA256_HEAD: [u64; 18] = [
            0xe3b0_c442_98fc_1c14,
            0xef2d_127d_e37b_942b,
            0xeeff_6ea9_e4c9_06be,
            0xedff_44a9_9ed7_bcfa,
            0x0613_b1cd_633b_5ac9,
            0xd31a_ecb2_ae56_e7ea,
            0xef95_829a_7f95_f9bb,
            0x19ef_b4ee_3678_e72a,
            0x92b0_02c2_9b31_82bf,
            0x2b01_bd61_107b_9cd2,
            0x9c45_75ac_ef5a_af8c,
            0x10cc_4c74_0280_7680,
            0x39ad_4f1d_0478_9409,
            0xc3d7_aef8_2bd6_8713,
            0xb79f_baee_773f_06b1,
            0x0670_a3f9_abb6_6048,
            0x5dea_0ddb_d6a2_5b16,
            0x1714_ffef_fd0e_5e36,
        ];
        const SHA512_TAIL: [u64; 18] = [
            0xa538_327a_f927_da3e,
            0xf92f_fb9b_86d0_1e25,
            0x8841_d35a_4e03_7020,
            0x87f2_46b7_1d9c_a108,
            0xda94_33bd_f8a2_165b,
            0x3a8b_9505_4cf9_630b,
            0xb3c4_1b3b_b401_bbc5,
            0x5828_c5d0_6bc7_c11a,
            0x7a44_d0ac_8918_16b2,
            0xc87b_f4dc_3a8b_f40c,
            0xdbb6_03dd_02f4_1aac,
            0x15d8_9189_df55_898b,
            0xc2ea_ac37_d472_4177,
            0xd7f5_5eca_d1d6_cd1e,
            0xbe5e_cf91_fd1e_780b,
            0x2625_73f5_342d_7e90,
            0x76be_87f7_9bd1_0d2f,
            0x028e_4d65_b2b3_1fe2,
        ];
        let msg: Vec<u8> = (0..1000usize)
            .map(|i| (i as u8).wrapping_mul(0x9d) ^ 0x35)
            .collect();
        for (i, &len) in LENS.iter().enumerate() {
            let d256 = sha256_digest(&msg[..len]);
            let d512 = sha512_digest(&msg[..len]);
            let head = u64::from_be_bytes(d256[..8].try_into().unwrap());
            let tail = u64::from_be_bytes(d512[56..].try_into().unwrap());
            assert_eq!(head, SHA256_HEAD[i], "SHA-256 len={len}");
            assert_eq!(tail, SHA512_TAIL[i], "SHA-512 len={len}");
        }
    }

    #[test]
    fn lane_select_mask_is_u32_equality() {
        let edge = [0u32, 1, 2, 15, 16, 1 << 16, 1 << 31, u32::MAX - 1, u32::MAX];
        for &a in &edge {
            for &b in &edge {
                let want = if a == b { u64::MAX } else { 0 };
                assert_eq!(ct_eq_mask_u64(u64::from(a), u64::from(b)), want);
            }
        }
    }

    #[test]
    fn test_prehash_nist_vectors_and_hash_slh_dsa_domain_separation() {
        // FIPS 180-4 SHA-256("abc")
        assert_eq!(
            sha256_digest(b"abc"),
            [
                0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae,
                0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61,
                0xf2, 0x00, 0x15, 0xad
            ]
        );
        // FIPS 180-4 SHA-512("abc") first 8 bytes = ddaf35a193617aba
        let s512 = sha512_digest(b"abc");
        assert_eq!(
            &s512[..8],
            &[0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba]
        );
        // FIPS 202 SHA3-256("abc") first 8 bytes = 3a985da74fe225b2
        let s3_256 = SlhPreHash::Sha3_256.hash_message(b"abc");
        assert_eq!(
            &s3_256[..8],
            &[0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2]
        );

        let params = Fips205Params::SLH_DSA_SHAKE_COMPACT_TEST;
        let (sk, pk) = slh_keygen_from_seed(&params, b"hash-slh-seed").unwrap();
        let msg = b"domain-separated-message";
        let ctx = b"qsag-v1-ctx";

        for ph in [
            SlhPreHash::Sha256,
            SlhPreHash::Sha512,
            SlhPreHash::Sha3_256,
            SlhPreHash::Sha3_384,
            SlhPreHash::Sha3_512,
            SlhPreHash::Shake128,
            SlhPreHash::Shake256,
        ] {
            let sig_ph = hash_slh_sign(&params, ph, msg, ctx, &sk, None).unwrap();
            assert!(hash_slh_verify(&params, ph, msg, &sig_ph, ctx, &pk));
            // Pure verify MUST reject Pre-Hash signature (`0x00` vs `0x01` domain byte)
            assert!(!slh_verify(&params, msg, &sig_ph, ctx, &pk));
            // Wrong context MUST reject
            assert!(!hash_slh_verify(
                &params,
                ph,
                msg,
                &sig_ph,
                b"other-ctx",
                &pk
            ));
        }

        let overlong_ctx = [0x42u8; 256];
        assert_eq!(
            hash_slh_sign(&params, SlhPreHash::Sha256, msg, &overlong_ctx, &sk, None),
            Err(Fips205Error::ContextTooLong(256))
        );

        // FIPS 205 §9.3 pre-hash category downgrade refusal ([P1-08]):
        assert!(!SlhPreHash::Sha256.is_allowed_for_security_n(24));
        assert!(!SlhPreHash::Shake128.is_allowed_for_security_n(24));
        assert!(SlhPreHash::Sha3_384.is_allowed_for_security_n(24));
        assert!(!SlhPreHash::Sha3_384.is_allowed_for_security_n(32));
        assert!(SlhPreHash::Sha512.is_allowed_for_security_n(32));
        assert!(SlhPreHash::Shake256.is_allowed_for_security_n(32));
    }

    #[test]
    fn test_fips205_128f_192f_256f_roundtrip_and_exact_128f_kat() {
        let mut sk_seed = [0u8; 16];
        let mut sk_prf = [0u8; 16];
        let mut pk_seed = [0u8; 16];
        for i in 0..16 {
            sk_seed[i] = (i + 1) as u8;
            sk_prf[i] = (i + 0x21) as u8;
            pk_seed[i] = (i + 0x41) as u8;
        }
        let p128f = Fips205Params::SLH_DSA_SHAKE_128F;
        let (sk, pk) = slh_keygen_internal(&p128f, &sk_seed, &sk_prf, &pk_seed).unwrap();
        // Cross-verified bit-for-bit against OpenSSL 3.5.7 `SLH-DSA-SHAKE-128f` (`hexseed`):
        assert_eq!(
            pk.pk_root_slice(),
            &[
                0xbe, 0xa2, 0x2e, 0x4c, 0x51, 0xb2, 0xb7, 0xc6, 0x7d, 0xe2, 0x32, 0x12, 0x41, 0x09,
                0x27, 0xbd
            ]
        );
        let msg = b"qsag-openssl-test";
        let sig = slh_sign(&p128f, msg, &[], &sk, None).unwrap();
        assert_eq!(sig.len(), 17_088);
        assert!(slh_verify(&p128f, msg, &sig, &[], &pk));

        // Verify 192f (n=24, 35,664 B) and 256f (n=32, 49,856 B) sign/verify roundtrip + tamper refusal
        for params in [
            Fips205Params::SLH_DSA_SHAKE_192F,
            Fips205Params::SLH_DSA_SHAKE_256F,
        ] {
            let (sk_hi, pk_hi) = slh_keygen_from_seed(&params, b"qsag-high-sec-seed").unwrap();
            let sig_hi = slh_sign(&params, msg, b"ctx-192-256", &sk_hi, None).unwrap();
            assert_eq!(sig_hi.len(), params.sig_bytes());
            assert!(slh_verify(&params, msg, &sig_hi, b"ctx-192-256", &pk_hi));
            assert!(!slh_verify(&params, msg, &sig_hi, b"wrong-ctx", &pk_hi));
            let mut bad = sig_hi.clone();
            bad[params.sig_bytes() / 2] ^= 0x80;
            assert!(!slh_verify(&params, msg, &bad, b"ctx-192-256", &pk_hi));
        }

        // Flattened FORS address space must fit in 32-bit `f6` (`k * 2^a <= 2^32`).
        let mut overflow_fors = Fips205Params::SLH_DSA_SHAKE_128S;
        overflow_fors.a = 20;
        overflow_fors.k = 4097;
        overflow_fors.m = (4097 * 20usize).div_ceil(8)
            + (overflow_fors.h - overflow_fors.hp).div_ceil(8)
            + overflow_fors.hp.div_ceil(8);
        assert!(!overflow_fors.is_valid());
    }

    #[test]
    fn test_committed_hedged_randomizer_coin_toss_and_mpc_signing() {
        use crate::keccak_mpc::{RssSlhMpcCluster, run_dealerless_rss_dkg_2of3};
        use crate::preprocessing::PartyPrivateRng;

        let sid = [0x93u8; 32];
        let roster = [10u64, 20u64, 30u64];
        let r0 = vec![0x11u8; 16];
        let r1 = vec![0x22u8; 16];
        let r2 = vec![0x77u8; 16];
        let (c0, o0) = HedgedRandomizerOpen::commit_and_open(&sid, 10, r0.clone(), [0xA0; 32]);
        let (c1, o1) = HedgedRandomizerOpen::commit_and_open(&sid, 20, r1.clone(), [0xA1; 32]);
        let (c2, o2) = HedgedRandomizerOpen::commit_and_open(&sid, 30, r2.clone(), [0xA2; 32]);

        let committed = CommittedHedgedRandomizer::from_coin_toss(
            &sid,
            &roster,
            16,
            &[c0, c1, c2],
            &[o0.clone(), o1.clone(), o2.clone()],
        )
        .unwrap();
        assert_eq!(committed.sid(), &sid);
        assert_eq!(committed.as_slice(), &[0x44u8; 16]);

        // Rushing party attempting to alter `r_share` after observing honest openings MUST fail:
        let mut tampered_o2 = o2.clone();
        tampered_o2.r_share[0] ^= 0x01;
        assert_eq!(
            CommittedHedgedRandomizer::from_coin_toss(
                &sid,
                &roster,
                16,
                &[c0, c1, c2],
                &[o0.clone(), o1.clone(), tampered_o2],
            ),
            Err(Fips205Error::MpcActiveTamperDetected)
        );

        // Wrong session id, wrong salt, duplicate roster, or mismatched length MUST fail:
        let wrong_sid = [0x94u8; 32];
        assert_eq!(
            CommittedHedgedRandomizer::from_coin_toss(
                &wrong_sid,
                &roster,
                16,
                &[c0, c1, c2],
                &[o0.clone(), o1.clone(), o2.clone()],
            ),
            Err(Fips205Error::MpcActiveTamperDetected)
        );
        assert_eq!(
            CommittedHedgedRandomizer::from_coin_toss(
                &sid,
                &[10, 20, 20],
                16,
                &[c0, c1, c2],
                &[o0.clone(), o1.clone(), o2.clone()],
            ),
            Err(Fips205Error::MpcActiveTamperDetected)
        );
        assert_eq!(
            CommittedHedgedRandomizer::from_coin_toss(
                &sid,
                &roster,
                32,
                &[c0, c1, c2],
                &[o0, o1, o2],
            ),
            Err(Fips205Error::InvalidNodeBytes {
                expected: 32,
                actual: 16,
            })
        );

        // Full 3-custodian MPC hedged signing roundtrip against `SLH_DSA_SHAKE_COMPACT_TEST`:
        let params = Fips205Params::SLH_DSA_SHAKE_COMPACT_TEST;
        let mut rngs = [
            PartyPrivateRng::from_seed([0x31; 32], b"hedged-r-p0"),
            PartyPrivateRng::from_seed([0x32; 32], b"hedged-r-p1"),
            PartyPrivateRng::from_seed([0x33; 32], b"hedged-r-p2"),
        ];
        let (keys, raw_pk_seed) = run_dealerless_rss_dkg_2of3(sid, 16, &mut rngs).unwrap();
        let pk_seed = raw_pk_seed[..16].to_vec();

        let mut cluster = RssSlhMpcCluster::new(sid, keys, rngs).unwrap();
        let mpc_pk = slh_keygen_mpc(&params, &mut cluster, &pk_seed).unwrap();

        let msg = b"hedged-coin-toss-threshold-slh-dsa";
        let ctx = b"r-commit-v1";
        let mpc_sig_hedged =
            slh_sign_mpc(&params, &mut cluster, msg, ctx, &mpc_pk, Some(&committed)).unwrap();
        let mpc_sig_hedged_repeat =
            slh_sign_mpc(&params, &mut cluster, msg, ctx, &mpc_pk, Some(&committed)).unwrap();
        let mpc_sig_det = slh_sign_mpc(&params, &mut cluster, msg, ctx, &mpc_pk, None).unwrap();

        let (c0b, o0b) =
            HedgedRandomizerOpen::commit_and_open(&sid, 10, vec![0x99u8; 16], [0xB0; 32]);
        let (c1b, o1b) =
            HedgedRandomizerOpen::commit_and_open(&sid, 20, vec![0x22u8; 16], [0xB1; 32]);
        let (c2b, o2b) =
            HedgedRandomizerOpen::commit_and_open(&sid, 30, vec![0x77u8; 16], [0xB2; 32]);
        let committed_alt = CommittedHedgedRandomizer::from_coin_toss(
            &sid,
            &roster,
            16,
            &[c0b, c1b, c2b],
            &[o0b, o1b, o2b],
        )
        .unwrap();
        let mpc_sig_hedged_alt = slh_sign_mpc(
            &params,
            &mut cluster,
            msg,
            ctx,
            &mpc_pk,
            Some(&committed_alt),
        )
        .unwrap();

        assert_eq!(mpc_sig_hedged, mpc_sig_hedged_repeat);
        assert_ne!(mpc_sig_hedged, mpc_sig_det);
        assert_ne!(mpc_sig_hedged, mpc_sig_hedged_alt);
        assert!(slh_verify(&params, msg, &mpc_sig_hedged, ctx, &mpc_pk));
        assert!(slh_verify(&params, msg, &mpc_sig_hedged_alt, ctx, &mpc_pk));
    }

    #[test]
    #[allow(clippy::needless_range_loop)]
    fn batch_x8_prf_f_h_match_scalar_across_all_security_widths() {
        for n in [16usize, 24, 32] {
            let pk_seed: Vec<u8> = (0..n)
                .map(|i| (0x31u8).wrapping_add((i as u8) * 7))
                .collect();
            let sk_seed: Vec<u8> = (0..n)
                .map(|i| (0xA5u8).wrapping_add((i as u8) * 13))
                .collect();

            let adrs_prf: [Fips205Adrs; 8] = core::array::from_fn(|lane| {
                let mut a = Fips205Adrs::ZERO;
                a.layer = (lane as u32) % 7;
                a.set_tree_address(0x0123_4567_89AB_CDEFu128 + (lane as u128) * 19);
                a.adrs_type = Fips205AdrsType::WotsPrf;
                a.key_pair = 100 + lane as u32;
                a.f5 = lane as u32;
                a
            });
            let got_prf = shake256_prf_x8(n, &pk_seed, &sk_seed, &adrs_prf);
            for lane in 0..8 {
                let exp = fips205_prf(n, &pk_seed, &sk_seed, &adrs_prf[lane]);
                assert_eq!(got_prf[lane], exp, "PRF mismatch at n={n}, lane={lane}");
            }

            let adrs_f: [Fips205Adrs; 8] = core::array::from_fn(|lane| {
                let mut a = adrs_prf[lane].with_type_and_clear(Fips205AdrsType::WotsHash);
                a.key_pair = 100 + lane as u32;
                a.f5 = lane as u32;
                a.f6 = (lane as u32) * 2;
                a
            });
            let got_f = shake256_f_x8(n, &pk_seed, &adrs_f, &got_prf);
            for lane in 0..8 {
                let exp = fips205_f(n, &pk_seed, &adrs_f[lane], &got_prf[lane]);
                assert_eq!(got_f[lane], exp, "F mismatch at n={n}, lane={lane}");
            }

            let adrs_h: [Fips205Adrs; 8] = core::array::from_fn(|lane| {
                let mut a = adrs_prf[lane].with_type_and_clear(Fips205AdrsType::Tree);
                a.f5 = 1 + (lane as u32);
                a.f6 = 42 + (lane as u32);
                a
            });
            let got_h = shake256_h_x8(n, &pk_seed, &adrs_h, &got_prf, &got_f);
            for lane in 0..8 {
                let exp = fips205_h(n, &pk_seed, &adrs_h[lane], &got_prf[lane], &got_f[lane]);
                assert_eq!(got_h[lane], exp, "H mismatch at n={n}, lane={lane}");
            }
        }
    }
}
