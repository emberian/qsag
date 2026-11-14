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
        let ty = match qsag_verified::Fips205AdrsType::from_u32(self.adrs_type.to_u32()) {
            Some(ty) => ty,
            None => unreachable!(),
        };
        qsag_verified::encode_fips205_adrs(qsag_verified::Fips205Adrs::from_tree_u96(
            self.layer, self.tree, ty, self.key_pair, self.f5, self.f6,
        ))
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
    let ell1 = 2 * n;
    let mut digits = [0u8; 67];
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
    Ok((digits, ell1 + 3))
}

/// Compute the `2n + 3` base-16 WOTS+ digits (`2n` message nibbles + `3` big-endian checksum
/// nibbles of `csum << 4`) for an `n`-byte message block (`n` in `{16, 24, 32}`).
/// Clamps `msg_n` to `<= 32` bytes so untrusted slices can never panic in release builds (`[P1-08]`).
pub fn wots_base16_digits_and_csum(msg_n: &[u8]) -> ([u8; 67], usize) {
    let n = msg_n.len().min(32);
    debug_assert!(msg_n.len() == 16 || msg_n.len() == 24 || msg_n.len() == 32);
    let ell1 = 2 * n;
    let mut digits = [0u8; 67];
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

/// NIST FIPS 205 Algorithm 6 `wots_pkGen(SK.seed, PK.seed, ADRS)`.
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
    let mut i = 0;
    while i < ell {
        sk_adrs.f5 = i as u32;
        let mut sk_i = fips205_prf(n, pk_seed, sk_seed, &sk_adrs);
        chain_adrs.f5 = i as u32;
        tmp[i] = fips205_chain(sk_i, 0, 15, pk_seed, chain_adrs);
        sk_i.wipe();
        i += 1;
    }
    let mut wotspk_adrs = adrs.with_type_and_clear(Fips205AdrsType::WotsPk);
    wotspk_adrs.key_pair = adrs.key_pair;
    fips205_th(n, pk_seed, &wotspk_adrs, &tmp[..ell])
}

/// NIST FIPS 205 Algorithm 7 `wots_sign(M, SK.seed, PK.seed, ADRS)`.
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
    for i in 0..ell {
        let di = digits[i] as u32;
        chain_adrs.f5 = i as u32;
        tmp[i] = fips205_chain(sig[i], di, 15 - di, pk_seed, chain_adrs);
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
    let n_leaves = 1usize << params.hp;
    let mut leaves = Vec::with_capacity(n_leaves);
    for kp in 0..n_leaves {
        let mut leaf_adrs = base_adrs;
        leaf_adrs.key_pair = kp as u32;
        leaves.push(wots_pk_gen(params, sk_seed, pk_seed, leaf_adrs));
    }
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

        let mut leaves = Vec::with_capacity(n_leaves);
        for kp in 0..n_leaves {
            let mut leaf_adrs = layer_adrs;
            leaf_adrs.key_pair = kp as u32;
            if kp as u32 == idx_leaf {
                leaves.push(wots_pk_from_sig(
                    params,
                    &wots_sig,
                    &cur_msg,
                    sk.pk_seed_slice(),
                    leaf_adrs,
                ));
            } else {
                leaves.push(wots_pk_gen(
                    params,
                    sk.sk_seed_slice(),
                    sk.pk_seed_slice(),
                    leaf_adrs,
                ));
            }
        }
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
    fn bind_key_params(&mut self, params: &Fips205Params, pk_seed: &[u8]) -> Result<(), Fips205Error>;

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

/// Distributed MPC `SLH-DSA` internal signing (`slhSignMpc`):
/// - Takes ONLY sealed `oracles: &mut O` and public `pk: &SlhPublicKey` (`0` `SlhSecretKey`!);
/// - Requires `CutBoundaryMacToken` barriers strictly before every cut opening;
/// - Cross-checks `F(PK.seed, leaf_adrs_i, revealed_sks[i]) == fors_all_leaves[i][idx_i]` (`[P0-08]`);
/// - Runs `slh_verify_internal(params, m_prime, &sig, pk)` before returning `Ok(sig)` (`[P0-08]`)!
pub fn slh_sign_internal_mpc<O: SlhMpcOracles>(
    params: &Fips205Params,
    oracles: &mut O,
    m_prime: &[u8],
    pk: &SlhPublicKey,
    addrnd: Option<&[u8]>,
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
            r
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
pub fn slh_sign_mpc<O: SlhMpcOracles>(
    params: &Fips205Params,
    oracles: &mut O,
    msg: &[u8],
    ctx: &[u8],
    pk: &SlhPublicKey,
    addrnd: Option<&[u8]>,
) -> Result<Vec<u8>, Fips205Error> {
    let m_prime = format_pure_m_prime(msg, ctx)?;
    slh_sign_internal_mpc(params, oracles, &m_prime, pk, addrnd)
}

/// Pre-Hash NIST FIPS 205 §9.3 distributed MPC `HashSLH-DSA` signing (enforcing category strength).
pub fn hash_slh_sign_mpc<O: SlhMpcOracles>(
    params: &Fips205Params,
    ph: SlhPreHash,
    oracles: &mut O,
    msg: &[u8],
    ctx: &[u8],
    pk: &SlhPublicKey,
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
    }
}
