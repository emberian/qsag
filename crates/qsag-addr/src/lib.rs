#![no_std]
#![forbid(unsafe_code)]
//! Strict `Bech32m` (`0x2bc830a3`) post-quantum address codec, domain-separated `cSHAKE256` &
//! `Poseidon2` 256-bit script/pubkey commitments, and non-malleable `HybridPinnedEnvelope`.

extern crate alloc;

pub mod bech32m;

use alloc::string::String;
use alloc::vec::Vec;

use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::goldilocks::{GOLDILOCKS_PRIME, gl_is_canonical};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_accel::poseidon2::poseidon2_hash_framed_limbs4;

pub use bech32m::{
    AddrError, BECH32_LEGACY_CONST, BECH32M_CONST, HybridComponent, bech32_hrp_expand,
    bech32_polymod, bech32_polymod_step, bech32m_create_checksum, bech32m_decode_5bit,
    bech32m_encode_5bit, convert_bits,
};

/// Address commitment hash version tag (`witness_version` 5-bit leader in BIP-350 style).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum AddressVersion {
    /// Domain-separated 256-bit `cSHAKE256` script/pubkey commitment (`version = 1`).
    V1Cshake256 = 0x01,
    /// Domain-separated algebraic Width-12 Goldilocks `Poseidon2` 4-limb commitment (`version = 2`).
    V2Poseidon2 = 0x02,
}

impl AddressVersion {
    pub const fn from_u8(v: u8) -> Result<Self, AddrError> {
        match v {
            0x01 => Ok(Self::V1Cshake256),
            0x02 => Ok(Self::V2Poseidon2),
            other => Err(AddrError::UnsupportedVersion(other)),
        }
    }
}

/// Canonical cryptographic suite tags for PQ keys, HD wallets, FTS, and conjunctive hybrids.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum WitnessSuiteTag {
    MlDsa44 = 0x0101,
    MlDsa65 = 0x0102,
    MlDsa87 = 0x0103,
    SlhDsa128s = 0x0201,
    SlhDsa128f = 0x0202,
    SlhDsa192s = 0x0203,
    SlhDsa192f = 0x0204,
    SlhDsa256s = 0x0205,
    SlhDsa256f = 0x0206,
    FrontierSumFts = 0x0301,
    ParallelSeededFts = 0x0302,
    PiHdCommitInventory = 0x0401,
    PiHdLinearModule = 0x0402,
    HybridSecp256k1MlDsa44 = 0x0501,
    HybridEd25519MlDsa65 = 0x0502,
    PolicyPredicateScript = 0x0601,
}

impl WitnessSuiteTag {
    pub const fn from_u16(v: u16) -> Result<Self, AddrError> {
        match v {
            0x0101 => Ok(Self::MlDsa44),
            0x0102 => Ok(Self::MlDsa65),
            0x0103 => Ok(Self::MlDsa87),
            0x0201 => Ok(Self::SlhDsa128s),
            0x0202 => Ok(Self::SlhDsa128f),
            0x0203 => Ok(Self::SlhDsa192s),
            0x0204 => Ok(Self::SlhDsa192f),
            0x0205 => Ok(Self::SlhDsa256s),
            0x0206 => Ok(Self::SlhDsa256f),
            0x0301 => Ok(Self::FrontierSumFts),
            0x0302 => Ok(Self::ParallelSeededFts),
            0x0401 => Ok(Self::PiHdCommitInventory),
            0x0402 => Ok(Self::PiHdLinearModule),
            0x0501 => Ok(Self::HybridSecp256k1MlDsa44),
            0x0502 => Ok(Self::HybridEd25519MlDsa65),
            0x0601 => Ok(Self::PolicyPredicateScript),
            other => Err(AddrError::UnsupportedSuiteTag(other)),
        }
    }

    /// Canonical [`KeyIdentityKind`] mandated by this suite tag.
    pub const fn expected_identity_kind(self) -> KeyIdentityKind {
        match self {
            Self::HybridSecp256k1MlDsa44 | Self::HybridEd25519MlDsa65 => {
                KeyIdentityKind::HybridConjunctive
            }
            Self::PolicyPredicateScript => KeyIdentityKind::ScriptPredicate,
            Self::MlDsa44
            | Self::MlDsa65
            | Self::MlDsa87
            | Self::SlhDsa128s
            | Self::SlhDsa128f
            | Self::SlhDsa192s
            | Self::SlhDsa192f
            | Self::SlhDsa256s
            | Self::SlhDsa256f
            | Self::FrontierSumFts
            | Self::ParallelSeededFts
            | Self::PiHdCommitInventory
            | Self::PiHdLinearModule => KeyIdentityKind::SingleOrThreshold,
        }
    }

    /// Returns `Ok(())` iff `(self, kind)` is a valid pair, else
    /// [`AddrError::InconsistentSuiteIdentityKind`].
    pub const fn validate_identity_kind(self, kind: KeyIdentityKind) -> Result<(), AddrError> {
        if (self.expected_identity_kind() as u8) == (kind as u8) {
            Ok(())
        } else {
            Err(AddrError::InconsistentSuiteIdentityKind {
                suite_tag: self as u16,
                kind: kind as u8,
            })
        }
    }
}

/// Key/script identity kind (`SingleOrThreshold` preserves 100% single-vs-MPC indistinguishability!).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum KeyIdentityKind {
    SingleOrThreshold = 0x01,
    HybridConjunctive = 0x02,
    ScriptPredicate = 0x03,
}

impl KeyIdentityKind {
    pub const fn from_u8(v: u8) -> Result<Self, AddrError> {
        match v {
            0x01 => Ok(Self::SingleOrThreshold),
            0x02 => Ok(Self::HybridConjunctive),
            0x03 => Ok(Self::ScriptPredicate),
            other => Err(AddrError::UnsupportedIdentityKind(other)),
        }
    }
}

/// Canonical 35-byte (`version` witness symbol + 35-byte program = `1 + 56 = 57` 5-bit symbols ->
/// `67` chars total for 3-char HRP `"qsp"`, strictly `< 90` BIP-350 bound!) post-quantum address.
///
/// Wire layout:
/// - Leading 5-bit witness symbol: `version as u8` (`1` or `2`, `< 16` per BIP-350),
/// - 35-byte witness program (`convert_bits(..., 8, 5, true)`):
///   `suite_tag: u16_be (2 B) || identity_kind: u8 (1 B) || commitment_256: [u8; 32]`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct QsagAddress {
    pub hrp: String,
    pub version: AddressVersion,
    pub suite_tag: WitnessSuiteTag,
    pub kind: KeyIdentityKind,
    pub commitment_256: [u8; 32],
}

impl QsagAddress {
    /// Derive a domain-separated `V1Cshake256` address binding `(hrp, version, suite_tag, kind, pubkey_or_script)`
    /// inside the cryptographic 256-bit preimage (not merely in the 30-bit BCH checksum!).
    pub fn from_pubkey_cshake256(
        hrp: &str,
        suite_tag: WitnessSuiteTag,
        kind: KeyIdentityKind,
        pubkey_or_script: &[u8],
    ) -> Result<Self, AddrError> {
        suite_tag.validate_identity_kind(kind)?;
        let hrp_norm = normalize_hrp(hrp)?;
        let ver_byte = [AddressVersion::V1Cshake256 as u8];
        let suite_be = (suite_tag as u16).to_be_bytes();
        let kind_byte = [kind as u8];
        let commitment_256 = cshake256_framed_32(
            b"QSAG.ADDR.CSHAKE256.V1",
            &[
                hrp_norm.as_bytes(),
                &ver_byte,
                &suite_be,
                &kind_byte,
                pubkey_or_script,
            ],
        );
        Ok(Self {
            hrp: hrp_norm,
            version: AddressVersion::V1Cshake256,
            suite_tag,
            kind,
            commitment_256,
        })
    }

    /// Derive a domain-separated `V2Poseidon2` algebraic address whose `commitment_256` consists of
    /// 4 canonical little-endian Goldilocks limbs (`< p`) for native SNARK/Sumcheck verification.
    pub fn from_pubkey_poseidon2(
        hrp: &str,
        suite_tag: WitnessSuiteTag,
        kind: KeyIdentityKind,
        pubkey_or_script: &[u8],
    ) -> Result<Self, AddrError> {
        suite_tag.validate_identity_kind(kind)?;
        let hrp_norm = normalize_hrp(hrp)?;
        let ver_byte = [AddressVersion::V2Poseidon2 as u8];
        let suite_be = (suite_tag as u16).to_be_bytes();
        let kind_byte = [kind as u8];
        let limbs4 = poseidon2_hash_framed_limbs4(
            0x5153_4147_4144_5232, // "QSAGADR2"
            &[
                hrp_norm.as_bytes(),
                &ver_byte,
                &suite_be,
                &kind_byte,
                pubkey_or_script,
            ],
        );
        let mut commitment_256 = [0u8; 32];
        for (i, &limb) in limbs4.iter().enumerate() {
            debug_assert!(limb < GOLDILOCKS_PRIME);
            commitment_256[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
        }
        Ok(Self {
            hrp: hrp_norm,
            version: AddressVersion::V2Poseidon2,
            suite_tag,
            kind,
            commitment_256,
        })
    }

    /// Encode into strict `Bech32m` (`0x2bc830a3`).
    pub fn encode(&self) -> Result<String, AddrError> {
        self.suite_tag.validate_identity_kind(self.kind)?;
        let hrp_norm = normalize_hrp(&self.hrp)?;
        if hrp_norm != self.hrp {
            return Err(AddrError::EmptyOrInvalidHrp);
        }
        let mut prog = [0u8; 35];
        prog[0..2].copy_from_slice(&(self.suite_tag as u16).to_be_bytes());
        prog[2] = self.kind as u8;
        prog[3..35].copy_from_slice(&self.commitment_256);

        let prog5 = convert_bits(&prog, 8, 5, true)?;
        let mut data5 = Vec::with_capacity(1 + prog5.len());
        data5.push(self.version as u8);
        data5.extend_from_slice(&prog5);
        bech32m_encode_5bit(&self.hrp, &data5)
    }

    /// Strictly decode and validate a `Bech32m` post-quantum address, rejecting legacy BIP-173
    /// `Bech32`, non-zero padding bits, unknown tags, inconsistent `(suite, kind)`, and
    /// non-canonical Poseidon2 limbs!
    pub fn decode_for_hrp(encoded: &str, expected_hrp: &str) -> Result<Self, AddrError> {
        let address = Self::decode(encoded)?;
        if address.hrp != normalize_hrp(expected_hrp)? {
            return Err(AddrError::EmptyOrInvalidHrp);
        }
        Ok(address)
    }

    pub fn decode(encoded: &str) -> Result<Self, AddrError> {
        let (hrp, data5) = bech32m_decode_5bit(encoded)?;
        if data5.is_empty() {
            return Err(AddrError::InvalidPayloadLength);
        }
        let version = AddressVersion::from_u8(data5[0])?;
        let prog = convert_bits(&data5[1..], 5, 8, false)?;
        if prog.len() != 35 {
            return Err(AddrError::InvalidPayloadLength);
        }
        let suite_raw = u16::from_be_bytes([prog[0], prog[1]]);
        let suite_tag = WitnessSuiteTag::from_u16(suite_raw)?;
        let kind = KeyIdentityKind::from_u8(prog[2])?;
        suite_tag.validate_identity_kind(kind)?;
        let mut commitment_256 = [0u8; 32];
        commitment_256.copy_from_slice(&prog[3..35]);

        if version == AddressVersion::V2Poseidon2 {
            for i in 0..4 {
                let limb =
                    u64::from_le_bytes(commitment_256[i * 8..(i + 1) * 8].try_into().unwrap());
                if !gl_is_canonical(limb) {
                    return Err(AddrError::NonCanonicalPoseidonLimb);
                }
            }
        }

        Ok(Self {
            hrp,
            version,
            suite_tag,
            kind,
            commitment_256,
        })
    }
}

fn normalize_hrp(hrp: &str) -> Result<String, AddrError> {
    if hrp.is_empty() || hrp.len() > 16 {
        return Err(AddrError::EmptyOrInvalidHrp);
    }
    let mut lower = false;
    let mut upper = false;
    let mut out = String::with_capacity(hrp.len());
    for b in hrp.bytes() {
        if !(33..=126).contains(&b) {
            return Err(AddrError::EmptyOrInvalidHrp);
        }
        lower |= b.is_ascii_lowercase();
        upper |= b.is_ascii_uppercase();
        out.push(b.to_ascii_lowercase() as char);
    }
    if lower && upper {
        return Err(AddrError::MixedCase);
    }
    Ok(out)
}

// ============================================================================
// Non-Malleable Conjunctive Hybrid Pinning Envelope (`HybridPinnedEnvelope`)
// ============================================================================

/// Canonical domain prefix of both role-separated signing transcripts of a
/// [`HybridPinnedEnvelope`].
pub const HYBRID_PINNED_MAGIC: &[u8; 14] = b"QSAG.HYBRID.V2";

/// Canonical wire header magic for [`HybridPinnedEnvelope::to_bytes`] and
/// [`HybridPinnedEnvelope::from_bytes`].
pub const HYBRID_ENVELOPE_WIRE_MAGIC: &[u8; 18] = b"QSAG.HYBRID.ENV.V1";

/// Signature algorithm of one envelope component, with its exact wire encodings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum HybridComponentAlgorithm {
    /// secp256k1 ECDSA: 33-byte compressed SEC1 key, 64-byte compact `r || s` with low `s`.
    Secp256k1EcdsaCompact = 0x0001,
    /// Ed25519: 32-byte key, 64-byte `R || S` with canonical `S`.
    Ed25519 = 0x0002,
    /// ML-DSA-44: 1312-byte key, 2420-byte signature.
    MlDsa44 = 0x0101,
    /// ML-DSA-65: 1952-byte key, 3309-byte signature.
    MlDsa65 = 0x0102,
}

impl HybridComponentAlgorithm {
    pub const fn from_u16(v: u16) -> Result<Self, AddrError> {
        match v {
            0x0001 => Ok(Self::Secp256k1EcdsaCompact),
            0x0002 => Ok(Self::Ed25519),
            0x0101 => Ok(Self::MlDsa44),
            0x0102 => Ok(Self::MlDsa65),
            _ => Err(AddrError::HybridAlgorithmTagMismatch),
        }
    }

    pub const fn public_key_len(self) -> usize {
        match self {
            Self::Secp256k1EcdsaCompact => 33,
            Self::Ed25519 => 32,
            Self::MlDsa44 => 1312,
            Self::MlDsa65 => 1952,
        }
    }

    pub const fn signature_len(self) -> usize {
        match self {
            Self::Secp256k1EcdsaCompact | Self::Ed25519 => 64,
            Self::MlDsa44 => 2420,
            Self::MlDsa65 => 3309,
        }
    }
}

/// Which key signs a given transcript; the two roles never sign the same bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum HybridRole {
    Classical = 0x01,
    PostQuantum = 0x02,
}

/// The classical and post-quantum algorithms fixed by a hybrid [`WitnessSuiteTag`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HybridSuiteSpec {
    pub suite_tag: WitnessSuiteTag,
    pub classical: HybridComponentAlgorithm,
    pub pq: HybridComponentAlgorithm,
}

/// secp256k1 group order `n`, big-endian.
const SECP256K1_ORDER_BE: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
    0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B, 0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41,
];
/// `floor(n / 2)` for secp256k1, big-endian: the largest low-`s` value.
const SECP256K1_HALF_ORDER_BE: [u8; 32] = [
    0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x5D, 0x57, 0x6E, 0x73, 0x57, 0xA4, 0x50, 0x1D, 0xDF, 0xE9, 0x2F, 0x46, 0x68, 0x1B, 0x20, 0xA0,
];
/// Ed25519 group order `L`, big-endian.
const ED25519_ORDER_BE: [u8; 32] = [
    0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x14, 0xDE, 0xF9, 0xDE, 0xA2, 0xF7, 0x9C, 0xD6, 0x58, 0x12, 0x63, 0x1A, 0x5C, 0xF5, 0xD3, 0xED,
];

/// Big-endian `a < b` over public 32-byte integers.
fn be_lt(a: &[u8], b: &[u8; 32]) -> bool {
    a.len() == 32 && a < &b[..]
}

fn is_nonzero(a: &[u8]) -> bool {
    a.iter().any(|&b| b != 0)
}

impl HybridSuiteSpec {
    /// The algorithm pair for `suite_tag`, or [`AddrError::HybridUnsupportedSuite`] if the tag is
    /// not a conjunctive hybrid suite.
    pub const fn for_suite(suite_tag: WitnessSuiteTag) -> Result<Self, AddrError> {
        let (classical, pq) = match suite_tag {
            WitnessSuiteTag::HybridSecp256k1MlDsa44 => (
                HybridComponentAlgorithm::Secp256k1EcdsaCompact,
                HybridComponentAlgorithm::MlDsa44,
            ),
            WitnessSuiteTag::HybridEd25519MlDsa65 => (
                HybridComponentAlgorithm::Ed25519,
                HybridComponentAlgorithm::MlDsa65,
            ),
            other => return Err(AddrError::HybridUnsupportedSuite(other as u16)),
        };
        Ok(Self {
            suite_tag,
            classical,
            pq,
        })
    }

    /// Exact length and encoding checks for both public keys.
    pub fn validate_public_keys(&self, pk_classical: &[u8], pk_pq: &[u8]) -> Result<(), AddrError> {
        let classical_ok = pk_classical.len() == self.classical.public_key_len()
            && match self.classical {
                HybridComponentAlgorithm::Secp256k1EcdsaCompact => {
                    matches!(pk_classical[0], 0x02 | 0x03)
                }
                _ => true,
            };
        if !classical_ok {
            return Err(AddrError::HybridMalformedComponent(
                HybridComponent::ClassicalPublicKey,
            ));
        }
        if pk_pq.len() != self.pq.public_key_len() {
            return Err(AddrError::HybridMalformedComponent(
                HybridComponent::PqPublicKey,
            ));
        }
        Ok(())
    }

    /// Exact length checks for both signatures, plus the scalar-range checks that make the
    /// classical signature encoding unique: `0 < r < n` and `0 < s <= n/2` for compact ECDSA,
    /// `S < L` for Ed25519.
    pub fn validate_signatures(
        &self,
        sig_classical: &[u8],
        sig_pq: &[u8],
    ) -> Result<(), AddrError> {
        let classical_ok = sig_classical.len() == self.classical.signature_len()
            && match self.classical {
                HybridComponentAlgorithm::Secp256k1EcdsaCompact => {
                    let (r, s) = sig_classical.split_at(32);
                    is_nonzero(r)
                        && is_nonzero(s)
                        && be_lt(r, &SECP256K1_ORDER_BE)
                        && (be_lt(s, &SECP256K1_HALF_ORDER_BE) || s == SECP256K1_HALF_ORDER_BE)
                }
                HybridComponentAlgorithm::Ed25519 => {
                    let mut s_be = [0u8; 32];
                    for (dst, src) in s_be.iter_mut().zip(sig_classical[32..].iter().rev()) {
                        *dst = *src;
                    }
                    be_lt(&s_be, &ED25519_ORDER_BE)
                }
                _ => true,
            };
        if !classical_ok {
            return Err(AddrError::HybridMalformedComponent(
                HybridComponent::ClassicalSignature,
            ));
        }
        if sig_pq.len() != self.pq.signature_len() {
            return Err(AddrError::HybridMalformedComponent(
                HybridComponent::PqSignature,
            ));
        }
        Ok(())
    }
}

/// Non-malleable conjunctive hybrid signature envelope. Each key signs its own role-separated
/// transcript (see [`HybridPinnedEnvelope::signing_transcript`]) that pins the suite, both
/// algorithm tags, both public-key digests, and their joint identity commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
