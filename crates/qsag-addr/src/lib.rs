#![no_std]
#![forbid(unsafe_code)]
//! Strict `Bech32m` (`0x2bc830a3`) post-quantum address codec, domain-separated `cSHAKE256` &
//! `Poseidon2` 256-bit script/pubkey commitments, and non-malleable `HybridPinnedEnvelope`.

// The codec requires an allocator even with default features disabled; it never requires std.
extern crate alloc;

pub mod bech32m;

use alloc::string::String;
use alloc::vec::Vec;

use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::goldilocks::{GOLDILOCKS_PRIME, gl_is_canonical};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_accel::poseidon2::poseidon2_hash_framed_limbs4;
pub use qsag_verified::{
    CanonicalIntent128, HybridRoleTag, INTENT_V1_MAGIC, IntentAddressVersion, IntentIdentityKind,
    IntentSuiteTag, check_hybrid_domain_framing, decode_intent_128,
    derive_hybrid_transcript_digest, encode_intent_128,
};

pub use bech32m::{
    AddrError, BECH32_LEGACY_CONST, BECH32M_CONST, HybridComponent, bech32_hrp_expand,
    bech32_polymod, bech32_polymod_step, bech32m_create_checksum, bech32m_decode_5bit,
    bech32m_encode_5bit, convert_bits,
};

/// Address wire discriminator (`witness_version`, a BIP-350-style 5-bit leader).
/// Each value selects a commitment hash profile; it is independent of the framing
/// version of that hash's domain. V2 selects canonical hardened Poseidon2-12.
/// `QSAGADR2` is its stable domain discriminator, not a Poseidon round-constant version.
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
        validate_commitment(self.version, &self.commitment_256)?;
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
        normalize_hrp(&hrp)?;
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

        validate_commitment(version, &commitment_256)?;

        Ok(Self {
            hrp,
            version,
            suite_tag,
            kind,
            commitment_256,
        })
    }
}

fn validate_commitment(version: AddressVersion, commitment: &[u8; 32]) -> Result<(), AddrError> {
    if version == AddressVersion::V2Poseidon2 {
        for chunk in commitment.as_chunks::<8>().0 {
            let limb = u64::from_le_bytes(*chunk);
            if !gl_is_canonical(limb) {
                return Err(AddrError::NonCanonicalPoseidonLimb);
            }
        }
    }
    Ok(())
}

/// Address HRPs are capped at 16 characters so every address stays within BIP-350's 90.
fn normalize_hrp(hrp: &str) -> Result<String, AddrError> {
    bech32m::lowercase_hrp(hrp, 16)
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

impl HybridRole {
    /// Convert into the MIR-verified `qsag_verified::HybridRoleTag` domain separator.
    #[inline]
    pub const fn to_verified_tag(self) -> HybridRoleTag {
        match self {
            Self::Classical => HybridRoleTag::Classical,
            Self::PostQuantum => HybridRoleTag::PostQuantum,
        }
    }
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

    /// Check public-key lengths and the compressed SEC1 prefix. Curve membership,
    /// canonical point encodings, subgroup checks, and PQ decoding belong to the
    /// algorithm-specific verifier callbacks.
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
pub struct HybridPinnedEnvelope {
    pub suite_tag: WitnessSuiteTag,
    pub classical_algorithm: HybridComponentAlgorithm,
    pub pq_algorithm: HybridComponentAlgorithm,
    pub id_commit: [u8; 32],
    pub pk_classical_digest: [u8; 32],
    pub pk_pq_digest: [u8; 32],
    pub pk_classical: Vec<u8>,
    pub pk_pq: Vec<u8>,
    pub sig_classical: Vec<u8>,
    pub sig_pq: Vec<u8>,
}

impl HybridPinnedEnvelope {
    fn hash_pk(
        customization: &[u8],
        spec: &HybridSuiteSpec,
        alg: HybridComponentAlgorithm,
        pk: &[u8],
    ) -> [u8; 32] {
        let suite = (spec.suite_tag as u16).to_be_bytes();
        let alg = (alg as u16).to_be_bytes();
        cshake256_framed_32(customization, &[&suite, &alg, pk])
    }

    /// Domain-separated classical public-key digest (binds suite and algorithm tag).
    pub fn hash_classical_pk(spec: &HybridSuiteSpec, pk_classical: &[u8]) -> [u8; 32] {
        Self::hash_pk(
            b"QSAG.HYBRID.PK_CLASSICAL.V2",
            spec,
            spec.classical,
            pk_classical,
        )
    }

    /// Domain-separated post-quantum public-key digest (binds suite and algorithm tag).
    pub fn hash_pq_pk(spec: &HybridSuiteSpec, pk_pq: &[u8]) -> [u8; 32] {
        Self::hash_pk(b"QSAG.HYBRID.PK_PQ.V2", spec, spec.pq, pk_pq)
    }

    /// Conjunctive identity commitment pinning both key digests under the suite's algorithm pair.
    pub fn compute_id_commit(
        spec: &HybridSuiteSpec,
        pk_classical_digest: &[u8; 32],
        pk_pq_digest: &[u8; 32],
    ) -> [u8; 32] {
        let suite = (spec.suite_tag as u16).to_be_bytes();
        let classical = (spec.classical as u16).to_be_bytes();
        let pq = (spec.pq as u16).to_be_bytes();
        cshake256_framed_32(
            b"QSAG.HYBRID.ID_COMMIT.V2",
            &[&suite, &classical, &pq, pk_classical_digest, pk_pq_digest],
        )
    }

    /// The exact bytes signed by the key in `role`:
    ///
    /// `"QSAG.HYBRID.V2" || role (1) || suite (2, BE) || classical alg (2, BE) || pq alg (2, BE)
    /// || id_commit (32) || pk_classical_digest (32) || pk_pq_digest (32) || len(msg) (8, BE) || msg`
    ///
    /// The role byte makes the two transcripts distinct, so neither signature can stand in for
    /// the other and neither is valid outside this envelope format.
    pub fn signing_transcript(
        role: HybridRole,
        spec: &HybridSuiteSpec,
        id_commit: &[u8; 32],
        pk_classical_digest: &[u8; 32],
        pk_pq_digest: &[u8; 32],
        msg: &[u8],
    ) -> Vec<u8> {
        let mut out = Vec::with_capacity(HYBRID_PINNED_MAGIC.len() + 7 + 96 + 8 + msg.len());
        out.extend_from_slice(HYBRID_PINNED_MAGIC);
        out.push(role as u8);
        out.extend_from_slice(&(spec.suite_tag as u16).to_be_bytes());
        out.extend_from_slice(&(spec.classical as u16).to_be_bytes());
        out.extend_from_slice(&(spec.pq as u16).to_be_bytes());
        out.extend_from_slice(id_commit);
        out.extend_from_slice(pk_classical_digest);
        out.extend_from_slice(pk_pq_digest);
        out.extend_from_slice(&(msg.len() as u64).to_be_bytes());
        out.extend_from_slice(msg);
        out
    }

    /// Assemble a signed envelope using caller-supplied classical and PQ signers.
    ///
    /// The suite and both public keys are validated before either signer runs, and both
    /// returned signatures are validated before the envelope is returned.
    pub fn sign_with<FC, FP>(
        suite_tag: WitnessSuiteTag,
        pk_classical: Vec<u8>,
        pk_pq: Vec<u8>,
        msg: &[u8],
        sign_classical: FC,
        sign_pq: FP,
    ) -> Result<Self, AddrError>
    where
        FC: FnOnce(&[u8]) -> Vec<u8>,
        FP: FnOnce(&[u8]) -> Vec<u8>,
    {
        let spec = HybridSuiteSpec::for_suite(suite_tag)?;
        spec.validate_public_keys(&pk_classical, &pk_pq)?;
        let pk_classical_digest = Self::hash_classical_pk(&spec, &pk_classical);
        let pk_pq_digest = Self::hash_pq_pk(&spec, &pk_pq);
        let id_commit = Self::compute_id_commit(&spec, &pk_classical_digest, &pk_pq_digest);
        let transcript = |role| {
            Self::signing_transcript(
                role,
                &spec,
                &id_commit,
                &pk_classical_digest,
                &pk_pq_digest,
                msg,
            )
        };
        let sig_classical = sign_classical(&transcript(HybridRole::Classical));
        let sig_pq = sign_pq(&transcript(HybridRole::PostQuantum));
        spec.validate_signatures(&sig_classical, &sig_pq)?;
        Ok(Self {
            suite_tag,
            classical_algorithm: spec.classical,
            pq_algorithm: spec.pq,
            id_commit,
            pk_classical_digest,
            pk_pq_digest,
            pk_classical,
            pk_pq,
            sig_classical,
            sig_pq,
        })
    }

    /// Derive the corresponding conjunctive `QsagAddress` (`KeyIdentityKind::HybridConjunctive`).
    pub fn to_address(&self, hrp: &str, version: AddressVersion) -> Result<QsagAddress, AddrError> {
        match version {
            AddressVersion::V1Cshake256 => QsagAddress::from_pubkey_cshake256(
                hrp,
                self.suite_tag,
                KeyIdentityKind::HybridConjunctive,
                &self.id_commit,
            ),
            AddressVersion::V2Poseidon2 => QsagAddress::from_pubkey_poseidon2(
                hrp,
                self.suite_tag,
                KeyIdentityKind::HybridConjunctive,
                &self.id_commit,
            ),
        }
    }

    /// Every check that needs no signature verification, in this order:
    ///
    /// 1. the suite tag names a hybrid pair, and both algorithm tags are that pair;
    /// 2. both public keys have their exact length and the SEC1 prefix is valid;
    /// 3. both signatures have their exact length and canonical scalar ranges;
    /// 4. both carried digests are the digests of the carried keys, the carried `id_commit` is
    ///    their commitment, and it equals `expected_id_commit`.
    pub fn validate_structure(
        &self,
        expected_id_commit: &[u8; 32],
    ) -> Result<HybridSuiteSpec, AddrError> {
        let spec = HybridSuiteSpec::for_suite(self.suite_tag)?;
        if self.classical_algorithm != spec.classical || self.pq_algorithm != spec.pq {
            return Err(AddrError::HybridAlgorithmTagMismatch);
        }
        spec.validate_public_keys(&self.pk_classical, &self.pk_pq)?;
        spec.validate_signatures(&self.sig_classical, &self.sig_pq)?;
        let classical_digest = Self::hash_classical_pk(&spec, &self.pk_classical);
        let pq_digest = Self::hash_pq_pk(&spec, &self.pk_pq);
        let id_commit = Self::compute_id_commit(&spec, &classical_digest, &pq_digest);
        let commitments_ok = ct_eq_bytes(&classical_digest, &self.pk_classical_digest)
            & ct_eq_bytes(&pq_digest, &self.pk_pq_digest)
            & ct_eq_bytes(&id_commit, &self.id_commit)
            & ct_eq_bytes(&id_commit, expected_id_commit)
            & check_hybrid_domain_framing(
                HYBRID_PINNED_MAGIC,
                HybridRole::Classical as u8,
                HybridRoleTag::Classical,
                self.suite_tag as u16,
                expected_id_commit,
                &self.id_commit,
            )
            & check_hybrid_domain_framing(
                HYBRID_PINNED_MAGIC,
                HybridRole::PostQuantum as u8,
                HybridRoleTag::PostQuantum,
                self.suite_tag as u16,
                expected_id_commit,
                &self.id_commit,
            );
        if !commitments_ok {
            return Err(AddrError::HybridCommitmentMismatch);
        }
        Ok(spec)
    }

    /// Derive the role-separated 32-byte `SHAKE256` signing transcript digest via the
    /// MIR-verified `qsag_verified::derive_hybrid_transcript_digest` kernel after checking
    /// `check_hybrid_domain_framing`.
    pub fn signing_transcript_digest(
        &self,
        role: HybridRole,
        msg: &[u8],
    ) -> Result<[u8; 32], AddrError> {
        self.validate_structure(&self.id_commit)?;
        if !check_hybrid_domain_framing(
            HYBRID_PINNED_MAGIC,
            role as u8,
            role.to_verified_tag(),
            self.suite_tag as u16,
            &self.id_commit,
            &self.id_commit,
        ) {
            return Err(AddrError::HybridCommitmentMismatch);
        }
        derive_hybrid_transcript_digest(
            role.to_verified_tag(),
            self.suite_tag as u16,
            &self.id_commit,
            &self.pk_classical_digest,
            &self.pk_pq_digest,
            msg,
        )
        .ok_or(AddrError::HybridUnsupportedSuite(self.suite_tag as u16))
    }

    /// Conjunctive verification. [`Self::validate_structure`] must pass before either callback
    /// is invoked; then `verify_classical(pk_classical, classical transcript, sig_classical)`
    /// and `verify_pq(pk_pq, post-quantum transcript, sig_pq)` must both accept.
    pub fn verify_with<VC, VP>(
        &self,
        expected_id_commit: &[u8; 32],
        msg: &[u8],
        verify_classical: VC,
        verify_pq: VP,
    ) -> Result<(), AddrError>
    where
        VC: FnOnce(&[u8], &[u8], &[u8]) -> bool,
        VP: FnOnce(&[u8], &[u8], &[u8]) -> bool,
    {
        let spec = self.validate_structure(expected_id_commit)?;
        self.run_verifiers(&spec, msg, verify_classical, verify_pq)
    }

    /// Run both verifier callbacks over their role-separated transcripts. Callers must have
    /// obtained `spec` from [`Self::validate_structure`] on this envelope. The post-quantum
    /// verifier is not consulted once the classical one has rejected.
    fn run_verifiers<VC, VP>(
        &self,
        spec: &HybridSuiteSpec,
        msg: &[u8],
        verify_classical: VC,
        verify_pq: VP,
    ) -> Result<(), AddrError>
    where
        VC: FnOnce(&[u8], &[u8], &[u8]) -> bool,
        VP: FnOnce(&[u8], &[u8], &[u8]) -> bool,
    {
        let verify_transcript_framing = |role: HybridRole, transcript: &[u8]| -> bool {
            let Some(magic14) = transcript
                .get(..14)
                .and_then(|s| <[u8; 14]>::try_from(s).ok())
            else {
                return false;
            };
            let Some(&wire_role) = transcript.get(14) else {
                return false;
            };
            let Some(wire_id) = transcript
                .get(21..53)
                .and_then(|s| <[u8; 32]>::try_from(s).ok())
            else {
                return false;
            };
            check_hybrid_domain_framing(
                &magic14,
                wire_role,
                role.to_verified_tag(),
                spec.suite_tag as u16,
                &self.id_commit,
                &wire_id,
            ) && derive_hybrid_transcript_digest(
                role.to_verified_tag(),
                spec.suite_tag as u16,
                &self.id_commit,
                &self.pk_classical_digest,
                &self.pk_pq_digest,
                msg,
            )
            .is_some_and(|d| ct_eq_bytes(&d, &qsag_verified::shake256_32(transcript)))
        };
        let classical_transcript = Self::signing_transcript(
            HybridRole::Classical,
            spec,
            &self.id_commit,
            &self.pk_classical_digest,
            &self.pk_pq_digest,
            msg,
        );
        if !verify_transcript_framing(HybridRole::Classical, &classical_transcript)
            || !verify_classical(
                &self.pk_classical,
                &classical_transcript,
                &self.sig_classical,
            )
        {
            return Err(AddrError::HybridVerificationFailed);
        }
        let pq_transcript = Self::signing_transcript(
            HybridRole::PostQuantum,
            spec,
            &self.id_commit,
            &self.pk_classical_digest,
            &self.pk_pq_digest,
            msg,
        );
        if !verify_transcript_framing(HybridRole::PostQuantum, &pq_transcript)
            || !verify_pq(&self.pk_pq, &pq_transcript, &self.sig_pq)
        {
            return Err(AddrError::HybridVerificationFailed);
        }
        Ok(())
    }

    /// Structural and address-level binding check before invoking signature verifiers:
    ///
    /// 1. `expected_hrp` normalizes cleanly and equals `expected_address.hrp`;
    /// 2. `expected_address` has `KeyIdentityKind::HybridConjunctive` and `self.suite_tag`;
    /// 3. [`Self::validate_structure`] passes on `self.id_commit`;
    /// 4. recomputing [`Self::to_address`] under `(expected_address.hrp, expected_address.version)`
    ///    reproduces its commitment using constant-time digest comparison. Metadata
    ///    (HRP, version, suite, and kind) is public and compared normally.
    pub fn validate_for_address(
        &self,
        expected_address: &QsagAddress,
        expected_hrp: &str,
    ) -> Result<HybridSuiteSpec, AddrError> {
        let hrp_norm = normalize_hrp(expected_hrp)?;
        if expected_address.hrp != hrp_norm {
            return Err(AddrError::AddressBindingMismatch);
        }
        expected_address
            .suite_tag
            .validate_identity_kind(expected_address.kind)?;
        if expected_address.kind != KeyIdentityKind::HybridConjunctive
            || expected_address.suite_tag != self.suite_tag
        {
            return Err(AddrError::AddressBindingMismatch);
        }
        let spec = self.validate_structure(&self.id_commit)?;
        let derived = self.to_address(&hrp_norm, expected_address.version)?;
        let addr_ok = ct_eq_bytes(&derived.commitment_256, &expected_address.commitment_256)
            & (derived.version == expected_address.version)
            & (derived.suite_tag == expected_address.suite_tag)
            & (derived.kind == expected_address.kind)
            & (derived.hrp == expected_address.hrp);
        if !addr_ok {
            return Err(AddrError::AddressBindingMismatch);
        }
        Ok(spec)
    }

    /// Conjunctive verification bound directly to an expected [`QsagAddress`] and HRP (`expected_hrp`),
    /// preventing cross-network HRP substitution, `AddressVersion` confusion, or wrong-address
    /// witness replay.
    pub fn verify_bound_address<VC, VP>(
        &self,
        expected_address: &QsagAddress,
        expected_hrp: &str,
        msg: &[u8],
        verify_classical: VC,
        verify_pq: VP,
    ) -> Result<(), AddrError>
    where
        VC: FnOnce(&[u8], &[u8], &[u8]) -> bool,
        VP: FnOnce(&[u8], &[u8], &[u8]) -> bool,
    {
        let spec = self.validate_for_address(expected_address, expected_hrp)?;
        self.run_verifiers(&spec, msg, verify_classical, verify_pq)
    }

    /// Decode `encoded_address` strictly under `expected_hrp`, verify address binding, and run
    /// conjunctive classical + post-quantum verification.
    pub fn verify_bound_encoded_address<VC, VP>(
        &self,
        encoded_address: &str,
        expected_hrp: &str,
        msg: &[u8],
        verify_classical: VC,
        verify_pq: VP,
    ) -> Result<QsagAddress, AddrError>
    where
        VC: FnOnce(&[u8], &[u8], &[u8]) -> bool,
        VP: FnOnce(&[u8], &[u8], &[u8]) -> bool,
    {
        let address = QsagAddress::decode_for_hrp(encoded_address, expected_hrp)?;
        self.verify_bound_address(&address, expected_hrp, msg, verify_classical, verify_pq)?;
        Ok(address)
    }

    /// Canonical length-prefixed wire serialization:
    ///
    /// `"QSAG.HYBRID.ENV.V1" (18 B) || suite_u16_be (2 B) || classical_alg_u16_be (2 B)
    /// || pq_alg_u16_be (2 B) || id_commit (32 B) || pk_classical_digest (32 B)
    /// || pk_pq_digest (32 B) || u32_be(len(pk_classical)) || pk_classical
    /// || u32_be(len(pk_pq)) || pk_pq || u32_be(len(sig_classical)) || sig_classical
    /// || u32_be(len(sig_pq)) || sig_pq`
    pub fn to_bytes(&self) -> Result<Vec<u8>, AddrError> {
        self.validate_structure(&self.id_commit)?;
        let total_len = HYBRID_ENVELOPE_WIRE_MAGIC.len()
            + 6
            + 96
            + 16
            + self.pk_classical.len()
            + self.pk_pq.len()
            + self.sig_classical.len()
            + self.sig_pq.len();
        let mut out = Vec::with_capacity(total_len);
        out.extend_from_slice(HYBRID_ENVELOPE_WIRE_MAGIC);
        out.extend_from_slice(&(self.suite_tag as u16).to_be_bytes());
        out.extend_from_slice(&(self.classical_algorithm as u16).to_be_bytes());
        out.extend_from_slice(&(self.pq_algorithm as u16).to_be_bytes());
        out.extend_from_slice(&self.id_commit);
        out.extend_from_slice(&self.pk_classical_digest);
        out.extend_from_slice(&self.pk_pq_digest);
        for field in [
            self.pk_classical.as_slice(),
            self.pk_pq.as_slice(),
            self.sig_classical.as_slice(),
            self.sig_pq.as_slice(),
        ] {
            let len_u32 =
                u32::try_from(field.len()).map_err(|_| AddrError::InvalidEnvelopeWireFormat)?;
            out.extend_from_slice(&len_u32.to_be_bytes());
            out.extend_from_slice(field);
        }
        Ok(out)
    }

    /// Parse and structurally validate a [`HybridPinnedEnvelope`] from canonical wire bytes,
    /// rejecting bad headers, truncated/oversized length prefixes, trailing bytes, non-canonical
    /// scalars, and mismatched digests before allocating untrusted lengths.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, AddrError> {
        const FIXED_HEADER_LEN: usize = HYBRID_ENVELOPE_WIRE_MAGIC.len() + 6 + 96;
        if bytes.len() < FIXED_HEADER_LEN + 16 {
            return Err(AddrError::InvalidEnvelopeWireFormat);
        }
        if &bytes[..HYBRID_ENVELOPE_WIRE_MAGIC.len()] != HYBRID_ENVELOPE_WIRE_MAGIC {
            return Err(AddrError::InvalidEnvelopeWireFormat);
        }
        let mut pos = HYBRID_ENVELOPE_WIRE_MAGIC.len();
        let suite_raw = u16::from_be_bytes([bytes[pos], bytes[pos + 1]]);
        pos += 2;
        let cl_raw = u16::from_be_bytes([bytes[pos], bytes[pos + 1]]);
        pos += 2;
        let pq_raw = u16::from_be_bytes([bytes[pos], bytes[pos + 1]]);
        pos += 2;

        let suite_tag = WitnessSuiteTag::from_u16(suite_raw)?;
        let spec = HybridSuiteSpec::for_suite(suite_tag)?;
        let classical_algorithm = HybridComponentAlgorithm::from_u16(cl_raw)?;
        let pq_algorithm = HybridComponentAlgorithm::from_u16(pq_raw)?;
        if classical_algorithm != spec.classical || pq_algorithm != spec.pq {
            return Err(AddrError::HybridAlgorithmTagMismatch);
        }

        let mut id_commit = [0u8; 32];
        id_commit.copy_from_slice(&bytes[pos..pos + 32]);
        pos += 32;
        let mut pk_classical_digest = [0u8; 32];
        pk_classical_digest.copy_from_slice(&bytes[pos..pos + 32]);
        pos += 32;
        let mut pk_pq_digest = [0u8; 32];
        pk_pq_digest.copy_from_slice(&bytes[pos..pos + 32]);
        pos += 32;

        let read_component = |cursor: &mut usize,
                              expected_len: usize,
                              component: HybridComponent|
         -> Result<&[u8], AddrError> {
            let hdr = bytes
                .get(*cursor..*cursor + 4)
                .ok_or(AddrError::InvalidEnvelopeWireFormat)?;
            let declared_len = u32::from_be_bytes([hdr[0], hdr[1], hdr[2], hdr[3]]) as usize;
            *cursor += 4;
            if declared_len > bytes.len().saturating_sub(*cursor) {
                return Err(AddrError::InvalidEnvelopeWireFormat);
            }
            if declared_len != expected_len {
                return Err(AddrError::HybridMalformedComponent(component));
            }
            let slice = &bytes[*cursor..*cursor + declared_len];
            *cursor += declared_len;
            Ok(slice)
        };

        let pk_classical = read_component(
            &mut pos,
            spec.classical.public_key_len(),
            HybridComponent::ClassicalPublicKey,
        )?;
        let pk_pq = read_component(
            &mut pos,
            spec.pq.public_key_len(),
            HybridComponent::PqPublicKey,
        )?;
        let sig_classical = read_component(
            &mut pos,
            spec.classical.signature_len(),
            HybridComponent::ClassicalSignature,
        )?;
        let sig_pq = read_component(
            &mut pos,
            spec.pq.signature_len(),
            HybridComponent::PqSignature,
        )?;

        if pos != bytes.len() {
            return Err(AddrError::InvalidEnvelopeWireFormat);
        }

        let env = Self {
            suite_tag,
            classical_algorithm,
            pq_algorithm,
            id_commit,
            pk_classical_digest,
            pk_pq_digest,
            pk_classical: pk_classical.to_vec(),
            pk_pq: pk_pq.to_vec(),
            sig_classical: sig_classical.to_vec(),
            sig_pq: sig_pq.to_vec(),
        };
        env.validate_structure(&env.id_commit)?;
        Ok(env)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn test_strict_bech32m_roundtrip_and_legacy_bech32_rejection() {
        let addr_v1 = QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            &[0x42u8; 1952],
        )
        .unwrap();
        let enc = addr_v1.encode().unwrap();
        assert!(enc.len() < 90);
        let dec = QsagAddress::decode(&enc).unwrap();
        assert_eq!(dec, addr_v1);

        // Poseidon2 v2 address roundtrip
        let addr_v2 = QsagAddress::from_pubkey_poseidon2(
            "qsp",
            WitnessSuiteTag::ParallelSeededFts,
            KeyIdentityKind::SingleOrThreshold,
            &[0xABu8; 64],
        )
        .unwrap();
        let enc_v2 = addr_v2.encode().unwrap();
        assert_eq!(QsagAddress::decode(&enc_v2).unwrap(), addr_v2);

        // Construct a legacy BIP-173 Bech32 (`const == 1`) string with the exact same payload and
        // prove `bech32m_decode_5bit` EXPLICITLY rejects it with `LegacyBech32Rejected`!
        let (hrp, data5) = bech32m_decode_5bit(&enc).unwrap();
        let mut poly_vals = bech32_hrp_expand(hrp.as_bytes()).unwrap();
        poly_vals.extend_from_slice(&data5);
        poly_vals.extend_from_slice(&[0u8; 6]);
        let legacy_pmod = bech32_polymod(&poly_vals) ^ BECH32_LEGACY_CONST;
        let charset = b"qpzry9x8gf2tvdw0s3jn54khce6mua7l";
        let mut legacy_str = String::from(&hrp);
        legacy_str.push('1');
        for &d in &data5 {
            legacy_str.push(charset[d as usize] as char);
        }
        for i in 0..6 {
            let sym = ((legacy_pmod >> (5 * (5 - i))) & 0x1f) as usize;
            legacy_str.push(charset[sym] as char);
        }
        assert_eq!(
            QsagAddress::decode(&legacy_str),
            Err(AddrError::LegacyBech32Rejected)
        );

        // Single-character substitution anywhere in the data/checksum part MUST fail checksum!
        let mut bytes = enc.into_bytes();
        let sep = bytes.iter().rposition(|&b| b == b'1').unwrap();
        for idx in (sep + 1)..bytes.len() {
            let orig = bytes[idx];
            bytes[idx] = if orig == b'q' { b'p' } else { b'q' };
            let mutated = core::str::from_utf8(&bytes).unwrap();
            assert!(QsagAddress::decode(mutated).is_err());
            bytes[idx] = orig;
        }
    }

    const SECP_SUITE: WitnessSuiteTag = WitnessSuiteTag::HybridSecp256k1MlDsa44;

    /// Stand-in "signature": a keyed hash stretched to `len` bytes. For classical components
    /// the top bits of both 32-byte halves are cleared so the result is in canonical range.
    fn toy_sig(label: &[u8], pk: &[u8], transcript: &[u8], len: usize) -> Vec<u8> {
        let mut out = vec![0u8; len];
        qsag_accel::keccak::cshake256_framed_xof(label, &[pk, transcript], &mut out);
        if len == 64 {
            out[0] &= 0x3F;
            out[32] &= 0x3F;
            out[63] &= 0x0F;
        }
        out
    }
    fn toy_keys(suite: WitnessSuiteTag) -> (Vec<u8>, Vec<u8>) {
        let spec = HybridSuiteSpec::for_suite(suite).unwrap();
        let mut pk_cl = vec![0x5Au8; spec.classical.public_key_len()];
        pk_cl[0] = 0x02;
        (pk_cl, vec![0xA5u8; spec.pq.public_key_len()])
    }
    fn toy_envelope(suite: WitnessSuiteTag, msg: &[u8]) -> HybridPinnedEnvelope {
        let spec = HybridSuiteSpec::for_suite(suite).unwrap();
        let (pk_cl, pk_pq) = toy_keys(suite);
        HybridPinnedEnvelope::sign_with(
            suite,
            pk_cl.clone(),
            pk_pq.clone(),
            msg,
            |tr| toy_sig(b"TEST.CL.SIG", &pk_cl, tr, 64),
            |tr| toy_sig(b"TEST.PQ.SIG", &pk_pq, tr, spec.pq.signature_len()),
        )
        .unwrap()
    }
    fn toy_verify_cl(pk: &[u8], tr: &[u8], sig: &[u8]) -> bool {
        ct_eq_bytes(&toy_sig(b"TEST.CL.SIG", pk, tr, 64), sig)
    }
    fn toy_verify_pq(pk: &[u8], tr: &[u8], sig: &[u8]) -> bool {
        ct_eq_bytes(&toy_sig(b"TEST.PQ.SIG", pk, tr, sig.len()), sig)
    }
    /// Verify with callbacks that accept everything and record whether they ran.
    fn verify_recording_calls(
        env: &HybridPinnedEnvelope,
        expected: &[u8; 32],
    ) -> (Result<(), AddrError>, bool) {
        let called = core::cell::Cell::new(false);
        let result = env.verify_with(
            expected,
            b"m",
            |_, _, _| {
                called.set(true);
                true
            },
            |_, _, _| {
                called.set(true);
                true
            },
        );
        (result, called.get())
    }

    #[test]
    fn hybrid_envelope_accepts_both_suites_and_binds_message_and_roles() {
        for suite in [SECP_SUITE, WitnessSuiteTag::HybridEd25519MlDsa65] {
            let msg = b"authorize cross-epoch treasury settlement";
            let env = toy_envelope(suite, msg);
            assert_eq!(
                env.verify_with(&env.id_commit, msg, toy_verify_cl, toy_verify_pq),
                Ok(())
            );
            assert_eq!(
                env.verify_with(
                    &env.id_commit,
                    b"other message",
                    toy_verify_cl,
                    toy_verify_pq
                ),
                Err(AddrError::HybridVerificationFailed)
            );
            let spec = HybridSuiteSpec::for_suite(suite).unwrap();
            let transcript = |role| {
                HybridPinnedEnvelope::signing_transcript(
                    role,
                    &spec,
                    &env.id_commit,
                    &env.pk_classical_digest,
                    &env.pk_pq_digest,
                    msg,
                )
            };
            assert_ne!(
                transcript(HybridRole::Classical),
                transcript(HybridRole::PostQuantum)
            );
            // A signature made over the other role's transcript does not verify.
            let mut swapped = env.clone();
            swapped.sig_classical = toy_sig(
                b"TEST.CL.SIG",
                &env.pk_classical,
                &transcript(HybridRole::PostQuantum),
                64,
            );
            assert_eq!(
                swapped.verify_with(&env.id_commit, msg, toy_verify_cl, toy_verify_pq),
                Err(AddrError::HybridVerificationFailed)
            );
        }
    }

    #[test]
    fn hybrid_envelope_rejects_malformed_structure_before_calling_verifiers() {
        use HybridComponent::*;
        let good = toy_envelope(SECP_SUITE, b"m");
        assert_eq!(
            verify_recording_calls(&good, &good.id_commit),
            (Ok(()), true)
        );

        let malformed = |c| Err(AddrError::HybridMalformedComponent(c));
        type Mutation = fn(&mut HybridPinnedEnvelope);
        let cases: [(Mutation, Result<(), AddrError>); 15] = [
            (
                |e| e.suite_tag = WitnessSuiteTag::MlDsa44,
                Err(AddrError::HybridUnsupportedSuite(0x0101)),
            ),
            (
                |e| e.suite_tag = WitnessSuiteTag::HybridEd25519MlDsa65,
                Err(AddrError::HybridAlgorithmTagMismatch),
            ),
            (
                |e| e.classical_algorithm = HybridComponentAlgorithm::Ed25519,
                Err(AddrError::HybridAlgorithmTagMismatch),
            ),
            (
                |e| e.pq_algorithm = HybridComponentAlgorithm::MlDsa65,
                Err(AddrError::HybridAlgorithmTagMismatch),
            ),
            (
                |e| {
                    e.pk_classical.pop();
                },
                malformed(ClassicalPublicKey),
            ),
            (|e| e.pk_classical.push(0), malformed(ClassicalPublicKey)),
            (|e| e.pk_classical[0] = 0x04, malformed(ClassicalPublicKey)),
            (
                |e| {
                    e.pk_pq.pop();
                },
                malformed(PqPublicKey),
            ),
            (|e| e.pk_pq.push(0), malformed(PqPublicKey)),
            (
                |e| {
                    e.sig_classical.pop();
                },
                malformed(ClassicalSignature),
            ),
            (
                |e| e.sig_classical[..32].fill(0),
                malformed(ClassicalSignature),
            ),
            (
                |e| e.sig_classical[..32].fill(0xFF),
                malformed(ClassicalSignature),
            ),
            // High `s`: the mirrored encoding `n - s` of an otherwise valid signature.
            (
                |e| e.sig_classical[32] = 0x80,
                malformed(ClassicalSignature),
            ),
            (
                |e| {
                    e.sig_pq.pop();
                },
                malformed(PqSignature),
            ),
            (|e| e.sig_pq.push(0), malformed(PqSignature)),
        ];
        for (i, (mutate, expected)) in cases.iter().enumerate() {
            let mut bad = good.clone();
            mutate(&mut bad);
            assert_eq!(
                verify_recording_calls(&bad, &good.id_commit),
                (*expected, false),
                "case {i}"
            );
        }

        let commitment_cases: [Mutation; 5] = [
            |e| e.pk_classical[5] ^= 1,
            |e| e.pk_pq[5] ^= 1,
            |e| e.pk_classical_digest[0] ^= 1,
            |e| e.pk_pq_digest[0] ^= 1,
            |e| e.id_commit[0] ^= 1,
        ];
        for (i, mutate) in commitment_cases.iter().enumerate() {
            let mut bad = good.clone();
            mutate(&mut bad);
            assert_eq!(
                verify_recording_calls(&bad, &good.id_commit),
                (Err(AddrError::HybridCommitmentMismatch), false),
                "commitment case {i}"
            );
        }
        let mut other_identity = good.id_commit;
        other_identity[31] ^= 1;
        assert_eq!(
            verify_recording_calls(&good, &other_identity),
            (Err(AddrError::HybridCommitmentMismatch), false)
        );
    }

    #[test]
    fn hybrid_envelope_scalar_range_boundaries_are_exact() {
        let spec = HybridSuiteSpec::for_suite(SECP_SUITE).unwrap();
        let pq = vec![0u8; 2420];
        let mut sig = [0u8; 64];
        sig[31] = 1;
        sig[32..].copy_from_slice(&SECP256K1_HALF_ORDER_BE);
        assert_eq!(spec.validate_signatures(&sig, &pq), Ok(()));
        sig[63] += 1;
        assert!(spec.validate_signatures(&sig, &pq).is_err());
        sig[32..].fill(0);
        sig[63] = 1;
        sig[..32].copy_from_slice(&SECP256K1_ORDER_BE);
        assert!(spec.validate_signatures(&sig, &pq).is_err());
        sig[31] -= 1;
        assert_eq!(spec.validate_signatures(&sig, &pq), Ok(()));

        let ed = HybridSuiteSpec::for_suite(WitnessSuiteTag::HybridEd25519MlDsa65).unwrap();
        let pq = vec![0u8; 3309];
        let mut sig = [0u8; 64];
        for (dst, src) in sig[32..].iter_mut().zip(ED25519_ORDER_BE.iter().rev()) {
            *dst = *src;
        }
        assert!(ed.validate_signatures(&sig, &pq).is_err());
        sig[32] -= 1;
        assert_eq!(ed.validate_signatures(&sig, &pq), Ok(()));
    }

    #[test]
    fn hybrid_signing_validates_keys_before_calling_signers() {
        let (pk_cl, pk_pq) = toy_keys(SECP_SUITE);
        let called = core::cell::Cell::new(false);
        let run = |suite, cl: Vec<u8>, pq: Vec<u8>| {
            HybridPinnedEnvelope::sign_with(
                suite,
                cl,
                pq,
                b"m",
                |_| {
                    called.set(true);
                    vec![1u8; 64]
                },
                |_| {
                    called.set(true);
                    vec![1u8; 2420]
                },
            )
            .map(|_| ())
        };
        assert_eq!(
            run(WitnessSuiteTag::SlhDsa128s, pk_cl.clone(), pk_pq.clone()),
            Err(AddrError::HybridUnsupportedSuite(0x0201))
        );
        assert_eq!(
            run(SECP_SUITE, pk_cl[..32].to_vec(), pk_pq.clone()),
            Err(AddrError::HybridMalformedComponent(
                HybridComponent::ClassicalPublicKey
            ))
        );
        assert_eq!(
            run(SECP_SUITE, pk_cl.clone(), vec![0u8; 1952]),
            Err(AddrError::HybridMalformedComponent(
                HybridComponent::PqPublicKey
            ))
        );
        assert!(!called.get());
        assert_eq!(run(SECP_SUITE, pk_cl, pk_pq), Ok(()));
        assert!(called.get());
    }

    #[test]
    fn hybrid_envelope_blocks_rogue_key_repinning() {
        // The attacker keeps the honest classical key and signature, swaps in its own PQ key,
        // and recomputes every commitment so the structure is valid. The honest classical
        // signature was made over the original commitments, so verification must fail.
        let msg = b"authorize cross-epoch treasury settlement";
        let env = toy_envelope(SECP_SUITE, msg);
        let spec = HybridSuiteSpec::for_suite(SECP_SUITE).unwrap();
        let pk_pq_rogue = vec![0x99u8; 1312];
        let pq_rogue_dig = HybridPinnedEnvelope::hash_pq_pk(&spec, &pk_pq_rogue);
        let rogue_id =
            HybridPinnedEnvelope::compute_id_commit(&spec, &env.pk_classical_digest, &pq_rogue_dig);
        let rogue_tr = HybridPinnedEnvelope::signing_transcript(
            HybridRole::PostQuantum,
            &spec,
            &rogue_id,
            &env.pk_classical_digest,
            &pq_rogue_dig,
            msg,
        );
        let rogue_env = HybridPinnedEnvelope {
            id_commit: rogue_id,
            pk_pq_digest: pq_rogue_dig,
            sig_pq: toy_sig(b"TEST.PQ.SIG", &pk_pq_rogue, &rogue_tr, 2420),
            pk_pq: pk_pq_rogue,
            ..env.clone()
        };
        assert_eq!(rogue_env.validate_structure(&rogue_id).map(|_| ()), Ok(()));
        assert_eq!(
            rogue_env.verify_with(&rogue_id, msg, toy_verify_cl, toy_verify_pq),
            Err(AddrError::HybridVerificationFailed)
        );
        // Presented against the honest identity, it is rejected before any verifier runs.
        assert_eq!(
            verify_recording_calls(&rogue_env, &env.id_commit),
            (Err(AddrError::HybridCommitmentMismatch), false)
        );
    }

    #[test]
    fn decode_and_builders_reject_inconsistent_suite_and_identity_kind() {
        // Builders reject mismatched (suite, kind) immediately.
        assert_eq!(
            QsagAddress::from_pubkey_cshake256(
                "qsp",
                WitnessSuiteTag::HybridSecp256k1MlDsa44,
                KeyIdentityKind::SingleOrThreshold,
                &[0x11; 32],
            ),
            Err(AddrError::InconsistentSuiteIdentityKind {
                suite_tag: WitnessSuiteTag::HybridSecp256k1MlDsa44 as u16,
                kind: KeyIdentityKind::SingleOrThreshold as u8,
            })
        );
        assert_eq!(
            QsagAddress::from_pubkey_poseidon2(
                "qsp",
                WitnessSuiteTag::MlDsa65,
                KeyIdentityKind::HybridConjunctive,
                &[0x22; 32],
            ),
            Err(AddrError::InconsistentSuiteIdentityKind {
                suite_tag: WitnessSuiteTag::MlDsa65 as u16,
                kind: KeyIdentityKind::HybridConjunctive as u8,
            })
        );
        assert_eq!(
            QsagAddress::from_pubkey_cshake256(
                "qsp",
                WitnessSuiteTag::PolicyPredicateScript,
                KeyIdentityKind::SingleOrThreshold,
                &[0x33; 32],
            ),
            Err(AddrError::InconsistentSuiteIdentityKind {
                suite_tag: WitnessSuiteTag::PolicyPredicateScript as u16,
                kind: KeyIdentityKind::SingleOrThreshold as u8,
            })
        );

        // Craft valid Bech32m strings with inconsistent (suite_tag, kind) in the raw 35-byte
        // witness program and verify `QsagAddress::decode` rejects every mismatch!
        let bad_pairs = [
            (
                WitnessSuiteTag::HybridSecp256k1MlDsa44,
                KeyIdentityKind::SingleOrThreshold,
            ),
            (
                WitnessSuiteTag::HybridEd25519MlDsa65,
                KeyIdentityKind::ScriptPredicate,
            ),
            (WitnessSuiteTag::MlDsa44, KeyIdentityKind::HybridConjunctive),
            (
                WitnessSuiteTag::SlhDsa128s,
                KeyIdentityKind::ScriptPredicate,
            ),
            (
                WitnessSuiteTag::PolicyPredicateScript,
                KeyIdentityKind::HybridConjunctive,
            ),
        ];
        for (suite, kind) in bad_pairs {
            let mut prog = [0u8; 35];
            prog[0..2].copy_from_slice(&(suite as u16).to_be_bytes());
            prog[2] = kind as u8;
            prog[3..35].fill(0x07);
            let prog5 = convert_bits(&prog, 8, 5, true).unwrap();
            let mut data5 = Vec::with_capacity(1 + prog5.len());
            data5.push(AddressVersion::V1Cshake256 as u8);
            data5.extend_from_slice(&prog5);
            let forged_bech32m = bech32m_encode_5bit("qsp", &data5).unwrap();
            assert_eq!(
                QsagAddress::decode(&forged_bech32m),
                Err(AddrError::InconsistentSuiteIdentityKind {
                    suite_tag: suite as u16,
                    kind: kind as u8,
                })
            );
        }
    }

    #[test]
    fn hybrid_envelope_bound_address_verifies_hrp_version_and_commitment() {
        let msg = b"settle bound address transfer";
        let env = toy_envelope(SECP_SUITE, msg);

        for version in [AddressVersion::V1Cshake256, AddressVersion::V2Poseidon2] {
            let addr = env.to_address("qsp", version).unwrap();
            let encoded = addr.encode().unwrap();
            assert_eq!(
                env.verify_bound_address(&addr, "qsp", msg, toy_verify_cl, toy_verify_pq),
                Ok(())
            );
            assert_eq!(
                env.verify_bound_encoded_address(
                    &encoded,
                    "QSP",
                    msg,
                    toy_verify_cl,
                    toy_verify_pq,
                ),
                Ok(addr.clone())
            );

            // Wrong expected HRP is rejected before verifiers run.
            let called = core::cell::Cell::new(false);
            assert_eq!(
                env.verify_bound_address(
                    &addr,
                    "qstest",
                    msg,
                    |_, _, _| {
                        called.set(true);
                        true
                    },
                    |_, _, _| {
                        called.set(true);
                        true
                    },
                ),
                Err(AddrError::AddressBindingMismatch)
            );
            assert!(!called.get());
        }

        // Address derived for a different HRP or a different envelope is rejected before verifiers run.
        let testnet_addr = env
            .to_address("qstest", AddressVersion::V1Cshake256)
            .unwrap();
        assert_eq!(
            env.verify_bound_address(&testnet_addr, "qsp", msg, toy_verify_cl, toy_verify_pq),
            Err(AddrError::AddressBindingMismatch)
        );
        let other_env = toy_envelope(WitnessSuiteTag::HybridEd25519MlDsa65, msg);
        let other_addr = other_env
            .to_address("qsp", AddressVersion::V1Cshake256)
            .unwrap();
        assert_eq!(
            env.verify_bound_address(&other_addr, "qsp", msg, toy_verify_cl, toy_verify_pq),
            Err(AddrError::AddressBindingMismatch)
        );
        let single_addr = QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::MlDsa44,
            KeyIdentityKind::SingleOrThreshold,
            &env.id_commit,
        )
        .unwrap();
        assert_eq!(
            env.verify_bound_address(&single_addr, "qsp", msg, toy_verify_cl, toy_verify_pq),
            Err(AddrError::AddressBindingMismatch)
        );
    }

    #[test]
    fn hybrid_envelope_wire_codec_roundtrip_and_mutation_rejection() {
        for suite in [SECP_SUITE, WitnessSuiteTag::HybridEd25519MlDsa65] {
            let msg = b"canonical hybrid envelope wire serialization";
            let env = toy_envelope(suite, msg);
            let wire = env.to_bytes().unwrap();
            let parsed = HybridPinnedEnvelope::from_bytes(&wire).unwrap();
            assert_eq!(parsed, env);
            assert_eq!(
                parsed.verify_with(&env.id_commit, msg, toy_verify_cl, toy_verify_pq),
                Ok(())
            );

            // Empty / truncated / trailing-byte wire slices must fail.
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&[]),
                Err(AddrError::InvalidEnvelopeWireFormat)
            );
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&wire[..wire.len() - 1]),
                Err(AddrError::InvalidEnvelopeWireFormat)
            );
            let mut trailing = wire.clone();
            trailing.push(0x00);
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&trailing),
                Err(AddrError::InvalidEnvelopeWireFormat)
            );

            // Bad magic header fails.
            let mut bad_magic = wire.clone();
            bad_magic[0] ^= 0xFF;
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&bad_magic),
                Err(AddrError::InvalidEnvelopeWireFormat)
            );

            // Oversized u32::MAX length prefix on first component fails cleanly without OOM.
            let first_len_off = HYBRID_ENVELOPE_WIRE_MAGIC.len() + 6 + 96;
            let mut huge_len = wire.clone();
            huge_len[first_len_off..first_len_off + 4].copy_from_slice(&u32::MAX.to_be_bytes());
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&huge_len),
                Err(AddrError::InvalidEnvelopeWireFormat)
            );

            // Shortened declared length (leaving mismatch / trailing bytes) fails.
            let mut short_len = wire.clone();
            short_len[first_len_off..first_len_off + 4].copy_from_slice(&1u32.to_be_bytes());
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&short_len),
                Err(AddrError::HybridMalformedComponent(
                    HybridComponent::ClassicalPublicKey
                ))
            );

            // Corrupting id_commit or public-key bytes in wire fails structural digest check.
            let id_off = HYBRID_ENVELOPE_WIRE_MAGIC.len() + 6;
            let mut bad_id = wire.clone();
            bad_id[id_off] ^= 0x01;
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&bad_id),
                Err(AddrError::HybridCommitmentMismatch)
            );

            let pk_cl_data_off = first_len_off + 4;
            let mut bad_pk = wire.clone();
            bad_pk[pk_cl_data_off + 2] ^= 0x01;
            assert_eq!(
                HybridPinnedEnvelope::from_bytes(&bad_pk),
                Err(AddrError::HybridCommitmentMismatch)
            );
        }

        // High-s ECDSA scalar in wire is rejected during `from_bytes`.
        let env = toy_envelope(SECP_SUITE, b"scalar check");
        let mut wire = env.to_bytes().unwrap();
        let sig_cl_data_off = HYBRID_ENVELOPE_WIRE_MAGIC.len()
            + 6
            + 96
            + 4
            + env.pk_classical.len()
            + 4
            + env.pk_pq.len()
            + 4;
        wire[sig_cl_data_off + 32] = 0x80;
        assert_eq!(
            HybridPinnedEnvelope::from_bytes(&wire),
            Err(AddrError::HybridMalformedComponent(
                HybridComponent::ClassicalSignature
            ))
        );
    }

    #[test]
    fn verified_hybrid_transcript_digest_and_canonical_intent128_kats() {
        for suite in [SECP_SUITE, WitnessSuiteTag::HybridEd25519MlDsa65] {
            let msg = b"qsag-verified hybrid transcript byte-identity check";
            let env = toy_envelope(suite, msg);
            let spec = HybridSuiteSpec::for_suite(suite).unwrap();
            for role in [HybridRole::Classical, HybridRole::PostQuantum] {
                let raw = HybridPinnedEnvelope::signing_transcript(
                    role,
                    &spec,
                    &env.id_commit,
                    &env.pk_classical_digest,
                    &env.pk_pq_digest,
                    msg,
                );
                let digest = env.signing_transcript_digest(role, msg).unwrap();
                assert_eq!(digest, qsag_verified::shake256_32(&raw));
                assert!(check_hybrid_domain_framing(
                    HYBRID_PINNED_MAGIC,
                    role as u8,
                    role.to_verified_tag(),
                    suite as u16,
                    &env.id_commit,
                    &env.id_commit,
                ));
                let other_role = match role {
                    HybridRole::Classical => HybridRoleTag::PostQuantum,
                    HybridRole::PostQuantum => HybridRoleTag::Classical,
                };
                assert!(!check_hybrid_domain_framing(
                    HYBRID_PINNED_MAGIC,
                    role as u8,
                    other_role,
                    suite as u16,
                    &env.id_commit,
                    &env.id_commit,
                ));
            }
            assert_ne!(
                env.signing_transcript_digest(HybridRole::Classical, msg)
                    .unwrap(),
                env.signing_transcript_digest(HybridRole::PostQuantum, msg)
                    .unwrap()
            );
        }

        let intent = CanonicalIntent128 {
            suite_tag: IntentSuiteTag::HybridEd25519MlDsa65,
            address_version: IntentAddressVersion::V2,
            identity_kind: IntentIdentityKind::PolicyBound,
            chain_id: 0x0102_0304_0506_0708,
            nonce: 42,
            timestamp_secs: 1_735_689_600,
            amount_units: 123_456_789_012_345_678_901u128,
            rolling_window_spent: 987_654_321u128,
            recipient_commitment: [0xAB; 32],
            payload_digest: [0xCD; 32],
        };
        let wire128 = encode_intent_128(&intent);
        assert_eq!(&wire128[0..4], &INTENT_V1_MAGIC.to_be_bytes());
        let decoded = decode_intent_128(&wire128).expect("canonical 128-byte intent must decode");
        assert_eq!(decoded.suite_tag, intent.suite_tag);
        assert_eq!(decoded.address_version, intent.address_version);
        assert_eq!(decoded.identity_kind, intent.identity_kind);
        assert_eq!(decoded.chain_id, intent.chain_id);
        assert_eq!(decoded.nonce, intent.nonce);
        assert_eq!(decoded.timestamp_secs, intent.timestamp_secs);
        assert_eq!(decoded.amount_units, intent.amount_units);
        assert_eq!(decoded.rolling_window_spent, intent.rolling_window_spent);
        assert_eq!(decoded.recipient_commitment, intent.recipient_commitment);
        assert_eq!(decoded.payload_digest, intent.payload_digest);

        let mut bad_magic = wire128;
        bad_magic[0] ^= 0x01;
        assert!(decode_intent_128(&bad_magic).is_none());
        let mut bad_suite = wire128;
        bad_suite[4] = 0xFF;
        assert!(decode_intent_128(&bad_suite).is_none());
    }
}

#[cfg(test)]
mod audit_tests;
