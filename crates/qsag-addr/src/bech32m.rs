//! Strict BIP-350 `Bech32m` (`0x2bc830a3`) GF(32) BCH encoder/decoder explicitly rejecting
//! legacy BIP-173 `Bech32` (`1`) checksums, mixed-case strings, and non-zero 5-to-8-bit padding.

use alloc::string::String;
use alloc::vec::Vec;

/// Canonical BIP-350 `Bech32m` polymod target constant.
pub const BECH32M_CONST: u32 = 0x2bc8_30a3;
/// Legacy BIP-173 `Bech32` constant — **explicitly rejected** to prevent `p`-suffix length-extension mutability!
pub const BECH32_LEGACY_CONST: u32 = 1;

const BECH32_CHARSET: &[u8; 32] = b"qpzry9x8gf2tvdw0s3jn54khce6mua7l";

const BECH32_REV: [i8; 128] = [
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    15, -1, 10, 17, 21, 20, 26, 30, 7, 5, -1, -1, -1, -1, -1, -1, -1, 29, -1, 24, 13, 25, 9, 8, 23,
    -1, 18, 22, 31, 27, 19, -1, 1, 0, 3, 16, 11, 28, 12, 14, 6, 4, 2, -1, -1, -1, -1, -1, -1, 29,
    -1, 24, 13, 25, 9, 8, 23, -1, 18, 22, 31, 27, 19, -1, 1, 0, 3, 16, 11, 28, 12, 14, 6, 4, 2, -1,
    -1, -1, -1, -1,
];

const GENERATOR: [u32; 5] = [
    0x3b6a_57b2,
    0x2650_8e6d,
    0x1ea1_19fa,
    0x3d42_33dd,
    0x2a14_62b3,
];

/// Errors produced by the strict `Bech32m` address codec.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AddrError {
    EmptyOrInvalidHrp,
    StringTooLongOrTooShort,
    MixedCase,
    MissingSeparator,
    InvalidCharacter,
    /// Explicit detection of a legacy BIP-173 (`const == 1`) Bech32 string!
    LegacyBech32Rejected,
    InvalidChecksum,
    InvalidBitConversion,
    NonZeroPadding,
    InvalidPayloadLength,
    UnsupportedVersion(u8),
    UnsupportedSuiteTag(u16),
    UnsupportedIdentityKind(u8),
    /// The `(suite_tag, kind)` combination is semantically inconsistent (e.g. a hybrid suite with
    /// `SingleOrThreshold` or a single-key suite with `HybridConjunctive`).
    InconsistentSuiteIdentityKind {
        suite_tag: u16,
        kind: u8,
    },
    NonCanonicalPoseidonLimb,
    /// A signature verifier callback rejected its component signature.
    HybridVerificationFailed,
    /// The suite tag does not name a conjunctive classical + post-quantum pair.
    HybridUnsupportedSuite(u16),
    /// The envelope's per-component algorithm tags are not the pair fixed by its suite tag.
    HybridAlgorithmTagMismatch,
    /// A key or signature has the wrong length or a non-canonical encoding for its algorithm.
    HybridMalformedComponent(HybridComponent),
    /// A public-key digest or the identity commitment does not match the carried keys or the
    /// identity the verifier expected.
    HybridCommitmentMismatch,
    /// The envelope's derived `QsagAddress` or HRP does not match the caller's expected address.
    AddressBindingMismatch,
    /// Wire encoding of a `HybridPinnedEnvelope` has a bad magic header, length prefix, or trailing bytes.
    InvalidEnvelopeWireFormat,
}

/// The envelope field rejected by structural validation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HybridComponent {
    ClassicalPublicKey,
    PqPublicKey,
    ClassicalSignature,
    PqSignature,
}

#[inline]
pub const fn bech32_polymod_step(chk: u32, v: u8) -> u32 {
    let top = chk >> 25;
    let mut next = ((chk & 0x01ff_ffff) << 5) ^ ((v & 0x1f) as u32);
    let mut i = 0usize;
    while i < 5 {
        if ((top >> i) & 1) == 1 {
            next ^= GENERATOR[i];
        }
        i += 1;
    }
    next
}

pub fn bech32_hrp_expand(hrp_lower: &[u8]) -> Result<Vec<u8>, AddrError> {
    if hrp_lower.is_empty() || hrp_lower.len() > 83 {
        return Err(AddrError::EmptyOrInvalidHrp);
    }
    let mut out = Vec::with_capacity(hrp_lower.len() * 2 + 1);
    for &b in hrp_lower {
        if !(33..=126).contains(&b) || b.is_ascii_uppercase() {
            return Err(AddrError::EmptyOrInvalidHrp);
        }
        out.push(b >> 5);
    }
    out.push(0);
    for &b in hrp_lower {
        out.push(b & 0x1f);
    }
    Ok(out)
}

pub fn bech32_polymod(values: &[u8]) -> u32 {
    let mut chk = 1u32;
    for &v in values {
        chk = bech32_polymod_step(chk, v);
    }
    chk
}

pub fn bech32m_create_checksum(hrp_lower: &[u8], data5: &[u8]) -> Result<[u8; 6], AddrError> {
    if data5.iter().any(|&symbol| symbol >= 32) {
        return Err(AddrError::InvalidCharacter);
    }
    let mut values = bech32_hrp_expand(hrp_lower)?;
    values.extend_from_slice(data5);
    values.extend_from_slice(&[0u8; 6]);
    let pmod = bech32_polymod(&values) ^ BECH32M_CONST;
    let mut ret = [0u8; 6];
    for (i, slot) in ret.iter_mut().enumerate() {
        *slot = ((pmod >> (5 * (5 - i))) & 0x1f) as u8;
    }
    Ok(ret)
}

/// Convert `from_bits` groups into `to_bits` groups; when `pad == false`, rejects non-zero trailing bits!
pub fn convert_bits(
    data: &[u8],
    from_bits: u32,
    to_bits: u32,
    pad: bool,
) -> Result<Vec<u8>, AddrError> {
    if !(1..=8).contains(&from_bits) || !(1..=8).contains(&to_bits) {
        return Err(AddrError::InvalidBitConversion);
    }
    let mut acc = 0u32;
    let mut bits = 0u32;
    let maxv = (1u32 << to_bits) - 1;
    let max_acc = (1u32 << (from_bits + to_bits - 1)) - 1;
    let capacity = data
        .len()
        .checked_mul(from_bits as usize)
        .ok_or(AddrError::InvalidBitConversion)?
        .div_ceil(to_bits as usize);
    let mut ret = Vec::with_capacity(capacity);

    for &value in data {
        let v = value as u32;
        if (v >> from_bits) != 0 {
            return Err(AddrError::InvalidBitConversion);
        }
        acc = ((acc << from_bits) | v) & max_acc;
        bits += from_bits;
        while bits >= to_bits {
            bits -= to_bits;
            ret.push(((acc >> bits) & maxv) as u8);
        }
    }

    if pad {
        if bits > 0 {
            ret.push(((acc << (to_bits - bits)) & maxv) as u8);
        }
    } else if bits >= from_bits {
        return Err(AddrError::InvalidBitConversion);
    } else if ((acc << (to_bits - bits)) & maxv) != 0 {
        return Err(AddrError::NonZeroPadding);
    }

    Ok(ret)
}

/// Encode `(hrp, data5)` strictly with `Bech32m` (`0x2bc830a3`), enforcing BIP-350 `<= 90` total length.
pub fn bech32m_encode_5bit(hrp: &str, data5: &[u8]) -> Result<String, AddrError> {
    if hrp.is_empty() || hrp.len() > 83 {
        return Err(AddrError::EmptyOrInvalidHrp);
    }
    let mut has_lower = false;
    let mut has_upper = false;
    let mut hrp_lower = Vec::with_capacity(hrp.len());
    for b in hrp.bytes() {
        if !(33..=126).contains(&b) {
            return Err(AddrError::EmptyOrInvalidHrp);
        }
        if b.is_ascii_lowercase() {
            has_lower = true;
        }
        if b.is_ascii_uppercase() {
            has_upper = true;
        }
        hrp_lower.push(b.to_ascii_lowercase());
    }
    if has_lower && has_upper {
        return Err(AddrError::MixedCase);
    }

    if data5.len() > 90 - hrp_lower.len() - 7 {
        return Err(AddrError::StringTooLongOrTooShort);
    }

    let total_len = hrp_lower.len() + 7 + data5.len();
    let checksum = bech32m_create_checksum(&hrp_lower, data5)?;
    let mut out = String::with_capacity(total_len);
    for &b in &hrp_lower {
        out.push(b as char);
    }
    out.push('1');
    for &d in data5 {
        if d >= 32 {
            return Err(AddrError::InvalidCharacter);
        }
        out.push(BECH32_CHARSET[d as usize] as char);
    }
    for &c in &checksum {
        out.push(BECH32_CHARSET[c as usize] as char);
    }
    Ok(out)
}

/// Decode a `Bech32m` string into `(hrp_lowercase, data5)`, **explicitly rejecting** legacy BIP-173
/// `Bech32` (`const == 1`) with [`AddrError::LegacyBech32Rejected`].
pub fn bech32m_decode_5bit(encoded: &str) -> Result<(String, Vec<u8>), AddrError> {
    let bytes = encoded.as_bytes();
    if bytes.len() < 8 || bytes.len() > 90 {
        return Err(AddrError::StringTooLongOrTooShort);
    }

    let mut has_lower = false;
    let mut has_upper = false;
    for &b in bytes {
        if !(33..=126).contains(&b) {
            return Err(AddrError::InvalidCharacter);
        }
        if b.is_ascii_lowercase() {
            has_lower = true;
        }
        if b.is_ascii_uppercase() {
            has_upper = true;
        }
    }
    if has_lower && has_upper {
        return Err(AddrError::MixedCase);
    }

    let sep_pos = bytes
        .iter()
        .rposition(|&b| b == b'1')
        .ok_or(AddrError::MissingSeparator)?;
    if sep_pos == 0 || sep_pos + 7 > bytes.len() {
        return Err(AddrError::MissingSeparator);
    }

    let mut hrp_lower = Vec::with_capacity(sep_pos);
    for &b in &bytes[..sep_pos] {
        hrp_lower.push(b.to_ascii_lowercase());
    }

    let data_part = &bytes[sep_pos + 1..];
    let mut data_and_chk = Vec::with_capacity(data_part.len());
    for &b in data_part {
        let idx = BECH32_REV[b as usize];
        if idx < 0 {
            return Err(AddrError::InvalidCharacter);
        }
        data_and_chk.push(idx as u8);
    }

    let mut poly_input = bech32_hrp_expand(&hrp_lower)?;
    poly_input.extend_from_slice(&data_and_chk);
    let residue = bech32_polymod(&poly_input);
    if residue == BECH32_LEGACY_CONST {
        return Err(AddrError::LegacyBech32Rejected);
    }
    if residue != BECH32M_CONST {
        return Err(AddrError::InvalidChecksum);
    }

    let payload_len = data_and_chk.len() - 6;
    data_and_chk.truncate(payload_len);
    let hrp_str = String::from_utf8(hrp_lower).map_err(|_| AddrError::EmptyOrInvalidHrp)?;
    Ok((hrp_str, data_and_chk))
}

impl core::fmt::Display for AddrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for AddrError {}

#[cfg(test)]
mod bit_width_tests {
    use super::*;
    #[test]
    fn rejects_invalid_widths_and_symbols() {
        for width in [0, 9, 32, u32::MAX] {
            assert!(convert_bits(&[], width, 8, true).is_err());
            assert!(convert_bits(&[], 8, width, false).is_err());
        }
        assert!(convert_bits(&[32], 5, 8, true).is_err());
        assert!(convert_bits(&[2], 1, 8, true).is_err());
        assert_eq!(convert_bits(&[255], 8, 8, true).unwrap(), [255]);
    }
}

#[cfg(test)]
mod adversarial_tests {
    use super::*;

    #[test]
    fn bip350_vectors_and_legacy_rejection() {
        // Generic codec vectors, not Bitcoin witness-program semantics.
        // https://github.com/bitcoin/bips/blob/master/bip-0350.mediawiki
        for encoded in [
            "A1LQFN3A",
            "a1lqfn3a",
            "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6",
            "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx",
            "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8",
            "split1checkupstagehandshakeupstreamerranterredcaperredlc445v",
            "?1v759aa",
        ] {
            let (hrp, data) = bech32m_decode_5bit(encoded).unwrap();
            assert_eq!(
                bech32m_encode_5bit(&hrp, &data).unwrap(),
                encoded.to_ascii_lowercase()
            );
        }
        for encoded in [
            " 1xj0phk",
            "\u{7f}1g6xzxy",
            "\u{80}1vctc34",
            "an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11d6pts4",
            "qyrz8wqd2c9m",
            "1qyrz8wqd2c9m",
            "y1b0jsk6g",
            "lt1igcx5c0",
            "in1muywd",
            "mm1crxm3i",
            "au1s5cgom",
            "M1VUXWEZ",
            "16plkw9",
            "1p2gdwpf",
        ] {
            assert!(bech32m_decode_5bit(encoded).is_err(), "{encoded}");
        }
        for legacy in [
            "A12UEL5L",
            "a12uel5l",
            "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w",
            "?1ezyfcl",
        ] {
            assert_eq!(
                bech32m_decode_5bit(legacy),
                Err(AddrError::LegacyBech32Rejected)
            );
        }
    }

    #[test]
    fn exhaustive_single_symbol_and_short_burst_mutations() {
        let data: Vec<u8> = (0..57).map(|i| (i % 32) as u8).collect();
        let original = bech32m_encode_5bit("qsp", &data).unwrap().into_bytes();
        // Every printable substitution, including HRP and separator. A one-letter
        // case change is mixed case, whereas all-uppercase remains valid.
        for i in 0..original.len() {
            for replacement in 33..=126 {
                if replacement == original[i] {
                    continue;
                }
                let mut changed = original.clone();
                changed[i] = replacement;
                assert!(bech32m_decode_5bit(core::str::from_utf8(&changed).unwrap()).is_err());
            }
        }
        // Deterministic bursts of 2..=4 changed GF(32) symbols, spanning data/checksum.
        for width in 2..=4 {
            for start in 4..=original.len() - width {
                for delta in 1..32 {
                    let mut changed = original.clone();
                    for b in &mut changed[start..start + width] {
                        *b = BECH32_CHARSET[(BECH32_REV[*b as usize] as usize) ^ delta];
                    }
                    assert!(bech32m_decode_5bit(core::str::from_utf8(&changed).unwrap()).is_err());
                }
            }
        }
    }

    #[test]
    fn case_charset_length_and_padding_boundaries() {
        assert_eq!(bech32m_decode_5bit("a1LQFN3A"), Err(AddrError::MixedCase));
        assert_eq!(bech32m_encode_5bit("qSp", &[]), Err(AddrError::MixedCase));
        let hrp = "a".repeat(83);
        let max = bech32m_encode_5bit(&hrp, &[]).unwrap();
        assert_eq!(max.len(), 90);
        assert!(bech32m_decode_5bit(&max).is_ok());
        assert!(bech32m_encode_5bit(&hrp, &[0]).is_err());
        assert!(bech32m_encode_5bit(&"a".repeat(84), &[]).is_err());
        assert!(bech32m_encode_5bit("", &[]).is_err());
        for symbol in 32..=255 {
            assert_eq!(
                bech32m_create_checksum(b"qsp", &[symbol]),
                Err(AddrError::InvalidCharacter)
            );
            assert_eq!(
                bech32m_encode_5bit("qsp", &[symbol]),
                Err(AddrError::InvalidCharacter)
            );
        }
        assert_eq!(
            convert_bits(&[0, 1], 5, 8, false),
            Err(AddrError::NonZeroPadding)
        );
        assert_eq!(
            convert_bits(&[0], 5, 8, false),
            Err(AddrError::InvalidBitConversion)
        );
        assert_eq!(convert_bits(&[0, 0], 5, 8, false).unwrap(), [0]);
    }
}
