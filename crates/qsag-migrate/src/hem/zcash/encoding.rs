//! Zcash address and key encodings: Base58Check transparent addresses, Bech32 and
//! Bech32m, F4Jumble, ZIP 316 unified containers (Revision 0) and Sapling payment
//! addresses.
//!
//! Sources: Zcash protocol specification v2026.9.0 section 5.6 (transparent prefixes in
//! 5.6.1.1, Sapling payment addresses in 5.6.3.1), BIP 173, BIP 350, and ZIP 316. Where
//! the ZIP leaves a choice the behaviour follows `zcash_address` 0.14.0:
//!
//! * F4Jumble accepts 38 to 4194368 bytes. Revision 0 of ZIP 316 said 48; the current
//!   text says 38 and notes that no Revision 0 container is shorter than 48 bytes, so the
//!   difference is not observable through the unified decoders.
//! * A unified container needs one item that is neither transparent (typecodes `0x00`,
//!   `0x01`) nor metadata (`0xC0..=0xFC`). An item of unassigned typecode satisfies this,
//!   as it does in `zcash_address`.
//! * Metadata typecodes `0xE0..=0xFC` are "MUST-understand" and Revision 0 defines none:
//!   such a container is rejected. Metadata typecodes `0xC0..=0xDF` are kept as unknown
//!   items.
//! * Typecode `0x01` has no meaning in a Revision 0 viewing key: decoding keeps it as an
//!   unknown item and encoding refuses it.
//!
//! One rule is stricter than `zcash_address`: a viewing key whose only items are
//! typecodes `0x00` and `0x01` is rejected here as transparent-only (`zcash_address`
//! counts the unrecognised `0x01` item as non-transparent).
//!
//! Revision 2 (`zu`, `tu`, `uvf`, `uvi` prefixes) is not implemented. Item payloads are
//! checked for length only; whether 43 bytes are a valid Sapling or Orchard address is
//! for the key layer to decide.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use qsag_accel::sha2::sha256;

use super::blake2::{blake2b_512, blake2b_var};

/// Why a string or byte sequence was rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EncodingError {
    /// A character outside the Base58 alphabet.
    Base58Character,
    /// The Base58Check checksum does not match, or the payload is too short to hold one.
    Base58Checksum,
    /// The decoded payload has the wrong length for its kind.
    Length,
    /// The Base58Check version bytes are not a Zcash transparent address prefix.
    UnknownPrefix,
    /// A Bech32 character outside the printable range or the data alphabet, or no
    /// separator.
    Bech32Character,
    /// The string mixes upper and lower case.
    MixedCase,
    /// The human-readable part is empty, too long, or not the expected one.
    Hrp,
    /// The Bech32 or Bech32m checksum does not match.
    Bech32Checksum,
    /// The 5-bit to 8-bit regrouping leaves five or more bits, or non-zero bits.
    Bech32Padding,
    /// The input length is outside the range F4Jumble accepts.
    F4JumbleLength,
    /// The unjumbled container does not end in the 16-byte padded human-readable part.
    UnifiedPadding,
    /// An item runs past the end of the container.
    Truncated,
    /// A CompactSize value is not in its shortest form.
    NonCanonicalCompactSize,
    /// A typecode or length exceeds `0x2000000`.
    OutOfRange,
    /// A metadata item in the MUST-understand range.
    MustUnderstand,
    /// A typecode that the revision does not define for this container.
    NotDefinedInRevision,
    /// Items are not in ascending typecode order.
    ItemOrder,
    /// The same typecode appears twice.
    DuplicateTypecode,
    /// Both a P2PKH and a P2SH receiver.
    BothP2pkhAndP2sh,
    /// No item other than transparent ones.
    OnlyTransparent,
    /// No item other than metadata.
    NoDataItems,
    /// An item of a known typecode has the wrong length.
    ItemLength,
}

/// The Zcash network an encoding belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Network {
    Main,
    Test,
}

// ---------------------------------------------------------------------------------------
// Base58Check and transparent addresses.
// ---------------------------------------------------------------------------------------

const BASE58_ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

/// Base58 of `data` (Bitcoin alphabet; each leading zero byte is a leading `1`).
pub fn base58_encode(data: &[u8]) -> String {
    let zeros = data.iter().take_while(|&&b| b == 0).count();
    // Little-endian base-58 digits of the number.
    let mut digits: Vec<u8> = Vec::with_capacity(data.len() * 138 / 100 + 1);
    for &byte in &data[zeros..] {
        let mut carry = u32::from(byte);
        for d in digits.iter_mut() {
            carry += u32::from(*d) << 8;
            *d = (carry % 58) as u8;
            carry /= 58;
        }
        while carry > 0 {
            digits.push((carry % 58) as u8);
            carry /= 58;
        }
    }
    let mut out = String::with_capacity(zeros + digits.len());
    for _ in 0..zeros {
        out.push('1');
    }
    for &d in digits.iter().rev() {
        out.push(BASE58_ALPHABET[d as usize] as char);
    }
    out
}

/// The inverse of [`base58_encode`].
pub fn base58_decode(s: &str) -> Result<Vec<u8>, EncodingError> {
    let bytes = s.as_bytes();
    let ones = bytes.iter().take_while(|&&b| b == b'1').count();
    // Little-endian base-256 digits of the number.
    let mut num: Vec<u8> = Vec::with_capacity(bytes.len() * 733 / 1000 + 1);
    for &ch in &bytes[ones..] {
        let digit = BASE58_ALPHABET
            .iter()
            .position(|&a| a == ch)
            .ok_or(EncodingError::Base58Character)?;
        let mut carry = digit as u32;
        for b in num.iter_mut() {
            carry += u32::from(*b) * 58;
            *b = carry as u8;
            carry >>= 8;
        }
        while carry > 0 {
            num.push(carry as u8);
            carry >>= 8;
        }
    }
    let mut out = vec![0u8; ones];
    out.extend(num.iter().rev());
    Ok(out)
}

fn base58check_checksum(payload: &[u8]) -> [u8; 4] {
    let digest = sha256(&sha256(payload));
    [digest[0], digest[1], digest[2], digest[3]]
}

/// Base58Check: Base58 of `payload || SHA-256(SHA-256(payload))[..4]`.
pub fn base58check_encode(payload: &[u8]) -> String {
    let mut data = Vec::with_capacity(payload.len() + 4);
    data.extend_from_slice(payload);
    data.extend_from_slice(&base58check_checksum(payload));
    base58_encode(&data)
}

/// The payload of a Base58Check string, after verifying its checksum.
pub fn base58check_decode(s: &str) -> Result<Vec<u8>, EncodingError> {
    let mut data = base58_decode(s)?;
    if data.len() < 4 {
        return Err(EncodingError::Base58Checksum);
    }
    let split = data.len() - 4;
    if base58check_checksum(&data[..split]) != data[split..] {
        return Err(EncodingError::Base58Checksum);
    }
    data.truncate(split);
    Ok(data)
}

/// The two kinds of transparent address.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransparentKind {
    /// Pay to public key hash (`t1...` on mainnet, `tm...` on testnet).
    P2pkh,
    /// Pay to script hash (`t3...` on mainnet, `t2...` on testnet).
    P2sh,
}

/// The two-byte Base58Check prefix of a transparent address (protocol specification
/// section 5.6.1.1).
pub const fn transparent_prefix(network: Network, kind: TransparentKind) -> [u8; 2] {
    match (network, kind) {
        (Network::Main, TransparentKind::P2pkh) => [0x1c, 0xb8],
        (Network::Main, TransparentKind::P2sh) => [0x1c, 0xbd],
        (Network::Test, TransparentKind::P2pkh) => [0x1d, 0x25],
        (Network::Test, TransparentKind::P2sh) => [0x1c, 0xba],
    }
}

/// A Zcash transparent address for a 20-byte public key hash or script hash.
pub fn encode_transparent(network: Network, kind: TransparentKind, hash160: &[u8; 20]) -> String {
    let mut payload = [0u8; 22];
    payload[..2].copy_from_slice(&transparent_prefix(network, kind));
    payload[2..].copy_from_slice(hash160);
    base58check_encode(&payload)
}

/// Decodes a Zcash transparent address. Anything but a 22-byte payload under one of the
/// four prefixes is rejected.
pub fn decode_transparent(s: &str) -> Result<(Network, TransparentKind, [u8; 20]), EncodingError> {
    let payload = base58check_decode(s)?;
    if payload.len() != 22 {
        return Err(EncodingError::Length);
    }
    let hash: [u8; 20] = payload[2..].try_into().expect("20 bytes");
    for network in [Network::Main, Network::Test] {
        for kind in [TransparentKind::P2pkh, TransparentKind::P2sh] {
            if payload[..2] == transparent_prefix(network, kind) {
                return Ok((network, kind, hash));
            }
        }
    }
    Err(EncodingError::UnknownPrefix)
}

// ---------------------------------------------------------------------------------------
// Bech32 and Bech32m.
// ---------------------------------------------------------------------------------------

/// The checksum constant: BIP 173 (Bech32) or BIP 350 (Bech32m).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bech32Variant {
    Bech32,
    Bech32m,
}

impl Bech32Variant {
    const fn constant(self) -> u32 {
        match self {
            Bech32Variant::Bech32 => 1,
            Bech32Variant::Bech32m => 0x2bc8_30a3,
        }
    }
}

const BECH32_CHARSET: &[u8; 32] = b"qpzry9x8gf2tvdw0s3jn54khce6mua7l";
const BECH32_MAX_HRP: usize = 83;

fn bech32_polymod_step(chk: u32, value: u8) -> u32 {
    const GEN: [u32; 5] = [
        0x3b6a_57b2,
        0x2650_8e6d,
        0x1ea1_19fa,
        0x3d42_33dd,
        0x2a14_62b3,
    ];
    let top = chk >> 25;
    let mut chk = ((chk & 0x01ff_ffff) << 5) ^ u32::from(value);
    for (i, g) in GEN.iter().enumerate() {
        if (top >> i) & 1 == 1 {
            chk ^= g;
        }
    }
    chk
}

/// The polymod over the expanded (lower-case) human-readable part and `values`.
fn bech32_polymod(hrp: &[u8], values: impl Iterator<Item = u8>) -> u32 {
    let mut chk = 1u32;
    for &c in hrp {
        chk = bech32_polymod_step(chk, c >> 5);
    }
    chk = bech32_polymod_step(chk, 0);
    for &c in hrp {
        chk = bech32_polymod_step(chk, c & 31);
    }
    for v in values {
        chk = bech32_polymod_step(chk, v);
    }
    chk
}

fn bech32_check_hrp(hrp: &str) -> Result<(), EncodingError> {
    let ok = !hrp.is_empty()
        && hrp.len() <= BECH32_MAX_HRP
        && hrp
            .bytes()
            .all(|c| (33..=126).contains(&c) && !c.is_ascii_uppercase());
    if ok { Ok(()) } else { Err(EncodingError::Hrp) }
}

/// Bech32 or Bech32m of a lower-case human-readable part and 5-bit values, with no limit
/// on the total length (ZIP 316 lifts the 90-character limit of BIP 173).
pub fn bech32_encode_u5(
    variant: Bech32Variant,
    hrp: &str,
    values: &[u8],
) -> Result<String, EncodingError> {
    bech32_check_hrp(hrp)?;
    if values.iter().any(|&v| v >= 32) {
        return Err(EncodingError::Bech32Character);
    }
    let polymod = bech32_polymod(
        hrp.as_bytes(),
        values.iter().copied().chain(core::iter::repeat_n(0, 6)),
    ) ^ variant.constant();
    let mut out = String::with_capacity(hrp.len() + 1 + values.len() + 6);
    out.push_str(hrp);
    out.push('1');
    for &v in values {
        out.push(BECH32_CHARSET[v as usize] as char);
    }
    for i in 0..6 {
        out.push(BECH32_CHARSET[((polymod >> (5 * (5 - i))) & 31) as usize] as char);
    }
    Ok(out)
}

/// Decodes a Bech32 or Bech32m string into its human-readable part (lower-cased) and
/// 5-bit values. Mixed case, characters outside the alphabet and a wrong checksum
/// (including a valid checksum of the other variant) are rejected; the total length is
/// not limited.
pub fn bech32_decode_u5(
    variant: Bech32Variant,
    s: &str,
) -> Result<(String, Vec<u8>), EncodingError> {
    let bytes = s.as_bytes();
    if bytes.iter().any(|c| !(33..=126).contains(c)) {
        return Err(EncodingError::Bech32Character);
    }
    let has_lower = bytes.iter().any(u8::is_ascii_lowercase);
    let has_upper = bytes.iter().any(u8::is_ascii_uppercase);
    if has_lower && has_upper {
        return Err(EncodingError::MixedCase);
    }
    let sep = bytes
        .iter()
        .rposition(|&c| c == b'1')
        .ok_or(EncodingError::Bech32Character)?;
    if sep == 0 || sep > BECH32_MAX_HRP {
        return Err(EncodingError::Hrp);
    }
    let hrp: Vec<u8> = bytes[..sep].iter().map(u8::to_ascii_lowercase).collect();
    let data = &bytes[sep + 1..];
    if data.len() < 6 {
        return Err(EncodingError::Bech32Checksum);
    }
    let mut values = Vec::with_capacity(data.len());
    for &c in data {
        let lower = c.to_ascii_lowercase();
        let v = BECH32_CHARSET
            .iter()
            .position(|&a| a == lower)
            .ok_or(EncodingError::Bech32Character)?;
        values.push(v as u8);
    }
    if bech32_polymod(&hrp, values.iter().copied()) != variant.constant() {
        return Err(EncodingError::Bech32Checksum);
    }
    values.truncate(values.len() - 6);
    let hrp = String::from_utf8(hrp).expect("printable ASCII");
    Ok((hrp, values))
}

/// Regroups bytes into 5-bit values, most significant bit first, zero-padding the last.
fn bits_8_to_5(data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(data.len() * 8 / 5 + 1);
    let mut acc = 0u32;
    let mut bits = 0u32;
    for &b in data {
        acc = (acc << 8) | u32::from(b);
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(((acc >> bits) & 31) as u8);
        }
    }
    if bits > 0 {
        out.push(((acc << (5 - bits)) & 31) as u8);
    }
    out
}

/// Regroups 5-bit values into bytes. The leftover must be fewer than five bits, all zero.
fn bits_5_to_8(values: &[u8]) -> Result<Vec<u8>, EncodingError> {
    let mut out = Vec::with_capacity(values.len() * 5 / 8);
    let mut acc = 0u32;
    let mut bits = 0u32;
    for &v in values {
        acc = ((acc << 5) | u32::from(v)) & 0xfff;
        bits += 5;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
        }
    }
    if bits >= 5 || acc & ((1 << bits) - 1) != 0 {
        return Err(EncodingError::Bech32Padding);
    }
    Ok(out)
}

/// Bech32 or Bech32m of a byte string (regrouped into 5-bit values with zero padding).
pub fn bech32_encode(
    variant: Bech32Variant,
    hrp: &str,
    data: &[u8],
) -> Result<String, EncodingError> {
    bech32_encode_u5(variant, hrp, &bits_8_to_5(data))
}

/// Decodes a Bech32 or Bech32m string into its human-readable part (lower-cased) and
/// byte string. Strict as [`bech32_decode_u5`], and the padding of the last group must be
/// fewer than five zero bits.
pub fn bech32_decode(variant: Bech32Variant, s: &str) -> Result<(String, Vec<u8>), EncodingError> {
    let (hrp, values) = bech32_decode_u5(variant, s)?;
    Ok((hrp, bits_5_to_8(&values)?))
}

// ---------------------------------------------------------------------------------------
// F4Jumble.
// ---------------------------------------------------------------------------------------

/// The shortest input F4Jumble accepts (ZIP 316, "Jumbling").
pub const F4JUMBLE_MIN_LEN: usize = 38;
/// The longest input F4Jumble accepts: `(2^16 + 1) * 64` bytes.
pub const F4JUMBLE_MAX_LEN: usize = 4_194_368;

fn f4jumble_h_round(left: &mut [u8], right: &[u8], i: u8) {
    let mut personal = *b"UA_F4Jumble_H\0\0\0";
    personal[13] = i;
    let mut hash = [0u8; 64];
    blake2b_var(&personal, &[right], &mut hash[..left.len()]);
    for (l, h) in left.iter_mut().zip(hash) {
        *l ^= h;
    }
}

fn f4jumble_g_round(left: &[u8], right: &mut [u8], i: u8) {
    for (j, chunk) in right.chunks_mut(64).enumerate() {
        let mut personal = *b"UA_F4Jumble_G\0\0\0";
        personal[13] = i;
        personal[14..].copy_from_slice(&(j as u16).to_le_bytes());
        let hash = blake2b_512(&personal, &[left]);
        for (r, h) in chunk.iter_mut().zip(hash) {
            *r ^= h;
        }
    }
}

fn f4jumble_split(message: &mut [u8]) -> Result<(&mut [u8], &mut [u8]), EncodingError> {
    if !(F4JUMBLE_MIN_LEN..=F4JUMBLE_MAX_LEN).contains(&message.len()) {
        return Err(EncodingError::F4JumbleLength);
    }
    let left_len = (message.len() / 2).min(64);
    Ok(message.split_at_mut(left_len))
}

/// F4Jumble (ZIP 316) in place.
pub fn f4jumble_mut(message: &mut [u8]) -> Result<(), EncodingError> {
    let (left, right) = f4jumble_split(message)?;
    f4jumble_g_round(left, right, 0);
    f4jumble_h_round(left, right, 0);
    f4jumble_g_round(left, right, 1);
    f4jumble_h_round(left, right, 1);
    Ok(())
}

/// The inverse of F4Jumble, in place.
pub fn f4jumble_inv_mut(message: &mut [u8]) -> Result<(), EncodingError> {
    let (left, right) = f4jumble_split(message)?;
    f4jumble_h_round(left, right, 1);
    f4jumble_g_round(left, right, 1);
    f4jumble_h_round(left, right, 0);
    f4jumble_g_round(left, right, 0);
    Ok(())
}

/// F4Jumble of `message`.
pub fn f4jumble(message: &[u8]) -> Result<Vec<u8>, EncodingError> {
    let mut out = message.to_vec();
    f4jumble_mut(&mut out)?;
    Ok(out)
}

/// The inverse of F4Jumble.
pub fn f4jumble_inv(message: &[u8]) -> Result<Vec<u8>, EncodingError> {
    let mut out = message.to_vec();
    f4jumble_inv_mut(&mut out)?;
    Ok(out)
}

// ---------------------------------------------------------------------------------------
// ZIP 316 unified containers, Revision 0.
// ---------------------------------------------------------------------------------------

/// Typecode of a P2PKH receiver or transparent viewing key item.
pub const TYPECODE_P2PKH: u32 = 0x00;
/// Typecode of a P2SH receiver.
pub const TYPECODE_P2SH: u32 = 0x01;
/// Typecode of a Sapling item.
pub const TYPECODE_SAPLING: u32 = 0x02;
/// Typecode of an Orchard item.
pub const TYPECODE_ORCHARD: u32 = 0x03;

/// The largest typecode or item length (the CompactSize bound of ZIP 316).
const UNIFIED_MAX_FIELD: u64 = 0x0200_0000;
const UNIFIED_PADDING_LEN: usize = 16;
const METADATA_MIN: u32 = 0xc0;
const METADATA_MUST_UNDERSTAND_MIN: u32 = 0xe0;
const METADATA_MAX: u32 = 0xfc;

/// A receiver of a Unified Address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Receiver {
    /// The 20-byte validating key hash of a P2PKH address.
    P2pkh([u8; 20]),
    /// The 20-byte script hash of a P2SH address.
    P2sh([u8; 20]),
    /// A raw Sapling payment address, `d (11) || pk_d (32)`.
    Sapling([u8; 43]),
    /// A raw Orchard address, `d (11) || pk_d (32)`.
    Orchard([u8; 43]),
    /// An item of a typecode with no Revision 0 meaning, kept as found.
    Unknown { typecode: u32, data: Vec<u8> },
}

/// An item of a Unified Full Viewing Key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FvkItem {
    /// A transparent account key: `chain code (32) || compressed public key (33)`.
    P2pkh([u8; 65]),
    /// A Sapling full viewing key with its diversifier key: `ak || nk || ovk || dk`.
    Sapling([u8; 128]),
    /// An Orchard full viewing key: `ak || nk || rivk`.
    Orchard([u8; 96]),
    /// An item of a typecode with no Revision 0 meaning (including `0x01`), kept as found.
    Unknown { typecode: u32, data: Vec<u8> },
}

/// An item of a Unified Incoming Viewing Key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IvkItem {
    /// A transparent external key: `chain code (32) || compressed public key (33)`.
    P2pkh([u8; 65]),
    /// A Sapling incoming viewing key: `dk || ivk`.
    Sapling([u8; 64]),
    /// An Orchard incoming viewing key: `dk || ivk`.
    Orchard([u8; 64]),
    /// An item of a typecode with no Revision 0 meaning (including `0x01`), kept as found.
    Unknown { typecode: u32, data: Vec<u8> },
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Container {
    Address,
    Fvk,
    Ivk,
}

impl Container {
    const fn hrp(self, network: Network) -> &'static str {
        match (self, network) {
            (Container::Address, Network::Main) => "u",
            (Container::Address, Network::Test) => "utest",
            (Container::Fvk, Network::Main) => "uview",
            (Container::Fvk, Network::Test) => "uviewtest",
            (Container::Ivk, Network::Main) => "uivk",
            (Container::Ivk, Network::Test) => "uivktest",
        }
    }

    fn network(self, hrp: &str) -> Option<Network> {
        [Network::Main, Network::Test]
            .into_iter()
            .find(|&n| self.hrp(n) == hrp)
    }

    /// The exact length of an item whose typecode Revision 0 defines for this container.
    const fn item_len(self, typecode: u32) -> Option<usize> {
        match (self, typecode) {
            (Container::Address, TYPECODE_P2PKH | TYPECODE_P2SH) => Some(20),
            (Container::Address, TYPECODE_SAPLING | TYPECODE_ORCHARD) => Some(43),
            (Container::Fvk | Container::Ivk, TYPECODE_P2PKH) => Some(65),
            (Container::Fvk, TYPECODE_SAPLING) => Some(128),
            (Container::Fvk, TYPECODE_ORCHARD) => Some(96),
            (Container::Ivk, TYPECODE_SAPLING | TYPECODE_ORCHARD) => Some(64),
            _ => None,
        }
    }
}

type RawItem = (u32, Vec<u8>);

/// The validity rules of ZIP 316 ("Requirements for both Unified Addresses and Unified
/// Viewing Keys") for a Revision 0 container whose items are in encoding order.
fn unified_validate(
    container: Container,
    items: &[RawItem],
    producing: bool,
) -> Result<(), EncodingError> {
    let mut prev: Option<u32> = None;
    let mut has_data = false;
    let mut has_shielded = false;
    let mut encoded_len = UNIFIED_PADDING_LEN;
    for (typecode, data) in items {
        let typecode = *typecode;
        if u64::from(typecode) > UNIFIED_MAX_FIELD || data.len() as u64 > UNIFIED_MAX_FIELD {
            return Err(EncodingError::OutOfRange);
        }
        if (METADATA_MUST_UNDERSTAND_MIN..=METADATA_MAX).contains(&typecode) {
            return Err(EncodingError::MustUnderstand);
        }
        if producing && container != Container::Address && typecode == TYPECODE_P2SH {
            return Err(EncodingError::NotDefinedInRevision);
        }
        match prev {
            Some(p) if typecode < p => return Err(EncodingError::ItemOrder),
            Some(p) if typecode == p => return Err(EncodingError::DuplicateTypecode),
            _ => {}
        }
        if container == Container::Address
            && typecode == TYPECODE_P2SH
            && prev == Some(TYPECODE_P2PKH)
        {
            return Err(EncodingError::BothP2pkhAndP2sh);
        }
        if container
            .item_len(typecode)
            .is_some_and(|len| data.len() != len)
        {
            return Err(EncodingError::ItemLength);
        }
        if !(METADATA_MIN..=METADATA_MAX).contains(&typecode) {
            has_data = true;
            if typecode != TYPECODE_P2PKH && typecode != TYPECODE_P2SH {
                has_shielded = true;
            }
        }
        encoded_len += compact_size_len(u64::from(typecode))
            + compact_size_len(data.len() as u64)
            + data.len();
        prev = Some(typecode);
    }
    if !has_data {
        return Err(EncodingError::NoDataItems);
    }
    if !has_shielded {
        return Err(EncodingError::OnlyTransparent);
    }
    if !(F4JUMBLE_MIN_LEN..=F4JUMBLE_MAX_LEN).contains(&encoded_len) {
        return Err(EncodingError::F4JumbleLength);
    }
    Ok(())
}

const fn compact_size_len(n: u64) -> usize {
    match n {
        0..=252 => 1,
        253..=0xffff => 3,
        0x1_0000..=0xffff_ffff => 5,
        _ => 9,
    }
}

fn compact_size_write(out: &mut Vec<u8>, n: u64) {
    match n {
        0..=252 => out.push(n as u8),
        253..=0xffff => {
            out.push(253);
            out.extend_from_slice(&(n as u16).to_le_bytes());
        }
        0x1_0000..=0xffff_ffff => {
            out.push(254);
            out.extend_from_slice(&(n as u32).to_le_bytes());
        }
        _ => {
            out.push(255);
            out.extend_from_slice(&n.to_le_bytes());
        }
    }
}

/// Reads a canonical CompactSize no larger than `0x2000000` from the front of `buf`.
fn compact_size_read(buf: &mut &[u8]) -> Result<u64, EncodingError> {
    fn take<'a>(buf: &mut &'a [u8], n: usize) -> Result<&'a [u8], EncodingError> {
        if buf.len() < n {
            return Err(EncodingError::Truncated);
        }
        let (head, tail) = buf.split_at(n);
        *buf = tail;
        Ok(head)
    }
    let flag = take(buf, 1)?[0];
    let (value, min) = match flag {
        253 => {
            let b = take(buf, 2)?;
            (u64::from(u16::from_le_bytes([b[0], b[1]])), 253)
        }
        254 => {
            let b = take(buf, 4)?;
            (
                u64::from(u32::from_le_bytes([b[0], b[1], b[2], b[3]])),
                0x1_0000,
            )
        }
        255 => {
            let b = take(buf, 8)?;
            (
                u64::from_le_bytes(b.try_into().expect("8 bytes")),
                0x1_0000_0000,
            )
        }
        n => (u64::from(n), 0),
    };
    if value < min {
        return Err(EncodingError::NonCanonicalCompactSize);
    }
    if value > UNIFIED_MAX_FIELD {
        return Err(EncodingError::OutOfRange);
    }
    Ok(value)
}

/// Jumbles and Bech32m-encodes `items` as given, without checking any container rule.
fn unified_encode_raw(hrp: &str, items: &[RawItem]) -> Result<String, EncodingError> {
    let mut raw = Vec::new();
    for (typecode, data) in items {
        compact_size_write(&mut raw, u64::from(*typecode));
        compact_size_write(&mut raw, data.len() as u64);
        raw.extend_from_slice(data);
    }
    let mut padding = [0u8; UNIFIED_PADDING_LEN];
    padding[..hrp.len()].copy_from_slice(hrp.as_bytes());
    raw.extend_from_slice(&padding);
    f4jumble_mut(&mut raw)?;
    bech32_encode(Bech32Variant::Bech32m, hrp, &raw)
}

fn unified_encode(
    container: Container,
    network: Network,
    mut items: Vec<RawItem>,
) -> Result<String, EncodingError> {
    items.sort_by_key(|(typecode, _)| *typecode);
    unified_validate(container, &items, true)?;
    unified_encode_raw(container.hrp(network), &items)
}

/// The decoding procedure of ZIP 316 on the Bech32m payload of a container.
fn unified_parse(
    container: Container,
    hrp: &str,
    mut jumbled: Vec<u8>,
) -> Result<Vec<RawItem>, EncodingError> {
    f4jumble_inv_mut(&mut jumbled)?;
    let mut padding = [0u8; UNIFIED_PADDING_LEN];
    padding[..hrp.len()].copy_from_slice(hrp.as_bytes());
    let split = jumbled.len() - UNIFIED_PADDING_LEN;
    if jumbled[split..] != padding {
        return Err(EncodingError::UnifiedPadding);
    }
    let mut rest = &jumbled[..split];
    let mut items = Vec::new();
    while !rest.is_empty() {
        let typecode = compact_size_read(&mut rest)? as u32;
        let len = compact_size_read(&mut rest)? as usize;
        if rest.len() < len {
            return Err(EncodingError::Truncated);
        }
        let (data, tail) = rest.split_at(len);
        items.push((typecode, data.to_vec()));
        rest = tail;
    }
    unified_validate(container, &items, false)?;
    Ok(items)
}

fn unified_decode(container: Container, s: &str) -> Result<(Network, Vec<RawItem>), EncodingError> {
    let (hrp, jumbled) = bech32_decode(Bech32Variant::Bech32m, s)?;
    let network = container.network(&hrp).ok_or(EncodingError::Hrp)?;
    Ok((network, unified_parse(container, &hrp, jumbled)?))
}

impl Receiver {
    fn to_raw(&self) -> RawItem {
        match self {
            Receiver::P2pkh(d) => (TYPECODE_P2PKH, d.to_vec()),
            Receiver::P2sh(d) => (TYPECODE_P2SH, d.to_vec()),
            Receiver::Sapling(d) => (TYPECODE_SAPLING, d.to_vec()),
            Receiver::Orchard(d) => (TYPECODE_ORCHARD, d.to_vec()),
            Receiver::Unknown { typecode, data } => (*typecode, data.clone()),
        }
    }

    fn from_raw((typecode, data): RawItem) -> Self {
        // `unified_validate` has checked the length of every known typecode.
        match typecode {
            TYPECODE_P2PKH => Receiver::P2pkh(data.try_into().expect("checked length")),
            TYPECODE_P2SH => Receiver::P2sh(data.try_into().expect("checked length")),
            TYPECODE_SAPLING => Receiver::Sapling(data.try_into().expect("checked length")),
            TYPECODE_ORCHARD => Receiver::Orchard(data.try_into().expect("checked length")),
            _ => Receiver::Unknown { typecode, data },
        }
    }
}

impl FvkItem {
    fn to_raw(&self) -> RawItem {
        match self {
            FvkItem::P2pkh(d) => (TYPECODE_P2PKH, d.to_vec()),
            FvkItem::Sapling(d) => (TYPECODE_SAPLING, d.to_vec()),
            FvkItem::Orchard(d) => (TYPECODE_ORCHARD, d.to_vec()),
            FvkItem::Unknown { typecode, data } => (*typecode, data.clone()),
        }
    }

    fn from_raw((typecode, data): RawItem) -> Self {
        match typecode {
            TYPECODE_P2PKH => FvkItem::P2pkh(data.try_into().expect("checked length")),
            TYPECODE_SAPLING => FvkItem::Sapling(data.try_into().expect("checked length")),
            TYPECODE_ORCHARD => FvkItem::Orchard(data.try_into().expect("checked length")),
            _ => FvkItem::Unknown { typecode, data },
        }
    }
}

impl IvkItem {
    fn to_raw(&self) -> RawItem {
        match self {
            IvkItem::P2pkh(d) => (TYPECODE_P2PKH, d.to_vec()),
            IvkItem::Sapling(d) => (TYPECODE_SAPLING, d.to_vec()),
            IvkItem::Orchard(d) => (TYPECODE_ORCHARD, d.to_vec()),
            IvkItem::Unknown { typecode, data } => (*typecode, data.clone()),
        }
    }

    fn from_raw((typecode, data): RawItem) -> Self {
        match typecode {
            TYPECODE_P2PKH => IvkItem::P2pkh(data.try_into().expect("checked length")),
            TYPECODE_SAPLING => IvkItem::Sapling(data.try_into().expect("checked length")),
            TYPECODE_ORCHARD => IvkItem::Orchard(data.try_into().expect("checked length")),
            _ => IvkItem::Unknown { typecode, data },
        }
    }
}

/// Encodes a Revision 0 Unified Address (`u1...`, `utest1...`). Receivers are written in
/// ascending typecode order whatever order they are given in; a set that ZIP 316 does not
/// allow is refused.
pub fn encode_unified_address(
    network: Network,
    receivers: &[Receiver],
) -> Result<String, EncodingError> {
    let items = receivers.iter().map(Receiver::to_raw).collect();
    unified_encode(Container::Address, network, items)
}

/// Decodes a Revision 0 Unified Address into its receivers, in encoding order.
pub fn decode_unified_address(s: &str) -> Result<(Network, Vec<Receiver>), EncodingError> {
    let (network, items) = unified_decode(Container::Address, s)?;
    Ok((network, items.into_iter().map(Receiver::from_raw).collect()))
}

/// Encodes a Revision 0 Unified Full Viewing Key (`uview1...`, `uviewtest1...`).
pub fn encode_unified_fvk(network: Network, items: &[FvkItem]) -> Result<String, EncodingError> {
    let items = items.iter().map(FvkItem::to_raw).collect();
    unified_encode(Container::Fvk, network, items)
}

/// Decodes a Revision 0 Unified Full Viewing Key into its items, in encoding order.
pub fn decode_unified_fvk(s: &str) -> Result<(Network, Vec<FvkItem>), EncodingError> {
    let (network, items) = unified_decode(Container::Fvk, s)?;
    Ok((network, items.into_iter().map(FvkItem::from_raw).collect()))
}

/// Encodes a Revision 0 Unified Incoming Viewing Key (`uivk1...`, `uivktest1...`).
pub fn encode_unified_ivk(network: Network, items: &[IvkItem]) -> Result<String, EncodingError> {
    let items = items.iter().map(IvkItem::to_raw).collect();
    unified_encode(Container::Ivk, network, items)
}

/// Decodes a Revision 0 Unified Incoming Viewing Key into its items, in encoding order.
pub fn decode_unified_ivk(s: &str) -> Result<(Network, Vec<IvkItem>), EncodingError> {
    let (network, items) = unified_decode(Container::Ivk, s)?;
    Ok((network, items.into_iter().map(IvkItem::from_raw).collect()))
}

// ---------------------------------------------------------------------------------------
// Sapling payment addresses.
// ---------------------------------------------------------------------------------------

const fn sapling_address_hrp(network: Network) -> &'static str {
    match network {
        Network::Main => "zs",
        Network::Test => "ztestsapling",
    }
}

/// The Bech32 encoding of a raw Sapling payment address `d (11) || pk_d (32)` (protocol
/// specification section 5.6.3.1).
pub fn encode_sapling_address(network: Network, raw: &[u8; 43]) -> String {
    bech32_encode(Bech32Variant::Bech32, sapling_address_hrp(network), raw)
        .expect("a fixed valid human-readable part")
}

/// Decodes a Sapling payment address into its 43 raw bytes. The bytes are not checked to
/// be a valid diversifier and `pk_d`.
pub fn decode_sapling_address(s: &str) -> Result<(Network, [u8; 43]), EncodingError> {
    let (hrp, data) = bech32_decode(Bech32Variant::Bech32, s)?;
    let network = [Network::Main, Network::Test]
        .into_iter()
        .find(|&n| sapling_address_hrp(n) == hrp)
        .ok_or(EncodingError::Hrp)?;
    let raw: [u8; 43] = data.try_into().map_err(|_| EncodingError::Length)?;
    Ok((network, raw))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hem::zcash::blake2::blake2b_512;
    use alloc::string::ToString;

    fn hex(s: &str) -> Vec<u8> {
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
            .collect()
    }

    fn arr<const N: usize>(s: &str) -> [u8; N] {
        hex(s).try_into().unwrap()
    }

    /// Replaces the character at `at` by a different one of the same alphabet.
    fn corrupt(s: &str, at: usize, a: char, b: char) -> String {
        let mut chars: Vec<char> = s.chars().collect();
        chars[at] = if chars[at] == a { b } else { a };
        chars.into_iter().collect()
    }

    // ---- transparent ----

    /// `zcash_keys` 0.17.0 `src/keys/transparent/test_vectors.rs` (from zcashd's
    /// `base58_keys_valid.json`): address, network, kind, hash from the script.
    const T_ADDRS: [(&str, Network, TransparentKind, &str); 8] = [
        (
            "t1T8yaLVhNqxA5KJcmiqqFN88e8DNp2PBfF",
            Network::Main,
            TransparentKind::P2pkh,
            "65a16059864a2fdbc7c99a4723a8395bc6f188eb",
        ),
        (
            "t3VDyGHn9mbyCf448m2cHTu5uXvsJpKHbiZ",
            Network::Main,
            TransparentKind::P2sh,
            "74f209f6ea907e2ea48f74fae05782ae8a665257",
        ),
        (
            "tmHMBeeYRuc2eVicLNfP15YLxbQsooCA6jb",
            Network::Test,
            TransparentKind::P2pkh,
            "53c0307d6851aa0ce7825ba883c6bd9ad242b486",
        ),
        (
            "t2Fbo6DBKKVYw1SfrY8bEgz56hYEhywhEN6",
            Network::Test,
            TransparentKind::P2sh,
            "6349a418fc4578d10a372b54b45c280cc8c4382f",
        ),
        (
            "t1TpfguJj5zxKUfWcsNTrh6eod2XXsTKtvB",
            Network::Main,
            TransparentKind::P2pkh,
            "6d23156cbbdcc82a5a47eee4c2c7c583c18b6bf4",
        ),
        (
            "t3hc9Y2stuEWjS2dRDtGdiu3enMpxAbeUiK",
            Network::Main,
            TransparentKind::P2sh,
            "fcc5460dd6e2487c7d75b1963625da0e8f4c5975",
        ),
        (
            "tmXm2g5ouU8Pzksmqx3KYmeoeaWrAvj3rB5",
            Network::Test,
            TransparentKind::P2pkh,
            "f1d470f9b02370fdec2e6b708b08ac431bf7a5f7",
        ),
        (
            "t2QYxHjM8btztWTsMnFnZNurm7RXENk9ZhR",
            Network::Test,
            TransparentKind::P2sh,
            "c579342c2c4c9220205e2cdc285617040c924a0a",
        ),
    ];

    #[test]
    fn transparent_addresses_match_zcashd_vectors() {
        for (addr, network, kind, hash) in T_ADDRS {
            let hash: [u8; 20] = arr(hash);
            assert_eq!(encode_transparent(network, kind, &hash), addr);
            assert_eq!(decode_transparent(addr), Ok((network, kind, hash)));
        }
    }

    #[test]
    fn transparent_decoder_rejects() {
        let good = T_ADDRS[0].0;
        assert_eq!(
            decode_transparent(&corrupt(good, 10, 'x', 'y')),
            Err(EncodingError::Base58Checksum)
        );
        // `0`, `O`, `I` and `l` are not Base58 characters.
        assert_eq!(
            decode_transparent(&corrupt(good, 10, '0', '0')),
            Err(EncodingError::Base58Character)
        );
        // A Bitcoin mainnet P2PKH address: valid Base58Check, 21-byte payload.
        assert_eq!(
            decode_transparent("1BvBMSEYstWetqTFn5Au4m4GFg7xJaNVN2"),
            Err(EncodingError::Length)
        );
        // A 22-byte payload under the Sprout address prefix bytes.
        let mut payload = [7u8; 22];
        payload[..2].copy_from_slice(&[0x16, 0x9a]);
        assert_eq!(
            decode_transparent(&base58check_encode(&payload)),
            Err(EncodingError::UnknownPrefix)
        );
        assert_eq!(decode_transparent(""), Err(EncodingError::Base58Checksum));
    }

    #[test]
    fn base58_keeps_leading_zeros() {
        // The Bitcoin address above is version byte 0 and a hash; the decoder must return
        // the zero byte and the encoder must write it back as `1`.
        let payload = base58check_decode("1BvBMSEYstWetqTFn5Au4m4GFg7xJaNVN2").unwrap();
        assert_eq!(payload.len(), 21);
        assert_eq!(payload[0], 0);
        assert_eq!(
            base58check_encode(&payload),
            "1BvBMSEYstWetqTFn5Au4m4GFg7xJaNVN2"
        );
        assert_eq!(base58_encode(&[0, 0, 1]), "112");
        assert_eq!(base58_decode("112"), Ok(vec![0, 0, 1]));
    }

    // ---- Bech32 ----

    #[test]
    fn bech32_bip_173_and_350_valid_strings() {
        // BIP 173 and BIP 350 "valid" lists (as in bech32 0.12.0 `tests/`).
        let bech32 = [
            "A12UEL5L",
            "a12uel5l",
            "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1tt5tgs",
            "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw",
            "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqc8247j",
            "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w",
            "?1ezyfcl",
        ];
        let bech32m = [
            "A1LQFN3A",
            "a1lqfn3a",
            "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11sg7hg6",
            "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx",
            "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllludsr8",
            "split1checkupstagehandshakeupstreamerranterredcaperredlc445v",
            "?1v759aa",
        ];
        for (variant, other, list) in [
            (Bech32Variant::Bech32, Bech32Variant::Bech32m, bech32),
            (Bech32Variant::Bech32m, Bech32Variant::Bech32, bech32m),
        ] {
            for s in list {
                let (hrp, values) = bech32_decode_u5(variant, s).unwrap();
                assert_eq!(
                    bech32_encode_u5(variant, &hrp, &values).unwrap(),
                    s.to_ascii_lowercase()
                );
                assert_eq!(
                    bech32_decode_u5(other, s),
                    Err(EncodingError::Bech32Checksum)
                );
            }
        }
        let (hrp, values) = bech32_decode_u5(
            Bech32Variant::Bech32,
            "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw",
        )
        .unwrap();
        assert_eq!(hrp, "abcdef");
        assert_eq!(values, (0..32).collect::<Vec<u8>>());
    }

    #[test]
    fn bech32_segwit_programs() {
        // BIP 173 / BIP 350 address vectors: witness version symbol, then the program.
        let (hrp, values) = bech32_decode_u5(
            Bech32Variant::Bech32,
            "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4",
        )
        .unwrap();
        assert_eq!(hrp, "bc");
        assert_eq!(values[0], 0);
        assert_eq!(
            bits_5_to_8(&values[1..]).unwrap(),
            hex("751e76e8199196d454941c45d1b3a323f1433bd6")
        );
        let (_, values) = bech32_decode_u5(
            Bech32Variant::Bech32m,
            "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0",
        )
        .unwrap();
        assert_eq!(values[0], 1);
        assert_eq!(
            bits_5_to_8(&values[1..]).unwrap(),
            hex("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
        );
    }

    #[test]
    fn bech32_decoder_rejects() {
        use Bech32Variant::{Bech32, Bech32m};
        // Invalid checksum (BIP 173 invalid address 1).
        assert_eq!(
            bech32_decode_u5(Bech32, "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5"),
            Err(EncodingError::Bech32Checksum)
        );
        // Mixed case (BIP 173 invalid address 6, BIP 350 invalid address 11).
        assert_eq!(
            bech32_decode_u5(
                Bech32,
                "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sL5k7"
            ),
            Err(EncodingError::MixedCase)
        );
        assert_eq!(
            bech32_decode_u5(
                Bech32m,
                "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq"
            ),
            Err(EncodingError::MixedCase)
        );
        // Invalid character in the checksum (BIP 350 invalid address 6).
        assert_eq!(
            bech32_decode_u5(
                Bech32m,
                "bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4"
            ),
            Err(EncodingError::Bech32Character)
        );
        // Zero padding of more than four bits (BIP 173 invalid address 7, BIP 350 12).
        for (variant, s) in [
            (Bech32, "bc1zw508d6qejxtdg4y5r3zarvaryvqyzf3du"),
            (
                Bech32m,
                "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf",
            ),
        ] {
            let (_, values) = bech32_decode_u5(variant, s).unwrap();
            assert_eq!(bits_5_to_8(&values[1..]), Err(EncodingError::Bech32Padding));
        }
        // Non-zero padding (BIP 173 invalid address 8, BIP 350 13).
        for (variant, s) in [
            (
                Bech32,
                "tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3pjxtptv",
            ),
            (
                Bech32m,
                "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j",
            ),
        ] {
            let (_, values) = bech32_decode_u5(variant, s).unwrap();
            assert_eq!(bits_5_to_8(&values[1..]), Err(EncodingError::Bech32Padding));
        }
        // No separator, empty human-readable part, short data part.
        assert_eq!(
            bech32_decode_u5(Bech32, "pzry9x0s0muk"),
            Err(EncodingError::Bech32Character)
        );
        assert_eq!(
            bech32_decode_u5(Bech32, "1pzry9x0s0muk"),
            Err(EncodingError::Hrp)
        );
        assert_eq!(
            bech32_decode_u5(Bech32, "li1dgmt3"),
            Err(EncodingError::Bech32Checksum)
        );
        assert_eq!(bech32_encode_u5(Bech32, "Ab", &[]), Err(EncodingError::Hrp));
    }

    // ---- Sapling payment addresses ----

    /// `zcash_keys` 0.17.0 `src/encoding.rs`, test `payment_address`.
    const SAPLING_RAW: &str =
        "0000000000000000000000308e119d72992b560d2650ffe0be7f3542fd97003cb7cc3abff81a7f9037f3ea";
    const SAPLING_MAIN: &str =
        "zs1qqqqqqqqqqqqqqqqqqcguyvaw2vjk4sdyeg0lc970u659lvhqq7t0np6hlup5lusxle75c8v35z";
    const SAPLING_TEST: &str =
        "ztestsapling1qqqqqqqqqqqqqqqqqqcguyvaw2vjk4sdyeg0lc970u659lvhqq7t0np6hlup5lusxle75ss7jnk";
    const SAPLING_REGTEST: &str = "zregtestsapling1qqqqqqqqqqqqqqqqqqcguyvaw2vjk4sdyeg0lc970u659lvhqq7t0np6hlup5lusxle7505hlz3";

    #[test]
    fn sapling_payment_address_vectors() {
        let raw: [u8; 43] = arr(SAPLING_RAW);
        assert_eq!(encode_sapling_address(Network::Main, &raw), SAPLING_MAIN);
        assert_eq!(encode_sapling_address(Network::Test, &raw), SAPLING_TEST);
        assert_eq!(
            decode_sapling_address(SAPLING_MAIN),
            Ok((Network::Main, raw))
        );
        assert_eq!(
            decode_sapling_address(SAPLING_TEST),
            Ok((Network::Test, raw))
        );
        assert_eq!(
            decode_sapling_address(&SAPLING_MAIN.to_ascii_uppercase()),
            Ok((Network::Main, raw))
        );
    }

    #[test]
    fn sapling_payment_address_decoder_rejects() {
        assert_eq!(
            decode_sapling_address(SAPLING_REGTEST),
            Err(EncodingError::Hrp)
        );
        assert_eq!(
            decode_sapling_address(&corrupt(SAPLING_MAIN, 20, 'q', 'p')),
            Err(EncodingError::Bech32Checksum)
        );
        // The same bytes under the Bech32m checksum.
        let raw: [u8; 43] = arr(SAPLING_RAW);
        let m = bech32_encode(Bech32Variant::Bech32m, "zs", &raw).unwrap();
        assert_eq!(
            decode_sapling_address(&m),
            Err(EncodingError::Bech32Checksum)
        );
        let short = bech32_encode(Bech32Variant::Bech32, "zs", &raw[..42]).unwrap();
        assert_eq!(decode_sapling_address(&short), Err(EncodingError::Length));
    }

    // ---- F4Jumble ----

    /// f4jumble.json: the six vectors of 48 to 193 bytes (`normal`, `jumbled`).
    const F4JUMBLE: [(&str, &str); 6] = [
        (
            "5d7a8f739a2d9e945b0ce152a8049e294c4d6e66b164939daffa2ef6ee6921481cdd86b3cc4318d9614fc820905d042b",
            "0304d029141b995da5387c125970673504d6c764d91ea6c082123770c7139ccd88ee27368cd0c0921a0444c8e5858d22",
        ),
        (
            "b1ef9ca3f24988c7b3534201cfb1cd8dbf69b8250c18ef41294ca97993db546c1fe01f7e9c8e36d6a5e29d4e30a73594bf5098421c69378af1e40f64e125946f",
            "5271fa3321f3adbcfb075196883d542b438ec6339176537daf859841fe6a56222bff76d1662b5509a9e1079e446eeedd2e683c31aae3ee1851d7954328526be1",
        ),
        (
            "62c2fa7b2fecbcb64b6968912a6381ce3dc166d56a1d62f5a8d7551db5fd9313e8c7203d996af7d477083756d59af80d06a745f44ab023752cb5b406ed8985e18130ab33362697b0e4e4c763ccb8f676495c222f7fba1e31defa3d5a57efc2e1e9b01a035587d5fb1a38e01d94903d3c3e0ad3360c1d3710acd20b183e31d49f",
            "498cf1b1ba6f4577effe64151d67469adc30acc325e326207e7d78487085b4162669f82f02f9774c0cc26ae6e1a76f1e266c6a9a8a2f4ffe8d2d676b1ed71cc47195a3f19208998f7d8cdfc0b74d2a96364d733a62b4273c77d9828aa1fa061588a7c4c88dd3d3dde02239557acfaad35c55854f4541e1a1b3bc8c17076e7316",
        ),
        (
            "25c9a138f49b1a537edcf04be34a9851a7af9db6990ed83dd64af3597c04323ea51b0052ad8084a8b9da948d320dadd64f5431e61ddf658d24ae67c22c8d1309131fc00fe7f235734276d38d47f1e191e00c7a1d48af046827591e9733a97fa6b679f3dc601d008285edcbdae69ce8fc1be4aac00ff2711ebd931de518856878f7",
            "7508a3a146714f229db91b543e240633ed57853f6451c9db6d64c6e86af1b88b28704f608582c53c51ce7d5b8548827a971d2b98d41b7f6258655902440cd66ee11e84dbfac7d2a43696fd0468810a3d9637c3fa58e7d2d341ef250fa09b9fb71a78a41d389370138a55ea58fcde779d714a04e0d30e61dc2d8be0da61cd684509",
        ),
        (
            "3476f21a482ec9378365c8f7393c94e2885315eb4671098b79535e790fe53e29fef2b3766697ac32b4f473f468a008e72389fc03880d780cb07fcfaabe3f1a84b27db59a4a153d882d2b2103596555ed9494c6ac893c49723833ec8926c1039586a7afcf4a0d9c731e985d99589c8bb838e8aaf745533ed9e8ae3a1cd074a51a20da8aba18d1dbebbc862ded42435e92476930d069896cff30eb414f727b89e001afa2fb8dc3436d75a4a6f26572504b192232ecb9f0c02411e52596bc5e9045",
            "5139912fe8b95492c12731995a0f4478dbeb81ec36653a21bc80d673f3c6a0feef70b6c566f9d34bb726c098648382d105afb19b2b8486b73cbd47a17a0d2d1fd593b14bb9826c5d114b850c6f0cf3083a6f61e38e42713a37ef7997ebd2b376c8a410d797b3932e5a6e39e726b2894ce79604b4ae3c00acaea3be2c1dfe697fa644755102cf9ad78794d0594585494fe38ab56fa6ef3271a68a33481015adf3944c115311421a7dc3ce73ef2abf47e18a6aca7f9dd25a85ce8dbd6f1ad89c8d",
        ),
        (
            "7e745939ffedbd12863ce71a02af117d417adb3d15cc54dcb1fce467500c6b8fb86b12b56da9c382857deecc40a98d5f2935395ee4762dd21afdbb5d47fa9a6dd984d567db2857b927b7fae2db587105415d4642789d38f50b8dbcc129cab3d17d19f3355bcf73cecb8cb8a5da01307152f13936a270572670dc82d39026c6cb4cd4b0f7f5aa2a4f5a5341ec5dd715406f2fdd2afa733f5f641c8c21862a1bafce2609d9eecfa158cfb5cd79f88008e315dc7d8388e76c1782fd2795d18a763624",
            "1a52585e652da6ea46994954905cb79f55fca58171a4d7f773a57d23ed9ddec0c745ef0f4588fa7b2b68d69cdd25e5eb0e08c20523a3957171f1730ab0636faee75da2dc9e89562f0653d4e9422179286ae8305f01371f47ab16eed692c3895ce2fd655e4b19651c35d83c81894f687055b581114440646508e39a49b0d5a99004560af7367cc2738344d4e797a995ed66df72228e3d3746674337104700144c73b6db27d238c9e1770662feb0957d5028b5086f3839aacf275022dd7e7e983b6d",
        ),
    ];
    /// f4jumble_long.json, both vectors (`length`, `jumbled_hash`).
    const F4JUMBLE_LONG: [(usize, &str); 2] = [
        (
            3246395,
            "3fc2ecdfb68696571d89e8beddb647e6990b63a0171c36442273d687bd99257ec5002ec8197801b621732d6b05b8d70f688620a4c08873c12e4439a0127dc945",
        ),
        (
            4194368,
            "a5f18f163e598d4adb6ea7248057e24c1b61f29b33b7abcdabd420a0f2ee6c3ed31394652f28b59c44d3ea9ecf85f4d501e6aac14df288efd62cf80d1829d025",
        ),
    ];
    /// unified_address.json: two vectors of each receiver combination in the file
    /// (`p2pkh`, `p2sh`, `sapling`, `orchard`, unknown typecode or 0, unknown bytes,
    /// address). An empty string is an absent receiver.
    #[allow(clippy::type_complexity)]
    const UNIFIED_ADDRESSES: [(&str, &str, &str, &str, u32, &str, &str); 20] = [
        (
            "7bb83570b8fae146e03c5331a020b1e0892f631d",
            "",
            "d8ef8293d26de832e7193f296ba1922d90f122c6135bc231eebd91efdb03b1a8606771cd4fd6480574d43e",
            "",
            0,
            "",
            "u1l8xunezsvhq8fgzfl7404m450nwnd76zshscn6nfys7vyz2ywyh4cc5daaq0c7q2su5lqfh23sp7fkf3kt27ve5948mzpfdvckzaect2jtte308mkwlycj2u0eac077wu70vqcetkxf",
        ),
        (
            "a7244a362f49f29644a955cf0039b88a61657861",
            "",
            "435b0bbc95b5b7d52531a3944f2b85603ee22aaf850963bc156eb561edf2cbe7cf0e770e393ae5d7049026",
            "",
            0,
            "",
            "u1fl5mprj0t9p4jg92hjjy8q5myvwc60c9wv0xachauqpn3c3k4xwzlaueafq27dcg7tzzzaz5jl8tyj93wgs983y0jq0qfhzu6n4r8rakpv5f4gg2lrw4z6pyqqcrcqx04d38yunc6je",
        ),
        (
            "cad268758c5e71493066446b98e71df9d1d6a5ca",
            "",
            "9f6e0bf90a18fc0b9b83ae9f23ad4358648638482b5def8975635b66fd8a708335f9235a3186ec0f033f84",
            "cecbe5e689a453a3fe10ccf7617e6c1fb382819d7fc9200a1f42092ac84a30378f8c1fb90dff71a6d5042d",
            0,
            "",
            "u1pg2aaph7jp8rpf6yhsza25722sg5fcn3vaca6ze27hqjw7jvvhhuxkpcg0ge9xh6drsgdkda8qjq5chpehkcpxf87rnjryjqwymdheptpvnljqqrjqzjwkc2ma6hcq666kgwfytxwac8eyex6ndgr6ezte66706e3vaqrd25dzvzkc69kw0jgywtd0cmq52q5lkw6uh7hyvzjse8ksx",
        ),
        (
            "8d653347a0fd3cd0842a790a5eaf89d8e3854659",
            "",
            "e1adf156a07d56bcac91bdb2f7bb3ea7c44569dcfee54273c09e8065807b6823faa94a77219554d0f6e017",
            "24f8a60cbd97e012618d56054ad39241411a28fdd50ee35efa91152f60d5fa21172e5d458ddbcb6b709896",
            0,
            "",
            "u19mzuf4l37ny393m59v4mxx4t3uyxkh7qpqjdfvlfk9f504cv9w4fpl7cql0kqvssz8jay8mgl8lnrtvg6yzh9pranjj963acc3h2z2qt7007du0lsmdf862dyy40c3wmt0kq35k5z836tfljgzsqtdsccchayfjpygqzkx24l77ga3ngfgskqddyepz8we7ny4ggmt7q48cgvgu57mz",
        ),
        (
            "",
            "",
            "88533c398a49c2513dc85162bf220abaf47dc983f14e908ddaaa7322dba16531bc62efe750fe575c8d149b",
            "953f3c78d103c32b60559299462ebb27348964b892acad10482fe502c99f0d524959ba7be4f188e3a27138",
            0,
            "",
            "u1ay3aawlldjrmxqnjf5medr5ma6p3acnet464ht8lmwplq5cd3ugytcmlf96rrmtgwldc75x94qn4n8pgen36y8tywlq6yjk7lkf3fa8wzjrav8z2xpxqnrnmjxh8tmz6jhfh425t7f3vy6p4pd3zmqayq49efl2c4xydc0gszg660q9p",
        ),
        (
            "",
            "",
            "616fe1a9d887148d6ca10f48ccd92d0dcad24f7c4c9d73ee8122b1766459b04dac4dc07e80edb9d229bbbc",
            "cc802699330bc4748e34dd598c7124e72299e6a6d5bcc32e90409c8024868b2705aadfab6068d458f69b0c",
            0,
            "",
            "u19a4vmx7ysmtavmnaz4d2dgl9pyshexw35rl5ezg5dkkxktg08p42lng7kf9hqtn2fhr63qzyhe8gtnvgtfl9yvne46x6zfzwgedx7c0chnrxty0k5r5qqph8k02zs8e3keul9vj8myju7rvqgjaysa9kt0fucxpzuky6kf0pjgy0a6hx",
        ),
        (
            "871a089d446268aa7ac03d2a6f60ae70808f3974",
            "",
            "",
            "31844683a07bf8e30057902b0d23e2b2ce9cad0b22190238ca4f329da92c7979052b00f735cb210671bdb0",
            0,
            "",
            "u1snf9yr883aj2hm8pksp9aymnqdwzy42rpzuffevj35hhxeckays5pcpeq7vy2mtgzlcuc4mnh9443qnuyje0yx6h59angywka4v2ap6kchh2j96ezf9w0c0auyz3wwts2lx5gmk2sk9",
        ),
        (
            "7cb07c31b58040ac7cc12bfaaa138cfbefb38457",
            "",
            "",
            "05683c0303858388a785b4cf15d41ac69e1d435b0ad23838e18d62f7ec41c37fc86af71dffd94dfff6b207",
            0,
            "",
            "u1szwcx2zdxalyp7cfqwrptv95rnpyajejs6jmwacz4cgm2g3vzdxl5perhpg3nyhnuplvptdr4g63gupdfj5zal9v35s3e6adqsckv68hyrclan3gxaj6mz8aejzsnhqjyn32jcpnpra",
        ),
        (
            "06974d8bcd8ba8ef89ce36a653d93868251c2e3d",
            "",
            "",
            "3c40246912b6efefab9a55244ac2c174e1a9f8c0bc0fd526933963c6ecb9b84ec8b0f6b40dc858fa23c72b",
            65532,
            "d56a1d62f5a8d7551db5fd9313e8c7203d996af7d477083756d59af80d06a745f44ab023752cb5b406ed8985e18130ab33362697b0e4e4c763ccb8f676495c222f7fba1e31defa3d5a57efc2e1e9b01a035587d5fb1a38e01d94903d3c3e0ad3360c1d3710acd20b183e31d49f25c9a138f49b1a537edcf04be34a9851a7af9db6990ed83dd64af3597c04323ea51b0052ad8084a8b9da948d320dadd64f5431e61ddf658d24ae67c22c8d13",
            "u1en8ysypun4gdkdnu8zqqg6k73ankr9ffwfzg08wtzg9z939w0wupewemfrc8a630e8gc4uqucym0l4v44fszy3et4veyypt3jsyp0whfpfsn2lw30kj8nepe6wvvasf00wklh85u9v8glqndupmamk9z2ja9sanf70pp4yxvkt3dmyzxa0kkhv2c9pxmkghrxqk0590azvya3nzrtevj449nu3laskrhf7c7nj9cyw7ty38mccg4znrr876guu6pzndx7ngwzhmlsn8d89saf5araaacrhr9958xr6z23mj4qtzzn98whdpu8u7n8fhf5d2vypljda62q73du44sf0e0kxmq3gvgkta0qqgq9w6r403gc5jz2any02etmwlttkv84hgh95czhdf2jugk3u36ke0kchcthg240",
        ),
        (
            "cdd4b2be1b57f24c85fc1e43c77bb2da2d2646f1",
            "",
            "",
            "fc235122892d611e52ee5b447a77ec5a296213948fb56d721f66f264e32e7d0ce5473005fc4c0bcf421e8f",
            65532,
            "09131fc00fe7f235734276d38d47f1e191e00c7a1d48af046827591e9733a97fa6b679f3dc601d008285edcbdae69ce8fc1be4aac00ff2711ebd931de518856878f73476f21a482ec9378365c8f7393c94e2885315eb4671098b79535e790fe53e29fef2b3766697ac32b4f473f468a008e72389fc03880d780cb07fcfaabe3f1a84b27db59a4a153d882d2b2103596555ed9494c6ac893c49723833ec8926c1039586a7afcf4a0d9c731e98",
            "u1a7gz63aey4tnj4klwauth00vnkmltwafwzk9nld2ys7yz3yjzjcdp47crc37zc4g9aq4athg9zh8r792e44kd6g2f4drhsl5ph4ja8pe4gcc9yjyf3rn7pej808hcy6xh0x6y8khmzljehjlwqq4h2czp35vu3l7aa7rpw5vcng9gswwlaqn5ptes592wejx7f49rxsvmzeqjekjtyfevehanvyksa8gtkpk75yrqnam26hzuxrtm6agaluy4hv0ha4sg6h22394m0x5th6r8uj7svzlklaja852vv9ud5gznu2sqyrsqveqjmfk9rcs59sprjj8nrt2nke862xlhvjq9y9zswen27eqj5slg52q2zch59uzwaeat8jw6z6092uu8yqqnnj7h0yguhypgd8y2wu9ftgg38ym3",
        ),
        (
            "",
            "",
            "da2672c010f7364df6fad49dd39be0e4d4be73c45e239448fcc385cc68094bf36ddbc4ec0219b567955556",
            "",
            65533,
            "d17d19f3355bcf73cecb8cb8a5da01307152f13936a270572670dc82d39026c6cb4cd4b0f7f5aa2a4f5a5341ec5dd715406f2fdd2afa733f5f641c8c21862a1bafce2609d9eecfa158cfb5cd79f88008e315dc7d8388e76c1782fd2795d18a763624c25fa959cc97489ce75745824b77868c53239cfbdf73ca",
            "u1sem2gcey0emntrvxyjv8hyhq0w5fr4sxaj3cppgrfqgg6laydh8m78gy2cw2p54zzak3alnnsx4xjuhazpkrfcd90wl0c7ldj6y095hh5j6j2evry9vg5jqp4dyqpwqeryu7pes4sxyyyqwn6egs5daxk4473v9xpgzrwv5n0tvs93nlj4xpphq4vs2w8um9ph7zkte08t7fa509mnrt9apuhr22xq34mp2svjnq6rvfn0hg6lkehxtlj39vgjxjlkjfhx8rw2f02ckq8k5szcxsnhkgr2cqlmf2udl2gqdqr5t6",
        ),
        (
            "",
            "",
            "9b728ad6f50371e961236630b3c8cdd8149ca22cdb87a62cc0ba3e3cfd2b0adcc82930e447f8dcf54b450b",
            "",
            65533,
            "ec65604037314faaceb56218c6bd30f8374ac13386793f21a9fb80ad03bc0cda4a44946c00e1b1a1df0e5b87b5bece477a709649e950060591394812951e1fe3895b8cc3d14d2cf6556df6ed4b4ddd3d9a69f53357d7767f4f5ccbdbc596631277f8fecd08cb056b95e3025b9792fff7f244fc716269b926d6",
            "u10j2s9sy4dmuakf57z58jc5t8yuswega82jpd2hk3q62l6fsphwyjxvmvfwy8skvvvea6dnkl8l9zpjf3m27qsav9y9nlj59hagmjf5xh0xxyqr8lymnmtjn6gzgrn04dr5s0k9k9wuxc2udzjh4llv47zm6jn6ff0j65s54h3m6p0n9ajswrqzpvy8eh4d5pvypyc6rp5m07uwmjp4sr0upca5hl7gr4pxg45m7vlnx5r7va4n6mfyr98twvjrhcyalwhddelnnjrkhcj0wcp5eyas2c2kcadrxyzw28vvv47q74",
        ),
        (
            "",
            "",
            "",
            "e340636542ece1c81285ed4eab448adbb5a8c0f4d386eeff337e88e6915f6c3ec1b6ea835a88d56612d2bd",
            0,
            "",
            "u1ddnjsdcpm36r6aq79n3s68shjweksnmwtdltrh046s8m6xcws9ygyawalxx8n6hg6vegk0wh8zjnafxgh6msppjsljvyt0ynece3lvm0",
        ),
        (
            "",
            "",
            "",
            "3fadf8edb20a3301e8260aa311f4cbd54d7d6a76baac88c244b0b121c6dc22a8bcce15898e267829fc1e01",
            0,
            "",
            "u1nztelxna9h7w0vtpd2xjhxt4lpu8s9cmdl8n8vcr7actf2ny45nd07cy8cyuhuvw3axcp545y0ktq9cezuzx84jyhex8dk4tdvwhu4dl",
        ),
        (
            "",
            "",
            "99ae333db1074fca1a6a94bed3ea548c1db2512dfbe75af9e84c162260b4813bb6bdb4443969daa5713ff1",
            "cdf7fed0d0822fd849cffb20a4d5ee701ad8141e66d81ddfabf87875117c05092240603c546b8dc187cd8c",
            65532,
            "657b43ee8da645443814cc7329f3e9b4e54c236c29af3923101756d9fa4bd0f7d2ddaacb6b0f86a2658e0a07a05ac5b950051cd24c47a88d13d659ba2a46ca1830816d09cd7646f76f716abec5de",
            "u1xdrenc94696j8clxa2xnkdg8xd5t3y8s24urctyxu87vggv0u46qr4lkpnh7gqqdev9wwugt6xkv8c8du8ufhfl8nfjnzusf6cw20wpm85hlshmnmj2lkyhka9rua7qw7kr0xeajk7y2rlsuwl6z6l5l3wq3v6rrqt9e8zy7sc7pww45jznrj4xy6h9rp4kjy5xtl5upr30u4cyk58kv3t80k3p8w97k3e345h7avmjylxakx6sgyk5ss8th5kqay50ewav62eeep7tghzejaflsdstpwz55haex398jqpq27007me2",
        ),
        (
            "",
            "",
            "52d58f91376aa980f2b9a6283ff357e84246d6942352184886449ffea8fad7e7ca5b490d090a96e0323392",
            "e4e01051b99c08506834971f80dadec44a4da13ecdcba617f77fc48d25324f57cb1d4d7424705d573cd682",
            65532,
            "07fe9b523410806ea6f288f8736c23357c85f45791e1708029d9824d90704607f387a03e49bf9836574431345a7877efaa8a08e73081ef8d62cb780ab6883a50a0d470190dfba10a857f82842d38",
            "u1y647tzm2ms4stj8skfswfljmvatmhwqzjzl2uq5v3a78ys2mls2g9thdap4yfmr9tw6y5h9gnehzhpddyl43enmhd6xv2udcttqmas35l62jt2yar33jwr5eulchzxg3d8upf2raqcx3jup8s3dep6an5n5xh9ngdjfp4hjv8fwfhh34kvglsug57zf0duypq6ugmysw0mnhdg5fz9sndputdc7pdssg6k3ks76wrrnuu5najqxj8xchp5xv5ahfh3f2szrfl5cm6mslq2f69ja9r54plen209xwpdpwsvm6zep4gwl",
        ),
        (
            "",
            "",
            "",
            "6ed96d65379d5ece656901f5cb20cf554ce18600d4a1edcf6812f4459d7ff73cf2b88cd8476b75e8c08d28",
            65535,
            "34d6e84bf59c1e04619a7c23a996941d889e4622a9b9b1d59d5e319094318cd405ba27b7e2c084762d31453ec4549a4d97729d033460fcf89d6494f2ffd789e98082ea5ce9534b3acd60fe49e37e4f666931677319ed89f85588741b3128901a93bd78e4be0225a9e2692c77c969ed0176bdf9555948cbd5a332d045de6ba6bf4490adfe7444cd467a09075417fcc0062e49f008c51ad4227439c1b4476ccd8e97862dab7be1e8d399c05ef27c6e22ee273e15786e394c8f1be31682a30147963ac8da8d41d804258426a3f70289b8ad19d8de13be4eebe3bd4c8a6f55d6e0c373",
            "u1uehkuaq6rpfgt4ed5zpvhczg9apgpmyk5eq9qg23j8w7jxkhdnqzacte6gu8zgzfzgxy48ryzus3wnkhfxrxmlhs34xde3f34uxcnv3y6dsgj288vu56xs9f6ghvqsgkhuwtz4kkfxj8pa27v5p3ttlst340zvwx9nj6s0zw8p3wwk3zh37dwc7znqz52gj2fpaapzxzyagah0aeyxwa9fxxvyyj6w989v96ymsgf7s8s6ej9346p60fcjzzynvf9rmxevumdvt8l9mvhdfz4u5j4h7e0zjr2sde7fu7z9s02447qg6qzllm22egnx6ej6qczkkk2ygvpy08un9ggp853sddp6vskrlar6sygxec5f6c2t2eu9zmc728esy4sj9z853gxuplr6hw7lpcwzk20d85vuflnhlfv8nr3020r0v9z83ryudsyjv66rttxq2cscqlrdxakrmpjptzcf",
        ),
        (
            "",
            "",
            "",
            "b6f481042a780462ffa96f81e1288978e5f05c791587de7e957729bcac6eb95892532b0fe13e9c7eef6a24",
            65535,
            "d456851879f5fbc282db9e134806bff71e11bc33ab75dd6ca067fb73a043b646a7cf39cab4928386786d2f24141ee120fdc34d6764eafc66880ee0204f53cc1167ed20b43a52dea3ca7cff8ef35cd8e6d7c111a68ef44bcd0c1513ad47ca61c659cc5d325b440f6b9f59aff66879bb6688fd2859362b182f207b3175961f6411a493bffd048e7d0d87d82fe6f990a2b0a25f5aa0111a6e68f37bf6f3ac2d26b84686e569d58d99c1383597fad81193c4c1b16e6a90e2d507cdfe6fbdaa86163e9cf5de3100fbca7e8da047b090db9f37952fbfee76af61668190bd52ed490e677b",
            "u1m76hh3wch9vwctg92h0jjt8zu6dry4zl97q9q94huutng5sxyhlzgfj64jqnvla2vqrqe0ndt67td2kejv6zlcw9zeurexxs67l7y67p7mww2j2uvfsp6uynct2apcr0m9xrmswtktmgs3x2glvndrqazy0gyrp30j328h4m5gkju9rl3pfrtjn9tm8v0rzr6t8gkklqfxgwk976dvv4kh7hl5utp9gjryu8wwu80h733ss5cjwpeewdgd3l8h46c0c7hxz4c6daws3vurq2fj9h0hpjnycup9tu8nfahvqjxewyhyuzynnjxa7jrvw2ekdytqs7sn02gqx4vxtkjzfrcy67lkmr6p5kalj0g8apazeyzqw3ywppy9482wj8k4tm06573nr3h78ecq9n260g7c0hm5jm3ffa4g2vk0edpdsnemksdegxgt9s7h8v8pjmcp23rnahmzf8pxdtdt",
        ),
        (
            "",
            "",
            "eee19641bc6b802f353eb793f728b17a277ef0358696a24a7122bc56537b229647f3810d27ce45227c6f39",
            "",
            0,
            "",
            "u187vrwl4ampyxd5m6aj38n4ndkmj8v6gs97hkt23aps3sn5k89a0gk2smluexgdprcrtm56ezc5c7tjwlrnnl79tjtrxmqd42c5mpyz7g",
        ),
        (
            "",
            "",
            "50ca46f825f7f423007aa4147169b529f07f1c8ed634fafc8145a4813177dd1257ee8d8fc5f44e9b564f6a",
            "",
            0,
            "",
            "u1xd83nhheggwe78x3lvcygdl8cmwz3gfxnr02sytkxvfpwdep9dzl7vte48zhkx39s705yqp20rw4l835fhg3ylkde44l7glt3cyps5wk",
        ),
    ];
    /// unified_full_viewing_keys.json: two vectors of each item combination in the file (transparent
    /// key, Sapling item, Orchard item, unknown typecode or 0, unknown bytes, key).
    const UNIFIED_FVKS: [(&str, &str, &str, u32, &str, &str); 10] = [
        (
            "9ba0439c6a2d3d903883d4537c362288626da62c6299012e362d8fb6efebab4702ed638532c475f67400350fb1d6eda559cdc289a19b4319eb175140aa86893836",
            "",
            "7648764a4567b7165410bc313f922b72fa34153dcad112a3971620240ffbf30d7f19edb9f295cdf160be1863b41c96312daf7273ba01198f5066f28629b56f17e4ab726579eea0fb19ab5ae2b8889ce455c79c5959bfda796823ee805c794814",
            65533,
            "f6ee6921481cdd86b3cc4318d9614fc820905d042bb1ef9ca3f24988c7b3534201cfb1cd8dbf69b8250c18ef41294ca97993db546c1fe0",
            "uview1cgrqnry478ckvpr0f580t6fsahp0a5mj2e9xl7hv2d2jd4ldzy449mwwk2l9yeuts85wjls6hjtghdsy5vhhvmjdw3jxl3cxhrg3vs296a3czazrycrr5cywjhwc5c3ztfyjdhmz0exvzzeyejamyp0cr9z8f9wj0953fzht0m4lenk94t70ruwgjxag2tvp63wn9ftzhtkh20gyre3w5s24f6wlgqxnjh40gd2lxe75sf3z8h5y2x0atpxcyf9t3em4h0evvsftluruqne6w4sm066sw0qe5y8qg423grple5fftxrqyy7xmqmatv7nzd7tcjadu8f7mqz4l83jsyxy4t8pkayytyk7nrp467ds85knekdkvnd7hqkfer8mnqd7pv",
        ),
        (
            "fa9291b353be21ac452f85cb96e4fc978d352e34c5c0259ac28d0beab1b8e29803fc399e613d010865d5a1fa8765b7109f9db1ed56218983f9bd54b8c712478829",
            "",
            "b5523cae2a454d3dbcd88b8cebf4c4336db6f906264af982ab4dd4a797dd6f051a139b42cd6e6378ba7c9c7ae0a52dc311fd0a92730e56834c0ab07a99cea50b1160f497b619794819d5f654c57a60ed9e5358fb55aea05bac7133ee381a4324",
            0,
            "",
            "uview1672278wdrucacpeujnzt2tuhtdlj5e6ecjlgl72ul9rtud4ycnjactva9clneg2q39sva69kdx5frq0f4h7pk9y40zl3pgjffff9d6n0fxvjhpsk66zx5g5336hf8qrr3q0whm9tt5m58j8gssnykts6rsyl0e6hwulqr7wn6zyjt57d8us0ydqh722xcsg8vnr0sssczrdwk7mv5meheqg3r0try3druwk8cyeykzy86gucu2jmttvvzxcetclmkulq3ulrppfnd50zwplkvd5eqldmsw9c3ujws0fv",
        ),
        (
            "f6a704fc093882166a88eeb243e2658f0eb7b5b7943ce47c3924c67c96474cea029f1794895562430d5dc8be5e88cfeee3261d6be4e6eb5b238ecc9e7ebdeb1bf0",
            "0fec4a4553bde5638ff97ac262635ddce4fd10e9b9eedb3bf2b60a4cb01730e1971db5d0921a68a3e4d78379076f47fb26388a874a16c14dd21cacfc0f14475e4381ed27a5002ea7a9c87339d66ba14675e7f806d9580b2e71c4d166c15243a57b2ce29b1c441fb68534de0441e5d75c2da24667372d9ae6db6cf63693f44d86",
            "",
            0,
            "",
            "uview18jpf4cjyt5nfa747ua4sawtv9cppl8g576a4utmtslvenzm2ajyefz2fye2w7ljjm63f6r903fuhdm6fmvg3dnpgxw07tllfq7hcede8qyl2fanaarvsm8d0trz5ckc7k47dne78mfw5lrkgc883akkaw2vt37cdmvy6snapxufr857r5p9vmf9jx3s00w73we6fz4w49yy9wdc3u92krx0vs05t3c4r6favdtg9uj2tqs94skm5xdn9q4vpwgfmkcgwl3c8sj4epph8f69839q8p7pt86xvd5ejs7k87dn3tlwfenzqzlhalm7vwwaqy56mmdysdnqemmses6s653n6xq4",
        ),
        (
            "3ebe46d6204feeb43bd83511cd816134c2f03d8582c664318cc60063eca38a04020f8aed7690bc84e3fa6510c362bb9290904b6ff5b75e4e5ca6de821bf3389fae",
            "507cc7052c6a80b54f01eb8ffb6aed4e3d5ecc50f3447076612df3412d098256ac7767bd7c7b3e6705bc39c86a22800e76cd503258d9fa8fb8b28b719e98362bc697040a0f00c948ef2e110cb09bee90a4a7ebe424b058ec9d97272f9d4f9d687da2f89c201c6f5fa2ac7a7bf73ee32344d13d6f89e8960452613212fe98d0cc",
            "",
            0,
            "",
            "uview1aqjrk6swt0f8w23ev5gumkz3dn99097fa2ne8gpmtra7z0lt2xv8qp7vzvfgfxmcdzy8jtpftdujuvm7plle92476vws0m95zlffyp7rr0v2rzv6nyhrvh60at9qqswtj8yl44vt9gdwusz5l6p2dzczrm5zml3uqcudg9eeac4rg0v9yehquzh4x4l3wrc67mqu2uvqwt044jsvhv78hu5ghxtd7reycf3lwurxgyr5r872sssj8h6mr4crwc09n0d68c0ylswhxwy6k05vrk0t63k6ydcv578v8y4znastxpnrgwh0pa2hx7g9pr2z7dmwwwtfgcv3lyraxyt9s3eag3h",
        ),
        (
            "934d5c7b67ecebc7fe717ffba06f30973ecdb4735dd8c8173528c357ec23311f039efddc9cc1bf9f4214a09a7f0188540789b26197cdededc993be5381587f79de",
            "",
            "0572a55aa8d307c5be909a8f4ae2d9307292b9f7ba7ba7657193fbfa3cba7104cab2e3d78fb6bcb1c824f0b61c08185c0efb62e502dea31ec88145d295be4214a0b79dd0caa56c5fb2a53b78597c1be7663c5191fe1542e72d903273e653d901",
            0,
            "",
            "uview19emmwhm9qyrg3l3twe4l5x0dm4ur6q4nvs7w6mgurkk56nyzqr6j86fg6kwnsh0mah9q54gynmkxfasseck4k8pdvgsx8v2u8jdn08j8msrsnzphrhev8cq0scma9z3kkype8m6jmgjay6ncet9jjlpskzvyzxczfhhtvj47zze0ctrk3pa89j6cnmndn6ncrvfmms4h0s234pf6zmtt6njysvlqm5m44rv04g6d059gj8v3xdr5p2d3rnplm7hzmljjn8t5k89djpyl8r23gwswwyh03lvg6g8u4pan",
        ),
        (
            "",
            "",
            "dd7a56b35e69c4ad129df5aa0d3f087d4bcfc9090978b511c18cd39ce83a402c2fe1828d9d1f3a5f71e7ad056aa8e60e6f3fe4eabd258abe3c3316fb098d9115261c9a4499c984cd6a62e70c24967f1650d7c4354d60a8c4671a5c3a4d67380e",
            0,
            "",
            "uview18nq2gepps6tpwl9cagzljngkt334p53akqwkde2nh54xgptf3ccd4tyeh3glek9pmvk6axxks8yl9h75pquntlm9g9f7arhfr63n6907tnfaxs70nw4pu88fxsn3n8awp29cju7r4h5vvv25espnnny3sdkt69hgdgqehkalxwzegur8tz70jzc2ws2rk",
        ),
        (
            "",
            "",
            "48e057b53fc1c94392f04b631c1f4696fdefb74fb91ad813a91fd70290845e09a1d6cb1108385b9c20238733b3ca1b3586c5353ea6b323ad37413d001770c20b325f2e53aecdac5d36cb6585e402e96f9f079d3b888add2e6037f0a09ea8272f",
            0,
            "",
            "uview18dtp7qna4jcl9k8595lqxym4dehzmpsueh029gc7wqkrke6xdk28dyej6mcg20qn3e8hzdyvfy3jugw2yf7krpfkte6ff8adnjka9zx3agmcjpu7f8uvsc72a4acszhkmjgxmsv37ve3uz0sc2dqvuxfk25fphqcngy45teuevy2wvpgx0jt8wqsfqg7g",
        ),
        (
            "b60895766bdad050ed932d0099832255dc0966eab8f98a3b1577f450f226a9410295599fc048f2181156f9e453735d989eb61623f6eee8a060b8f3fa59666cdfe1",
            "65aeee89ce971199487ac959c2960cee07477bad7d07a4c71a363894d671edc7090213b1b25d74d9d07cbe5b5034248bad5bc5394972c8532ea24b3f3887f9e6d312ca8ed244af57ce0412209ba3d537bcac08bf7f64744100dafac55fb25629204f19a123bdbbba7159510e52376938fb893ebdadde04d5f0646a3ad0f4cbc6",
            "20f8c2edbe19901c0d1b5cc7ab185e67354511bfc5174fe6bc0e6362c5880b28fabbf237258f8d03b200ad7fe0f3fa7e80e628f2b745dc9983b038c3a81f8237b6654db322e68436a972c6d3bc56e5560fb8658055524a11d6ee62e5a7d7a516",
            0,
            "",
            "uview1qtdjghnl06nh4tuypvextrazr9uxes52h64wgh7xkwpf5ahvugkaevdswnryh83fwevdwr905f9gqgm7vx70q7p8grl6cj99zmhjmn7phge5qmp97fy04544kcey9m48yyrdqakl86azp44jmweyn9yy70qhjp0rdyq0j34umhahesy6tsu78syu2s92gwcgexkk53qktsk4cuk85maezc0xqrx2ky779mgx047206wnq9vs4jvquf6z79v4d86x0hn2gfj3pe7nhusw5n4ryq3u4urs2k9d0y4lnhxzrdvhsgext5vc26fgt7zpr67vgdn9rlgnv9mkcnnj8pcxe70z4ktvef7mfp235frwavsp49pf0gcz0yxjhdgw3tf9l2eq6pm3vch44xtu3nsdwr6nfuus7887r2hdfrsny40sjx74cc5k500x009q0gv222af5plg7acngnc96apy696q3fyr34zgk6lfey0948tkrkn7cyr6v5e8",
        ),
        (
            "",
            "82c3b3d788f6cc8714421d6b74c20b5bc58debd9a33e24b4be99a4c601959b34d8436534693bb2f793ad6e4b488d9c7e202771f11cae68405ec816c71b4a906401d4cb12115fbd978735bf537d8589154a8a84ca61d6c202b60477107a5e0cf8de349c22cd8bfab48e92e90834504d65a438ab76010e3bab7437153a79755d17",
            "",
            0,
            "",
            "uview1krnvjn9nk9ysyzazqctrwct7xpkp75hr09zu8laz8ae5kuj9tgujr5ufm2fadxmyr9cl2ycsmeednh4jdeyt7ttzq7c7rjhqn7w3wq50l2xec85stczj2wvp7cu6uc2du6ye00q00fg90vnfwrwyuwfctnfzwk6zk489q0avc4juehte32lktanszeu7h8zus0xp3cg6sk8nstahex05watuw05e483qyhnf6r2dxv5qyte3",
        ),
        (
            "6f5ea3456800b2fcd67d451af033ac9e0978ceed3b4dc656c420fe6a313a040f03f9d51fdf9593ab447a1bc8a8ee8ee802ce85efbe7d2d0b3c2b9d15682a1d7ec0",
            "",
            "310e66c574051ac9d885f9fe9a4a7c0c76f32c60258e75a091b86117a733d024ae45b81a071cddb7e1095da271a20cd62a7e85e57167d10cc0aaf2e9fb081b3f47dbb1af9421a75be2ca3bac8b86a60ae8fe9af14f893c0c5714319b2a0b1f23",
            65533,
            "91e00c7a1d48af046827591e9733a97fa6b679f3dc601d008285edcbdae69ce8fc1be4aac00ff2711ebd931de518856878f73476f21a482ec9378365c8f7393c94e2885315eb4671098b79535e790fe53e29fef2b3766697ac32b4f473f468a008e72389fc03880d780cb07fcfaabe3f1a84b27db59a4a153d882d2b2103596555ed9494c6ac893c49723833ec8926c1",
            "uview1unwwq6rjtxhw7nhqp9grelqhdgdtg0zs8npa2dl92wmkspjxq50usmlhvjkjln2mnre5td82uvjz03039fppk0kh68l5krg5v3e0jpgdaz08qhlr2nad9g99f60xydehl76g85hvf0e2ayue9qvuu2ltymq5dm02hdy06hr39sj3pe0pfw3ghvrvlrf0psav8xv2qshzrcm72azxdaswqxgy2wyd2ur983vcxwldyfa0hkq6jqz4ld62mvudmhp37c73e78hd0c6zaf35yh2ga38h6qc0sn67c4uh823e0j7kzy3vlt3j44r9uzm3ajygdr84cm9jgyls7aqqs7xa6fzvu2998fkjgpm2pwgrpzprwvp9yh4eyzc523zegrp00qpfv3weyn4lssv4skwun9p9ghmuz0004ztgt3zerf9cldfjrpcxa0gzmp6faym688dqru50z9frvm8wr3awxw6je67fsu9983d62darra6dtwvtcc8vuse37zshng62jfydzsj294mafgtth40y",
        ),
    ];
    /// unified_incoming_viewing_keys.json: two vectors of each item combination in the file (transparent
    /// key, Sapling item, Orchard item, unknown typecode or 0, unknown bytes, key).
    const UNIFIED_IVKS: [(&str, &str, &str, u32, &str, &str); 13] = [
        (
            "42d67b570a664b8dc3cebb8f0af4243ff9e7e6e8d086084e2325678803b142d10387eba04dbfb406b2b2f046e661408459bc3d1e0e7aa0f147043b076d00d5e111",
            "",
            "aa47607810549c231e0e8415d5b932a7c9d9798ff11ecb9ca9dd892b9a43b23025b7227d3c54b8cdd380a2c64bcd461aca877bfa37b360f3fe69717bf31bc401",
            65533,
            "f6ee6921481cdd86b3cc4318d9614fc820905d042bb1ef9ca3f24988c7b3534201cfb1cd8dbf69b8250c18ef41294ca97993db546c1fe0",
            "uivk1djetqg3fws7y7qu5tekynvcdhz69gsyq07ewvppmzxdqhpfzdgmx8urnkqzv7ylz78ez43ux266pqjhecd59fzhn7wpe6zarnzh804hjtkyad25ryqla5pnc8p5wdl3phj9fczhz64zprun3ux7y9jc08567xryumuz59rjmg4uuflpjqwnq0j0tzce0x74t4tv3gfjq7nczkawxy6y7hse733ae3vw7qfjd0ss0pytvezxp42p6rrpzeh6t2zrz7zpjk0xhngcm6gwdppxs58jkx56gsfflugehf5vjlmu7vj3393gj6u37wenavtqyhdvcdeaj86s6jczl4zq",
        ),
        (
            "37a637e240128072ffe346f30d408860ab46ef542e30e31f3c0e589aee53f2c403744abcc9f8fa78571b5854068e2716976fb97d296e8720af3701e411fca2fc03",
            "",
            "dcb06b72b9bbaa7fac4a1fc8cbe121014516abb7481401228948d1b432821005939a2cad3f53d2cd03252b0c30123988d04cdcd090413700b0b9885696fe3219",
            0,
            "",
            "uivk1ctq5evjm2yr52k4zpdf4swtea4f8p6f3p9vh2pa7tsd8vafqj6rac5mj0kfupwj9es20spcfm66jh4yuh4xnazd28rapk2dj9w3g20rq7hc693mmzltf45au69ychg3jld36nm7uemz2lf45s4x5tf6hjzsghe5eugku2r3w9juj0t8yrwpv398djsf0vm6trg9nkcdtv7v6yzgwgn06w5hktgnxe2empdcquwld5m43kqcpcw9qv",
        ),
        (
            "337990744a6a643b895f714715b5e059b7807716d715f91812d26dcbf87fa3b6027f09e81a920cec15908be8c95d74f061f25698f8df46b9480777877aff5aa12b",
            "7b2ce29b1c441fb68534de0441e5d75c2da24667372d9ae6db6cf63693f44d86bcc4dc4510f83aef5a266ca049e832eb81f06c8a410be94613c267c8fd87b407",
            "",
            0,
            "",
            "uivk1dtzc2ay3jnzjtk93tsqxqn0fnef75lvpv3qc2zdtn6fxvjh3q2pz5r9ehd2c3mycen6mjh55kag3u936y8qzsr2wnvm4gtc76tg3s93cmre204ttjeunpc8ud9zq6w7z4kz27xhf2lwsu4cllk2me9ux84rtswhqstue8garyxz4x7fxmtye26udl34qexn9ykjpdd25mxgsvlj57yjljhaz8eurdf6umkc6mk6780m8y8qnnj683",
        ),
        (
            "daae5df91a1ef13f87a15522039618732fe838e2d08731c9e2eef31fcb12f8b50397a45934c752be23b170d8cbe60903917b9d1eea06eba205a9bac2d1d1fbadb5",
            "7da2f89c201c6f5fa2ac7a7bf73ee32344d13d6f89e8960452613212fe98d0ccef5f815d91a614121a5fb0aa6222c1f4c1d01e103115e4977c3be2d61ee50606",
            "",
            0,
            "",
            "uivk1uldmvh8ggsqj50kncwmzf5g9wtawtxz2ylpnj32dv4cfwg7329ae39fxw9fqvtuhr3h0newvr3lajq6rwdspv4fd3xq7swhhyfm52kmctndn3wpgsxse7cx2acta75tvlzzv58hx52um2qe0p8hywml4geklwg2kf23wavakrlqa9sgwzc37ej2krs6c5j5x2athd2aevywdg2gkpugts5n0f7yn579gedr42p96jut69aqtu3hyh",
        ),
        (
            "cec5ff35a0d7a907308242290096df9c8329f8967a3aa8e3c5b870a76204e0e6030f4fd21eacfed91ddd469b76aef9ae9234e9cd2882e7a4b0207012ad3838b24d",
            "",
            "8ad93cb898ca518f9b104752e92dd888f0cfefa89e961424fc238ff81eea51a2cc2321ff81d085ca03f0d46891521433e459165f1eb1712633bdfea6ea028131",
            0,
            "",
            "uivk1tm6fujj8k90lvts72davkt8nd6pucrp3jhr76zc7n5arws4a6vn7w0wrj47mtlrjuve6tc7vfp398wdxt0mc7g0xl6y73pu8lzvyglh0a2q9lae6ax0ek8fjl33dfvhnj9uhwqdefvaukw0j06hmga3zs433sdgnlvz6qpnqq3wx33tavd5fcqd5wsrg0tk6nk2el3s5tq7z9h9gla9yct59eaaztrhy7jazpf97fsc795snytwnl",
        ),
        (
            "",
            "",
            "994d637fb112cd191f7387e22640d585d6a7a05d8ee5f46c2db5832d6b99e4243dc033b88ea5cad99c24a62db7c5ce253e617da8dddc010ad81e63583b19681d",
            0,
            "",
            "uivk1cc3f8ep2w4fypdn56y7vyq2akr3dkc73ktt5acjdrsax029dwc04aedq2qt73akswj4ktverlljxurheyhg3ntvkea673rsvh95q43mcqzgdu402r4h3qg49h5xu92tuekjsz0mhqu",
        ),
        (
            "",
            "",
            "bb2244678a2aa718cd49f7f510d76422c948ef4d238e301c61aed5bd8db90ba5df323b4952e07c4f320e94499d5baede4f7409636314bf85227fb18111472525",
            0,
            "",
            "uivk1e4wf95tg7dzm20n64al269lzvht56tyxwsdlsuhkjm08ly7wdeq5f3uesavxg0uw3e0cfvqxamceldhl4fgmnd30h09dt24s0hmxjdxty7t78a7a38e2p3fyku5peyfrm24qqfusk6",
        ),
        (
            "ff43d48ff8be7faa6229adb478d8f3974c2f7fc6dc288b5febe88b8f92e239cb03bb94c3164cbcd022fb055e9cb0755b065e60d8fbf30dd91513428a6ee17fa720",
            "204f19a123bdbbba7159510e52376938fb893ebdadde04d5f0646a3ad0f4cbc67c74277a2206cf8ecbfc565cfb44765a6fbf3b66069f9d75b914c01345af8702",
            "82cc9d79742fe5ae9a142b9336a98677b154fe20401eb18998dbed915b0453ce6eb1b28062dbe644840487082089bf08e1f549a53226084252f9a7f98e41e820",
            0,
            "",
            "uivk1uy0jwv5l3h2us3ymnpxz4hxjkv24fm86xwyktq54y55nl0cwnvdpuh7m8f3p85et5u86wqw433lzj0seu2senvxnykdy54hpdlgq3m0vv4sn0n9e9g7en87esw6e9szn5d7kqmqutx9lt9czetl54gl5fznxh5z3h0599mjsncu32fdmrv2uf9j3eyg4m4wzdqxlukhumxspfdsg8sq57n37wqajvpgs57vxu60g99qe3wj92at9jjdl46mm9fxhqnjrg947rml22qzfxqerpawwdm44q2k20e57752th4vrx7xdjqkzs635y8ygwamc9nlrwy4djp4znlladgrv0xrx9xggtc",
        ),
        (
            "",
            "de349c22cd8bfab48e92e90834504d65a438ab76010e3bab7437153a79755d171e954da24e7ee5caed39936394a895457e048de71baada990590464dbdde5406",
            "",
            0,
            "",
            "uivk1mqattl4qc8wjgqqhmwq49an4njac8hvk5ds5rtfclgt9nssu23gwlrxaqlpmj7h3ftvfl64w0kqxqjlnk6enxclqqgygr706n56p8527yy8s32vyfg2fxmdwv7gxrvcrw5ss5h3yhf",
        ),
        (
            "13033bdea8c619d5a261d61a01fbf37e36500fdfc2aa0eeb5c03656ed3c433ab03294022bbb5c0a00796b4861b52cc716ff2703d35310d8f44a20855bb198aeb76",
            "",
            "b6438009b399eaad1eb18669a1ebf8e9242d46d8c4dcc4060d82bad1cbb16830fe30a5730c3820a56a2b7ba79b52e8d0e58706580d19b02aa7bcedf4eeea000e",
            65533,
            "91e00c7a1d48af046827591e9733a97fa6b679f3dc601d008285edcbdae69ce8fc1be4aac00ff2711ebd931de518856878f73476f21a482ec9378365c8f7393c94e2885315eb4671098b79535e790fe53e29fef2b3766697ac32b4f473f468a008e72389fc03880d780cb07fcfaabe3f1a84b27db59a4a153d882d2b2103596555ed9494c6ac893c49723833ec8926c1",
            "uivk1v756uxuu6amgn5axxm7er4zeag3hudhf3zrd9lcs28nvkchr942da2n6mq5vprgxl5k22tnsz56dc7f2v5xxyfrzt7jzla0kps5n6436z5fr0c30qhn94g7x5wnra9eu0rcpxrjgpvd4klr2rg5gnvt393szhvm9a8vj0epqlk3h2svk9zeaa0r8xw329ptxem7eh3t83pqashpchx7gga8lq2h0fd77q9udyyy0z2xsdr5zywja9wyvwt9mzcpp2ea9w306j6arthfvfr4q6nfqz6q9s654hazmk2q2ce58wmy0az4gdjar9yvrg3zyd4a97nz89k5md4ejcwjtlkjg67ntdshku9nstlnlr0ktp37yx3up5ka7pcqrpdkdyr5wec9fv5rsfwrgm7x26we5wpkqk3tskj2sffh8x9jqzdx9msswwgdaqz4qy7znw27p58m7pca7y2rrnyqfxy42m3zqvcfhsa",
        ),
        (
            "79d6e3b75d3c7891b8c084a2ce2ebcbb8a2d3ee650516943778c4b8b6e476752029e49c5c6003c1ab6b2f7d5346e13ed40ed58816eace415bf0cdaaa3e4a485da1",
            "0737d310920e67d83715ca4646d38d5ab5387e86db43751daa166840888724273ef42124959e5fa0d3216c2bf5e61ef7624326702cd687146e9022eda4a5d506",
            "d2743f76ce05ac16af7776d54988e43b72137da8716ef832ed6ca0cc68e0cfc284a966dc3e44c0907c06fea01a458b03940cbaab60fe8a15f063771ce4822512",
            0,
            "",
            "uivk19ewz2n6csd3tsvhv00s2as08pwypsp7ml3mfvauj7f09864xj8fhuwns2vwx4ykkuy2cekujx4arjpt6ye4l5qck9nne7gjep99l0w9asjagne4wfa67zqcc6l4c4l0qrsxxsjch74nt664hmnarnkplj4muvvc3rjlxdg9jtentjwas37p0wkdv5e2wv769nttr4cy3da8q928zvecrddhwkceppuz8y4rqhnasujedep2ej0kjcg8at9yh4nwqffe7eezrtr4gpgpymenkxyrsw02r677up39ewv03rfhyyw8uj24tgzpj2vjvt3zmt8yzz286428fpm9umh2cm0d7qwmvm7",
        ),
        (
            "",
            "60e3822c1e69731a1e5013c7055a4348cf53e8bde2758f95b87a3a43c9e6ff6dbbe59edb90b36af81e25153326b562aa7b3249dbd77904cfe52d2489c0931004",
            "d5878888c16b478f26a9e4d62340bce37690242e3e7fc0f27d68fd522803bd43c7bb455ba63907b0982c11223bec5c8d9cacc101e0eec4eae376a8083ba0d03e",
            0,
            "",
            "uivk1ayhxg3vt2zwfnm66dle9vfscal8cjwj330am3rgjn8z60cs3y5d0vdndt8yz8922axfmgfwcnkajhl7tl4pq4p0dj8n6l4268jz4k973lykywrtc5s2chsmpjy3zyf9597s638fn5ad5mwd3ep6juk6y7hka4ckd8kfaxhrtrlr2t9vd55pf9h5cuf02kvfscde7ejxx8rsx0vlghmavzgck45s30xevsh2nnxzmfjzjsnpxmw0",
        ),
        (
            "",
            "fd3dc2815d5052e67991abf2ef9742d788e7c45264af01b6237558157596ed96142cf5adbbc2f584ee00346badd66bb5c93258872cc8fa9a40fe56b8c984d307",
            "0d194b0ec31aee751bdc4d60a4d19eaf6480240420409c8952d8b077698d5e8f4c6aff998e44c8688a03f8b6ab5818077cbcaa645bb416157fa2c407dc3a4d04",
            0,
            "",
            "uivk17gx3lk7dzq3shnhxz2w50qgyamxf4jg46yv3mzf262kvmfqucexl2n3k0u4k0xvc95ngug2kz6jekjshjpqweuktqgrkw7plc85uhxjpvurqzjex95ug85322wkw07nx8hscuqzfl4u6sg349kzy8a53mkhkkqcnshzqr73cg3x95hlwefqzkxwyejccztqgans4x84t3wq8tlks92zx06ffjx4plehy08rw6h2kvurfcktsu2a",
        ),
    ];
    /// `zcash_address` 0.14.0 `src/kind/unified/ivk.rs`, tests `padding`, `truncated` and
    /// `only_transparent`: jumbled container bytes for the `uivk` prefix.
    const REF_INVALID_PADDING: &str = "babcc071cd3bfd9a32197eeb8aa76ed4accb59c25426c6ab71c7c3720ca9ada4ad8c9e357b4c5dc766128ac54289c17732dce84b5131300320e3b68cbbabe889f8edac6d8eb183e8921828701e817656b615";
    const REF_TRUNCATED_PADDING: &str = "96736a56bc4438e247411c70e40687beb690bdab1bd82710002130027787002596948f1e39d2d865b43c72d8acec5ba218623f0b88b441f1553953bf2ad6cfdd46b7d8c139344df9654914ab7c557b3947";
    const REF_TRUNCATED_SAPLING_DATA: &str = "cebcfec5ef2d0e66c28c34dc2e24d2c74bac36e04372a733a40ee0521564669236a7608e48e8b0304dcb0d6f05d4b8726adc6c5c0af8df955abae1aa8251e2708d1316886ac0c1993caf2c1654807e0bad312926dd7a559801180b1494b26b816773a6d02094173af9984358d601107332b499ad6bfec097afd2ee08e5836bb6d900ef84ffe858bae810ea2dee72f5d58ab51a";
    const REF_TRUNCATED_AFTER_SAPLING_TYPECODE: &str = "f703d8be6a27faa1d311ea2594e20bdeed6aaa08467de4b10ef1de61d795f78262327a738c5593a16375e2cacb73d5e5a3bdb3f226fa1ca2adb6d8215e080a82952174";
    const REF_ONLY_TRANSPARENT: &str = "125137c7ac8c0d133a5fc6845390f8e72334fbda493c871c8f1ae163badf776443cfdc371fd28960e37720d01c0540e54355c4e5f8aa0e7ae78c5315b88f90143330522b088990bdfea4b747209206f000f964";

    #[test]
    fn f4jumble_official_vectors() {
        for (normal, jumbled) in F4JUMBLE {
            let (normal, jumbled) = (hex(normal), hex(jumbled));
            assert_eq!(f4jumble(&normal).unwrap(), jumbled);
            assert_eq!(f4jumble_inv(&jumbled).unwrap(), normal);
        }
    }

    /// BLAKE2b-512 with an all-zero personalization is plain unkeyed BLAKE2b-512.
    fn plain_blake2b(data: &[u8]) -> Vec<u8> {
        blake2b_512(&[0; 16], &[data]).to_vec()
    }

    #[test]
    fn f4jumble_official_long_vectors() {
        // f4jumble_long.json: the message is `i & 0xff` and the vector is the plain
        // BLAKE2b-512 digest of the jumbled message.
        for (len, digest) in F4JUMBLE_LONG {
            let message: Vec<u8> = (0..len).map(|i| i as u8).collect();
            let jumbled = f4jumble(&message).unwrap();
            assert_eq!(plain_blake2b(&jumbled), hex(digest), "length {len}");
            assert_eq!(f4jumble_inv(&jumbled).unwrap(), message);
        }
    }

    #[test]
    fn f4jumble_length_limits() {
        assert_eq!(f4jumble(&[0; 37]), Err(EncodingError::F4JumbleLength));
        assert_eq!(f4jumble_inv(&[0; 37]), Err(EncodingError::F4JumbleLength));
        assert!(f4jumble(&[0; 38]).is_ok());
        assert_eq!(
            f4jumble(&vec![0; F4JUMBLE_MAX_LEN + 1]),
            Err(EncodingError::F4JumbleLength)
        );
    }

    // ---- unified containers ----

    fn opt<const N: usize>(s: &str) -> Option<[u8; N]> {
        (!s.is_empty()).then(|| arr(s))
    }

    #[test]
    fn unified_address_official_vectors() {
        for (p2pkh, p2sh, sapling, orchard, unknown_tc, unknown, encoded) in UNIFIED_ADDRESSES {
            // Preference order, to check that the encoder sorts.
            let mut receivers = Vec::new();
            if let Some(d) = opt(orchard) {
                receivers.push(Receiver::Orchard(d));
            }
            if let Some(d) = opt(sapling) {
                receivers.push(Receiver::Sapling(d));
            }
            if unknown_tc != 0 {
                receivers.push(Receiver::Unknown {
                    typecode: unknown_tc,
                    data: hex(unknown),
                });
            }
            if let Some(d) = opt(p2sh) {
                receivers.push(Receiver::P2sh(d));
            }
            if let Some(d) = opt(p2pkh) {
                receivers.push(Receiver::P2pkh(d));
            }
            assert_eq!(
                encode_unified_address(Network::Main, &receivers).unwrap(),
                encoded
            );
            let (network, mut decoded) = decode_unified_address(encoded).unwrap();
            assert_eq!(network, Network::Main);
            receivers.sort_by_key(|r| r.to_raw().0);
            decoded.sort_by_key(|r| r.to_raw().0);
            assert_eq!(decoded, receivers);
        }
        assert!(UNIFIED_ADDRESSES.len() >= 12);
        assert!(UNIFIED_ADDRESSES.iter().any(|v| v.4 != 0));
    }

    #[test]
    fn unified_fvk_official_vectors() {
        for (t_key, sapling, orchard, unknown_tc, unknown, encoded) in UNIFIED_FVKS {
            let mut items = Vec::new();
            if let Some(d) = opt(t_key) {
                items.push(FvkItem::P2pkh(d));
            }
            if let Some(d) = opt(sapling) {
                items.push(FvkItem::Sapling(d));
            }
            if let Some(d) = opt(orchard) {
                items.push(FvkItem::Orchard(d));
            }
            if unknown_tc != 0 {
                items.push(FvkItem::Unknown {
                    typecode: unknown_tc,
                    data: hex(unknown),
                });
            }
            assert_eq!(
                decode_unified_fvk(encoded),
                Ok((Network::Main, items.clone()))
            );
            items.reverse();
            assert_eq!(encode_unified_fvk(Network::Main, &items).unwrap(), encoded);
        }
        assert!(UNIFIED_FVKS.len() >= 8);
        assert!(UNIFIED_FVKS.iter().any(|v| v.3 != 0));
    }

    #[test]
    fn unified_ivk_official_vectors() {
        for (t_key, sapling, orchard, unknown_tc, unknown, encoded) in UNIFIED_IVKS {
            let mut items = Vec::new();
            if let Some(d) = opt(t_key) {
                items.push(IvkItem::P2pkh(d));
            }
            if let Some(d) = opt(sapling) {
                items.push(IvkItem::Sapling(d));
            }
            if let Some(d) = opt(orchard) {
                items.push(IvkItem::Orchard(d));
            }
            if unknown_tc != 0 {
                items.push(IvkItem::Unknown {
                    typecode: unknown_tc,
                    data: hex(unknown),
                });
            }
            assert_eq!(
                decode_unified_ivk(encoded),
                Ok((Network::Main, items.clone()))
            );
            items.reverse();
            assert_eq!(encode_unified_ivk(Network::Main, &items).unwrap(), encoded);
        }
        assert!(UNIFIED_IVKS.len() >= 6);
        assert!(UNIFIED_IVKS.iter().any(|v| v.3 != 0));
    }

    #[test]
    fn unified_testnet_roundtrip() {
        let receivers = [Receiver::Sapling([3; 43]), Receiver::Orchard([4; 43])];
        let s = encode_unified_address(Network::Test, &receivers).unwrap();
        assert!(s.starts_with("utest1"));
        assert_eq!(
            decode_unified_address(&s),
            Ok((Network::Test, receivers.to_vec()))
        );
        let items = [FvkItem::P2pkh([5; 65]), FvkItem::Orchard([6; 96])];
        let s = encode_unified_fvk(Network::Test, &items).unwrap();
        assert!(s.starts_with("uviewtest1"));
        assert_eq!(decode_unified_fvk(&s), Ok((Network::Test, items.to_vec())));
        let items = [IvkItem::Sapling([7; 64])];
        let s = encode_unified_ivk(Network::Test, &items).unwrap();
        assert!(s.starts_with("uivktest1"));
        assert_eq!(decode_unified_ivk(&s), Ok((Network::Test, items.to_vec())));
    }

    fn raw(typecode: u32, len: usize) -> RawItem {
        (typecode, vec![typecode as u8 ^ 0x5a; len])
    }

    #[test]
    fn unified_decoder_rejects_checksum_hrp_and_case() {
        let good = UNIFIED_ADDRESSES[0].6;
        assert_eq!(
            decode_unified_address(&corrupt(good, 30, 'q', 'p')),
            Err(EncodingError::Bech32Checksum)
        );
        let mixed = corrupt(good, 30, 'Q', 'P');
        assert_eq!(
            decode_unified_address(&mixed),
            Err(EncodingError::MixedCase)
        );
        // A valid container of another kind.
        assert_eq!(decode_unified_fvk(good), Err(EncodingError::Hrp));
        assert_eq!(
            decode_unified_ivk(UNIFIED_FVKS[0].5),
            Err(EncodingError::Hrp)
        );
        assert_eq!(
            decode_unified_address(UNIFIED_IVKS[0].5),
            Err(EncodingError::Hrp)
        );
        // The payload re-encoded under the testnet prefix: the checksum is valid and the
        // padding, which repeats the prefix, is not.
        let (_, payload) = bech32_decode(Bech32Variant::Bech32m, good).unwrap();
        let moved = bech32_encode(Bech32Variant::Bech32m, "utest", &payload).unwrap();
        assert_eq!(
            decode_unified_address(&moved),
            Err(EncodingError::UnifiedPadding)
        );
        // The same payload under the Bech32 checksum.
        let old = bech32_encode(Bech32Variant::Bech32, "u", &payload).unwrap();
        assert_eq!(
            decode_unified_address(&old),
            Err(EncodingError::Bech32Checksum)
        );
        // A Revision 2 prefix.
        let r2 = bech32_encode(Bech32Variant::Bech32m, "zu", &payload).unwrap();
        assert_eq!(decode_unified_address(&r2), Err(EncodingError::Hrp));
    }

    #[test]
    fn unified_decoder_rejects_reference_byte_vectors() {
        for (bytes, want) in [
            (REF_INVALID_PADDING, EncodingError::UnifiedPadding),
            (REF_TRUNCATED_PADDING, EncodingError::UnifiedPadding),
            (REF_TRUNCATED_SAPLING_DATA, EncodingError::Truncated),
            // The reference test accepts any encoding error for these bytes; they fail at
            // the padding check.
            (
                REF_TRUNCATED_AFTER_SAPLING_TYPECODE,
                EncodingError::UnifiedPadding,
            ),
            (REF_ONLY_TRANSPARENT, EncodingError::OnlyTransparent),
        ] {
            let s = bech32_encode(Bech32Variant::Bech32m, "uivk", &hex(bytes)).unwrap();
            assert_eq!(decode_unified_ivk(&s), Err(want), "{bytes}");
        }
    }

    #[test]
    fn unified_decoder_rejects_invalid_item_sets() {
        let cases: [(Vec<RawItem>, EncodingError); 12] = [
            // Wrong order.
            (vec![raw(3, 43), raw(2, 43)], EncodingError::ItemOrder),
            // Duplicate typecode.
            (
                vec![raw(2, 43), raw(2, 43)],
                EncodingError::DuplicateTypecode,
            ),
            // Both transparent kinds.
            (
                vec![raw(0, 20), raw(1, 20), raw(3, 43)],
                EncodingError::BothP2pkhAndP2sh,
            ),
            // Transparent only.
            (
                vec![raw(0, 20), raw(0xc0, 40)],
                EncodingError::OnlyTransparent,
            ),
            (vec![raw(1, 40)], EncodingError::ItemLength),
            // Metadata only.
            (vec![raw(0xc0, 40)], EncodingError::NoDataItems),
            // MUST-understand metadata in Revision 0.
            (
                vec![raw(3, 43), raw(0xe0, 4)],
                EncodingError::MustUnderstand,
            ),
            (
                vec![raw(3, 43), raw(0xfc, 4)],
                EncodingError::MustUnderstand,
            ),
            // Wrong lengths of known items.
            (vec![raw(3, 42)], EncodingError::ItemLength),
            (vec![raw(0, 21), raw(2, 43)], EncodingError::ItemLength),
            // Typecode above the CompactSize bound.
            (
                vec![raw(3, 43), raw(0x0200_0001, 4)],
                EncodingError::OutOfRange,
            ),
            // Too short for F4Jumble.
            (vec![raw(0xfffa, 10)], EncodingError::F4JumbleLength),
        ];
        for (items, want) in cases {
            match unified_encode_raw("u", &items) {
                Ok(s) => assert_eq!(decode_unified_address(&s), Err(want), "{items:?}"),
                Err(e) => assert_eq!(e, want, "{items:?}"),
            }
            assert_eq!(
                unified_validate(Container::Address, &items, true),
                Err(want)
            );
        }
        // The sets above that are valid once sorted or reduced do decode.
        let s = unified_encode_raw("u", &[raw(2, 43), raw(3, 43)]).unwrap();
        assert!(decode_unified_address(&s).is_ok());
        let s = unified_encode_raw("u", &[raw(1, 20), raw(3, 43), raw(0xc0, 4)]).unwrap();
        assert!(decode_unified_address(&s).is_ok());
    }

    #[test]
    fn unified_decoder_rejects_malformed_raw_encodings() {
        let jumble = |mut raw: Vec<u8>| -> String {
            let mut padding = [0u8; 16];
            padding[0] = b'u';
            raw.extend_from_slice(&padding);
            bech32_encode(Bech32Variant::Bech32m, "u", &f4jumble(&raw).unwrap()).unwrap()
        };
        // An Orchard receiver whose length is written as a three-byte CompactSize.
        let mut non_canonical = vec![3, 253, 43, 0];
        non_canonical.extend_from_slice(&[9; 43]);
        assert_eq!(
            decode_unified_address(&jumble(non_canonical)),
            Err(EncodingError::NonCanonicalCompactSize)
        );
        // A trailing byte after a complete item.
        let mut trailing = vec![3, 43];
        trailing.extend_from_slice(&[9; 43]);
        trailing.push(2);
        assert_eq!(
            decode_unified_address(&jumble(trailing)),
            Err(EncodingError::Truncated)
        );
        // A length beyond the bound.
        let mut long = vec![3, 254, 1, 0, 0, 2];
        long.extend_from_slice(&[9; 43]);
        assert_eq!(
            decode_unified_address(&jumble(long)),
            Err(EncodingError::OutOfRange)
        );
        // The well-formed version of the same container.
        let mut good = vec![3, 43];
        good.extend_from_slice(&[9; 43]);
        assert_eq!(
            decode_unified_address(&jumble(good)),
            Ok((Network::Main, vec![Receiver::Orchard([9; 43])]))
        );
    }

    #[test]
    fn unified_viewing_key_typecode_one() {
        // Revision 0: typecode 0x01 in a viewing key is unrecognised on decode and
        // refused on encode; it does not count as a shielded item.
        let with_orchard = [raw(0, 65), raw(1, 30), raw(3, 96)];
        let s = unified_encode_raw("uview", &with_orchard).unwrap();
        let (_, items) = decode_unified_fvk(&s).unwrap();
        assert_eq!(
            items[1],
            FvkItem::Unknown {
                typecode: 1,
                data: vec![1 ^ 0x5a; 30]
            }
        );
        assert_eq!(
            encode_unified_fvk(Network::Main, &items),
            Err(EncodingError::NotDefinedInRevision)
        );
        let s = unified_encode_raw("uivk", &[raw(0, 65), raw(1, 30)]).unwrap();
        assert_eq!(decode_unified_ivk(&s), Err(EncodingError::OnlyTransparent));
    }

    #[test]
    fn unified_encoder_refuses_invalid_sets() {
        assert_eq!(
            encode_unified_address(Network::Main, &[Receiver::P2pkh([1; 20])]),
            Err(EncodingError::OnlyTransparent)
        );
        assert_eq!(
            encode_unified_address(
                Network::Main,
                &[
                    Receiver::Orchard([1; 43]),
                    Receiver::P2sh([1; 20]),
                    Receiver::P2pkh([1; 20])
                ]
            ),
            Err(EncodingError::BothP2pkhAndP2sh)
        );
        assert_eq!(
            encode_unified_address(
                Network::Main,
                &[Receiver::Orchard([1; 43]), Receiver::Orchard([2; 43])]
            ),
            Err(EncodingError::DuplicateTypecode)
        );
        assert_eq!(
            encode_unified_address(Network::Main, &[]),
            Err(EncodingError::NoDataItems)
        );
        assert_eq!(
            encode_unified_address(
                Network::Main,
                &[
                    Receiver::Orchard([1; 43]),
                    Receiver::Unknown {
                        typecode: 2,
                        data: vec![0; 5]
                    }
                ]
            ),
            Err(EncodingError::ItemLength)
        );
        assert_eq!(
            UNIFIED_ADDRESSES[0].6.to_string(),
            encode_unified_address(
                Network::Main,
                &decode_unified_address(UNIFIED_ADDRESSES[0].6).unwrap().1
            )
            .unwrap()
        );
    }
}
