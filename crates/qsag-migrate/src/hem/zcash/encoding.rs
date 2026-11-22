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
